"""Complete final origins, axioms, source/runtime pins and rejection controls."""
from pathlib import Path
import json,copy,re,subprocess,os
from rebuild import ROOT,HERE,run,digest,audit_text,parse_audit,H

def clean_source(s):
    out=[];i=0;depth=0;quote=False
    while i<len(s):
        if depth:
            if s.startswith('/-',i):depth+=1;i+=2
            elif s.startswith('-/',i):depth-=1;i+=2
            else:i+=1
        elif quote:
            if s[i]=='\\':i+=2
            elif s[i]=='"':quote=False;i+=1
            else:i+=1
        elif s.startswith('/-',i):depth=1;i+=2;out.append(' ')
        elif s.startswith('--',i):
            j=s.find('\n',i);i=len(s) if j<0 else j;out.append('\n')
        elif s[i]=='"':quote=True;i+=1;out.append(' ')
        else:out.append(s[i]);i+=1
    assert not depth and not quote
    return ''.join(out)

def main():
    root_result=ROOT/'research/rmaf/results'
    result=json.loads((root_result/'algorithm-assembly-fresh-review-completion-rebuild-v1.json').read_text())
    mods=[r['module'] for r in result['source_inputs']]+['NonauthorConsumer']
    b=HERE/'isolated-completion';builds=[]
    (b/'FreshFinalAudit.lean').write_text(audit_text(mods,'\nimport '.join(mods)))
    r=run(b,'FreshFinalAudit');builds.append(r);assert not r['exit']
    audit=parse_audit(b/'FreshFinalAudit.log',mods);assert not audit['forbidden']
    names=', '.join('`'+m for m in mods)
    ledger='''import IMPORTS
import Lean
open Lean Elab Command
run_cmd do
  let env ← getEnv
  let wanted : List Name := [NAMES]
  let ns := ((env.constants.map₁.toList ++ env.constants.map₂.toList).map (·.1)).filter fun n =>
    match env.getModuleIdxFor? n with
    | some idx => wanted.contains env.header.moduleNames[idx.toNat]!
    | none => false
  let ns := ns.eraseDups
  for n in ns do
    if let some idx := env.getModuleIdxFor? n then
      let m := env.header.moduleNames[idx.toNat]!
      if wanted.contains m then logInfo m!"LEDGER|{m}|{n}"
'''.replace('IMPORTS','\nimport '.join(mods)).replace('NAMES',names)
    (b/'FreshOriginLedger.lean').write_text(ledger);r=run(b,'FreshOriginLedger');builds.append(r);assert not r['exit']
    expected={(s.split('|')[1],s.split('|')[2]) for s in (b/'FreshOriginLedger.log').read_text().splitlines() if s.startswith('LEDGER|')}
    def reconcile(rows):
        actual={(r['module'],r['name']) for r in rows}
        assert len(actual)==len(rows),'duplicate record'
        assert actual==expected,'missing/extra/wrong-module private/generated declaration'
    reconcile(audit['rows'])
    forged=[]
    for label,predicate,operation in [
       ('missing-private',lambda r:r['name'].startswith('_private.'),'delete'),
       ('missing-generated',lambda r:'.eq_' in r['name'],'delete'),
       ('wrong-private-origin',lambda r:r['name'].startswith('_private.'),'origin'),
       ('wrong-public-origin',lambda r:r['name']=='Universal233.CoreProgram.generate','origin')]:
        rows=copy.deepcopy(audit['rows']);idx=next(i for i,r in enumerate(rows) if predicate(r))
        if operation=='delete':removed=rows.pop(idx)
        else:removed=copy.deepcopy(rows[idx]);rows[idx]['module']='ForgedOrigin'
        caught=False
        try:reconcile(rows)
        except AssertionError:caught=True
        assert caught;forged.append({'id':label,'caught':True,'affected':removed})
    printer='''import IMPORTS
import Lean
open Lean Elab Command
run_cmd do
  let env ← getEnv
  let wanted : List Name := [NAMES]
  let mut count : Nat := 0
  for (n,ci) in env.constants do
    if let some idx := env.getModuleIdxFor? n then
      let m := env.header.moduleNames[idx.toNat]!
      if wanted.contains m then
        match ci with
        | .thmInfo _ =>
          logInfo m!"PRINT_ORIGIN|{m}|{n}"
          elabCommand (← `(command| #print axioms $(mkIdent n)))
          count := count+1
        | _ => pure ()
  logInfo m!"PRINT_TOTAL|{count}"
'''.replace('IMPORTS','\nimport '.join(mods)).replace('NAMES',names)
    (b/'FreshPrintAxioms.lean').write_text(printer);r=run(b,'FreshPrintAxioms');builds.append(r);assert not r['exit']
    printed=sum(s.startswith('PRINT_ORIGIN|') for s in (b/'FreshPrintAxioms.log').read_text().splitlines())
    assert printed==sum(r['kind']=='theorem' for r in audit['rows'])
    scan=[]
    for m in mods:
        p=b/(m+'.lean');flags=re.findall(r'\b(?:sorry|admit|native_decide|axiom|unsafe|extern|implemented_by|csimp)\b',clean_source(p.read_text()))
        assert not flags,(m,flags)
        scan.append({'module':m,'source_sha256':digest(p),'flags':flags})
    # Copy ONLY immutable own prerelease toy sources. The unused axioms are
    # deliberately outside every positive package/consumer import.
    toy=HERE/'toy-gates';toy.mkdir(exist_ok=False);toy_rows=[]
    for m in ['CleanToy','UnusedPublicToy','UnusedPrivateToy','PrivateUsedToy']:
        original=HERE.parent/'toy-build-v1'/(m+'.lean');(toy/(m+'.lean')).write_bytes(original.read_bytes())
        r=run(toy,m,['-o',m+'.olean']);builds.append(r);assert not r['exit']
        (toy/(m+'Audit.lean')).write_text(audit_text([m],m));r=run(toy,m+'Audit');builds.append(r);assert not r['exit']
        a=parse_audit(toy/(m+'Audit.log'),[m]);assert bool(a['forbidden'])==(m!='CleanToy')
        if m.startswith('Unused'):
            assert not next(x for x in a['rows'] if x['kind']=='theorem')['axioms']
            assert any(x['kind']=='axiom' for x in a['rows'])
        toy_rows.append({'module':m,'original_source_sha256':digest(original),
          'copied_source_sha256':digest(toy/(m+'.lean')),'audit':a,
          'clean_twin_accepted':m=='CleanToy','custom_axiom_rejected':m!='CleanToy'})
    # Full project source pin and originating-name identity composition.
    package_rows={}
    for arm in ['assembly','mass','hard','completion']:
        d=json.loads((root_result/f'algorithm-assembly-fresh-review-{arm}-rebuild-v1.json').read_text())
        package_rows[arm]=d
    csrc={r['module']:r for r in package_rows['completion']['source_inputs']};composition=[]
    for arm in ['assembly','mass','hard']:
        equal=[];excluded=[]
        for s in package_rows[arm]['source_inputs']:
            final=csrc[s['module']]
            if s['compiled_sha256']==final['compiled_sha256']:equal.append(s['module'])
            else:
                assert arm=='hard' and s['module']=='Controls'
                excluded.append({'module':'Controls','reason':'independent hard fixture module not imported by final consumer; final Controls is SourceCoverage fixture module',
                  'hard_sha256':s['compiled_sha256'],'final_sha256':final['compiled_sha256']})
        composition.append({'arm':arm,'byte_identical_modules':equal,'explicit_fixture_exclusions':excluded})
    origins={}
    for arm,d in package_rows.items():
        for row in d['audit']['rows']:origins.setdefault(row['name'],{})[arm]=row['module']
    adoptions={n:x for n,x in origins.items() if len(set(x.values()))>1}
    assert not adoptions,'unexpected origin adoption among four released stacks'
    # Historical core cut isolation generated this theorem in InitialCoverage;
    # present complete stacks adopt Entrypoint. Compare exact raw Expr bytes.
    collision='''import HardPaid
import Lean
open Lean Elab Command
run_cmd do
  let env ← getEnv
  let some c := env.find? `Universal233.CoreProgram.generate.eq_1 | throwError "missing declaration"
  logInfo m!"DECL_TYPE|{repr c.type}"
  match c with
  | .thmInfo t => logInfo m!"DECL_VALUE|{repr t.value}"
  | _ => throwError "expected theorem"
'''
    (b/'FreshHistoricalOrigin.lean').write_text(collision);r=run(b,'FreshHistoricalOrigin');builds.append(r);assert not r['exit']
    fingerprint=digest(b/'FreshHistoricalOrigin.log');assert fingerprint=='684dc9ed45b85799911abcf2595c33c5d14ed5f6a9703e3da3232cc02f44f399'
    runtime={}
    for flag in ['--version','--print-prefix']:
        p=subprocess.run([str(H.LEAN),flag],cwd=b,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True);assert not p.returncode
        runtime[flag]=p.stdout.strip();(b/('runtime'+flag+'.log')).write_text(p.stdout)
    prefix=Path(runtime['--print-prefix']);runtime['files']={str(p):digest(p) for p in [H.LEAN,prefix/'bin/lean',prefix/'lib/lean/Std.olean',prefix/'lib/lean/Lean.olean']}
    report={'status':'PASS_FINAL_SOURCE_ORIGIN_AXIOM_AND_TOY_GATES','builds':builds,'audit':audit,
      'dual_origin_ledger_exact_match':True,'literal_print_axioms_count':printed,'positive_source_scan':scan,
      'forged_origin_records':forged,'toy_gates':toy_rows,'composition_source_identity':composition,
      'origin_adoptions_among_four_current_stacks':adoptions,
      'historical_core_adoption':{'name':'Universal233.CoreProgram.generate.eq_1','old_cut_isolation':'InitialCoverage',
       'current_completion':'Entrypoint','exact_raw_Expr_type_and_proof_sha256':fingerprint},
      'runtime':runtime,'all_main_milestones':'OPEN','replication_count_added':0}
    (root_result/'algorithm-assembly-fresh-review-final-audit-v1.json').write_text(json.dumps(report,indent=2)+'\n')
    print(report['status'],audit['total'],'all origins;',printed,'literal theorem axiom prints')

if __name__=='__main__':main()
