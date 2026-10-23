"""PRE-CANDIDATE compiled unused/public/private axiom rejection controls.

Imports Std/Lean only. No candidate source is available to this instrument.
"""
import os,subprocess,time,json,hashlib
from pathlib import Path

HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[4]
ALLOW={'propext','Quot.sound','Classical.choice'}

SOURCES={
  'CleanToy':'import Std\nprivate def hiddenData : Nat := 7\nprivate theorem hiddenTrue : True := True.intro\n',
  'UnusedPublicToy':'import Std\naxiom unusedPublicDebt : True\nprivate theorem cleanUnrelated : True := True.intro\n',
  'UnusedPrivateToy':'import Std\nprivate axiom unusedPrivateDebt : False\nprivate theorem cleanUnrelated : True := True.intro\n',
  'PrivateUsedToy':'import Std\nprivate axiom hiddenDebt : False\nprivate theorem hiddenClaim : False := hiddenDebt\n'}

def audit_source(module):
    return '''import MODULE
import Lean
open Lean Elab Command
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for (n,c) in env.constants do
    if let some idx := env.getModuleIdxFor? n then
      let m := env.header.moduleNames[idx.toNat]!
      if m == `MODULE then
        let axs ← collectAxioms n
        let k := match c with
          | .axiomInfo _ => "axiom"
          | .thmInfo _ => "theorem"
          | _ => "other"
        logInfo m!"TOY|{m}|{n}|{k}|{String.intercalate "," (axs.toList.map toString)}"
        count := count + 1
  logInfo m!"TOY_TOTAL|{count}"
'''.replace('MODULE',module)

def parse(text,expected_module):
    rows=[];counts=[]
    for s in text.splitlines():
        if s.startswith('TOY|'):
            _,m,n,k,a=s.split('|');rows.append({'module':m,'name':n,'kind':k,'axioms':a.split(',') if a else []})
        elif s.startswith('TOY_TOTAL|'):counts.append(int(s.split('|')[1]))
    assert counts==[len(rows)] and rows,'missing private/generated audit record'
    assert len({r['name'] for r in rows})==len(rows),'duplicate audit record'
    assert all(r['module']==expected_module for r in rows),'wrong module origin'
    bad=[r for r in rows if r['kind']=='axiom' or any(x not in ALLOW for x in r['axioms'])]
    return rows,bad

def main():
    freeze=json.loads((HERE/'FREEZE-v1.json').read_text())
    for r in freeze['before_execution_files']:
        assert hashlib.sha256((ROOT/r['path']).read_bytes()).hexdigest()==r['sha256']
    build=HERE/'toy-build-v1';build.mkdir(exist_ok=False)
    receipts=[];controls=[]
    def run(m,args=()):
        env=os.environ.copy();env['LEAN_PATH']=str(build);start=time.perf_counter()
        p=subprocess.run([str(ROOT/'bootloops-lean'),*args,m+'.lean'],cwd=build,env=env,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
        path=build/(m+'.log');path.write_bytes(p.stdout)
        r={'module':m,'exit':p.returncode,'seconds':time.perf_counter()-start,
           'source_sha256':hashlib.sha256((build/(m+'.lean')).read_bytes()).hexdigest(),
           'log':str(path.relative_to(ROOT)),'log_sha256':hashlib.sha256(path.read_bytes()).hexdigest()}
        receipts.append(r);assert not p.returncode,r
    for m,s in SOURCES.items():
        (build/(m+'.lean')).write_text(s);run(m,['-o',m+'.olean'])
        (build/(m+'Audit.lean')).write_text(audit_source(m));run(m+'Audit')
        text=(build/(m+'Audit.log')).read_text();rows,bad=parse(text,m)
        expected=m!='CleanToy';assert bool(bad)==expected
        if 'Unused' in m:
            # The axiom is unused by the unrelated theorem. Auditing that
            # theorem alone is therefore insufficient; origin enumeration wins.
            thm=next(r for r in rows if r['kind']=='theorem');assert not thm['axioms']
            assert any(r['kind']=='axiom' for r in bad)
        controls.append({'module':m,'rows':rows,'custom_axiom_caught':bool(bad),'clean_expected':not expected})
    text=(build/'CleanToyAudit.log').read_text()
    lines=text.splitlines();removed=next(i for i,s in enumerate(lines) if s.startswith('TOY|') and '|_private.' in s)
    omitted=lines.pop(removed);caught=False
    try:parse('\n'.join(lines),'CleanToy')
    except AssertionError:caught=True
    assert caught;(build/'MissingPrivate.log').write_text('\n'.join(lines)+'\n')
    origin=text.replace('TOY|CleanToy|','TOY|ForgedOrigin|',1);caught_origin=False
    try:parse(origin,'CleanToy')
    except AssertionError:caught_origin=True
    assert caught_origin;(build/'ForgedOrigin.log').write_text(origin)
    result={'status':'PASS_PRE_CANDIDATE_TOY_AXIOM_GATES','candidate_compiled':False,
      'receipts':receipts,'controls':controls,'unused_public_axiom_caught':True,
      'unused_private_axiom_caught':True,'private_used_axiom_caught':True,
      'missing_private_record_caught':caught,'omitted_record':omitted,
      'wrong_origin_record_caught':caught_origin,'replication_count_added':0}
    (ROOT/'research/rmaf/results/algorithm-assembly-prerelease-review-toy-gates-v1.json').write_text(json.dumps(result,indent=2)+'\n')
    print(result['status'],'unused public/private and used private axioms caught; clean twin passes')

if __name__=='__main__':main()
