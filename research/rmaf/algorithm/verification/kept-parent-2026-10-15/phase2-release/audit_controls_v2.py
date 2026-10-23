"""Full source origin, dual inventory, literal axioms and rejection-gate replay."""
from pathlib import Path
import importlib.util,json,re,sys
sys.dont_write_bytecode=True
import rebuild as R

def main():
 H=R.helper();base=json.loads((R.ROOT/'research/rmaf/results/algorithm-kept-parent-fresh-review-rebuild-v2.json').read_text())
 modules=base['positive_modules']+['FreshReadout','FreshConsumer','FreshFalseTwins']
 text=H.audit_text(modules,'\nimport '.join(modules))
 (R.BUILD/'FreshFinalAuditV2.lean').write_text(text);a=H.run(R.BUILD,'FreshFinalAuditV2');assert a['exit']==0
 parsed=H.parse_audit(R.BUILD/'FreshFinalAuditV2.log',[m for m in modules if m!='Interfaces']);parsed['counts']['Interfaces']=0
 assert not parsed['forbidden'] and all(r['kind']!='axiom' for r in parsed['rows'])
 dual=text.replace('for (n, info) in env.constants do','for (n, info) in (env.constants.map₁.toList ++ env.constants.map₂.toList) do')
 assert dual!=text
 (R.BUILD/'FreshDualAuditV2.lean').write_text(dual);d=H.run(R.BUILD,'FreshDualAuditV2');assert d['exit']==0
 other=H.parse_audit(R.BUILD/'FreshDualAuditV2.log',[m for m in modules if m!='Interfaces'])
 key=lambda x:x['name'];assert sorted(parsed['rows'],key=key)==sorted(other['rows'],key=key)
 author=json.loads(R.CERT.read_text())
 assert {m:parsed['counts'][m] for m in author['module_origin_counts']}==author['module_origin_counts']
 # Force a full literal kernel axiom readout for EVERY positive theorem,
 # including private/generated theorems, in addition to every-constant closure.
 theorems=[r for r in parsed['rows'] if r['kind']=='theorem']
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
'''.replace('IMPORTS','\nimport '.join(modules)).replace('NAMES',', '.join('`'+m for m in modules))
 (R.BUILD/'FreshPrintedAxiomsV2.lean').write_text(printer)
 p=H.run(R.BUILD,'FreshPrintedAxiomsV2');assert p['exit']==0
 log=(R.BUILD/'FreshPrintedAxiomsV2.log').read_text()
 printed=[x for x in log.splitlines() if x.startswith('PRINT_ORIGIN|')]
 assert len(printed)==len(theorems),(len(printed),len(theorems))
 # Lexer strips nested comments and strings for an additional source gate.
 def code_only(src):
  out=[];i=0;depth=0;quoted=False
  while i<len(src):
   if depth:
    if src[i:i+2]=='/-':depth+=1;i+=2
    elif src[i:i+2]=='-/':depth-=1;i+=2
    else:i+=1
   elif quoted:
    if src[i]=='\\':i+=2
    elif src[i]=='"':quoted=False;i+=1
    else:i+=1
   elif src[i:i+2]=='/-':depth=1;i+=2
   elif src[i:i+2]=='--':
    j=src.find('\n',i);i=len(src) if j<0 else j
   elif src[i]=='"':quoted=True;i+=1
   else:out.append(src[i]);i+=1
  assert depth==0 and not quoted
  return ''.join(out)
 scans=[]
 for m in modules:
  path=R.BUILD/(m+'.lean');bad=re.findall(r'\b(?:sorry|admit|native_decide|axiom|unsafe|implemented_by|extern)\b',code_only(path.read_text()));assert not bad,(m,bad)
  scans.append({'module':m,'sha256':R.sha(path),'forbidden_source_tokens':bad})
 rows=parsed['rows'];names=[r['name'] for r in rows];assert len(names)==len(set(names))
 # Exercise exact inventory corruption detectors on actual, rather than toy,
 # records. Missing private/generated records and duplicates must fail.
 spec=importlib.util.spec_from_file_location('own_inventory_comparator',R.HERE.parent/'instrument.py');I=importlib.util.module_from_spec(spec);spec.loader.exec_module(I)
 private=next(r for r in rows if r['name'].startswith('_private.'))
 generated=next(r for r in rows if '.match_' in r['name'] or '.eq_' in r['name'])
 plants={'missing':rows[:-1],'duplicate':rows+[rows[0]],'missing-private':[r for r in rows if r['name']!=private['name']],'missing-generated':[r for r in rows if r['name']!=generated['name']]}
 assert I.exact_origins(rows,rows)
 catches={k:not I.exact_origins(rows,v) for k,v in plants.items()};assert all(catches.values())
 # COPY-only adapters inherited from the exact released stack; proof text is
 # compared to this reviewer's immutable original cut-package source copies.
 old=R.ROOT/'research/rmaf/algorithm/verification/core-completion-2026-10-15/phase2-release/isolated-cut'
 assert R.sha(old/'Coverage.lean')==R.sha(R.BUILD/'CutCoverage.lean')
 before=(old/'InitialCoverage.lean').read_text();after=(R.BUILD/'InitialCoverage.lean').read_text();assert before.replace('import Coverage\n','import CutCoverage\n',1)==after
 adapter={'CutCoverage':'filename only; identical original Coverage bytes','InitialCoverage':'one import Coverage -> CutCoverage; every other byte identical','original_initial_sha256':R.sha(old/'InitialCoverage.lean'),'mapped_initial_sha256':R.sha(R.BUILD/'InitialCoverage.lean')}
 # Retain the exact type/proof expression of the known lazy generated equation.
 expr='''import FreshConsumer
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
 (R.BUILD/'FreshHistoricalOrigin.lean').write_text(expr);e=H.run(R.BUILD,'FreshHistoricalOrigin');assert e['exit']==0
 fingerprint=R.sha(R.BUILD/'FreshHistoricalOrigin.log');assert fingerprint=='684dc9ed45b85799911abcf2595c33c5d14ed5f6a9703e3da3232cc02f44f399',fingerprint
 current_origin=next(r['module'] for r in rows if r['name']=='Universal233.CoreProgram.generate.eq_1')
 out={'status':'PASS_COMPLETE_ORIGINS_AND_STRICT_SOURCE_GATES','positive_modules':modules,'positive_module_count':len(modules),'audit':parsed,'audit_build':a,'dual_build':d,'dual_inventory_exact_match':True,'author_canonical_counts_exact_match':True,'literal_axiom_print_build':p,'literal_theorems_printed':len(theorems),'source_scans':scans,'actual_inventory_corruptions_caught':catches,'adapter':adapter,'lazy_generated_equation':{'name':'Universal233.CoreProgram.generate.eq_1','current_origin':current_origin,'historical_core_cut_origin':'InitialCoverage','historical_assembly_origin':'Entrypoint','exact_raw_type_and_proof_sha256':fingerprint},'all_main_milestones':'OPEN','replication_count_added':0}
 q=R.ROOT/'research/rmaf/results/algorithm-kept-parent-fresh-review-audit-v2.json';q.write_text(json.dumps(out,indent=2)+'\n');print(out['status'],len(modules),parsed['total'],len(theorems),current_origin)
if __name__=='__main__':main()
