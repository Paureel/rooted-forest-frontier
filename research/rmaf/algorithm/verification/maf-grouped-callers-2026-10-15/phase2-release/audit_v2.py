"""Final per-package complete origin/axiom/source/import/corruption gates."""
from pathlib import Path
import json,re,sys,copy
sys.dont_write_bytecode=True
import rebuild as R

def clean(src):
 out=[];i=0;depth=0;quote=False
 while i<len(src):
  if depth:
   if src[i:i+2]=='/-':depth+=1;i+=2
   elif src[i:i+2]=='-/':depth-=1;i+=2
   else:i+=1
  elif quote:
   if src[i]=='\\':i+=2
   elif src[i]=='"':quote=False;i+=1
   else:i+=1
  elif src[i:i+2]=='/-':depth=1;i+=2
  elif src[i:i+2]=='--':
   j=src.find('\n',i);i=len(src) if j<0 else j
  elif src[i]=='"':quote=True;i+=1
  else:out.append(src[i]);i+=1
 assert not depth and not quote;return ''.join(out)

def source_valid(row):
 src=R.ROOT/row['source'];frozen=R.ROOT/row['frozen_copy'];local=R.ROOT/row['local_copy'];mapping=row['import_only_mapping']
 if R.sha(src)!=row['source_sha256'] or R.sha(frozen)!=row['copy_sha256'] or R.sha(local)!=row['copy_sha256']:return False
 fixed=[]
 for line in src.read_text().splitlines(keepends=True):
  if line.startswith('import '):line='import '+' '.join(mapping.get(t,t) for t in line.strip().split()[1:])+ ('\n' if line.endswith('\n') else '')
  fixed.append(line)
 return ''.join(fixed)==local.read_text()

def main():
 H=R.helper();reports=[]
 for arm,suffix in [('maf','v1'),('groups','v2')]:
  base=json.loads((R.ROOT/f'research/rmaf/results/algorithm-maf-grouped-fresh-review-{arm}-rebuild-{suffix}.json').read_text());mods=base['modules']+['FreshReadout','FreshConsumer','FreshFalseTwins']+(['FreshChild'] if arm=='groups' else []);b=R.HERE/('isolated-'+arm)
  text=H.audit_text(mods,'\nimport '.join(mods));(b/'FreshFinalAudit.lean').write_text(text);a=H.run(b,'FreshFinalAudit');assert a['exit']==0
  parsed=H.parse_audit(b/'FreshFinalAudit.log',mods);assert not parsed['forbidden'] and all(r['kind']!='axiom' for r in parsed['rows'])
  dual=text.replace('for (n, info) in env.constants do','for (n, info) in (env.constants.map₁.toList ++ env.constants.map₂.toList) do');assert dual!=text;(b/'FreshDualAudit.lean').write_text(dual);d=H.run(b,'FreshDualAudit');assert d['exit']==0
  other=H.parse_audit(b/'FreshDualAudit.log',mods);assert sorted(parsed['rows'],key=lambda x:x['name'])==sorted(other['rows'],key=lambda x:x['name'])
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
'''.replace('IMPORTS','\nimport '.join(mods)).replace('NAMES',', '.join('`'+m for m in mods))
  (b/'FreshPrintAxioms.lean').write_text(printer);p=H.run(b,'FreshPrintAxioms');assert p['exit']==0
  printed=sum(x.startswith('PRINT_ORIGIN|') for x in (b/'FreshPrintAxioms.log').read_text().splitlines());assert printed==sum(x['kind']=='theorem' for x in parsed['rows'])
  scans=[]
  for m in mods:
   path=b/(m+'.lean');bad=re.findall(r'\b(?:sorry|admit|native_decide|axiom|unsafe|extern|implemented_by|csimp)\b',clean(path.read_text()));assert not bad,(arm,m,bad);scans.append({'module':m,'sha256':R.sha(path),'forbidden_tokens':bad})
  rows=parsed['rows'];assert all(source_valid(row) for row in base['sources'])
  # Same source-valid comparator evaluates both the clean production rows and
  # deliberately wrong original/copy/body pins. Author files never change.
  row=base['sources'][0];pinplants=[]
  for key in ('source_sha256','copy_sha256'):
   bad=copy.deepcopy(row);bad[key]='0'*64;assert not source_valid(bad);pinplants.append({'field':key,'caught':True})
  adapterrow=next(x for x in base['sources'] if x['import_only_mapping']);bad=copy.deepcopy(adapterrow);bad['import_only_mapping']={};assert not source_valid(bad);pinplants.append({'field':'import_adapter_omitted','caught':True})
  sourceplants={}
  wanted={(x['module'],x['name']) for x in rows}
  def exact(rs):return len(rs)==len({x['name'] for x in rs}) and {(x['module'],x['name']) for x in rs}==wanted
  for key,predicate,operation in [('missing-private',lambda x:x['name'].startswith('_private.'),'remove'),('missing-generated',lambda x:'.eq_' in x['name'] or '.match_' in x['name'],'remove'),('wrong-origin',lambda x:True,'wrong'),('duplicate',lambda x:True,'duplicate')]:
   bad=copy.deepcopy(rows);i=next(i for i,x in enumerate(bad) if predicate(x))
   if operation=='remove':bad.pop(i)
   elif operation=='wrong':bad[i]['module']='ForgedOrigin'
   else:bad.append(copy.deepcopy(bad[i]))
   assert not exact(bad);sourceplants[key]=True
  reports.append({'arm':arm,'status':'PASS_ALL_ORIGIN_AXIOM_SOURCE_GATES','positive_modules':mods,'audit':parsed,'audit_build':a,'dual_build':d,'literal_print_build':p,'dual_exact':True,'literal_theorems_printed':printed,'source_scans':scans,'same_source_valid_comparator_plants':pinplants,'actual_origin_corruptions':sourceplants,'all_import_adapters_body_exact':True})
  print(arm,len(mods),parsed['total'],printed,flush=True)
 out={'status':'PASS_TWO_ISOLATED_COMPLETE_SOURCE_AUDITS','packages':reports,'all_main_milestones':'OPEN','replication_count_added':0}
 p=R.ROOT/'research/rmaf/results/algorithm-maf-grouped-fresh-review-audit-v1.json';p.write_text(json.dumps(out,indent=2)+'\n')
if __name__=='__main__':main()
