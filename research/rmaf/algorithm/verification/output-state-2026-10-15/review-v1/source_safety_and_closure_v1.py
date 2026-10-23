from pathlib import Path
import json,re,subprocess,os,time,hashlib
H=Path(__file__).resolve().parent;R=next(p for p in H.parents if (p/'bootloops-lean').is_file());F=H/'isolated-source-v1';C=json.loads((H/'AUTHOR-certificate.json').read_text());mods=C['positive_order']+['FreshActualReadoutsV2','FreshEveryOutputConsumerV1','FreshActualCleanV1']
# Preserve newlines while removing nested Lean comments and string literals.
def code_only(s):
 out=[];i=0;depth=0;quote=False
 while i<len(s):
  if depth:
   if s.startswith('/-',i):depth+=1;i+=2
   elif s.startswith('-/',i):depth-=1;i+=2
   else:out.append('\n' if s[i]=='\n' else ' ');i+=1
  elif quote:
   if s[i]=='\\':out.extend('  ');i+=2
   elif s[i]=='"':quote=False;out.append(' ');i+=1
   else:out.append('\n' if s[i]=='\n' else ' ');i+=1
  elif s.startswith('/-',i):depth=1;out.extend('  ');i+=2
  elif s.startswith('--',i):
   end=s.find('\n',i);end=len(s) if end<0 else end;out.extend(' '*(end-i));i=end
  elif s[i]=='"':quote=True;out.append(' ');i+=1
  else:out.append(s[i]);i+=1
 assert depth==0 and not quote
 return ''.join(out)
rows=[]
for n in mods:
 p=F/(n+'.lean');hits=re.findall(r'\b(?:sorry|admit|native_decide|axiom|unsafe|implemented_by)\b',code_only(p.read_text()));assert not hits,(n,hits);rows.append({'module':n,'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'forbidden_tokens':hits})
roots=['OutputState.sourceForest','ForestGroups.owned','ForestState.agrees']
s='''import FreshEveryOutputConsumerV1
import Lean
open Lean Elab Command
def freshExprNames : Expr → List Name
 | .const n _ => [n]
 | .app a b => freshExprNames a ++ freshExprNames b
 | .lam _ t b _ => freshExprNames t ++ freshExprNames b
 | .forallE _ t b _ => freshExprNames t ++ freshExprNames b
 | .letE _ t v b _ => freshExprNames t ++ freshExprNames v ++ freshExprNames b
 | .mdata _ e => freshExprNames e
 | .proj _ _ e => freshExprNames e
 | _ => []
run_cmd do
 let env ← getEnv
 let modules : List Name := MODULES
 for root in ROOTS do
  let mut todo := [root]
  let mut seen : List Name := []
  let mut used : List Name := []
  while !todo.isEmpty do
   let n := todo.head!
   todo := todo.tail!
   if !seen.contains n then
    seen := n :: seen
    if let some idx := env.getModuleIdxFor? n then
     if modules.contains env.allImportedModuleNames[idx.toNat]! then
      used := n :: used
      if let some i := env.find? n then
       if let some v := i.value? then todo := freshExprNames v ++ todo
   if seen.length > 5000 then throwError "OPEN_CLOSURE_CAP"
  logInfo m!"CLOSURE|{root}|{String.intercalate "," (used.map Name.toString)}"
'''.replace('MODULES','['+','.join('`'+m for m in mods)+']').replace('ROOTS','(['+','.join('`'+n for n in roots)+'] : List Name)')
(F/'FreshSourceClosureV1.lean').write_text(s);env=os.environ.copy();env['LEAN_PATH']=str(F);start=time.monotonic();p=subprocess.run([str(R/'bootloops-lean'),'-o','FreshSourceClosureV1.olean','FreshSourceClosureV1.lean'],cwd=F,env=env,capture_output=True,text=True,timeout=30);log=p.stdout+p.stderr;(F/'FreshSourceClosureV1.log').write_text(log);assert p.returncode==0,log[-4000:]
closures={}
for line in log.splitlines():
 if line.startswith('CLOSURE|'):
  _,root,names=line.split('|');closures[root]=names.split(',')
assert set(closures)==set(roots)
for root,names in closures.items():assert root in names and not any(re.search(r'(?:^|\.)(?:solve|assignments|blocks|generate|pretest01)$',n) for n in names),(root,names)
# Mutation/clean twins for the source-token scanner itself.
assert not re.search(r'\bsorry\b',code_only('/- outer /- sorry -/ comment -/ theorem x : True := True.intro -- sorry\n'))
assert re.search(r'\bsorry\b',code_only('theorem x : False := by sorry'))
assert not re.search(r'\bnative_decide\b',code_only('def x := "native_decide"'))
assert re.search(r'\bnative_decide\b',code_only('theorem x : True := by native_decide'))
out={'verdict':'PASS_SOURCE_TOKEN_AND_EXECUTABLE_SCIENTIFIC_CLOSURE_GATES','positive_source_modules':len(mods),'sources':rows,'runtime_closures':closures,'closure_seconds':time.monotonic()-start,'token_scanner_clean_and_mutant_twins':4,'hidden_solver_or_generator_in_scoped_definition_closures':False,'scope':'source definitions only; does not prove instruction correspondence, recursion or scheduler runtime','all_main_milestones':'OPEN'}
(R/'research/rmaf/results/algorithm-output-state-fresh-source-closure-v1.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({'verdict':out['verdict'],'modules':len(mods),'closure_sizes':{k:len(v) for k,v in closures.items()}}))
