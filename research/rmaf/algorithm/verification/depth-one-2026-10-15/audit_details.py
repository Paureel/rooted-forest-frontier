#!/usr/bin/env python3
"""Complete local paths/types/body hashes plus executable dependency closure.
Full body text is pinned by source bytes/kernel replay, not exported as oversized Expr text.
"""
from pathlib import Path
import json,importlib.util,re
H=Path(__file__).resolve().parent
s=importlib.util.spec_from_file_location('own_std_api',H/'frozen-ready-v1/std_toy_gates.py');a=importlib.util.module_from_spec(s);s.loader.exec_module(a)
a.F=H/'isolated-release-v1';a.OUT=a.ROOT/'research/rmaf/results/algorithm-depth-one-fresh-details-v1.json';a.state={'runs':[],'audits':{},'all_main_milestones':'OPEN'}
b=json.loads((a.ROOT/'research/rmaf/results/algorithm-depth-one-fresh-source-rebuild-v1.json').read_text());mods=b['order']
source='\n'.join('import '+n for n in mods)+'''
import Lean
open Lean Elab Command
def freshRefs : Expr → List Name
 | .const n _ => [n]
 | .app f x => freshRefs f ++ freshRefs x
 | .lam _ t b _ => freshRefs t ++ freshRefs b
 | .forallE _ t b _ => freshRefs t ++ freshRefs b
 | .letE _ t v b _ => freshRefs t ++ freshRefs v ++ freshRefs b
 | .mdata _ e => freshRefs e
 | .proj _ _ e => freshRefs e
 | _ => []
run_cmd do
 let env ← getEnv
 let modules : List Name := MODULES
 for n in modules do
  let path ← liftIO <| findOLean n
  logInfo m!"PATH|{n}|{path}"
 for (n,i) in env.constants.toList do
  if let some idx := env.getModuleIdxFor? n then
   let origin := env.allImportedModuleNames[idx.toNat]!
   if modules.contains origin then
    let kind := match i with
     | .thmInfo _ => "theorem"
     | .defnInfo _ => "definition"
     | .opaqueInfo _ => "opaque"
     | .axiomInfo _ => "axiom"
     | _ => "inductive/constructor/recursor/quotient"
    let j := Json.mkObj [("name",toJson n.toString),("origin",toJson origin.toString),
      ("type",toJson (reprStr i.type)),("type_hash",toJson i.type.hash.toNat),
      ("body_hash",toJson ((i.value? true).map (fun e => e.hash.toNat))),("kind",toJson kind)]
    logInfo m!"DETAIL|{j.compress}"
 let mut pending : List Name := [`Universal233.DepthOne.pretest01]
 let mut seen : List Name := []
 while !pending.isEmpty do
  let n := pending.head!
  pending := pending.tail!
  if !seen.contains n then
   seen := n :: seen
   if let some i := env.find? n then
    let origin := match env.getModuleIdxFor? n with
      | none => `Unknown
      | some idx => env.allImportedModuleNames[idx.toNat]!
    logInfo m!"CALL|{n}|{origin}"
    if modules.contains origin then
     if let some value := i.value? true then pending := freshRefs value ++ pending
'''.replace('MODULES','['+','.join('`'+n for n in mods)+']')
def executable_text(s):
 out=[];i=0;depth=0;string=False
 while i<len(s):
  if depth:
   if s.startswith('/-',i):depth+=1;i+=2
   elif s.startswith('-/',i):depth-=1;i+=2
   else:i+=1
  elif string:
   if s[i]=='\\':i+=2
   elif s[i]=='"':string=False;i+=1
   else:i+=1
  elif s.startswith('/-',i):depth=1;i+=2
  elif s.startswith('--',i):
   n=s.find('\n',i);i=len(s) if n<0 else n;out.append('\n')
  elif s[i]=='"':string=True;i+=1
  else:out.append(s[i]);i+=1
 assert depth==0 and not string
 return ''.join(out)
try:
 n='FreshSourceDetails';(a.F/(n+'.lean')).write_text(source);log=a.compile(n);rows=[];paths={};calls=[]
 for line in log.splitlines():
  if line.startswith('DETAIL|'):rows.append(json.loads(line.split('|',1)[1]))
  elif line.startswith('PATH|'):
   _,n,p=line.split('|');paths[n]=p
  elif line.startswith('CALL|'):
   _,n,origin=line.split('|');calls.append({'name':n,'origin':origin})
 assert len(rows)==2041 and len({r['name'] for r in rows})==2041
 assert set(paths)==set(mods)
 for n,p in paths.items():assert Path(p).resolve()==a.F/(n+'.olean')
 closure={r['name'] for r in calls};forbidden=['RMAF.assignments','RMAF.blocks','RMAF.solve','Universal233.CoreProgram.generate','Universal233.CutRealization.source_core','Universal233.DepthOne.source_two_split']
 assert not closure.intersection(forbidden)
 required={'Universal233.DepthOne.pretest01','Universal233.DepthOne.candidates','Universal233.DepthOne.edges','Universal233.DepthOne.vertices','Universal233.DepthOne.forest','RMAF.best','RMAF.agreement'};assert required<=closure
 scans=[]
 for n in mods:
  p=a.F/(n+'.lean');tokens=re.findall(r'\b(?:sorry|admit|native_decide|axiom)\b',executable_text(p.read_text()));assert not tokens,(n,tokens);scans.append({'module':n,'sha256':a.sha(p),'forbidden_executable_tokens':tokens})
 a.state.update({'declarations':rows,'private_declarations':sum(r['name'].startswith('_private.') for r in rows),'actual_local_paths':paths,'executable_scientific_closure':calls,'forbidden_runtime_oracles_absent':forbidden,'source_token_scans':scans,'verdict':'PASS-COMPLETE-TYPE-BODY-HASH-LOCAL-PATH-AND-EXECUTABLE-CLOSURE-INVENTORY'});a.save();print(json.dumps({'verdict':a.state['verdict'],'declarations':len(rows),'closure_names':len(calls),'private':a.state['private_declarations']}))
except Exception as e:a.state['verdict']='OPEN-DETAIL-OR-CLOSURE-FAILURE';a.state['error']=repr(e);a.save();raise
