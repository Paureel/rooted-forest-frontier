#!/usr/bin/env python3
"""All accepted originating declaration signatures/bodies and exact path readout."""
from pathlib import Path
import json,importlib.util,re,hashlib
HERE=Path(__file__).resolve().parent
s=importlib.util.spec_from_file_location('own_api',HERE/'released_replay.py');a=importlib.util.module_from_spec(s);s.loader.exec_module(a)
a.OUT=a.RMAF/'results/algorithm-rank-restriction-fresh-signature-inventory-v1.json';a.state={'runs':[],'audits':{},'inventories':{}}
old=json.loads((a.RMAF/'results/algorithm-rank-restriction-fresh-source-rebuild-v1.json').read_text())
def source(imports,mods):
 return '\n'.join('import '+x for x in imports)+'''
import Lean
open Lean Elab Command
run_cmd do
  let env ← getEnv
  let modules : List Name := MODULES
  for m in modules do
    let p ← liftIO <| findOLean m
    logInfo m!"PATH|{m}|{p}"
  for (n,i) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? n then
      let origin := env.allImportedModuleNames[idx.toNat]!
      if modules.contains origin then
        let value := i.value? true
        let j := Json.mkObj [("origin",toJson origin.toString),("name",toJson n.toString),
          ("type",toJson (reprStr i.type)),("type_hash",toJson i.type.hash.toNat),
          ("body",toJson (value.map reprStr)),("body_hash",toJson (value.map (fun e => e.hash.toNat)))]
        logInfo m!"SIGNATURE|{j.compress}"
'''.replace('MODULES','['+','.join('`'+x for x in mods)+']')
def clean_code(s):
 # Nested Lean block comments and strings are ignored for executable-token gate.
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
   end=s.find('\n',i);i=len(s) if end<0 else end;out.append('\n')
  elif s[i]=='"':string=True;i+=1
  else:out.append(s[i]);i+=1
 assert depth==0 and not string
 return ''.join(out)
def run(kind,tag,imports,mods):
 folder=a.BUILD/kind;name='FreshSignatures'+tag;(folder/(name+'.lean')).write_text(source(imports,mods));log=a.compile_one(folder,name);rows=[];paths={}
 for l in log.splitlines():
  if l.startswith('SIGNATURE|'):rows.append(json.loads(l.split('|',1)[1]))
  elif l.startswith('PATH|'):
   _,m,p=l.split('|');paths[m]=p
 assert set(paths)==set(mods)
 for n,p in paths.items():assert Path(p).resolve()==folder/(n+'.olean')
 assert len(rows)==(2194 if kind=='rank' else 694)
 scans=[]
 for n in mods:
  p=folder/(n+'.lean');hits=re.findall(r'\b(?:sorry|admit|native_decide|axiom)\b',clean_code(p.read_text()));assert not hits,(n,hits);scans.append({'module':n,'sha256':a.digest(p),'rejected_tokens':hits})
 a.state['inventories'][tag]={'rows':rows,'paths':paths,'source_token_scans':scans,'total':len(rows),'private_names':sum(x['name'].startswith('_private.') for x in rows),'type_and_body_exported':True};a.save();return rows
rankmods=old['rank_order'];resmods=old['restriction_order']
try:
 run('rank','Rank',rankmods,rankmods)
 x=run('restriction','RestrictionAll',resmods,resmods);y=run('restriction','RestrictionConsumer',['Consumers'],resmods)
 dx={r['name']:r for r in x};dy={r['name']:r for r in y};assert set(dx)==set(dy)
 for n,r in dx.items():assert all(r[k]==dy[n][k] for k in ['type','type_hash','body','body_hash']),(n,'changed signature/body')
 a.state['verdict']='PASS-ALL-SIGNATURES-BODIES-LOCAL-PATHS-AND-EXACT-GENERATED-ADOPTION';a.state['restriction_same_exact_type_body_records']=694;a.save()
 print(json.dumps({'verdict':a.state['verdict'],'counts':{k:(v['total'],v['private_names']) for k,v in a.state['inventories'].items()}}))
except Exception as e:a.state['verdict']='OPEN-INVENTORY-FAILURE';a.state['error']=repr(e);a.save();raise
