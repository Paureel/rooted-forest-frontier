from pathlib import Path
import json,hashlib,subprocess,os,time
H=Path(__file__).resolve().parent;R=next(p for p in H.parents if (p/'bootloops-lean').is_file());F=H/'isolated-source-v1';O=H/'isolated-original-producers-v1';assert not O.exists();O.mkdir();C=json.loads((H/'AUTHOR-certificate.json').read_text());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
mods=['RMAF','Restriction','Embedding','Partition','Cost','Forward'];adapted=['RMAF','GroupRestriction','GroupEmbedding','GroupPartition','GroupCost','GroupForward'];inputs=[]
for old,new in zip(mods,adapted):
 row=next(r for r in C['source_inputs'] if r['module']==new);p=R/row['path'];assert sha(p)==row['sha256'];(O/(old+'.lean')).write_bytes(p.read_bytes());inputs.append({'module':old,'producer':row['path'],'sha256':sha(p),'adapted_module':new})
(H/'GENERATED-ADAPTER-REPLAY-PIN-v1.json').write_text(json.dumps({'before_execution':True,'sources':inputs,'expectation':'All RMAF-namespaced equations generated outside RMAF have identical names/types and proof bodies after only explicit private producer-module prefix transport. Origins map by the six stated module names. No generated declaration omitted.','private_prefix_transport':{old:new for old,new in zip(mods,adapted) if old!=new},'scientific_oleans_copied':False},indent=2)+'\n')
runs=[]
def compile(folder,n):
 env=os.environ.copy();env['LEAN_PATH']=str(folder);start=time.monotonic();p=subprocess.run([str(R/'bootloops-lean'),'-o',n+'.olean',n+'.lean'],cwd=folder,env=env,capture_output=True,text=True,timeout=30);log=p.stdout+p.stderr;(folder/(n+'.adapter.log')).write_text(log);runs.append({'folder':str(folder.relative_to(R)),'module':n,'seconds':time.monotonic()-start,'returncode':p.returncode});assert p.returncode==0,log[-2500:];return log
for n in mods:compile(O,n)
body='''
import Lean
open Lean Elab Command
run_cmd do
 let env ← getEnv
 let mods : List Name := MODULES
 for (n,i) in env.constants.toList do
  if n.toString.startsWith "RMAF." then
   if let some idx := env.getModuleIdxFor? n then
    let origin := env.allImportedModuleNames[idx.toNat]!
    if origin != `RMAF && mods.contains origin then
     let axs ← collectAxioms n
     if i.isAxiom || i.isUnsafe || axs.toList.any (fun a => !([`propext,`Classical.choice,`Quot.sound] : List Name).contains a) then throwError "FORBIDDEN_GENERATED_BODY"
     let b := match i.value? (allowOpaque := true) with | some v => reprStr v | none => "NONE"
     let obj := Json.mkObj [("name",toJson n.toString),("origin",toJson origin.toString),("type",toJson (reprStr i.type)),("body",toJson b),("axioms",toJson (axs.toList.map Name.toString))]
     logInfo m!"GENERATED|{obj.compress}"
'''
results=[]
for folder,module_list in [(O,mods),(F,adapted)]:
 n='FreshGeneratedProducerDumpV1';(folder/(n+'.lean')).write_text('\n'.join('import '+m for m in module_list)+body.replace('MODULES','['+','.join('`'+x for x in module_list)+']'));log=compile(folder,n);results.append({r['name']:r for line in log.splitlines() if line.startswith('GENERATED|') for r in [json.loads(line.split('|',1)[1])]})
a,b=results;assert set(a)==set(b);mapping=dict(zip(mods,adapted));comparisons=[]
for name in sorted(a):
 x,y=a[name],b[name];assert x['body']!='NONE' and y['body']!='NONE';normalized=x['body']
 for old,new in mapping.items():normalized=normalized.replace('_private.'+old+'.','_private.'+new+'.')
 same_type=x['type']==y['type'];same_body=x['body']==y['body'];transported=normalized==y['body'];assert same_type and transported and mapping[x['origin']]==y['origin'] and sorted(x['axioms'])==sorted(y['axioms']),name
 comparisons.append({'name':name,'original_origin':x['origin'],'adapted_origin':y['origin'],'exact_type_equal':same_type,'exact_body_equal':same_body,'body_equal_after_only_explicit_private_prefix_transport':transported,'original_type_sha256':hashlib.sha256(x['type'].encode()).hexdigest(),'adapted_type_sha256':hashlib.sha256(y['type'].encode()).hexdigest(),'original_body_sha256':hashlib.sha256(x['body'].encode()).hexdigest(),'adapted_body_sha256':hashlib.sha256(y['body'].encode()).hexdigest()})
out={'verdict':'PASS_EXACT_GENERATED_PRODUCER_TYPE_AND_BODY_ADAPTERS','generated_count':len(a),'raw_equal_bodies':sum(x['exact_body_equal'] for x in comparisons),'transported_private_prefix_bodies':sum(not x['exact_body_equal'] for x in comparisons),'comparisons':comparisons,'runs':runs,'full_original_and_adapted_expressions_retained_in_logs':True,'all_main_milestones':'OPEN'}
(R/'research/rmaf/results/algorithm-output-state-fresh-generated-adapters-v1.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({k:out[k] for k in ['verdict','generated_count','raw_equal_bodies','transported_private_prefix_bodies']}))
