from pathlib import Path
import json,hashlib,re,subprocess,os,time,sys,traceback
H=Path(__file__).resolve().parent;R=next(p for p in H.parents if (p/'bootloops-lean').is_file());F=H/'isolated-source-v1';C=json.loads((H/'AUTHOR-certificate.json').read_text());A=R/'results/algorithm-universal233-output-state-20261015T105826Z';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
state={'phase':'RELEASED_SOURCE_REVIEW','author_manifest_sha256':'d27ae69ef54c6c03f20c43767fc0b731e5ff96abcfa59f1f426223c77e6a67f5','source_copies':[],'runs':[],'all_main_milestones':'OPEN'}
OUT=R/'research/rmaf/results/algorithm-output-state-fresh-build-v1.json'
def save():OUT.write_text(json.dumps(state,indent=2)+'\n')
def setup():
 assert not F.exists();F.mkdir()
 for row in C['source_inputs']:
  origin=R/row['path'];assert sha(origin)==row['sha256'],('origin_drift',row['module'],row['path'])
  original=origin.read_bytes();s=original.decode()
  for old,new in row['adaptations'].items():s=re.sub(r'(?m)^import '+re.escape(old)+r'$', 'import '+new,s)
  snapshot=A/(row['module']+'.lean');assert sha(snapshot)==row['adapted_sha256'],('snapshot_drift',row['module'])
  assert s.encode()==snapshot.read_bytes(),('non_import_body_adapter',row['module'])
  dest=F/snapshot.name;dest.write_bytes(snapshot.read_bytes())
  imports=re.findall(r'(?m)^import (\S+)',s)
  state['source_copies'].append({**row,'snapshot':str(snapshot.relative_to(R)),'isolated':str(dest.relative_to(R)),'isolated_sha256':sha(dest),'import_only_body_unchanged':True,'imports':imports})
 assert len(state['source_copies'])==121 and [x['module'] for x in state['source_copies']]==C['positive_order']
 allmods=set(C['positive_order']);assert all(i in allmods or i in ['Lean','Std'] for x in state['source_copies'] for i in x['imports'])
 state['compiler']=subprocess.run([str(R/'bootloops-lean'),'--version'],capture_output=True,text=True,timeout=10).stdout.strip();save()
def build(modules):
 env=os.environ.copy();env['LEAN_PATH']=str(F)
 for n in modules:
  start=time.monotonic();cmd=[str(R/'bootloops-lean'),'-o',n+'.olean',n+'.lean']
  try:p=subprocess.run(cmd,cwd=F,env=env,capture_output=True,text=True,timeout=30);rc=p.returncode;log=p.stdout+p.stderr
  except subprocess.TimeoutExpired as e:rc=124;log='OPEN_30_SECOND_CAP\n'+str(e.stdout or '')+str(e.stderr or '')
  lp=F/(n+'.fresh.log');lp.write_text(log);row={'module':n,'returncode':rc,'seconds':time.monotonic()-start,'source_sha256':sha(F/(n+'.lean')),'log_sha256':sha(lp),'command':cmd};state['runs'].append(row);save()
  print(json.dumps({k:row[k] for k in ['module','returncode','seconds']}),flush=True)
  assert rc==0,(n,log[-4000:])
if __name__=='__main__':
 try:
  if sys.argv[1]=='pilot':setup();build(C['positive_order'][:3]);state['pilot_modules']=3;save()
  elif sys.argv[1]=='rest':state=json.loads(OUT.read_text());assert len(state['runs'])==3;build(C['positive_order'][3:]);state['verdict']='PASS_ISOLATED_SOURCE_ONLY_REBUILD';save()
 except Exception as e:state['verdict']='OPEN_SOURCE_BUILD_FAILURE';state['error']=repr(e);state['traceback']=traceback.format_exc();save();raise
