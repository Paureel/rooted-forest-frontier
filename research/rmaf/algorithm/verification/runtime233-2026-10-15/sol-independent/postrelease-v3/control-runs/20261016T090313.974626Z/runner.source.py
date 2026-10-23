#!/usr/bin/env python3
"""One-shot v3 controls adapter of calibrated bounded Lean runner.
Only expected-false exit handling is added. Baseline true/false controls run
first; no author auditor, oracle or author control module is executed.
"""
from pathlib import Path
import argparse,datetime,gzip,hashlib,json,os,re,selectors,shutil,signal,subprocess,time
ROOT=Path('/Users/paurel/Documents/ChatGPT/bootscience');HERE=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
a=argparse.ArgumentParser();a.add_argument('--baseline',action='store_true');args=a.parse_args()
plan=json.loads((HERE/'OWN-CONTROL-PLAN-v3.1.json').read_text());assert sha(HERE/plan['fixture'])==plan['fixture_sha256']
lean=ROOT/'.runtime/elan/toolchains/leanprover--lean4---v4.35.0/bin/lean'
out=HERE/'control-runs'/datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%S.%fZ');out.mkdir(parents=True)
shutil.copyfile(__file__,out/'runner.source.py');shutil.copyfile(HERE/'OWN-CONTROL-PLAN-v3.1.json',out/'plan.source.json')
def run(command,cwd,env,name):
    if shutil.disk_usage(HERE).free<plan['disk_floor_bytes']:raise RuntimeError('diskfloor')
    start=time.monotonic();deadline=start+plan['initial_subprocess_seconds']
    proc=subprocess.Popen(command,cwd=cwd,env=env,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,start_new_session=True)
    select=selectors.DefaultSelector();select.register(proc.stdout,selectors.EVENT_READ)
    count=0;currentline=0;overflow=False;timeout=False;chunks=[]
    log=out/(name+'.log.gz')
    with gzip.open(log,'wb') as f:
        while select.get_map():
            if time.monotonic()>=deadline:timeout=True;os.killpg(proc.pid,signal.SIGKILL);break
            for key,_ in select.select(timeout=0.2):
                chunk=os.read(key.fd,8192)
                if not chunk:select.unregister(key.fileobj);continue
                count+=len(chunk)
                for line in chunk.splitlines(keepends=True):
                    currentline+=len(line)
                    if currentline>plan['line_cap_bytes']:overflow=True
                    if line.endswith(b'\n'):currentline=0
                if count>plan['raw_cap_bytes']:overflow=True
                if overflow:os.killpg(proc.pid,signal.SIGKILL);break
                f.write(chunk);chunks.append(chunk)
            if overflow:break
    proc.wait(timeout=2);select.close();proc.stdout.close()
    receipt={'command':command,'cwd':str(cwd),'LEAN_PATH':env['LEAN_PATH'],'seconds':time.monotonic()-start,'exit_code':proc.returncode,'timeout':timeout,'overflow':overflow,'raw_bytes':count,'log':log.name,'log_sha256':sha(log)}
    (out/(name+'.receipt.json')).write_text(json.dumps(receipt,indent=2)+'\n')
    if timeout or overflow:raise RuntimeError('kernel process resource failure '+name)
    return b''.join(chunks).decode(),receipt

records=[]
try:
 if not args.baseline and not (HERE/'BASELINE-CONTROL-RECEIPT-v3.1.json').exists():raise RuntimeError('baseline controls first')
 for item in (plan['items'][:2] if args.baseline else plan['items'][2:]):
  own=HERE/item['source'];assert sha(own)==item['source_sha256'];shutil.copyfile(own,out/own.name)
  env=dict(os.environ);env['LEAN_PATH']=os.pathsep.join([str(ROOT/r) for r in ([item['root']]+item.get('additional_import_roots',[])) if r])
  printed,receipt=run([str(lean),'-M3072',str(out/own.name)],out,env,item['name'])
  if item['expected']=='pass':
   if receipt['exit_code']!=0:raise RuntimeError('known answer rejected '+item['name'])
  else:
   if receipt['exit_code']==0 or 'decide' not in printed or 'false' not in printed or printed.count('error:')!=1:raise RuntimeError('false control not diagnosed precisely '+item['name'])
  records.append({'case':item,'process':receipt,'observed':'known answer passed' if item['expected']=='pass' else 'false proposition rejected'})
 result={'status':'BASELINE_CONTROLS_MET' if args.baseline else 'OWN_POSTCONTACT_CONTROLS_MET','records':records,'new_blind_replication_credit':0,'scope':'Own hand-truth/corruption checks of finite source/reference semantics; no native/global runtime or actual-tree census'}
 (out/'receipt.json').write_text(json.dumps(result,indent=2)+'\n')
 if args.baseline:(HERE/'BASELINE-CONTROL-RECEIPT-v3.1.json').write_text(json.dumps({'path':str((out/'receipt.json').relative_to(HERE)),'sha256':sha(out/'receipt.json')},indent=2)+'\n')
 print(result['status']+'; '+str(sum(x['case']['statements'] for x in records if x['case']['expected']=='pass'))+' known statements; '+str(sum(x['case']['statements'] for x in records if x['case']['expected']=='false'))+' rejected false statements.')
 print('Maximum process seconds '+str(max(x['process']['seconds'] for x in records)));print(str(out))
except BaseException as error:
 (out/'failure.json').write_text(json.dumps({'error':repr(error),'completed':records},indent=2)+'\n');raise
