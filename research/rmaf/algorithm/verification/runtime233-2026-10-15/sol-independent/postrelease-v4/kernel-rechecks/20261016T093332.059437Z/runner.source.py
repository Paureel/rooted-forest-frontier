#!/usr/bin/env python3
"""One-shot selected cost-consumer source/kernel recheck. No author auditor runs.
Imports remain exact same-lineage reuse. This is not an origin/functional audit.
"""
from pathlib import Path
import argparse,datetime,gzip,hashlib,json,os,re,selectors,shutil,signal,subprocess,time
ROOT=Path('/Users/paurel/Documents/ChatGPT/bootscience');HERE=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
a=argparse.ArgumentParser();a.add_argument('--pilot',action='store_true');args=a.parse_args()
plan=json.loads((HERE/'RECHECK-PLAN-v4.json').read_text());idx=json.loads((HERE/'LICENSE-INDEX-v4.json').read_text())
lean=ROOT/'.runtime/elan/toolchains/leanprover--lean4---v4.35.0/bin/lean'
stamp=datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%S.%fZ')
out=HERE/'kernel-rechecks'/stamp;out.mkdir(parents=True)
shutil.copy2(__file__,out/'runner.source.py');shutil.copy2(HERE/'RECHECK-PLAN-v4.json',out/'plan.source.json')
def contact(path,expected,scope):
    p=ROOT/path
    if path not in idx or idx[path]!=expected or sha(p)!=expected:raise RuntimeError('pin/license drift '+path)
    with (HERE/'KERNEL-CONTACT-v4.jsonl').open('a') as f:f.write(json.dumps({'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'event':'NARROW_KERNEL_RECHECK_READ','path':path,'sha256':expected,'scope':scope,'new_blind_credit':0})+'\n')
    return p

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
    if proc.returncode or timeout or overflow:raise RuntimeError('kernel process failed '+name)
    return b''.join(chunks).decode(),receipt

records=[]
try:
    for item in (plan['modules'][:1] if args.pilot else plan['modules'][1:]):
        pkg=item['package'];module=item['module'];build=out/pkg;build.mkdir()
        source=contact(item['source'],item['source_sha256'],'selected v4 consumer proof source only, copied exactly')
        own=build/(module+'.lean');shutil.copyfile(source,own)
        assert sha(own)==item['source_sha256']
        roots=[item['canonical_import_root']]+item.get('additional_import_roots',[])
        prefixes=[r+'/' for r in roots]
        reused=[]
        for path,expected in sorted(idx.items()):
            if any(path.startswith(prefix) and '/' not in path.removeprefix(prefix) for prefix in prefixes) and path.endswith('.olean'):
                contact(path,expected,'same-lineage canonical imported binary pin only; no functional/origin producer replay')
                sourcepath=path[:-6]+'.lean'
                reused.append({'olean':path,'olean_sha256':expected,'source':sourcepath,'source_sha256':idx.get(sourcepath),'source_body_not_rebuilt':True})
        env=dict(os.environ);env['LEAN_PATH']=os.pathsep.join([str(build)]+[str(ROOT/r) for r in roots])
        output,compile_receipt=run([str(lean),'-M'+str(plan['lean_MiB']),'-o',str(build/(module+'.olean')),str(own)],build,env,pkg+'-compile')
        wrapper=build/'ConsumerCheck.lean'
        wrapper.write_text('import '+module+'\n'+''.join('#check '+th+'\n#print axioms '+th+'\n' for th in item['theorems']))
        printed,check_receipt=run([str(lean),'-M'+str(plan['lean_MiB']),str(wrapper)],build,env,pkg+'-interface')
        reports=re.findall(r"'[^']+' (?:does not depend on any axioms|depends on axioms: \[[^]]*\])",printed)
        axioms={n.strip() for block in re.findall(r'depends on axioms: \[([^]]*)\]',printed) for n in block.split(',') if n.strip()}
        if len(reports)!=len(item['theorems']) or not axioms<={'propext','Classical.choice','Quot.sound'}:raise RuntimeError('axiom/report check failed '+pkg)
        rec={'module':module,'package':pkg,'source_sha256':sha(own),'fresh_olean_sha256':sha(build/(module+'.olean')),'canonical_import_root':item['canonical_import_root'],'reused_pins':reused,'theorems':item['theorems'],'axiom_reports':reports,'axioms':sorted(axioms),'compile':compile_receipt,'interface':check_receipt,'scope':'Narrow source/kernel consumer check against exact same-lineage imports; no new independent functional/origin acceptance'}
        records.append(rec)
    receipt={'status':'PILOT_PASSED' if args.pilot else 'SELECTED_CONSUMERS_RECHECKED','records':records,'new_blind_credit':0,'global_algorithm_base_novelty':'OPEN','lean_binary_sha256':sha(lean)}
    (out/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(receipt['status']+' '+str(len(records))+' completed consumer modules; standard axiom allow-list')
    print('Maximum process seconds '+str(max(r[k]['seconds'] for r in records for k in ('compile','interface'))))
    print(str(out))
except BaseException as error:
    (out/'failure.json').write_text(json.dumps({'error':repr(error),'completed':records,'status':'FAILED'},indent=2)+'\n')
    raise
