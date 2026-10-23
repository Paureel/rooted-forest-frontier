#!/usr/bin/env python3
"""One-shot exact predecessor detector replay for only missing producer batches.
Same import context and detector. New gzip transport; no replication credit.
"""
import argparse,gzip,hashlib,json,os,selectors,shutil,signal,subprocess,time
from pathlib import Path
import continuation_v1 as c
P=c.P;POST=c.POST;PRE=c.PRE;D=POST/'CallerProducerAudit_chunk_v3.lean'

def run(imports,producers,build,label):
    target=P/(label+'.stdout.json.gz');err=P/(label+'.stderr.log')
    if target.exists() or err.exists():raise ValueError('existing raw receipt')
    assert c.sha(D)=='325642f06f2b7bbf97c51435ede1a71c487faaa9305edcb02e82deeead327050'
    assert shutil.disk_usage(P).free>2_000_000_000
    env=dict(os.environ,LEAN_PATH=str(build));cmd=[str(c.LEAN),'--run',str(D)]+imports+['--producers']+producers
    at=time.perf_counter();h=hashlib.sha256();raw=0;failure=None
    with err.open('xb') as e, target.open('xb') as out:
        proc=subprocess.Popen(cmd,cwd=POST,env=env,stdout=subprocess.PIPE,stderr=e,start_new_session=True)
        try:
            with gzip.GzipFile(fileobj=out,mode='wb',compresslevel=1,mtime=0) as g:
                sel=selectors.DefaultSelector();sel.register(proc.stdout,selectors.EVENT_READ)
                while sel.get_map():
                    if time.perf_counter()-at>120:raise TimeoutError('120-second cap')
                    if raw>4_000_000_000 or out.tell()>512_000_000:raise ValueError('output cap')
                    if shutil.disk_usage(P).free<1_500_000_000:raise ValueError('free-space margin')
                    for key,_ in sel.select(1):
                        b=os.read(key.fileobj.fileno(),1024*1024)
                        if not b:sel.unregister(key.fileobj);break
                        g.write(b);h.update(b);raw+=len(b)
            rc=proc.wait(timeout=3)
        except BaseException as exc:
            failure=repr(exc);os.killpg(proc.pid,signal.SIGKILL);proc.wait();rc=proc.returncode
    r={'command':cmd,'cwd':str(POST),'LEAN_PATH':str(build),'returncode':rc,'seconds':time.perf_counter()-at,'raw_bytes':raw,'raw_sha256':h.hexdigest(),'gzip_path':target.name,'gzip_bytes':target.stat().st_size,'gzip_sha256':c.sha(target),'stderr_sha256':c.sha(err),'error':failure,'detector_sha256':c.sha(D),'script_sha256':c.sha(Path(__file__))}
    c.write(label+'.receipt.json',r)
    if failure or rc:raise ValueError('raw command failed '+str(r))
    d=c.project(target);return d,r

def controls():
    results=[]
    for tag,ms,b,good in [('clean',['CallerCleanA','CallerCleanB'],PRE/'origin/build-full-v2',True),('hostile-forward',['CallerPrivateClean','CallerPrivateHostile'],PRE/'origin/private-imports',False),('hostile-reverse',['CallerPrivateHostile','CallerPrivateClean'],PRE/'origin/private-imports',False)]:
        d,r=run(ms,ms,b,'transport-control-'+tag+'-v1')
        try:c.gate(d,ms)
        except ValueError as e:
            assert not good;results.append({'control':tag,'reject':True,'reason':str(e),'transport':r})
        else:
            assert good;prior=c.project(POST/'chunk-v3-control-full.json');assert d==prior;results.append({'control':tag,'pass':True,'identical_prior_full_projection':True,'transport':r})
    c.write('TRANSPORT-CONTROLS-v1.json',{'status':'PASS','postcontact':True,'blind_credit':0,'controls':results})
    print(json.dumps({'transport_controls':'PASS','count':len(results)}))

def missing(indices):
    assert json.loads((P/'TRANSPORT-CONTROLS-v1.json').read_text())['status']=='PASS'
    ms=json.loads((POST/'source-order-v1.json').read_text());results=[]
    for i in indices:
        d,r=run(ms,ms[i*10:(i+1)*10],POST/'scientific-build',f'missing-producer-batch-{i}-v1')
        assert [h['module']for h in d['producers']]==ms[i*10:(i+1)*10]
        c.write(f'projected-missing-batch-{i}-v1.json',{'batch':i,'projection':d,'transport':r})
        results.append({'batch':i,'producers':len(d['producers']),'rows':len(d['rows']),'seconds':r['seconds'],'gzip_bytes':r['gzip_bytes'],'raw_bytes':r['raw_bytes']})
        print(json.dumps(results[-1]),flush=True)
    c.write('MISSING-BATCH-PILOT-v1.json' if indices==[15] else 'MISSING-BATCH-REST-v1.json',{'status':'RAW_AND_PROJECTION_COMPLETE_NOT_COMBINED_GATE','results':results})

def combine():
    ms=json.loads((POST/'source-order-v1.json').read_text());ds=[];receipts=[]
    for i in range(18):
        f=P/(f'projected-prior-batch-{i}-v1.json' if i<15 else f'projected-missing-batch-{i}-v1.json');r=json.loads(f.read_text());ds.append(r['projection']);receipts.append({'file':f.name,'sha256':c.sha(f)})
    d=dict(ds[0],rows=sum([z['rows']for z in ds],[]),producers=sum([z['producers']for z in ds],[]))
    assert all(z['loaded_modules']==d['loaded_modules'] and z['trustLevel']==0 for z in ds)
    inv=json.loads((POST/'integrity-pilot-v1.json').read_text());imports={r['module']:['Init','Init']+r['imports']for r in inv['sources']}
    g=c.gate(d,ms,imports)
    c.write('PRODUCER-COMBINED-PROJECTION-v1.json',d)
    r={'status':'STORED_PRODUCER_GATE_PASS_WITH_EXPLICIT_RUNTIME_LIMIT','producers':len(d['producers']),'stored':len(d['rows']),'unique_names':len({z['name']for z in d['rows']}),'empty_producers':[h['module']for h in d['producers']if h['count']==0],'batches':receipts,**g,'replication_credit':0,'scope':'all actual stored ConstantInfo kind/type/body/recursor RHS references and resolved-context axiom closures before coalescing; full173 import context; source cold-build correspondence as separately pinned; runtime/IR-only bodies excluded and remain unaccepted'}
    c.write('PRODUCER-GATE-v1.json',r);print(json.dumps({k:v for k,v in r.items()if k not in ['batches','proof_body_differences','partial_occurrences','unsafe_occurrences']}));print('partial',len(g['partial_occurrences']),'unsafe',len(g['unsafe_occurrences']),'proofdiff',len(g['proof_body_differences']))

if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('mode',choices=['controls','pilot','rest','combine']);a=ap.parse_args()
    {'controls':controls,'pilot':lambda:missing([15]),'rest':lambda:missing([16,17]),'combine':combine}[a.mode]()
