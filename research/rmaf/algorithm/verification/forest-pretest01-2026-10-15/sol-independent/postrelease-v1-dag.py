#!/usr/bin/env python3
"""One-shot scoped adapter + streamed gzip audit using the calibrated recorder.
Every producer type/body/rule is retained as a structural expression DAG.
Scientific module selection comes only from this reviewer's literal closure.
"""
import argparse
import gzip
import hashlib
import json
import os
from pathlib import Path
import queue
import shutil
import subprocess
import threading
import time
import traceback

HERE=Path(__file__).resolve().parent
BUILD=HERE/'postrelease-v1-scientific'
ROOT=Path('/Users/paurel/Documents/ChatGPT/bootscience')
LEAN=ROOT/'.runtime/elan/toolchains/leanprover--lean4---v4.35.0/bin/lean'

def require(c,m):
    if not c: raise AssertionError(m)

def environment():
    e=dict(os.environ);e['LEAN_PATH']=str(BUILD);return e

def compressed_total():
    return sum(p.stat().st_size for p in HERE.rglob('*.gz'))

def scoped_adapter():
    source=(HERE/'ProducerAudit.lean').read_text()
    source=source.replace('elab "audit_producers " pref:str','elab "audit_selected " pref:str')
    source=source.replace('if moduleName.toString.startsWith p then',
                          'if (p.splitOn ",").contains moduleName.toString then')
    path=BUILD/'PostreleaseProducerAudit.lean'
    if path.exists():require(path.read_text()==source,'adapter source drift')
    else:path.write_text(source)
    start=time.perf_counter()
    p=subprocess.run([str(LEAN),'-o','PostreleaseProducerAudit.olean','PostreleaseProducerAudit.lean'],
                     cwd=BUILD,env=environment(),text=True,capture_output=True,timeout=60)
    row={'source_sha256':hashlib.sha256(path.read_bytes()).hexdigest(),'exit_code':p.returncode,
         'seconds':time.perf_counter()-start,'stdout':p.stdout,'stderr':p.stderr,'timeout_seconds':60}
    require(p.returncode==0,'adapter compile failed: '+p.stdout)
    return row

def stream_scan(modules,label):
    require(shutil.disk_usage(HERE).free>=3*2**30,'disk floor before scan')
    require(compressed_total()<256*2**20,'compressed cap before scan')
    stem='IndependentDag'+label
    source=BUILD/(stem+'.lean')
    source.write_text('\n'.join('import '+m for m in modules)+
                      '\nimport PostreleaseProducerAudit\naudit_selected '+json.dumps(','.join(modules))+'\n')
    output=HERE/('postrelease-v1-dag-'+label+'.ndjson.gz')
    require(not output.exists(),'refuse compressed evidence overwrite')
    messages=queue.Queue()
    p=subprocess.Popen([str(LEAN),source.name],cwd=BUILD,env=environment(),stdout=subprocess.PIPE,stderr=subprocess.PIPE)
    def pump(pipe,kind):
        try:
            while True:
                data=pipe.read(65536)
                if not data:break
                messages.put((kind,data))
        finally:messages.put((kind,None))
    for pipe,kind in ((p.stdout,'stdout'),(p.stderr,'stderr')):
        threading.Thread(target=pump,args=(pipe,kind),daemon=True).start()
    start=time.perf_counter();closed=set();stderr=bytearray();raw_bytes=0;reason=None
    with output.open('wb') as file:
        with gzip.GzipFile(fileobj=file,mode='wb',mtime=0) as compressed:
            while len(closed)<2:
                try:
                    kind,data=messages.get(timeout=.1)
                    if data is None:closed.add(kind)
                    elif kind=='stdout':compressed.write(data);raw_bytes+=len(data)
                    else:stderr.extend(data)
                except queue.Empty:pass
                elapsed=time.perf_counter()-start
                if reason is None:
                    if elapsed>60:reason='60 second timeout'
                    elif shutil.disk_usage(HERE).free<3*2**30:reason='3 GiB live floor'
                    elif compressed_total()>256*2**20:reason='256 MiB compressed cap'
                    if reason:p.kill()
    code=p.wait(timeout=5)
    row={'modules':modules,'source':str(source.relative_to(ROOT)),'source_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),
         'seconds':time.perf_counter()-start,'timeout_seconds':60,'exit_code':code,'stop_reason':reason,
         'stderr':stderr.decode(errors='replace'),'gzip_path':str(output.relative_to(ROOT)),
         'gzip_sha256':hashlib.sha256(output.read_bytes()).hexdigest(),'compressed_bytes':output.stat().st_size,
         'uncompressed_bytes':raw_bytes,'disk_free_after':shutil.disk_usage(HERE).free}
    records=0;raw=0;merged=0;nodes=0;max_line=0;kind_counts={};summaries=[];errors=[]
    with gzip.open(output,'rt') as stream:
        for line in stream:
            max_line=max(max_line,len(line))
            if not line.startswith('PRODUCER '):
                if line.strip():errors.append(line[:2000])
                continue
            record=json.loads(line[9:]);records+=1
            layer=record['layer']
            if layer=='summary':summaries.append(record);continue
            producer=record['producer']
            if layer=='raw-module':
                raw+=1;kind_counts[producer['kind']]=kind_counts.get(producer['kind'],0)+1
                for expr in [producer['type'],producer['body']]+[r['rhs'] for r in producer['rules']]:
                    if expr is not None:nodes+=len(expr['nodes'])
            else:merged+=1
    row.update(records=records,raw_producers=raw,coalesced_producers=merged,dag_nodes_raw=nodes,
               maximum_record_bytes=max_line,kind_counts=kind_counts,summaries=summaries,diagnostics=errors)
    require(code==0 and reason is None and not errors,'DAG scan failed: '+str(row))
    require(len(summaries)==1 and summaries[0]['raw_occurrences']==raw,'DAG denominator')
    return row

def main():
    p=argparse.ArgumentParser();p.add_argument('--pilot',action='store_true');p.add_argument('--out',required=True)
    a=p.parse_args();out=Path(a.out);require(not out.exists(),'refuse receipt overwrite')
    start=time.perf_counter();result={'pilot':a.pilot,'scans':[],'disk_free_before':shutil.disk_usage(HERE).free}
    try:
        require(result['disk_free_before']>=3*2**30,'disk floor')
        build=json.loads((HERE/'postrelease-v1-build-full.json').read_text())
        require(build['status']=='PASS','fresh complete build prerequisite')
        modules=[r['module'] for r in build['closure']]
        if a.pilot:
            result['adapter_compile']=scoped_adapter()
            selected=['Bridge','Geometry','ForestPretestSemantics']
            result['scans'].append(stream_scan(selected,'Pilot'))
        else:
            pilot=json.loads((HERE/'postrelease-v1-dag-pilot.json').read_text())
            require(pilot['status']=='PASS','DAG pilot prerequisite')
            done=set(pilot['scans'][0]['modules'])
            remaining=[m for m in modules if m not in done]
            for i in range(0,len(remaining),8):
                result['scans'].append(stream_scan(remaining[i:i+8],f'Full{i//8:02}'))
                out.write_text(json.dumps(result,indent=2)+'\n')
        result['status']='PASS'
    except BaseException:
        result['status']='FAIL';result['failure']=traceback.format_exc()
    finally:
        result['seconds']=time.perf_counter()-start;result['compressed_total']=compressed_total()
        result['disk_free_after']=shutil.disk_usage(HERE).free
        out.write_text(json.dumps(result,indent=2)+'\n')
        print(json.dumps({k:result[k] for k in ('status','pilot','seconds','compressed_total','disk_free_after')}
                         | {'scans':len(result['scans']),'receipt':str(out)}))
    return 0 if result['status']=='PASS' else 1

if __name__=='__main__':raise SystemExit(main())
