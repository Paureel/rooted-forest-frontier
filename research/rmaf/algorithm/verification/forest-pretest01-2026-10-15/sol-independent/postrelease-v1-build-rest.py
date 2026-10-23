#!/usr/bin/env python3
"""One-shot independent exact-source closure collector and measured rebuild.
Copies only pinned scientific .lean sources reached by literal imports;
never copies candidate oleans or author audit/control implementations.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import time
import traceback

HERE=Path(__file__).resolve().parent
ROOT=Path('/Users/paurel/Documents/ChatGPT/bootscience')
LEAN=ROOT/'.runtime/elan/toolchains/leanprover--lean4---v4.35.0/bin/lean'
BUILD=HERE/'postrelease-v1-scientific'
CANONICAL='results/algorithm-universal233-forest-pretest01-replay-20261015T181834296403Z/'

def require(condition,message):
    if not condition:
        raise AssertionError(message)

def without_comments(text):
    out=[]
    i=0
    depth=0
    while i<len(text):
        if text[i:i+2]=='/-':
            depth+=1;i+=2
        elif depth and text[i:i+2]=='-/':
            depth-=1;i+=2
        elif depth:
            out.append('\n' if text[i]=='\n' else ' ');i+=1
        elif text[i:i+2]=='--':
            end=text.find('\n',i)
            if end<0:break
            out.append('\n');i=end+1
        else:
            out.append(text[i]);i+=1
    require(depth==0,'unterminated comment')
    return ''.join(out)

def collect():
    packages=json.loads((HERE/'postrelease-v1-package-pins.json').read_text())
    lookup={Path(x['path']).stem:x for x in packages[0]['members']
            if x['path'].startswith(CANONICAL) and x['path'].endswith('.lean')}
    seen={}
    order=[]
    def visit(name):
        if name in seen:
            require(seen[name]=='done','import cycle: '+name)
            return
        require(name in lookup,'unlicensed missing scientific import: '+name)
        require(not name.startswith(('FP','APIProbe')),'unexpected author auditor dependency: '+name)
        x=lookup[name]
        source=ROOT/x['path']
        data=source.read_bytes()
        require(hashlib.sha256(data).hexdigest()==x['sha256'],'source pin mismatch: '+str(source))
        text=without_comments(data.decode())
        imports=[]
        for line in text.splitlines():
            match=re.match(r'^\s*(?:public\s+|meta\s+)?import\s+(.+)$',line)
            if match:
                imports.extend(match.group(1).split())
        seen[name]='active'
        scientific=[]
        standard=[]
        for dependency in imports:
            if dependency.split('.')[0] in ('Std','Init','Lean'):
                standard.append(dependency)
            else:
                scientific.append(dependency)
                visit(dependency)
        seen[name]='done'
        order.append({'module':name,'source':x['path'],'sha256':x['sha256'],
                      'imports':scientific,'trusted_runtime_imports':standard,'bytes':len(data)})
        destination=BUILD/(name+'.lean')
        if destination.exists():
            require(destination.read_bytes()==data,'fresh source drift: '+name)
        else:
            destination.write_bytes(data)
    BUILD.mkdir(exist_ok=True)
    for root in ('ForestPretestSemantics','ForestPretestWork'):
        visit(root)
    return order

def main():
    p=argparse.ArgumentParser()
    p.add_argument('--pilot',action='store_true')
    p.add_argument('--out',required=True)
    a=p.parse_args()
    out=Path(a.out)
    require(not out.exists(),'refuse evidence overwrite')
    started=time.perf_counter()
    result={'phase':'postrelease','pilot':a.pilot,'build_commands':[],
            'runtime_binary_sha256':hashlib.sha256(LEAN.read_bytes()).hexdigest(),
            'disk_free_before':shutil.disk_usage(HERE).free}
    try:
        require(result['disk_free_before']>=3*2**30,'disk floor before')
        order=collect()
        result['closure']=order
        selected=order[:5] if a.pilot else order
        pilot=json.loads((HERE/'postrelease-v1-build-pilot.json').read_text())
        require(pilot['status']=='PASS','pilot prerequisite')
        completed={row['module'] for row in pilot['build_commands']}
        result['reused_fresh_pilot']=[]
        for row in selected:
            name=row['module']
            if name in completed:
                output=BUILD/(name+'.olean')
                require(output.exists(),'fresh pilot output missing: '+name)
                result['reused_fresh_pilot'].append({'module':name,'olean_sha256':hashlib.sha256(output.read_bytes()).hexdigest(),
                                                    'pilot_receipt':'postrelease-v1-build-pilot.json'})
                continue
            require(shutil.disk_usage(HERE).free>=3*2**30,'disk floor: '+name)
            command=[str(LEAN),'-o',name+'.olean',name+'.lean']
            environment=dict(os.environ)
            environment['LEAN_PATH']=str(BUILD)
            start=time.perf_counter()
            attempt={'module':name,'command':command,'timeout_seconds':60}
            try:
                process=subprocess.run(command,cwd=BUILD,env=environment,text=True,capture_output=True,timeout=60)
                attempt.update(exit_code=process.returncode,stdout=process.stdout,stderr=process.stderr,
                               status='PASS' if process.returncode==0 else 'FAIL')
            except subprocess.TimeoutExpired as error:
                attempt.update(status='TIMEOUT',stdout=str(error.stdout or ''),stderr=str(error.stderr or ''))
            attempt['seconds']=time.perf_counter()-start
            result['build_commands'].append(attempt)
            # Preserve partial completed evidence after each scientific module.
            out.write_text(json.dumps(result,indent=2)+'\n')
            require(attempt['status']=='PASS','scientific build failed: '+name)
        result['status']='PASS'
    except BaseException:
        result['status']='FAIL'
        result['failure']=traceback.format_exc()
    finally:
        result['seconds']=time.perf_counter()-started
        result['disk_free_after']=shutil.disk_usage(HERE).free
        out.write_text(json.dumps(result,indent=2)+'\n')
        print(json.dumps({k:result[k] for k in ('status','pilot','seconds','disk_free_after')}
                         | {'closure':len(result.get('closure',[])),'commands':len(result['build_commands']),'receipt':str(out)}))
    return 0 if result['status']=='PASS' else 1

if __name__=='__main__':
    raise SystemExit(main())
