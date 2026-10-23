#!/usr/bin/env python3
"""Cold isolated source build, restricted to exact released canonical payload.
No author build/audit code executed and no scientific oleans copied.
"""
import argparse, hashlib, json, os, pathlib, re, subprocess, time

ROOT=pathlib.Path('/Users/paurel/Documents/ChatGPT/bootscience')
HERE=pathlib.Path(__file__).resolve().parent
SRC=ROOT/'results/algorithm-universal233-both-bad-20261015T115125Z'
BUILD=HERE/'build'
WRAPPER=ROOT/'bootloops-lean'

def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def write(name,d): (HERE/name).write_text(json.dumps(d,indent=2,sort_keys=True)+'\n')

def main():
    ap=argparse.ArgumentParser();ap.add_argument('mode',choices=['pilot','full']);args=ap.parse_args()
    manifest=json.loads((ROOT/'research/rmaf/algorithm/universal233/both_bad/BOTH-BAD-MANIFEST-v1.json').read_text())
    pins={row['path']:row['sha256'] for row in manifest['immutable_files']}
    receipt=json.loads((SRC/'certificate.json').read_text())
    modules=[row['module'] for row in receipt['source_inputs']]
    assert len(modules)==160 and len(set(modules))==160
    BUILD.mkdir(exist_ok=True)
    copied=[]; imports={}
    for row in receipt['source_inputs']:
        name=row['module']; p=SRC/(name+'.lean'); rel=str(p.relative_to(ROOT))
        assert rel in pins and sha(p)==pins[rel]==row['adapted_sha256']
        dest=BUILD/p.name
        if dest.exists(): assert sha(dest)==sha(p)
        else: dest.write_bytes(p.read_bytes())
        text=dest.read_text()
        imports[name]=[x for line in text.splitlines() if re.match(r'^\s*(?:public\s+)?import\s+',line)
                       for x in re.sub(r'^\s*(?:public\s+)?import\s+','',line).split()]
        copied.append({'module':name,'source':rel,'sha256':sha(dest),'original_adaptations_from_receipt':row['adaptations']})
    allowed={'Std','Lean','Init'}
    assert all(i in modules or i in allowed for xs in imports.values() for i in xs)
    todo=set(modules);order=[]
    while todo:
        available=[n for n in modules if n in todo and not (set(imports[n])&todo)]
        assert available, 'cyclic source imports'
        order+=available;todo-=set(available)
    write('SOURCE-MAP-v1.json',{'copied_sources':copied,'imports':imports,'topological_order':order,
        'scientific_olean_copy_count':0,'isolated_LEAN_PATH':str(BUILD)})
    if args.mode=='pilot':
        assert not list(BUILD.glob('*.olean')), 'pilot must be cold'
        targets=order[:5]
    else: targets=order
    results=[];start=time.perf_counter();env=dict(os.environ,LEAN_PATH=str(BUILD))
    for name in targets:
        p=BUILD/(name+'.olean')
        # Pilot-built files are accepted only when their original own log exists.
        if args.mode=='full' and p.exists():
            prior=json.loads((HERE/'build-pilot.json').read_text())
            assert any(r['module']==name and r['exit']==0 for r in prior['results'])
            results.append({'module':name,'state':'own-pilot-already-built','exit':0});continue
        t=time.perf_counter()
        res=subprocess.run([str(WRAPPER),'-o',p.name,name+'.lean'],cwd=BUILD,env=env,
                           capture_output=True,text=True,timeout=60)
        (BUILD/(name+'.build.log')).write_text(res.stdout+res.stderr)
        row={'module':name,'seconds':time.perf_counter()-t,'exit':res.returncode,
             'source_sha256':sha(BUILD/(name+'.lean'))}
        results.append(row)
        write('build-'+args.mode+'.json',{'results':results,'elapsed_seconds':time.perf_counter()-start,
            'mode':args.mode,'completed':sum(r['exit']==0 for r in results),'target_count':len(targets)})
        print(json.dumps(row),flush=True)
        assert res.returncode==0,row
    print(json.dumps({'status':'SOURCE_BUILD_PASS','mode':args.mode,'count':len(targets),
                      'elapsed_seconds':time.perf_counter()-start}),flush=True)

if __name__=='__main__':main()
