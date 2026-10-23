#!/usr/bin/env python3
"""One-shot exact released source inventory/rebuild; no prebuilt scientific oleans."""
import argparse, hashlib, json, os, re, subprocess, time
from pathlib import Path
P=Path(__file__).resolve().parent; ROOT=P.parents[6]
LEAN=ROOT/'.runtime/elan/toolchains/leanprover--lean4---v4.35.0/bin/lean'
MANIFEST=ROOT/'research/rmaf/algorithm/universal233/cherry_branching/CHERRY-BRANCH-MANIFEST-v1.json'
SHA='5ffb1fa6e9810485f60ced7e4e5d9cccc0f915fa95e9ba9e4998550b17eebe5d'
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def inventory():
    assert sha(MANIFEST)==SHA
    d=json.loads(MANIFEST.read_text()); fs=d['immutable_files']; assert len(fs)==290
    for f in fs:
        p=ROOT/f['path']; assert sha(p)==f['sha256'] and p.stat().st_size==f['bytes'],f['path']
    directory=Path(d['canonical_receipt']).parent
    banned={'ModuleAudit','PlantAudit','AuditPlant','FalseControl','FalseControls','FalsePreControls','TrueControl'}
    src=P/'sources'; src.mkdir(exist_ok=True); modules={}
    for f in fs:
        p=Path(f['path']); n=p.stem
        if p.parent!=directory or p.suffix!='.lean' or n in banned: continue
        raw=(ROOT/p).read_bytes(); (src/p.name).write_bytes(raw)
        imports=[m for line in re.findall(r'^import\s+(.+)$',raw.decode(),re.M) for m in line.split()]
        modules[n]={'module':n,'source':str(p),'sha256':f['sha256'],'imports':imports}
    order=[]; visiting=set()
    def visit(n):
        if n in order: return
        assert n not in visiting,('cycle',n)
        visiting.add(n)
        for m in modules[n]['imports']:
            if m in {'Std','Lean'}: continue
            assert m in modules,('missing exact import',n,m)
            visit(m)
        visiting.remove(n); order.append(n)
    for n in sorted(modules): visit(n)
    (P/'source-inventory-v2.json').write_text(json.dumps({'candidate_sha256':SHA,'payloads_checked':290,'copied_oleans':0,'sources':list(modules.values()),'topological_order':order,'excluded_author_instruments':sorted(banned)},indent=2)+'\n')
    return modules,order
def main():
    ap=argparse.ArgumentParser(); ap.add_argument('mode',choices=['pilot','remaining']); a=ap.parse_args()
    modules,order=inventory(); build=P/'build'; build.mkdir(exist_ok=True)
    selected=order[:4] if a.mode=='pilot' else order[4:]
    if a.mode=='pilot': assert not any(build.glob('*.olean')),'fresh build must start without scientific oleans'
    else: assert all((build/(n+'.olean')).exists() for n in order[:4]),'own pilot required'
    records=[]; at=time.perf_counter(); out=P/('build-'+a.mode+'-run1.json')
    env=dict(os.environ); env['LEAN_PATH']=str(build)
    try:
        for n in selected:
            start=time.perf_counter(); cmd=[str(LEAN),'-o',str(build/(n+'.olean')),str(P/'sources'/(n+'.lean'))]
            r=subprocess.run(cmd,cwd=P/'sources',env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=120)
            (P/('build-'+n+'-run1.log')).write_text(r.stdout)
            records.append({'module':n,'command':cmd,'returncode':r.returncode,'seconds':time.perf_counter()-start,'source_sha256':sha(P/'sources'/(n+'.lean')),'olean_sha256':sha(build/(n+'.olean')) if r.returncode==0 else None})
            out.write_text(json.dumps({'mode':a.mode,'records':records,'completed':len(records),'expected':len(selected),'seconds':time.perf_counter()-at,'scope':'exact isolated rebuild only'},indent=2)+'\n')
            assert r.returncode==0,('source rebuild failed',n,r.stdout[-2000:])
        for n,v in modules.items(): assert sha(P/'sources'/(n+'.lean'))==v['sha256']
        print(json.dumps({'mode':a.mode,'modules':len(records),'total_sources':len(modules),'seconds':time.perf_counter()-at}))
    finally:
        if not out.exists(): out.write_text(json.dumps({'mode':a.mode,'records':records,'seconds':time.perf_counter()-at})+'\n')
if __name__=='__main__': main()
