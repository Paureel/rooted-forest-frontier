#!/usr/bin/env python3
"""One-shot fresh reviewer build runner; no candidate/checker code reused.
Copies exact audited sources into this review directory, compiles dependencies
in order with only that directory as LEAN_PATH, retains logs and hashes.
"""
import argparse, hashlib, json, os, re, shutil, subprocess, time
from pathlib import Path
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[4]
BUILD=HERE/'build'
SOURCES={
 'RMAF':'research/rmaf/lean/RMAF.lean',
 'PureBridge':'research/rmaf/pure_bridge/lean/PureBridge.lean',
 'GraphRegion':'research/rmaf/bridge_review/lean/GraphRegion.lean',
 'ExecutableConnectivity':'research/rmaf/bridge_review/executable/lean/ExecutableConnectivity.lean',
 'TreeAddresses':'research/rmaf/bridge_review/leastness/address_semantics/TreeAddresses.lean',
 'ExtractorLeastness':'research/rmaf/bridge_review/leastness/lean/ExtractorLeastness.lean',
 'ActualEmbedding':'research/rmaf/bridge_review/leastness/lean/ActualEmbedding.lean'}
def digest(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def freeze():
    BUILD.mkdir(exist_ok=True)
    rows=[]
    for module,path in SOURCES.items():
        src=ROOT/path; dst=BUILD/(module+'.lean')
        shutil.copyfile(src,dst)
        assert src.read_bytes()==dst.read_bytes()
        rows.append(dict(module=module,source=str(src),snapshot=str(dst),sha256=digest(src),
                         imports=re.findall(r'^import (.*)$',src.read_text(),re.M)))
    assert next(r['sha256'] for r in rows if r['module']=='TreeAddresses') == 'f2bbd08201b98893a0e824f041e9af72761933d7f29b4e9a89088d9d9e46fdb0'
    (HERE/'source-manifest.json').write_text(json.dumps(rows,indent=2)+'\n')
    print(json.dumps(rows))
def compile_modules(modules, receipt):
    rows=[]
    env=os.environ.copy(); env['LEAN_PATH']=str(BUILD)
    for name in modules:
        src=BUILD/(name+'.lean')
        t=time.monotonic()
        proc=subprocess.run([str(ROOT/'bootloops-lean'),'-o',str(BUILD/(name+'.olean')),str(src)],
                            cwd=BUILD,env=env,capture_output=True,text=True,timeout=60)
        text=proc.stdout+proc.stderr
        (HERE/(name+'.log')).write_text(text)
        row=dict(module=name,returncode=proc.returncode,seconds=time.monotonic()-t,
                 source_sha256=digest(src),log=str(HERE/(name+'.log')))
        rows.append(row)
        (HERE/receipt).write_text(json.dumps(rows,indent=2)+'\n')
        print(json.dumps(row),flush=True)
        if proc.returncode: raise SystemExit(proc.returncode)
if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('mode',choices=['freeze','pilot','full','review']);a=p.parse_args()
    if a.mode=='freeze':freeze()
    elif a.mode=='pilot':compile_modules(['RMAF'],'build-pilot.json')
    elif a.mode=='full':compile_modules(list(SOURCES)[1:],'build-main.json')
    else:compile_modules(['ReviewerChecks'],'build-review.json')
