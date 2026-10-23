#!/usr/bin/env python3
"""One-shot, source-bound Lean control replay; no prior checker imports."""
import hashlib,json,os,pathlib,shutil,subprocess,time
ROOT=pathlib.Path(__file__).resolve().parents[5]
HERE=pathlib.Path(__file__).resolve().parent
BUILD=HERE/'build'
SOURCES=[ROOT/'research/rmaf/lean/RMAF.lean',ROOT/'research/rmaf/pure_bridge/lean/PureBridge.lean',ROOT/'research/rmaf/bridge_review/lean/GraphRegion.lean',ROOT/'research/rmaf/bridge_review/executable/lean/ExecutableConnectivity.lean',ROOT/'research/rmaf/bridge_review/leastness/address_semantics/TreeAddresses.lean',ROOT/'research/rmaf/bridge_review/leastness/lean/ExtractorLeastness.lean',ROOT/'research/rmaf/bridge_review/leastness/lean/ActualEmbedding.lean',HERE/'lean/GraphRouteControls.lean']
rows=[];env=os.environ.copy();env['LEAN_PATH']=str(BUILD)
for src in SOURCES:
    dst=BUILD/src.name;shutil.copyfile(src,dst)
    start=time.perf_counter()
    run=subprocess.run([str(ROOT/'bootloops-lean'),'-o',str(dst.with_suffix('.olean')),str(dst)],cwd=ROOT,env=env,text=True,capture_output=True,timeout=60)
    log=BUILD/(src.stem+'.log');log.write_text(run.stdout+run.stderr)
    rows.append(dict(source=str(src.relative_to(ROOT)),source_sha256=hashlib.sha256(src.read_bytes()).hexdigest(),exit=run.returncode,seconds=time.perf_counter()-start,log_sha256=hashlib.sha256(log.read_bytes()).hexdigest()))
    if run.returncode: raise RuntimeError((src,run.stdout,run.stderr))
for src in sorted((HERE/'lean/negative').glob('*.lean')):
    start=time.perf_counter();run=subprocess.run([str(ROOT/'bootloops-lean'),str(src)],cwd=ROOT,env=env,text=True,capture_output=True,timeout=30)
    log=BUILD/(src.stem+'.log');log.write_text(run.stdout+run.stderr)
    caught=run.returncode!=0 and 'is false' in log.read_text()
    rows.append(dict(source=str(src.relative_to(ROOT)),source_sha256=hashlib.sha256(src.read_bytes()).hexdigest(),exit=run.returncode,seconds=time.perf_counter()-start,explicit_false=caught,log_sha256=hashlib.sha256(log.read_bytes()).hexdigest()))
    if not caught: raise RuntimeError((src,run.stdout,run.stderr))
(HERE/'lean-controls-receipt.json').write_text(json.dumps({'results':rows,'positive_modules':len(SOURCES),'explicit_false_controls':6,'scope':'Actual executable fixture checks only; dependency sources rebuilt and hash-bound'},indent=2)+'\n')
print(json.dumps({'positive_modules':len(SOURCES),'explicit_false_controls':6,'seconds':sum(r['seconds'] for r in rows)}))
