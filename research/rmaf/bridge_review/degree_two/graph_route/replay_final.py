#!/usr/bin/env python3
"""One-shot final source-bound replay. Output receipts belong to graph_route only.

This rebuilds the completed definitions and new formal intermediate, then runs
six frozen semantic falsity controls. It does not establish cross-tree transport.
"""
import hashlib,json,os,pathlib,re,shutil,subprocess,time
HERE=pathlib.Path(__file__).resolve().parent
ROOT=HERE.parents[4]
BUILD=HERE/'final-build'
BUILD.mkdir(exist_ok=True)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
accepted=json.loads((ROOT/'research/rmaf/bridge_review/leastness/acceptance.json').read_text())['source_hashes']
paths=['research/rmaf/lean/RMAF.lean','research/rmaf/pure_bridge/lean/PureBridge.lean','research/rmaf/bridge_review/lean/GraphRegion.lean','research/rmaf/bridge_review/executable/lean/ExecutableConnectivity.lean','research/rmaf/bridge_review/leastness/address_semantics/TreeAddresses.lean','research/rmaf/bridge_review/leastness/lean/ExtractorLeastness.lean','research/rmaf/bridge_review/leastness/lean/ActualEmbedding.lean']
source=[ROOT/p for p in paths]+[HERE/'lean'/p for p in ['GraphRouteControls.lean','DegreePropagation.lean','DegreePropagationControls.lean']]
rows=[];env=os.environ.copy();env['LEAN_PATH']=str(BUILD)
start_all=time.perf_counter()
for src in source:
    rel=str(src.relative_to(ROOT))
    if rel in accepted: assert sha(src)==accepted[rel], ('COMPLETED_PIN_MISMATCH',rel)
    else: assert not re.search(r'\b(sorry|admit|native_decide|axiom)\b',src.read_text()), ('FORBIDDEN_SOURCE',rel)
    dst=BUILD/src.name;shutil.copyfile(src,dst)
    start=time.perf_counter()
    run=subprocess.run([str(ROOT/'bootloops-lean'),'-o',str(dst.with_suffix('.olean')),str(dst)],cwd=ROOT,env=env,text=True,capture_output=True,timeout=60)
    log=BUILD/(src.stem+'.log');log.write_text(run.stdout+run.stderr)
    row=dict(source=rel,source_sha256=sha(src),exit=run.returncode,seconds=time.perf_counter()-start,log=str(log.relative_to(ROOT)),log_sha256=sha(log),source_bound_copy_sha256=sha(dst))
    rows.append(row)
    assert run.returncode==0 and 'sorryAx' not in log.read_text(), ('FAILED_BUILD',row)
    for axioms in re.findall(r'depends on axioms: \[(.*?)\]',log.read_text()):
        assert set(axioms.split(', ')) <= {'propext','Classical.choice','Quot.sound'}, ('CUSTOM_AXIOMS',axioms)
for src in sorted((HERE/'lean/negative').glob('*.lean')):
    start=time.perf_counter()
    run=subprocess.run([str(ROOT/'bootloops-lean'),str(src)],cwd=ROOT,env=env,text=True,capture_output=True,timeout=30)
    log=BUILD/(src.stem+'.log');log.write_text(run.stdout+run.stderr)
    caught=run.returncode!=0 and 'is false' in log.read_text()
    rows.append(dict(source=str(src.relative_to(ROOT)),source_sha256=sha(src),exit=run.returncode,seconds=time.perf_counter()-start,explicit_false=caught,log=str(log.relative_to(ROOT)),log_sha256=sha(log)))
    assert caught, ('NEGATIVE_NOT_EXPLICIT_FALSITY',src)
receipt={'created_utc':time.strftime('%Y-%m-%dT%H:%M:%SZ',time.gmtime()),'scope':'universal actual semantic degree propagation; finite refinement/consumer controls only','formal_target':'DegreeTwoGraph.actual_degree_propagation','degree_semantics':'ExactTwo enumerates precisely two distinct adjacent support vertices using GraphRegion.Adj; equivalent to undirected set degree two; no separate numeric-count equivalence theorem claimed','verdict':'COMPILES_PENDING_NONAUTHOR_REVIEW','results':rows,'seconds':time.perf_counter()-start_all,'missing_formal':['existence of deletion split with terminal-label correspondence','rooted restriction/isomorphism transport to actual u embeddings','general unchanged agreement-partition replacement consumer','G3/G4 and complete clearRest instance'],'diagnostic_attempts':'build/DegreePropagation-attempt*.lean and logs, CheckDegreeAPI logs; not proof evidence','checks_not_run':['project-wide bootloops-check','larger search','nonauthor review','novelty review']}
(HERE/'formal-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps({'verdict':receipt['verdict'],'seconds':receipt['seconds'],'positive_modules':len(source),'explicit_false_controls':6}))
