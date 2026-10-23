#!/usr/bin/env python3
"""Rebuild pinned dependency, graph proofs, axiom inventory and false controls.
One-campaign formal audit; its compile records do not certify graph extraction.
"""
import hashlib, json, os, re, subprocess, time
from pathlib import Path
root=Path(__file__).resolve().parents[3]
base=root/'research/rmaf/bridge_review/lean';audit=base/'audit';deps=audit/'deps';deps.mkdir(exist_ok=True)
env=os.environ.copy();env['LEAN_PATH']=str(deps)+':'+str(base)
receipt={'scope':'G1 graph support realization and original deepest-root consumer; executable extraction and G2–G7 remain open',
    'status':'pending','source_hashes':{},'builds':{},'axioms':{},'false_controls':{}}
def execute(name,path,output=None,expect_success=True):
    args=[str(root/'bootloops-lean')]
    if output: args+=['-o',str(output)]
    args+=[str(path)]
    started=time.perf_counter();p=subprocess.run(args,cwd=root,env=env,capture_output=True,text=True)
    log=p.stdout+p.stderr;(audit/(name+'.log')).write_text(log)
    record={'exit_code':p.returncode,'seconds':time.perf_counter()-started,'log':str((audit/(name+'.log')).relative_to(root))}
    assert (p.returncode==0)==expect_success,(name,p.returncode,log)
    if expect_success:
        assert 'sorryAx' not in log
        for theorem,body in re.findall(r"'([^']+)' (does not depend on any axioms|depends on axioms: \[[^\]]*\])",log,re.S):
            values=[] if body.startswith('does not') else [x.strip() for x in body.split('[',1)[1].rstrip(']').split(',')]
            assert set(values)<= {'propext','Classical.choice','Quot.sound'},(theorem,values)
            receipt['axioms'][theorem]=values
        receipt['builds'][name]=record
    else:
        assert 'error:' in log and ('failed' in log.lower() or 'is false' in log.lower()),(name,log)
        record['rejected']=True;receipt['false_controls'][name]=record
    return log
sources=[root/'research/rmaf/pure_bridge/lean/PureBridge.lean',base/'GraphRegion.lean',base/'GraphControls.lean',*sorted((base/'negative').glob('*.lean'))]
for p in sources:
    receipt['source_hashes'][str(p.relative_to(root))]=hashlib.sha256(p.read_bytes()).hexdigest()
    if 'negative' not in p.parts:
        assert not re.search(r'^\s*(axiom|opaque)\b|\b(sorry|admit|native_decide)\b',p.read_text(),re.M),p
execute('dependency-PureBridge',sources[0],deps/'PureBridge.olean')
execute('GraphRegion',base/'GraphRegion.lean',base/'GraphRegion.olean')
execute('GraphControls',base/'GraphControls.lean',base/'GraphControls.olean')
for p in sorted((base/'negative').glob('*.lean')): execute(p.stem,p,expect_success=False)
receipt['review_theorem_count']=sum(bool(re.search(r'^theorem\s',line)) for p in (base/'GraphRegion.lean',base/'GraphControls.lean') for line in p.read_text().splitlines())
receipt['status']='kernel-checked-graph-interface'
(audit/'certificate.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps({'status':receipt['status'],'review_theorem_count':receipt['review_theorem_count'],'false_controls':len(receipt['false_controls'])}))
