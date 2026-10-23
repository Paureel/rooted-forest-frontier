#!/usr/bin/env python3
"""One-shot independent isolated compiler/axiom replay; author audit not reused."""
import hashlib
import json
import os
import re
import subprocess
import time
from pathlib import Path

HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[4]
BUILD=HERE/'lean-isolated'
OUT=ROOT/'research/rmaf/results'
ALLOWED={'propext','Classical.choice','Quot.sound'}
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def clean(s):
    out=[];i=depth=0
    while i<len(s):
        if s[i:i+2]=='/-':depth+=1;i+=2
        elif depth and s[i:i+2]=='-/':depth-=1;i+=2
        elif depth:i+=1
        elif s[i:i+2]=='--':
            j=s.find('\n',i);i=len(s) if j<0 else j
        else:out.append(s[i]);i+=1
    assert depth==0
    return ''.join(out)
def theorem_names(path):
    namespace=[];names=[]
    for line in clean(path.read_text()).splitlines():
        ns=re.fullmatch(r'namespace\s+(\S+)\s*',line)
        if ns:namespace.append(ns[1])
        if re.fullmatch(r'end(?:\s+\S+)?\s*',line) and namespace:namespace.pop()
        th=re.match(r'^theorem\s+(\w+)',line)
        if th:names.append('.'.join(namespace+[th[1]]))
    return names
def compile_source(module,negative=False):
    p=BUILD/(module+'.lean');src=p.read_text()
    forbidden=re.findall(r'\b(?:sorry|admit|axiom|native_decide)\b',clean(src));assert not forbidden,(module,forbidden)
    env=dict(os.environ,LEAN_PATH=str(BUILD))
    cmd=[str(ROOT/'bootloops-lean')]
    if not negative:cmd += ['-o',str(BUILD/(module+'.olean'))]
    cmd += [str(p)]
    before=time.perf_counter();r=subprocess.run(cmd,cwd=ROOT,env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
    log=BUILD/(module+'.fresh.log');log.write_text(r.stdout)
    row=dict(module=module,source=str(p.relative_to(ROOT)),source_sha256=sha(p),log=str(log.relative_to(ROOT)),log_sha256=sha(log),exit=r.returncode,seconds=time.perf_counter()-before,negative=negative,forbidden=forbidden)
    if negative:
        expected=len(theorem_names(p));actual=r.stdout.count('proved that the proposition')
        row.update(expected_false_diagnostics=expected,actual_false_diagnostics=actual,
                   passed=r.returncode!=0 and actual==expected and r.stdout.count('is false')==expected)
    else:row['passed']=r.returncode==0
    print(json.dumps(row),flush=True)
    return row

import argparse
parser=argparse.ArgumentParser();parser.add_argument('--phase',choices=['pilot','full'],required=True);args=parser.parse_args()
if args.phase=='pilot':
    row=compile_source('Geometry');dest=OUT/'algorithm-geometry-fresh-review-lean-pilot.json';assert not dest.exists();dest.write_text(json.dumps(row,indent=2)+'\n');assert row['passed'];raise SystemExit(0)
pilot=json.loads((OUT/'algorithm-geometry-fresh-review-lean-pilot.json').read_text());assert pilot['passed'] and sha(BUILD/'Geometry.lean')==pilot['source_sha256']
rows=[pilot]
for module in ['RMAF','Bridge','Composition','Controls','GeometryFreshControls']:
    row=compile_source(module);rows.append(row)
    if not row['passed']:
        (OUT/'algorithm-geometry-fresh-review-lean-failed.json').write_text(json.dumps({'rows':rows},indent=2)+'\n');raise SystemExit(1)
names=[name for module in ['RMAF','Geometry','Bridge','Composition','Controls','GeometryFreshControls'] for name in theorem_names(BUILD/(module+'.lean'))]
assert len(names)==len(set(names))
audit=BUILD/'FreshAxioms.lean';assert not audit.exists();audit.write_text('import Controls\nimport GeometryFreshControls\n'+'\n'.join('#print axioms '+name for name in names)+'\n')
row=compile_source('FreshAxioms');rows.append(row);assert row['passed']
log=(BUILD/'FreshAxioms.fresh.log').read_text()
matches=re.findall(r"'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",log,re.S)
axioms={name:sorted({x.strip() for x in deps.split(',') if x.strip()}) for name,deps in matches}
assert set(axioms)==set(names) and all(set(a)<=ALLOWED for a in axioms.values())
for module in ['FalseControl','GeometryFreshNegative']:
    row=compile_source(module,True);rows.append(row);assert row['passed']
author=json.loads((ROOT/'research/rmaf/algorithm/universal233/geometry/certificate.json').read_text())
assert {name:axioms[name] for name in author['axioms']}==author['axioms']
receipt={'scope':'independent isolated replay of exact frozen geometry sources plus pre-candidate finite controls; not whole algorithm acceptance','same_reviewer_lineage':True,'additional_independent_replications':0,'all_passed':True,'rows':rows,'theorem_names':names,'axiom_inventory':axioms,'candidate_axiom_inventory_matches_author':True,'source_sha256':sha(Path(__file__)),'generation_adapter_sha256':sha(HERE/'prepare_replay.py'),'open_obligations':['OPEN-STATE-ORIGINAL','OPEN-CORE-REALIZATION','remaining source rules, termination, reconstruction and all charged costs']}
dest=OUT/'algorithm-geometry-fresh-review-lean.json';assert not dest.exists();dest.write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps({'all_passed':True,'modules_replayed':len(rows),'allowed_axioms_only':True,'explicit_false_controls_rejected':sum(r.get('actual_false_diagnostics',0) for r in rows)}))
