#!/usr/bin/env python3
"""One-shot leastness evidence audit; no mathematical derivation/enumeration.

Emitall GUIDE was checked: its numeric receipt comparisons do not classify Lean
imports/defs or malformed-proof semantics, so this small project adapter checks
those evidence categories and literal source hashes. Expected fixtures are the
separately frozen CONTROLS.json, never generated from this checker.
Usage: ./bootloops-python .../bookkeeping_audit.py [normalized-real-input.json]
Output: control-receipt.json and, if input given, audit-receipt.json. A passed
bookkeeping audit is not a proof, independent kernel, or novelty acceptance.
"""
import copy, hashlib, json, sys, time
from pathlib import Path
BASE=Path(__file__).resolve().parent

def check(x):
    errors=[]
    for d in x['declarations']:
        if d['count_as_new'] and d['origin']!='local': errors.append('imported_as_new')
        if d['count_as_new'] and d['kind']!='theorem': errors.append('definition_as_theorem')
    count=sum(d['origin']=='local' and d['kind']=='theorem' for d in x['declarations'])
    if count!=x['advertised_new_count']: errors.append('new_count_mismatch')
    for d in x['diagnostics']:
        if d['result']=='malformed_proof_failure' and d['claim']!='diagnostic_only': errors.append('malformed_as_false')
    for c in x['finite_checks']:
        if c['claim']!='finite_only': errors.append('finite_as_universal')
    for b in x['bindings']:
        actual=hashlib.sha256(Path(b['path']).read_bytes()).hexdigest() if 'path' in b else b['actual']
        if actual!=b['expected']: errors.append('source_hash_mismatch')
    return {'accepted':not errors,'errors':errors,'new_theorem_count':count}

def main():
    start=time.monotonic()
    p=BASE/'CONTROLS.json'
    f=json.loads(p.read_text())
    positive=check(f['positive']); null=check(f['null'])
    rows=[]
    for c in f['corruptions']:
        x=copy.deepcopy(f['positive']); target=x
        for key in c['path'][:-1]: target=target[key]
        target[c['path'][-1]]=c['value']
        got=check(x)
        rows.append({'id':c['id'],'expected_error':c['expected_error'],'result':got,'caught':c['expected_error'] in got['errors']})
    controls={'schema_version':1,'controls_sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'positive':positive,'null':null,'negative_controls':rows,'passed':positive['accepted'] and null['accepted'] and len(rows)==5 and all(r['caught'] for r in rows),'elapsed_seconds':time.monotonic()-start}
    (BASE/'control-receipt.json').write_text(json.dumps(controls,indent=2)+'\n')
    if not controls['passed']: raise SystemExit('CONTROL FAILURE')
    if len(sys.argv)>1:
        inp=Path(sys.argv[1]); result=check(json.loads(inp.read_text()))
        result.update({'input_sha256':hashlib.sha256(inp.read_bytes()).hexdigest(),'controls_sha256':controls['controls_sha256'],'script_sha256':controls['script_sha256'],'elapsed_seconds':time.monotonic()-start})
        (BASE/'audit-receipt.json').write_text(json.dumps(result,indent=2)+'\n')
        print(json.dumps(result))
        return 0 if result['accepted'] else 1
    print(json.dumps(controls))
    return 0
if __name__=='__main__': raise SystemExit(main())
