#!/usr/bin/env python3
"""One-shot same-source restriction pilot using the already frozen first case."""
import importlib.util,json,sys,time,hashlib
from pathlib import Path
HERE=Path(__file__).resolve().parent
source=HERE/'frozen-controls-v1/independent_rank_restriction.py'
sp=importlib.util.spec_from_file_location('own_rank_restriction_frozen',source)
m=importlib.util.module_from_spec(sp);sys.modules[sp.name]=m;sp.loader.exec_module(m)
pin=HERE/'frozen-controls-v1/CONTROL-PIN-v1.json'
spec=json.loads(pin.read_text());checks=m.Checks();start=time.monotonic()
result=m.restriction_case(spec['restriction_cases'][0],checks)
out={'phase':'PRERELEASE','verdict':'FROZEN-RESTRICTION-PILOT-PASSED','result':result,'checks':checks.rows,
     'literal_check_denominator':len(checks.rows),'seconds':time.monotonic()-start,
     'source_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),'spec_sha256':hashlib.sha256(pin.read_bytes()).hexdigest()}
assert out['seconds']<5
p=m.ROOT/'research/rmaf/results/algorithm-rank-restriction-fresh-restriction-pilot-v1.json'
p.write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({'verdict':out['verdict'],'seconds':out['seconds'],'literal_checks':len(checks.rows),'transports':len(result['transports'])}))
