"""Author replay of completed stored-producer audit plus new value gate."""
from pathlib import Path
import datetime, hashlib, importlib.util, json, os, subprocess, sys

R = Path(__file__).resolve().parents[6]
D = Path(__file__).resolve().parent
B = Path(sys.argv[1]).resolve()
assert B.parent == R/'results' and B.name.startswith('algorithm-universal233-ordinary-source-pool-')
rec = json.loads((B/'construction.json').read_text())
assert rec['status']=='SOURCE_POOL_ALL_LITERAL_SOURCES_REBUILT_PENDING_ORIGIN_AND_COMPATIBILITY_AUDIT'
old = R/'research/rmaf/algorithm/universal233/rule5_common_split/audit_graph.py'
def load(name,path):
    spec = importlib.util.spec_from_file_location(name,path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module
audit = load('completed_occurrence_audit',old)
gate = load('producer_value_gate',D.parent/'producer_compatibility/compatibility.py')
names = [x['module'] for x in rec['source_modules']]
out = B/'producer-records'
out.mkdir(exist_ok=True)
p = B/'PoolOccurrenceAudit.lean'
p.write_text(audit.audit_source(names,names,out))
inputs = [Path(__file__),old,D.parent/'producer_compatibility/compatibility.py',B/'construction.json',p]
pin = {'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
       'phase':'before actual pooled master-import/stored-producer/value audit',
       'pins':[{'path':str(x.relative_to(R)),'sha256':hashlib.sha256(x.read_bytes()).hexdigest()} for x in inputs]}
(B/'AUDIT-PIN-v1.json').write_text(json.dumps(pin,indent=2)+'\n')
run = subprocess.run([str(R/'bootloops-lean'),str(p)],cwd=B,
    env=dict(os.environ,LEAN_PATH=str(B)),capture_output=True,text=True,timeout=60)
log=run.stdout+run.stderr
(B/'PoolOccurrenceAudit.log').write_text(log)
if run.returncode:
    (B/'AUDIT-FAILURE-v1.json').write_text(json.dumps({'status':'FAILED_MASTER_IMPORT_OR_ORIGIN_AUDIT','exit':run.returncode,'output':log},indent=2)+'\n')
    print(log)
    raise SystemExit(run.returncode)
index=json.loads((out/'index.json').read_text())
assert not index['rejects']
assert {x['producer'] for x in index['producer_counts']}==set(names)
rows=[]
for count in index['producer_counts']:
    actual=json.loads((out/count['file']).read_text())
    assert not audit.parse_producer(count,actual)
    rows.extend(actual)
compatibility=gate.inspect(rows)
(B/'PRODUCER-COMPATIBILITY-v1.json').write_text(json.dumps(compatibility,indent=2)+'\n')
assert not compatibility['rejects'],compatibility['rejects']
for x in rec['source_modules']:
    assert hashlib.sha256((B/(x['module']+'.lean')).read_bytes()).hexdigest()==x['sha256']
for x in pin['pins']:
    assert hashlib.sha256((R/x['path']).read_bytes()).hexdigest()==x['sha256']
result={'status':'AUTHOR_POOL_MASTER_IMPORT_SOURCE_ORIGIN_VALUE_COMPATIBILITY_PASS',
        'independent_acceptance':False,'full_algorithm':False,'all_three_main_milestones':'OPEN',
        'source_modules':len(names),'stored_producer_occurrences':len(rows),
        'resolved_unique_names':len({x['actual_name'] for x in rows}),
        'axiom_union':sorted(set().union(*(set(x['axiom_references']) for x in rows))),
        'nonproof_compatibility':'exact type/body gate; other duplicate nonproof metadata refused',
        'duplicate_groups':len(compatibility['duplicates']),
        'construction_sha256':hashlib.sha256((B/'construction.json').read_bytes()).hexdigest(),
        'audit_source_sha256':hashlib.sha256(p.read_bytes()).hexdigest(),
        'audit_scope':'completed author detector reuse; fresh nonproof controls; not a new independent review'}
(B/'AUDIT-RESULT-v1.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result))
