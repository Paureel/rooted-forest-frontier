from pathlib import Path
import gzip,hashlib,json
D=Path(__file__).resolve().parent;R=D.parents[5];O=R/json.loads((D/'LATEST-AUDIT-v1.json').read_text())['directory'];x=json.loads((O/'certificate.json').read_text());assert x['status']=='PASS_AUTHOR_COMPLETE_CHERRY_SCAFFOLD_SOURCE_PRODUCER'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
rows=[]
for e in x['dependencies']:
 p=R/e['records'];assert sha(p)==e['records_sha256'];rows+=json.loads(gzip.decompress(p.read_bytes()))
for p in (O/'records-NewScaffold').glob('*.json.gz'):rows+=json.loads(gzip.decompress(p.read_bytes()))
g={}
for e in rows:g.setdefault(e['actual_name'],set()).update(e['direct_references'])
def reach(graph,roots):
 todo=list(roots);seen=set()
 while todo:
  n=todo.pop()
  if n in seen:continue
  seen.add(n);todo.extend(graph.get(n,[]))
 return seen
# Fresh planted reachability controls, before applying the unchanged walk.
assert 'ForbiddenGhost' in reach({'root':{'middle'},'middle':{'ForbiddenGhost'}},['root'])
assert 'ForbiddenGhost' not in reach({'root':{'safe'},'unused':{'ForbiddenGhost'}},['root'])
seen=reach(g,['OrdinaryScaffold.solve']);bad=sorted(n for n in seen if n.startswith('ForestMinCompletion.'))
assert not bad,bad
rec=dict(status='PASS_AUTHOR_LOCAL_REFERENCE_ABSENCE',scope='Conservative full direct-reference closure of actual selected local producers, including local proof/type references; Std/Lean/Init bodies are external. This is not compiled-machine callgraph semantics or independent verification.',roots=['OrdinaryScaffold.solve'],controls=['planted reachable forbidden name caught','unreachable forbidden name excluded'],reachable_local_names=sorted(n for n in seen if n in g),external_names=sorted(n for n in seen if n not in g),forbidden_prefix='ForestMinCompletion.',reached_forbidden_names=bad,audit_certificate_sha256=sha(O/'certificate.json'),instrument_sha256=sha(Path(__file__)))
p=O/'RUNTIME-LOCAL-REFERENCE-ABSENCE.json';p.write_text(json.dumps(rec,indent=2)+'\n');print(rec['status'],len(rec['reachable_local_names']),len(rec['external_names']))
