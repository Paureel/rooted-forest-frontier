from pathlib import Path
import json,gzip,sys
sys.dont_write_bytecode=True
import run,dag_instrument as ins
D=run.D;R=run.R;O=run.O;sha=run.sha
(O/'RADAGControls.lean').write_text('''import RABoundedAudit
open Lean Elab Command
run_cmd do
 let e:=Expr.app (.const `Nat []) (.const `Nat [])
 let (root,s)←match exprDAG e {} with | .ok d=>pure d | .error e=>throwError e
 unless root==1 && s.nodes.size==2 do throwError "DAG_SHARING_CONTROL_FAILED"
 let app:=s.nodes[1]!
 let edges←match app.getObjValAs? (Array Nat) "children" with | .ok a=>pure a | .error e=>throwError e
 unless edges==#[0,0] do throwError "DAG_EDGE_CONTROL_FAILED"
 logInfo "DAG_SHARED_CHILD_CONTROL_PASS"
''')
out=run.run('RADAGControls');assert 'DAG_SHARED_CHILD_CONTROL_PASS' in out
bad={'root':0,'nodes':[{'tag':'app','payload':None,'children':[0]}]}
try:ins.validate_dag(bad)
except AssertionError:pass
else:raise AssertionError('CYCLIC_DAG_CONTROL_FAILED')
rows=ins.parse(O/'producer-records-v1',['RAReceipt','RAState','RAAttempt','RAInterface','RAControls'],O)
# Cross-check the actual DAG constant nodes against independently exported references.
for row in rows:
 if row['body_dag']:
  consts={n['payload']['name'] for n in row['body_dag']['nodes'] if n['tag']=='const'}
  assert consts<=set(row['references']),(row['name'],consts-set(row['references']))
for n in ['Work','RCStorage','RILifetime','RSBinaryCompare']:
 try:run.run(n)
 except AssertionError as e:assert 'REFUSE_DEPENDENCY_REBUILD' in str(e)
 else:raise AssertionError('REBUILD_GUARD')
runs=[json.loads(p.read_text()) for p in O.glob('*.run.json')]
passruns=[x for x in runs if not x['stop_reasons']]
r={'status':'PASS_AUTHOR_DAG_SHARING_AND_REFERENCE_CONTROLS','certificate':'AUDIT-CERTIFICATE-v3.json','certificate_sha256':sha(O/'AUDIT-CERTIFICATE-v3.json'),'shared_child_DAG_nodes':2,'shared_child_edges':[0,0],'cyclic_DAG_rejected':True,'actual_body_constant_nodes_subset_exported_references':True,'no_rebuild_refusals':4,'peak_rss_bytes':max(x['peak_rss_bytes'] for x in passruns),'maximum_seconds':max(x['seconds'] for x in passruns),'compressed_bytes':sum(p.stat().st_size for p in O.rglob('*.gz')),'independent_credit':0,'native_runtime_open':True}
(O/'AUDIT-SUPPLEMENT-v1.json').write_text(json.dumps(r,indent=2)+'\n');print(r)