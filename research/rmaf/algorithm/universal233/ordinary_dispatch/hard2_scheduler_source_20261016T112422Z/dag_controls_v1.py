from pathlib import Path
import copy,importlib.util,json,sys
sys.dont_write_bytecode=True
D=Path(__file__).resolve().parent
s=importlib.util.spec_from_file_location('bounded_dag_engine',D/'dag_engine_v1.py');E=importlib.util.module_from_spec(s);s.loader.exec_module(E)
B=E.B;R=E.R;O=B/'dag-controls-v1';O.mkdir()
rec=dict(status='CHECKING',independent=False,controls={})
def save():(O/'controls.json').write_text(json.dumps(rec,indent=2)+'\n')
def rejects(label,lines):
 try:E.validate(lines)
 except (AssertionError,KeyError,TypeError,IndexError) as e:rec['controls'][label]=dict(rejected=True,reason=str(e));save();return
 raise AssertionError(('CORRUPTION_ACCEPTED',label))
save()
try:
 a,ar=E.export(O,'Zero',['DAGControlZero'],'DAGControlZero',0,1)
 b,br=E.export(O,'One',['DAGControlOne'],'DAGControlOne',0,1)
 assert a['rows'][0]['type']==b['rows'][0]['type'] and a['rows'][0]['body']!=b['rows'][0]['body']
 rec['controls']['changed_literal_body']=dict(passed=True,zero=ar,one=br)
 bad,badr=E.export(O,'Bad',['DAGControlBad'],'DAGControlBad',0,2,True)
 row=next(r for r in bad['rows'] if r['actual_name']=='dag_control_hidden_proof')
 assert 'dag_control_custom_axiom' in row['direct_references'] and 'dag_control_custom_axiom' in row['axiom_references']
 rec['controls']['proof_only_custom_axiom']=dict(rejected=True,receipt=badr)
 z=copy.deepcopy(a['raw_lines']);del z[-2];rejects('missing_stored_occurrence',z)
 z=copy.deepcopy(a['raw_lines']);z.insert(-1,copy.deepcopy(z[-2]));rejects('duplicate_stored_occurrence',z)
 z=copy.deepcopy(a['raw_lines']);z[-2]['resolved_origin']='invented';rejects('wrong_producer_origin',z)
 z=copy.deepcopy(a['raw_lines']);node=next(x for x in z if x['record']=='node');node['children']=[node['id']];rejects('forward_or_cyclic_node',z)
 # This exponential expanded tree has only 26 distinct nodes. Binder names
 # must remain distinct even though Expr's default BEq is alpha equality.
 folder=O/'sharing';folder.mkdir()
 src='''import BoundedExprDAG
open Lean Elab Command BoundedExprDAG
run_cmd do
 let mut e:=mkConst `Nat.zero
 for _ in [:25] do e:=mkApp e e
 let action:Dump (Nat×Nat×Nat):=do
  let a←expr e
  let x←expr (.lam `x (.sort .zero) (.bvar 0) .default)
  let y←expr (.lam `y (.sort .zero) (.bvar 0) .default)
  return (a,x,y)
 let ((a,x,y),s)←liftIO <| action.run {dir:='''+json.dumps(str(folder))+''',stem:="dag"}
 unless a=25 && x!=y && s.nodes=30 do throwError m!"DAG_SHARING_OR_BINDER_CONTROL|{a}|{x}|{y}|{s.nodes}"
 logInfo "DAG_SHARING_BINDER_PASS"
'''
 rr,ll=E.run(O,'Sharing',src);assert 'DAG_SHARING_BINDER_PASS' in ll
 rec['controls']['exponential_sharing_and_binder_names']=dict(passed=True,receipt=str((O/'Sharing.receipt.json').relative_to(R)),sha256=E.sha(O/'Sharing.receipt.json'))
 folder=O/'oversize';folder.mkdir()
 src='''import BoundedExprDAG
open Lean Elab Command BoundedExprDAG
run_cmd do
 let action:Dump Unit:=emit (toJson (String.ofList (List.replicate (5*1024*1024) 'x')))
 let _←liftIO <| action.run {dir:='''+json.dumps(str(folder))+''',stem:="dag"}
'''
 rr,ll=E.run(O,'Oversize',src,want=1);assert 'DAG_LINE_CAP' in ll and not list(folder.glob('dag-*'))
 rec['controls']['oversize_chunk_fail_closed']=dict(rejected=True,receipt=str((O/'Oversize.receipt.json').relative_to(R)),sha256=E.sha(O/'Oversize.receipt.json'))
 rec.update(status='PASS_AUTHOR_BOUNDED_DAG_PLANTED_BODY_AXIOM_OCCURRENCE_SHARING_BINDER_AND_CHUNK_CONTROLS')
 save();print(rec['status'])
except BaseException as e:rec.update(status='FAILED_INSTRUMENT_RETAINED',error=repr(e));save();raise
