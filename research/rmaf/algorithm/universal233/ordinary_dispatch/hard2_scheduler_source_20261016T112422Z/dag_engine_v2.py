"""Author-only bounded stored-expression DAG engine, not independent evidence.

Static imports only. Expression equality is ExprStructEq, not alpha equality.
Chunks <=4MiB; per-process emitted raw <=16MiB; each batch has <=16 stored
declarations. All processes run under the measured own-child-tree supervisor.
"""
from pathlib import Path
import gzip,hashlib,importlib.util,json,os,re,sys
sys.dont_write_bytecode=True
D=Path(__file__).resolve().parent;R=D.parents[5]
B=R/json.loads((D/'BUILD-v1.json').read_text())['directory']
spec=importlib.util.spec_from_file_location('dag_measured_supervisor',D/'supervisor_v4.py')
S=importlib.util.module_from_spec(spec);spec.loader.exec_module(S)
ALLOWED={'propext','Quot.sound','Classical.choice'}
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def run(out,label,source,want=0,seconds=30,pathroot=None):
 assert not (D/'RESOURCE-STOP-v1.json').exists(),'PERMANENT_RESOURCE_STOP'
 out=Path(out);out.mkdir(parents=True,exist_ok=True)
 p=out/(label+'.lean');assert not p.exists();p.write_text(source)
 cmd=[str(R/'bootloops-lean'),'--memory=2688',str(p)]
 try:row,log=S.run(cmd,B,dict(os.environ,LEAN_PATH=str(pathroot or B)),out,label,seconds=seconds,want=want)
 except BaseException:
  receipt=out/(label+'.receipt.json')
  if receipt.exists() and json.loads(receipt.read_text())['resource_stop']:
   (D/'RESOURCE-STOP-v1.json').write_text(json.dumps(dict(status='PERMANENT_AFFECTED_STAGE_RESOURCE_STOP',receipt=str(receipt.relative_to(R)),sha256=sha(receipt)),indent=2)+'\n')
  raise
 assert 'declaration uses `sorry`' not in log and 'sorryAx' not in log
 return row,log
def exporter(imports,module,start,end,out):
 assert 0<=start<end and end-start<=16
 return '\n'.join('import '+x for x in imports)+'''\nimport BoundedExprDAG
open Lean Elab Command BoundedExprDAG
run_cmd do
 let env←getEnv
 let producer:Name:=`'''+module+'''
 let some idx:=env.header.moduleNames.toList.idxOf? producer | throwError "DAG_PRODUCER_NOT_IMPORTED"
 let data:=env.header.moduleData[idx]!
 unless data.constants.size=data.constNames.size do throwError "DAG_PRODUCER_ARRAY_MISMATCH"
 unless '''+str(end)+'''≤data.constants.size do throwError "DAG_RANGE_MISMATCH"
 let mut metadataRows:Array (Nat×ConstantInfo×List (String×Json)):=#[]
 let mut rejects:=0
 for j in ['''+str(start)+''':'''+str(end)+'''] do
  let ci:=data.constants[j]!
  let stored:=data.constNames[j]!
  unless stored=ci.name do throwError "DAG_PRODUCER_NAME_MISMATCH"
  let refs:=ci.getUsedConstantsAsSet.toList
  let mut ax:List Name:=if ci.isAxiom then [ci.name] else []
  for n in refs do ax:=ax++(←collectAxioms n).toList
  ax:=ax.eraseDups
  if (ci.isAxiom && !([`propext,`Quot.sound,`Classical.choice]:List Name).contains ci.name) ||
    ax.any (fun n=>!([`propext,`Quot.sound,`Classical.choice]:List Name).contains n) then rejects:=rejects+1
  let resolved:=match env.getModuleIdxFor? ci.name with
   | some k=>env.header.moduleNames[k.toNat]!.toString | none=>"<unresolved>"
  metadataRows:=metadataRows.push (j,ci,[("record",toJson "declaration"),("producer",toJson producer.toString),
   ("index",toJson j),("stored_name",toJson stored.toString),("actual_name",toJson ci.name.toString),
   ("resolved_origin",toJson resolved),("kind",toJson (kind ci)),
   ("has_body",toJson (ci.value? true).isSome),("direct_references",toJson (refs.map Name.toString)),
   ("axiom_references",toJson (ax.map Name.toString)),("level_params",toJson (ci.levelParams.map (fun n=>reprStr n)))])
 let action:Dump Unit:=do
  emit <| Json.mkObj [("record",toJson "header"),("producer",toJson producer.toString),
   ("count",toJson data.constants.size),("start",toJson ('''+str(start)+''':Nat)),("end",toJson ('''+str(end)+''':Nat))]
  for (_,ci,fields) in metadataRows do
   let ty←expr ci.type
   let body : Option Nat ← match ci.value? true with
    | none=>pure none
    | some e=>do let r←expr e;pure (some r)
   emit <| Json.mkObj (fields++[("type_root",toJson ty),("body_root",toJson body)])
  let s←get
  emit <| Json.mkObj [("record",toJson "footer"),("declarations",toJson metadataRows.size),
   ("nodes",toJson s.nodes),("bytes_before_footer",toJson s.total),("rejects",toJson rejects)]
 let (_,sink)←liftIO <| action.run {dir:='''+json.dumps(str(out))+''',stem:="dag"}
 logInfo m!"DAG_DUMP|{producer}|{metadataRows.size}|{sink.nodes}|{sink.total}"
 if rejects>0 then throwError "DAG_CUSTOM_AXIOM_REJECTED"
'''
def read_chunks(folder,expect_reject=False):
 paths=sorted(Path(folder).glob('dag-*.jsonl'),key=lambda p:int(p.stem.split('-')[-1]))
 assert paths and [int(p.stem.split('-')[-1]) for p in paths]==list(range(len(paths)))
 lines=[];total=0
 for p in paths:
  assert p.stat().st_size<=4*(1<<20),'DAG_CHUNK_CAP'
  total+=p.stat().st_size;assert total<=16*(1<<20),'DAG_RAW_TOTAL_CAP'
  for line in p.read_bytes().splitlines():
   assert len(line)<=4*(1<<20),'DAG_LINE_CAP'
   lines.append(json.loads(line))
 return validate(lines,expect_reject)
def validate(lines,expect_reject=False):
 assert lines[0]['record']=='header' and lines[-1]['record']=='footer','DAG_ENVELOPES'
 h=lines[0];f=lines[-1];nodes=[];hashes=[];rows=[];seen=set()
 for z in lines[1:-1]:
  if z['record']=='node':
   i=z['id'];assert i==len(nodes),'DAG_NODE_ID_OR_ORDER'
   assert z['tag'] in {'bvar','fvar','mvar','sort','const','app','lam','forall','let','lit','mdata','proj'}
   ch=z['children'];assert all(isinstance(c,int) and 0<=c<i for c in ch),'DAG_FORWARD_CHILD'
   arity={'bvar':0,'fvar':0,'mvar':0,'sort':0,'const':0,'app':2,'lam':2,'forall':2,'let':3,'lit':0,'mdata':1,'proj':1}
   assert len(ch)==arity[z['tag']],'DAG_ARITY'
   key=json.dumps([z['tag'],z['fields'],ch],sort_keys=True,ensure_ascii=False)
   assert key not in seen,'DAG_DUPLICATE_NODE'
   seen.add(key);nodes.append(z)
   v=[z['tag'],z['fields'],[hashes[c] for c in ch]]
   hashes.append(hashlib.sha256(json.dumps(v,sort_keys=True,ensure_ascii=False,separators=(',',':')).encode()).hexdigest())
  else:
   assert z['record']=='declaration','DAG_UNEXPECTED_RECORD'
   assert z['producer']==h['producer'] and z['stored_name']==z['actual_name'],'DAG_PRODUCER_BINDING'
   assert z['resolved_origin']==h['producer'],'DAG_ORIGIN'
   assert z['kind'] in {'axiom','definition','opaque','theorem','inductive','constructor','recursor','quotient'}
   for root in [z['type_root']]+([z['body_root']] if z['body_root'] is not None else []):assert isinstance(root,int) and 0<=root<len(nodes),'DAG_ROOT'
   assert z['has_body']==(z['body_root'] is not None),'DAG_BODY_PRESENCE'
   if z['kind'] in {'definition','opaque','theorem'}:assert z['has_body'],'DAG_MISSING_STORED_BODY'
   z=dict(z,type='dag-sha256:'+hashes[z['type_root']],body='dag-sha256:'+hashes[z['body_root']] if z['body_root'] is not None else '<none>',body_text_scope='FULL_STRUCTURAL_EXPR_DAG')
   rows.append(z)
 assert f['nodes']==len(nodes) and f['declarations']==len(rows),'DAG_FOOTER_COUNT'
 assert [r['index'] for r in rows]==list(range(h['start'],h['end'])),'DAG_MISSING_OR_DUPLICATE_OCCURRENCE'
 assert len({r['actual_name'] for r in rows})==len(rows),'DAG_DUPLICATE_PRODUCER_NAME'
 rejects=[r for r in rows if (r['kind']=='axiom' and r['actual_name'] not in ALLOWED) or not set(r['axiom_references'])<=ALLOWED]
 assert len(rejects)==f['rejects'],'DAG_REJECT_COUNT'
 assert bool(rejects)==expect_reject,'DAG_UNEXPECTED_AXIOM_SCOPE'
 return dict(header=h,footer=f,rows=rows,nodes=len(nodes),node_hashes=hashes,raw_lines=lines)
def export(out,label,imports,module,start,end,expect_reject=False):
 out=Path(out);folder=out/('records-'+label);folder.mkdir()
 source=exporter(imports,module,start,end,folder)
 receipt,log=run(out,label,source,want=1 if expect_reject else 0,seconds=59)
 result=read_chunks(folder,expect_reject)
 compressed=[]
 for p in sorted(folder.glob('dag-*.jsonl')):
  q=p.with_suffix(p.suffix+'.gz')
  with q.open('wb') as f:
   with gzip.GzipFile(filename='',mode='wb',fileobj=f,mtime=0,compresslevel=1) as g:g.write(p.read_bytes())
  compressed.append(dict(path=str(q.relative_to(R)),sha256=sha(q),compressed_bytes=q.stat().st_size,raw_sha256=sha(p),raw_bytes=p.stat().st_size))
 return result,dict(module=module,start=start,end=end,receipt=str((out/(label+'.receipt.json')).relative_to(R)),receipt_sha256=sha(out/(label+'.receipt.json')),chunks=compressed,stored_occurrences=len(result['rows']),nodes=result['nodes'])
