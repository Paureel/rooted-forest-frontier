# One-shot local full-body audit adapter. Existing extractor and parser unchanged.
from pathlib import Path
import ast,datetime,gzip,hashlib,importlib.util,json,os,re,resource,selectors,shlex,shutil,signal,subprocess,time
D=Path(__file__).resolve().parent;R=D.parents[5]
P=json.loads((D/'DEPENDENCY-PINS-v1.json').read_text());B=R/P['pool'];S=R/P['semantic_pool'];O=D/'context-audit-v1';O.mkdir()
V=R/'research/rmaf/algorithm/universal233/ordinary_dispatch/resume_20261015T1810Z/compressed_pool_resume_v3.py'
assert hashlib.sha256(V.read_bytes()).hexdigest()=='626e3f21ba70fb417ad1085995a88b4af217a1b6f210191fa58ca442aad0098a'
def load(n,p):
 spec=importlib.util.spec_from_file_location(n,p);m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m);return m
A=load('numeric_audit_parser',R/'research/rmaf/algorithm/universal233/rule5_common_split/audit_graph.py')
for n in ast.parse(V.read_text()).body:
 if isinstance(n,ast.FunctionDef) and n.name in {'sha','string_sha','source','header_source'}:
  exec(compile(ast.Module(body=[n],type_ignores=[]),str(V),'exec'),globals())
qualified_source=source
def source(imports,modules,out):
 s=qualified_source(imports,modules,out)
 if not set(modules)<={'ProducerBudgetTrim','NumericAuditClean','NumericAuditHostile'}:return s
 a='let body := match ci with | .thmInfo _ => none | _ => ci.value? true';assert s.count(a)==1
 s=s.replace(a,'let body := ci.value? true')
 a='match ci with | .thmInfo _ => "OMITTED_THEOREM_PROOF_TEXT" | _ => "FULL_NONPROOF_BODY"';assert s.count(a)==1
 return s.replace(a,'"FULL_ALL_BODY"')
rec=dict(status='CHECKING',same_author=True,independent_credit=0,full233=False,native=False,novelty=False,runs=[],controls={},inputs={},sources=[],new_producers=[],inherited_audit_qualification='Frozen imported records remain at their existing qualifications; exact chosen source/object closure matched. No blanket re-extraction of imported full bodies.')
def save():(O/'certificate.json').write_text(json.dumps(rec,indent=2)+'\n')
def run(root,name,pathroot,build=False,want=0):
 assert shutil.disk_usage(D).free>=3*(1<<30)
 start=time.monotonic();cmd=[str(R/'bootloops-lean'),'--memory=3072']+(['-o',str(root/(name+'.olean'))] if build else [])+[str(root/(name+'.lean'))]
 def limit():resource.setrlimit(resource.RLIMIT_FSIZE,(16*(1<<20),16*(1<<20)))
 p=subprocess.Popen(cmd,cwd=root,env=dict(os.environ,LEAN_PATH=str(pathroot)),stdout=subprocess.PIPE,stderr=subprocess.STDOUT,preexec_fn=limit,start_new_session=True)
 size=0;chunks=[];failure=None;sel=selectors.DefaultSelector();sel.register(p.stdout,selectors.EVENT_READ)
 while sel.get_map():
  if time.monotonic()-start>30:failure='30S_PILOT_CAP'
  if size>4*(1<<20):failure='4MIB_STDOUT_CAP'
  if shutil.disk_usage(D).free<3*(1<<30):failure='3GIB_DISK_FLOOR'
  if failure:os.killpg(p.pid,signal.SIGTERM);break
  for key,event in sel.select(0.2):
   buf=os.read(key.fd,1<<16)
   if buf:chunks.append(buf);size+=len(buf)
   else:sel.unregister(key.fileobj)
 try:tail=p.communicate(timeout=3)[0]
 except subprocess.TimeoutExpired:os.killpg(p.pid,signal.SIGKILL);tail=p.communicate()[0]
 sel.close();chunks.append(tail);out=b''.join(chunks);(root/(name+'.log')).write_bytes(out)
 rec['runs'].append(dict(module=name,exit=p.returncode,expected=want,seconds=time.monotonic()-start,stdout_bytes=len(out),resource_stop=failure));save()
 assert failure is None and p.returncode==want,(name,failure,p.returncode,out[-1500:])
 assert b'declaration uses `sorry`' not in out
 return out.decode()
def extract(label,imports,mods,pathroot,want=0):
 folder=O/('records-'+label);folder.mkdir();name='Body'+label
 (O/(name+'.lean')).write_text(source(imports,mods,folder));run(O,name,pathroot,want=want)
 idx=json.loads((folder/'index.json').read_text());assert len(idx['producer_counts'])==len(mods)
 assert {r['producer'] for r in idx['producer_counts']}==set(mods)
 result=[]
 for c in idx['producer_counts']:
  f=folder/c['file'];assert f.stat().st_size<=16*(1<<20),'16MIB_COMPRESSED_CAP'
  with gzip.open(f,'rb') as stream:raw=stream.read(256*(1<<20)+1)
  assert len(raw)<=256*(1<<20),'256MIB_RAW_CAP'
  assert max(map(len,raw.splitlines()),default=0)<=128*(1<<20),'128MIB_LINE_CAP'
  rows=json.loads(raw);bad=A.parse_producer(c,rows,expect_reject=bool(want));assert bool(bad)==bool(want)
  expected_full=c['producer'] in {'ProducerBudgetTrim','NumericAuditClean','NumericAuditHostile'}
  assert all(r['body_text_scope']==('FULL_ALL_BODY' if expected_full or r['kind']!='theorem' else 'OMITTED_THEOREM_PROOF_TEXT') or (not expected_full and r['kind']!='theorem' and r['body_text_scope']=='FULL_NONPROOF_BODY') for r in rows)
  assert all(r['has_body'] and r['body']!='<none>' for r in rows if r['kind'] in {'definition','opaque'} or (expected_full and r['kind']=='theorem'))
  result.append((c,f,rows,len(raw)))
 return idx,result
save();(O/'lean-toolchain').write_bytes((D/'lean-toolchain').read_bytes())
try:
 rec['role']='ORIGINAL_CONTEXT_PUBLIC_DEFINITION_TYPE_NONPROOF_COMPARISON';rec['comparisons']=[]
 for p in [V,Path(A.__file__),Path(__file__),D/'DEPENDENCY-PINS-v1.json',D/'PRECONTROLS-v1.json']:
  rec['inputs'][str(p.relative_to(R))]=sha(p)
 def public(rows):return [(r['index'],r['actual_name'],r['kind'],r['type'],None if r['kind']=='theorem' else r['body'],r['has_body'] if r['kind']!='theorem' else None) for r in rows]
 def match(a,b):assert public(a)==public(b),'PUBLIC_TYPE_OR_NONPROOF_BODY_MISMATCH'
 # Same comparator must reject type and executable-body corruption.
 plant=[dict(index=0,actual_name='probe',kind='definition',type='Nat',body='0',has_body=True)]
 for label,field,value in [('type','type','Bool'),('body','body','1')]:
  try:match(plant,[dict(plant[0],**{field:value})])
  except AssertionError:rec['controls'][label+'_plant']='CAUGHT'
  else:raise AssertionError('PLANT_SURVIVED')
 mods=[f[:-6] for f in P['context_comparison']['differing_files']];assert len(mods)==29
 total=0
 for i,n in enumerate(mods):
  idx,l=extract('B'+str(i),[n],[n],B);assert not idx['rejects']
  idx,r=extract('S'+str(i),[n],[n],S);assert not idx['rejects']
  lc,lf,lr,lb=l[0];rc,rf,rr,rb=r[0];match(lr,rr)
  assert all(x['resolved_origin']==n for x in lr+rr)
  la=set().union(*(set(x['axiom_references']) for x in lr));ra=set().union(*(set(x['axiom_references']) for x in rr));assert la<=A.ALLOWED and ra<=A.ALLOWED
  total+=lf.stat().st_size+rf.stat().st_size;assert total<=128*(1<<20)
  rec['comparisons'].append(dict(module=n,status='EXACT_PUBLIC_TYPES_AND_NONPROOF_BODIES_EQUAL',declarations=len(lr),binary=dict(path=str(lf.relative_to(R)),sha256=sha(lf)),semantic=dict(path=str(rf.relative_to(R)),sha256=sha(rf)),binary_axioms=sorted(la),semantic_axioms=sorted(ra),theorem_pretty_text='OMITTED_BUT_ACTUAL_PROOF_REFERENCES_AXIOMS_WALKED',binary_object_sha256=sha(B/(n+'.olean')),semantic_object_sha256=sha(S/(n+'.olean'))));save();print('COMPATIBLE',n,len(lr),flush=True)
 rec.update(status='PASS_29_ORIGINAL_CONTEXT_PUBLIC_COMPATIBILITY',new_compressed_bytes=total,nonproof_body_and_type_exact=True,proof_qualification='Original compiled contexts retain distinct proof objects. All public types and all nonproof stored bodies compared exactly; actual proof reference/axiom walks use only standard three axioms. No source rebuild or blind object union.',independent_credit=0)
 save();print(rec['status'],flush=True)
except BaseException as e:rec.update(status='FAILED_NOT_ACCEPTED',error=repr(e));save();raise
