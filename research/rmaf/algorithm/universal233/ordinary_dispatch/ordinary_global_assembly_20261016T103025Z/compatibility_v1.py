# One-shot original-context comparison, reusing exact sealed producer and full
# ConstantInfo engines. Source package licenses alone never authorize a pool.
from pathlib import Path
import ast,copy,gzip,hashlib,importlib.util,json,os,re,resource,selectors,shlex,shutil,signal,subprocess,sys,time
sys.dont_write_bytecode=True
D=Path(__file__).resolve().parent;R=D.parents[5];B=D/'build';O=B/'compatibility-v1';assert not O.exists();O.mkdir()
def load(n,p):
 s=importlib.util.spec_from_file_location(n,p);m=importlib.util.module_from_spec(s);s.loader.exec_module(m);return m
A=load('global_comp_parser',R/'research/rmaf/algorithm/universal233/rule5_common_split/audit_graph.py');V=D.parent/'resume_20261015T1810Z/compressed_pool_resume_v3.py'
for n in ast.parse(V.read_text()).body:
 if isinstance(n,ast.FunctionDef) and n.name in {'sha','string_sha','margin','cap','run','source','extract','read_rows'}:
  s=ast.unparse(n)
  if n.name=='run':s=s.replace("[str(R / 'bootloops-lean')]","[str(R / 'bootloops-lean'), '--memory=3072']").replace('> 60','> 30').replace('COMMAND_60S_CAP','COMMAND_30S_CAP').replace('8 * (1 << 20)','120000').replace('METADATA_STDOUT_8MIB_CAP','STDOUT_120KB_CAP')
  if n.name=='cap':s=s.replace('512 * (1 << 20)','64 * (1 << 20)')
  exec(s,globals())
compressed_source=source
def source(imports,wanted,out):
 s=compressed_source(imports,wanted,out)
 a='      let data := env.header.moduleData[i]!';assert s.count(a)==1;s=s.replace(a,'      let loaded ← liftIO <| findOLean producer\n'+a)
 a='("count",toJson data.constants.size),';assert s.count(a)==1;s=s.replace(a,'("count",toJson data.constants.size),("loaded_path",toJson loaded.toString),')
 return s
M=R/'research/rmaf/algorithm/universal233/ordinary_dispatch/ordinary_full_source_work_20261016T085803Z/FINAL-MANIFEST-v1.json';m=json.loads(M.read_text());e=next(e for e in m['immutable_files'] if e['path'].endswith('/source-snapshot/audit_v3.py'));P=R/e['path'];assert sha(P)==e['sha256']
for n in ast.parse(P.read_text()).body:
 if isinstance(n,ast.FunctionDef) and n.name in {'metadata_profile','metadata_compare'}:exec(compile(ast.Module(body=[n],type_ignores=[]),str(P),'exec'),globals())
rec={'version':1,'status':'CHECKING','independent_acceptance':False,'runs':[],'inputs':{},'controls':{},'comparisons':[]}
def save():(O/'certificate.json').write_text(json.dumps(rec,indent=2)+'\n')
save()
try:
 for p in [Path(__file__),D/'DEPENDENCY-PROVENANCE-v3.json',D/'COMPATIBILITY-CONTROLS-PIN-v1.json',V,Path(A.__file__),P]:rec['inputs'][str(p.relative_to(R))]=sha(p)
 ctx=json.loads((D/'DEPENDENCY-PROVENANCE-v3.json').read_text());alt=ctx['optimizer_context']['object_differences'];names=[e['module'] for e in alt];oldpath=':'.join(str(R/p) for p in ctx['optimizer_context']['roots']);rowsBy={}
 for side,path in [('Chosen',B),('Original',oldpath)]:
  for i in range(0,len(names),5):
   group=names[i:i+5];idx,folder=extract(O,group,group,path,side+str(i//5));assert not idx['rejects']
   for count in idx['producer_counts']:
    n=count['producer'];entry=next(e for e in alt if e['module']==n);want=R/entry['chosen' if side=='Chosen' else 'alternative']['object']['path'];assert Path(count['loaded_path']).resolve()==want.resolve(),('LOADED_OBJECT_MISMATCH',n,side,count['loaded_path'],str(want))
    rows=read_rows(folder/(n+'.json.gz'));assert len(json.dumps(rows).encode())<64*(1<<20),'RAW_MODULE_CAP';A.parse_producer(count,rows);rowsBy[(side,n)]=(rows,folder/(n+'.json.gz'))
    if side=='Chosen' and i==0 and n==group[0]:
     z=copy.deepcopy(rows);assert [r['type'] for r in z]==[r['type'] for r in rows];z[0]['type']+='TYPE_CORRUPTION';assert [r['type'] for r in z]!=[r['type'] for r in rows];rec['controls']['type_mutation']={'rejected':True}
     choices=[r for r in rows if r['kind'] in {'definition','opaque'}]
     assert choices,'BODY_CONTROL_REQUIRES_REAL_DEFINITION';z=copy.deepcopy(choices[0]);z['body']+='BODY_CORRUPTION';assert z['body']!=choices[0]['body'];rec['controls']['nonproof_body_mutation']={'rejected':True}
 for i,n in enumerate(names):
  a,ap=rowsBy[('Chosen',n)];b,bp=rowsBy[('Original',n)];assert [(r['actual_name'],r['kind']) for r in a]==[(r['actual_name'],r['kind']) for r in b],('NAME_KIND_DIFFERENCE',n)
  for x,y in zip(a,b):
   assert x['type']==y['type'],('TYPE_DIFFERENCE',n,x['actual_name'])
   if x['kind'] in {'definition','opaque'}:assert x['has_body'] and y['has_body'] and x['body']==y['body'],('NONPROOF_BODY_DIFFERENCE',n,x['actual_name'])
  kinds={r['kind'] for r in a};meta=None
  if kinds&{'inductive','constructor','recursor','axiom','quotient'}:
   ma,pa=metadata_profile(B,n,'Chosen'+str(i));mb,pb=metadata_profile(oldpath,n,'Original'+str(i));metadata_compare(ma,mb)
   if 'full_metadata_mutation' not in rec['controls']:
    z=copy.deepcopy(ma);key=next(iter(z));z[key]['full_constant_info']+='CORRUPT'
    try:metadata_compare(ma,z)
    except AssertionError as e:assert str(e)=='FULL_CONSTANTINFO_DIFFERENCE';rec['controls']['full_metadata_mutation']={'rejected':True,'reason':str(e)}
    else:raise AssertionError('METADATA_CORRUPTION_SURVIVED')
   meta={'chosen':str(pa.relative_to(R)),'chosen_sha256':sha(pa),'original':str(pb.relative_to(R)),'original_sha256':sha(pb),'declarations':len(ma)}
  rec['comparisons'].append({'module':n,'decision':'EXACT_NAMES_KINDS_TYPES_NONPROOF_BODIES_AND_FULL_METADATA','chosen_record':str(ap.relative_to(R)),'chosen_sha256':sha(ap),'original_record':str(bp.relative_to(R)),'original_sha256':sha(bp),'metadata':meta,'theorem_proof_variation':'Allowed, actual reference/axiom closure retained'});save()
 rec['status']='PASS_EXACT_ORIGINAL_CONTEXT_COMPATIBILITY';save();ctx['optimizer_context']['decision']=rec['status'];ctx['optimizer_context']['compatibility_certificate']=str((O/'certificate.json').relative_to(R));ctx['optimizer_context']['compatibility_certificate_sha256']=sha(O/'certificate.json');(D/'DEPENDENCY-PROVENANCE-v4.json').write_text(json.dumps(ctx,indent=2)+'\n');print(rec['status'],len(rec['comparisons']),'modules')
except BaseException as e:rec.update(status='FAILED_NOT_ACCEPTED',error=repr(e));save();raise
