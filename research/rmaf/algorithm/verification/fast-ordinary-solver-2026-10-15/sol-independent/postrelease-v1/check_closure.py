"""Exact graph/axiom consumer of actual stored-body closure records."""
import copy,hashlib,json,pathlib,sys,time
from check_semantics import receipt
HERE=pathlib.Path(__file__).resolve().parent
RUNTIME=HERE.parents[6]/'.runtime/elan/toolchains/leanprover--lean4---v4.35.0'
def graph(rr):
 assert rr[0]['record']=='root-set' and rr[0]['actual_values']
 assert rr[-1]['record']=='actual-axiom-closure' and not rr[-1]['cached_axiom_extension_used']
 ds={r['name']:r for r in rr[1:-1]}
 if len(ds)!=len(rr)-2 or len(ds)!=rr[-1]['declarations']:raise ValueError('missing/duplicate dependency rows')
 if any(r['record']!='actual-dependency' for r in ds.values()):raise ValueError('unknown row')
 def reach(root):
  seen=set();todo=[root]
  while todo:
   n=todo.pop()
   if n in seen:continue
   if n not in ds:raise ValueError('unknown/missing dependency '+n)
   seen.add(n);todo.extend(ds[n]['refs'])
  return seen
 reached=set().union(*(reach(r) for r in rr[0]['roots']))
 if reached!=set(ds):raise ValueError('extraneous/unreachable dependency rows')
 axioms={n for n,r in ds.items() if r['kind']=='axiom'}
 if axioms!=set(rr[-1]['axioms']) or len(axioms)!=len(rr[-1]['axioms']):raise ValueError('axiom union mismatch')
 return ds,reach
def controls():
 clean=receipt('closure-control-clean');hidden=receipt('closure-control-hidden')
 graph(clean);graph(hidden);caught=[]
 for label,bad in [('missing-row',copy.deepcopy(clean)),('duplicate-row',copy.deepcopy(clean)),
                   ('forged-empty-axioms',copy.deepcopy(hidden))]:
  if label=='missing-row':bad.pop(1)
  elif label=='duplicate-row':bad.insert(1,copy.deepcopy(bad[1]))
  else:bad[-1]['axioms']=[]
  try:graph(bad)
  except (ValueError,AssertionError):caught.append(label)
  else:raise AssertionError('closure graph comparator blind')
 print(json.dumps({'status':'CLOSURE-GRAPH-CONTROLS-PASS','caught':caught,'postcontact':True}))
def check(label):
 start=time.perf_counter();rr=receipt(label);ds,reach=graph(rr)
 plan=json.loads((HERE/'COLD-SOURCE-PLAN-v1.json').read_text());custom=set(plan['order'])|{'IndependentInterface'}
 perroot={}
 for root in rr[0]['roots']:
  names=reach(root)
  perroot[root]={'declarations':len(names),'axioms':sorted(n for n in names if ds[n]['kind']=='axiom'),
   'partial':[n for n in sorted(names) if ds[n]['partial']],'unsafe':[n for n in sorted(names) if ds[n]['unsafe']],
   'assignment_oracle_names_present':sorted(names&{'RMAF.solve','RMAF.assignments'})}
 trusted=[];foreign=[]
 for module in sorted({r['module'] for r in ds.values()}):
  if module in custom:continue
  p=RUNTIME/'lib/lean'/pathlib.Path(*module.split('.')).with_suffix('.olean')
  if not p.is_file() or not p.resolve().is_relative_to(RUNTIME.resolve()):foreign.append(module)
  else:trusted.append({'module':module,'path':str(p),'bytes':p.stat().st_size,
                       'sha256':hashlib.sha256(p.read_bytes()).hexdigest()})
 if foreign:raise ValueError(('unlicensed runtime boundary',foreign))
 result={'label':label,'status':'ACTUAL-BODY-DEPENDENCY-CLOSURE-CHECKED','declarations':len(ds),
  'axioms':[{'name':n,'module':r['module']} for n,r in sorted(ds.items()) if r['kind']=='axiom'],
  'custom_axioms':[n for n,r in ds.items() if r['kind']=='axiom' and r['module'] in custom],
  'partial':[n for n,r in ds.items() if r['partial']],'unsafe':[n for n,r in ds.items() if r['unsafe']],
  'sorryAx_reached':'sorryAx' in ds,'per_root':perroot,'trusted_runtime_pins':trusted,
  'cached_axiom_extension_used':False,'seconds':time.perf_counter()-start,
  'runtime_equivalence_proved':False,'raw_global_cleanliness_claimed':False}
 (HERE/(label+'-CHECKED-v1.json')).write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
 print(json.dumps({'label':label,'declarations':len(ds),'axioms':result['axioms'],
  'custom_axioms':result['custom_axioms'],'partial':len(result['partial']),'unsafe':len(result['unsafe']),
  'sorryAx_reached':result['sorryAx_reached'],'roots':len(perroot),'trusted_modules':len(trusted),'seconds':result['seconds']},sort_keys=True))
if __name__=='__main__':
 if sys.argv[1]=='controls':controls()
 else:check(sys.argv[1])
