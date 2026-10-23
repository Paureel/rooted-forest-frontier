"""Own exact comparator and literal original-edge realization checker.

No author oracle/detector is imported. The graph check retains all original
vertices and rejects any leafless component. Truth comes from frozen hand
cases and the separate own graph/partition mathematical enumerators.
"""
import copy,gzip,hashlib,json,pathlib,sys,time
from semantic_oracles import canon_blocks
HERE=pathlib.Path(__file__).resolve().parent
def receipt(label):
 found=[]
 for p in (HERE/'evidence').glob('*.json'):
  r=json.loads(p.read_text())
  if r['label']==label:found.append(r)
 if len(found)!=1:raise ValueError('receipt denominator')
 r=found[0]
 if r['returncode']!=0 or r['stop_reason']:raise ValueError('evaluator process stopped')
 rows=[];raw=0
 for s in r['shards']:
  p=HERE/s['path'];assert hashlib.sha256(p.read_bytes()).hexdigest()==s['sha256']
  with gzip.open(p,'rb') as f:
   for line in f:
    raw+=len(line)
    if raw>64*1024**2 or len(line)>16*1024**2:raise ValueError('raw cap')
    rows.append(json.loads(line))
 assert raw==r['raw_bytes'];return rows

def original_components(tree,cuts):
 vertices={};edges=[]
 def build(t,p):
  vertices[p]=t if type(t) is int else None
  if type(t) is not int:
   for bit,child in zip((False,True),t):
    childpath=p+(bit,);edges.append((p,childpath));build(child,childpath)
 build(tree,())
 if not isinstance(cuts,list) or any(not isinstance(p,list) or any(type(b) is not bool for b in p) for p in cuts):
  raise ValueError('cut path encoding')
 removed=[tuple(p) for p in cuts]
 if len(set(removed))!=len(removed) or any(not p or p not in vertices for p in removed):raise ValueError('original cut validity')
 parent={p:p for p in vertices}
 def find(x):
  while parent[x]!=x:x=parent[x]
  return x
 for a,b in edges:
  if b not in removed:parent[find(b)]=find(a)
 comps={}
 for p,label in vertices.items():
  c=comps.setdefault(find(p),[])
  if label is not None:c.append(label)
 if len(comps)!=len(cuts)+1 or any(not c for c in comps.values()):raise ValueError('leafless/missing original component')
 return canon_blocks(comps.values())

def one(inp,truth,out):
 if truth.get('input_error'):
  if 'input_error' not in out:raise ValueError('outside typed API input was not refused by adapter')
  return 'adapter-refusal'
 if 'input_error' in out:raise ValueError(('unexpected adapter error',out))
 if inp['mode']=='agreement':
  if out['agreement'] is not truth['agreement']:raise ValueError('ordinary predicate mismatch')
  return 'agreement'
 if out['proper'] is not truth['proper']:raise ValueError('proper-input check mismatch')
 p=out['partition'];cuts=out['sourceCuts'];core=out['core'];k=inp['k']
 if not truth['proper']:
  if p is not None or cuts is not None or core is not None:raise ValueError('malformed typed input accepted')
  return 'malformed'
 optimum=truth['optimum'];valid={canon_blocks(v) for v in truth['valid_partitions']}
 core_feasible=optimum-1<=max(0,k-1)
 if core_feasible:
  if core is None or canon_blocks(core) not in valid or len(core)!=optimum:raise ValueError('core exactness/minimum')
 elif core is not None:raise ValueError('core false positive')
 if not truth['feasible']:
  if p is not None or cuts is not None:raise ValueError('bounded false positive')
  return 'bounded-negative'
 if p is None or cuts is None:raise ValueError('bounded false negative')
 if canon_blocks(p) not in valid or len(p)!=optimum or len(p)>k:raise ValueError('forest validity/minimum/budget')
 if len(cuts)+1!=len(p):raise ValueError('cut/component count')
 if original_components(inp['b'],cuts)!=canon_blocks(p):raise ValueError('original cut components do not realize returned partition')
 return 'optimal-original-cut-output'

def check_batch(batch,label,corruptions=False):
 inputs=[json.loads(line) for line in (HERE/'cases'/(batch+'.jsonl')).read_text().splitlines()]
 expected=json.loads((HERE/'SEMANTIC-EXPECTATIONS-v1.json').read_text());outs=receipt(label)
 def checkall(rows):
  ids=[r['id'] for r in rows]
  if len(ids)!=len(set(ids)) or set(ids)!={r['id'] for r in inputs}:raise ValueError('missing/duplicate output rows')
  table={r['id']:r for r in rows};hist={}
  for inp in inputs:
   kind=one(inp,expected[inp['id']],table[inp['id']]);hist[kind]=hist.get(kind,0)+1
  return hist
 hist=checkall(outs);caught=[]
 if corruptions:
  target_id='hand-three_disagree-k2';index=next(i for i,r in enumerate(outs) if r['id']==target_id)
  inp=next(r for r in inputs if r['id']==target_id)
  for name in ('false-negative','invalid-partition','wrong-optimum','root-cut','invalid-cut','duplicate-cut',
               'missing-cut','wrong-original-edge','missing-row','duplicate-row','wrong-properness'):
   bad=copy.deepcopy(outs);r=bad[index]
   if name=='false-negative':r['partition']=None;r['sourceCuts']=None
   elif name=='invalid-partition':r['partition']=[[999]]
   elif name=='wrong-optimum':r['partition']=[[0],[1],[2]]
   elif name=='root-cut':r['sourceCuts']=[[]]
   elif name=='invalid-cut':r['sourceCuts']=[[False]*20]
   elif name=='duplicate-cut':r['sourceCuts'].append(copy.deepcopy(r['sourceCuts'][0]))
   elif name=='missing-cut':r['sourceCuts']=[]
   elif name=='wrong-original-edge':
    wrong=None
    for path in ([False],[True],[False,False],[False,True]):
     try:c=original_components(inp['b'],[path])
     except ValueError:continue
     if c!=canon_blocks(r['partition']):wrong=[path];break
    if wrong is None:raise AssertionError('failed to construct wrong original edge control')
    r['sourceCuts']=wrong
   elif name=='missing-row':bad.pop()
   elif name=='duplicate-row':bad.append(copy.deepcopy(bad[0]))
   elif name=='wrong-properness':r['proper']=False
   try:checkall(bad)
   except (ValueError,KeyError,TypeError,AssertionError):caught.append(name)
   else:raise AssertionError('mutation escaped '+name)
 result={'status':'FINITE-ACTUAL-SOLVER-PASS','batch':batch,'label':label,'rows':len(inputs),
   'histogram':hist,'corruptions_caught':caught,'universal_proof':False}
 (HERE/(label+'-SEMANTIC-v1.json')).write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
 print(json.dumps(result,sort_keys=True))
if __name__=='__main__':check_batch(sys.argv[1],sys.argv[2],len(sys.argv)>3)
