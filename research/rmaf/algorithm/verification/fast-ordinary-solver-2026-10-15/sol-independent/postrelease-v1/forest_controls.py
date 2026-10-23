"""Fresh full-state graph-product and partition/restriction oracle controls."""
import itertools,json,pathlib,sys,copy
from semantic_oracles import graph_forests,partition_agreements,canon_blocks,validate_input
from check_semantics import receipt
HERE=pathlib.Path(__file__).resolve().parent
def state_truth(T,ss):
 if T is None:return ({()}, {()}) if not ss else (None,None)
 if not ss:return None,None
 joined=ss[0]
 for s in ss[1:]:joined=[joined,s]
 try:validate_input(T,joined)
 except ValueError:return None,None
 def leaves(t):return [t] if type(t) is int else leaves(t[0])+leaves(t[1])
 supports=[set(leaves(s)) for s in ss]
 pp={p for p in partition_agreements(T,joined) if all(any(set(b)<=u for u in supports) for b in p)}
 targets=graph_forests(T)[0]
 source_lists=[list(graph_forests(s)[0]) for s in ss]
 all_source={tuple(sorted(itertools.chain.from_iterable(parts))) for parts in itertools.product(*source_lists)}
 gg={tuple(b for b,_ in key) for key in targets.keys() & all_source}
 return pp,gg
def prepare():
 frozen=json.loads((HERE/'FOREST-HAND-v1.json').read_text());expected={}
 for f in frozen['cases']:
  p,g=state_truth(f['a'],f['b']);assert p==g
  assert (p is not None)==f['proper']
  if p is not None:assert min(map(len,p))==f['optimum']
  expected[f['id']]={'proper':f['proper'],'partitions':None if p is None else [[list(b) for b in x] for x in sorted(p)]}
 (HERE/'FOREST-INPUT-v1.jsonl').write_text(''.join(json.dumps(f,separators=(',',':'))+'\n' for f in frozen['cases']))
 (HERE/'FOREST-EXPECT-v1.json').write_text(json.dumps(expected,sort_keys=True)+'\n')
 print(json.dumps({'status':'FOREST-HAND-AND-TWO-ROUTES-PASS','cases':len(expected),'empty_forest_optimum':0,'crossing_optimum':3}))
def check(label):
 fs=json.loads((HERE/'FOREST-HAND-v1.json').read_text())['cases'];ex=json.loads((HERE/'FOREST-EXPECT-v1.json').read_text());rs=receipt(label)
 def compare(rows):
  table={r['id']:r for r in rows};assert len(table)==len(rows)==len(fs) and set(table)==set(ex)
  for f in fs:
   r=table[f['id']];truth=ex[f['id']];assert r['proper'] is truth['proper']
   if not truth['proper']:assert r['forest'] is None;continue
   feasible=f['optimum']-len(f['b'])<=f['q']
   if not feasible:assert r['forest'] is None;continue
   assert r['forest'] is not None and r['agrees'] is True
   assert len(r['forest'])==f['optimum']
   assert canon_blocks(r['forest']) in {canon_blocks(p) for p in truth['partitions']}
 compare(rs);caught=[]
 for name in ('missing-row','duplicate-row','wrong-global-minimum','false-negative','wrong-proper'):
  bad=copy.deepcopy(rs);idx=next(i for i,r in enumerate(bad) if r['id']=='crossing-q2-still-minimum')
  if name=='missing-row':bad.pop()
  elif name=='duplicate-row':bad.append(copy.deepcopy(bad[0]))
  elif name=='wrong-global-minimum':bad[idx]['forest']=[[0],[1],[2],[3]]
  elif name=='false-negative':bad[idx]['forest']=None
  else:bad[idx]['proper']=False
  try:compare(bad)
  except (AssertionError,TypeError):caught.append(name)
  else:raise AssertionError('forest comparator blind')
 result={'status':'ACTUAL-FOREST-INTERFACE-PASS','label':label,'cases':len(fs),'caught':caught,'postcontact':True,'universal_proof':False}
 (HERE/(label+'-CHECKED-v1.json')).write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,sort_keys=True))
if __name__=='__main__':
 if sys.argv[1]=='prepare':prepare()
 else:check(sys.argv[1])
