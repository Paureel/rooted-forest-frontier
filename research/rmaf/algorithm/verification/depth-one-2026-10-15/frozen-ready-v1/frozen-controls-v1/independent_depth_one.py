#!/usr/bin/env python3
"""One-shot blind depth-one controls, original graph edge deletion vs tiny partitions.
Reuses own frozen original graph/checker lineage; no candidate imports or code.
"""
from pathlib import Path
import argparse,importlib.util,json,hashlib,itertools,time,traceback
H=Path(__file__).resolve().parent
ROOT=next(p for p in (H,*H.parents) if (p/'bootloops-python').is_file())
BASE=ROOT/'research/rmaf/algorithm/verification/pair-case-2026-10-15/frozen-readiness-v1/independent_paircase.py'
assert hashlib.sha256(BASE.read_bytes()).hexdigest()=='9f9d9d33ddcfe867a9d82113478a07807f1ad73b32cf50c3180aa54a6770eab4'
sp=importlib.util.spec_from_file_location('own_frozen_graph',BASE);g=importlib.util.module_from_spec(sp);sp.loader.exec_module(g)
def canon(F):return g.canon_partition(F)
def family(Fs):return sorted(canon(F) for F in Fs)
def guard(S,T):return S.proper and T.proper and set(S.labels)==set(T.labels)
def components(S,cuts):
 removed={frozenset((p[:-1],p)) for p in cuts};seen=set();cs=[]
 for v in sorted(S.graph):
  if v in seen:continue
  seen.add(v);todo=[v];verts=[];labels=[]
  while todo:
   w=todo.pop();verts.append(w)
   if w in S.leaf_at:labels.append(S.leaf_at[w])
   for x in sorted(S.graph[w]-seen):
    if frozenset((w,x)) not in removed:seen.add(x);todo.append(x)
  cs.append({'vertices':sorted(verts),'labels':sorted(labels)})
 return cs
def realization(S,T,F,cuts):
 if not guard(S,T) or not g.partition_check(S.labels,F) or not g.partition_check(T.labels,F):return False
 if len(set(cuts))!=len(cuts) or any(not p or (p[:-1],p) not in S.edges for p in cuts):return False
 cs=components(S,cuts)
 return bool(all(c['labels'] for c in cs) and len(cs)==len(cuts)+1 and len(F)==len(cs)
             and canon(c['labels'] for c in cs)==canon(F) and g.agrees(S,T,F))
def minimum_forests(S,T):
 if not guard(S,T):return None,[],[]
 ps=list(g.partitions(sorted(S.labels)));valid=[p for p in ps if g.agrees(S,T,p)];assert valid
 value=min(len(p)-1 for p in valid)
 return value,[p for p in valid if len(p)-1==value],ps
def witness_minimum(S,T,F,cuts):
 if not realization(S,T,F,cuts):return False
 v,_,_=minimum_forests(S,T);return len(F)-1==v
def complete_negative_guard(S,T,edge_rows,zero_checked=True):
 expected={p for _,p in S.edges};actual=[r['edge'] for r in edge_rows]
 return bool(guard(S,T) and zero_checked and len(actual)==len(expected) and set(actual)==expected
             and not g.agrees(S,T,[S.labels]) and all(not r['agreement'] for r in edge_rows))
class Checks:
 def __init__(self):self.rows=[]
 def equal(self,id,actual,expected):
  okay=actual==expected;mutated={'deliberate_wrong_expectation':expected};rejected=actual!=mutated
  self.rows.append({'id':id,'actual':actual,'expected':expected,'passed':okay,'mismatched_expectation_rejected':rejected})
  assert okay and rejected,id

def prune(t,U,p=''):
 if isinstance(t,int):return None if t not in U else (p,t)
 a,b=prune(t[0],U,p+'0'),prune(t[1],U,p+'1')
 return b if a is None else a if b is None else (p,(a,b))
def unpack(node):
 mapping={}
 def rec(node,v=''):
  p,t=node;mapping[v]=p
  return t if isinstance(t,int) else (rec(t[0],v+'0'),rec(t[1],v+'1'))
 return rec(node),mapping

def plants(pin,c):
 rows=[]
 for name,f in pin['planted_witnesses'].items():
  S,T=g.Original(f['S']),g.Original(f['T']);cs=components(S,f['cuts'])
  c.equal(name+'/realization',realization(S,T,f['forest'],f['cuts']),f['valid_realization'])
  c.equal(name+'/minimum',witness_minimum(S,T,f['forest'],f['cuts']),f['global_minimum'])
  if 'graph_components' in f:
   c.equal(name+'/component_count',len(cs),f['graph_components']);c.equal(name+'/leaf_bearing',sum(bool(x['labels']) for x in cs),f['leaf_bearing_components']);c.equal(name+'/leafless',[x['vertices'] for x in cs if not x['labels']],f['leafless_component_vertices'])
  rows.append({'id':name,'components':cs})
 f=pin['false_extensions']['shape_without_embedding'];S,T=g.Original(f['S']),g.Original(f['T']);F=f['forest']
 shape=all(g.raw_shape(g.raw_restrict(S.tree,b))==g.raw_shape(g.raw_restrict(T.tree,b)) for b in F)
 c.equal('shape_without_embedding/shapes',shape,f['all_block_shapes_agree']);c.equal('shape_without_embedding/source',S.embedding_disjoint(F),f['source_embeddings']);c.equal('shape_without_embedding/target',T.embedding_disjoint(F),f['target_embeddings']);c.equal('shape_without_embedding/agreement',bool(g.agrees(S,T,F)),f['agreement'])
 f=pin['false_extensions']['rooted_topology'];c.equal('rooted_topology/whole',bool(g.agrees(g.Original(f['S']),g.Original(f['T']),f['forest'])),False)
 f=pin['false_extensions']['oriented_edge'];S=g.Original(f['tree']);a,b=f['parent'],f['child'];c.equal('oriented_edge/forward',(a,b) in S.edges,True);c.equal('oriented_edge/reverse',(b,a) in S.edges,False);c.equal('oriented_edge/undirected_same',frozenset((a,b))==frozenset((b,a)),True)
 f=pin['false_extensions']['incomplete_negative_search'];S,T=g.Original([[0,1],[2,3]]),g.Original([[0,2],[1,3]])
 ledger=[{'edge':p,'agreement':bool(g.agrees(S,T,[x['labels'] for x in components(S,[p])]))} for p in f['complete_edges']]
 c.equal('negative_complete_clean_twin',complete_negative_guard(S,T,ledger),True)
 omission=[x for x in ledger if x['edge']!=f['omit']];c.equal('negative_omission_rejected',complete_negative_guard(S,T,omission),False)
 duplicated=omission+[omission[0]];c.equal('negative_duplicate_record_rejected',complete_negative_guard(S,T,duplicated),False)
 c.equal('negative_missing_zero_check_rejected',complete_negative_guard(S,T,ledger,False),False)
 for i,F in enumerate(pin['false_extensions']['malformed_forests']):c.equal('malformed_forest/'+str(i),g.partition_check([0,1,2],F),False)
 statuses={'REFUSED':'REFUSED','TIMEOUT':'OPEN','UNSUPPORTED':'OPEN','EMPTY_WITHOUT_GUARD_OR_COMPLETENESS':'OPEN','COMPLETE_NEGATIVE':'MINIMUM_AT_LEAST_2'}
 for k,want in pin['false_extensions']['status_controls'].items():c.equal('status/'+k,statuses[k],want)
 for i,f in enumerate(pin['source_topology_controls']):
  S=g.Original(f['tree']);c.equal('topology/'+str(i),sorted(map(sorted,S.clusters(frozenset(f['selection'])))),sorted(f['clusters']))
 r=pin['restriction_controls'];S=g.Original(r['tree'])
 for name in ['empty_selection','absent_selection']:
  U=r[name];c.equal(name+'/restriction',g.raw_restrict(S.tree,U),None);c.equal(name+'/hull',sorted(S.hull(frozenset(U))),[])
 c.equal('absent_selected_guard',S.selected_guard(r['absent_selection']),False);c.equal('repeated_selected_guard',S.selected_guard(r['repeated_selection']),False)
 u,mp=unpack(prune(S.tree,set(r['root_selection'])));c.equal('root_restriction_shape',g.raw_shape(u),g.raw_shape(g.frozen_tree(r['root_shape'])));c.equal('root_original_hull',sorted(S.hull(frozenset(r['root_selection']))),r['root_hull']);c.equal('root_address_map',mp,r['local_to_original'])
 c.equal('displayed_edge_is_original',tuple(r['displayed_edge']) in S.edges,False);c.equal('displayed_path_edges',len(S.path(*r['displayed_edge']))-1,r['expanded_path_edges'])
 h=g.Original(u).hull(frozenset(r['root_selection']));c.equal('vertex_images_alone_are_original_hull',{mp[v] for v in h}==set(S.hull(frozenset(r['root_selection']))),False)
 expanded={mp[v] for v in h}
 for a,b in g.Original(u).edges:
  if a in h and b in h:expanded.update(S.path(mp[a],mp[b]))
 c.equal('expanded_original_paths_are_hull',sorted(expanded),r['root_hull'])
 for name,U,wantroot,wanthull in [('below_root',r['below_root_selection'],r['below_root_original_root'],r['below_root_hull']),('singleton',r['singleton_selection'],r['singleton_original_root'],r['singleton_hull'])]:
  _,mp=unpack(prune(S.tree,set(U)));c.equal(name+'/mapped_root',mp[''],wantroot);c.equal(name+'/hull',sorted(S.hull(frozenset(U))),wanthull)
 return rows

def fixture(f,pin,c):
 start=time.monotonic();S,T=g.Original(f['S']),g.Original(f['T']);good=guard(S,T);c.equal(f['id']+'/guard',good,f['guard'])
 if not good:
  c.equal(f['id']+'/status','REFUSED',f['status'])
  if 'raw_agreement_forest' in f:c.equal(f['id']+'/raw_agreement_does_not_override_guard',g.raw_agrees(S,T,f['raw_agreement_forest']),f['raw_agreement'])
  return {'id':f['id'],'status':'REFUSED','minimum_cost':None,'edge_checks':[],'one_two_partitions':[],'seconds':time.monotonic()-start}
 minimum,best,ps=minimum_forests(S,T);c.equal(f['id']+'/all_partition_denominator',len(ps),f['all_partition_count']);c.equal(f['id']+'/minimum',minimum,f['minimum_cost']);c.equal(f['id']+'/all_equal_cost_forests',family(best),family(f['minimum_forests']))
 edgechildren=[p for _,p in S.edges];c.equal(f['id']+'/original_edges',edgechildren,f['edges'])
 mapping='balanced' if f['id'] in ['identical_balanced','crossed_quartet','swapped_identical_shape'] else 'triple' if f['id'] in ['rooted_triple','swapped_triple_children'] else 'common_extra' if f['id']=='common_extra_leaf' else 'relabeled_triple' if f['id']=='relabeled_reordered_triple' else 'unary_path' if f['id']=='unary_path_identical' else 'reordered_quartet' if f['id']=='reordered_crossed_quartet' else None
 edges=[]
 for parent,child in S.edges:
  cs=components(S,[child]);F=[x['labels'] for x in cs];desc=S.descendants(child);ref=[sorted(desc),sorted(set(S.labels)-desc)]
  assert len(cs)==2 and all(x['labels'] for x in cs) and canon(F)==canon(ref)
  if mapping:c.equal(f['id']+'/edge_partition/'+child,canon(F),canon(pin['edge_partition_expectations'][mapping][child]))
  agrees=bool(g.agrees(S,T,F));raw=bool(g.raw_agrees(S,T,F));assert agrees==raw
  if agrees:assert realization(S,T,F,[child])
  edges.append({'edge':child,'oriented_edge':[parent,child],'components':cs,'partition':F,'agreement':agrees,'raw_agreement':raw})
 successful=[x['edge'] for x in edges if x['agreement']];c.equal(f['id']+'/all_successful_edges',successful,f['successful_edges'])
 successful_forests={canon(x['partition']) for x in edges if x['agreement']};c.equal(f['id']+'/all_one_cut_forests',sorted(successful_forests),family(f['one_cut_partitions']))
 small=[p for p in ps if len(p)<=2];c.equal(f['id']+'/one_two_partition_denominator',len(small),f['one_two_partition_count']);one_two=[]
 for F in small:
  agree=bool(g.agrees(S,T,F));raw=bool(g.raw_agrees(S,T,F));assert agree==raw
  one_two.append({'forest':F,'cost':len(F)-1,'agreement':agree,'raw_agreement':raw})
 assert {canon(x['forest']) for x in one_two if x['cost']==1 and x['agreement']}==successful_forests
 for F in ps:
  assert bool(g.agrees(S,T,F))==bool(g.raw_agrees(S,T,F))
  for B in F:assert set(S.hull(frozenset(B)))==g.raw_minimal(S.tree,B) and set(T.hull(frozenset(B)))==g.raw_minimal(T.tree,B)
 if minimum>=2:assert complete_negative_guard(S,T,edges)
 else:assert any(x['agreement'] and x['cost']==minimum for x in one_two)
 elapsed=time.monotonic()-start;assert elapsed<pin['limits']['case_seconds']
 return {'id':f['id'],'status':'RESOLVED_'+str(minimum) if minimum<=1 else 'MINIMUM_AT_LEAST_2','minimum_cost':minimum,'minimum_forests':best,'edge_checks':edges,'one_two_partitions':one_two,'all_partition_denominator':len(ps),'seconds':elapsed}

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--pin',required=True);ap.add_argument('--mode',choices=['pilot','battery'],required=True);ap.add_argument('--output',required=True);args=ap.parse_args();p=Path(args.pin);pin=json.loads(p.read_text());c=Checks();start=time.monotonic();rc=0
 result={'phase':'PRE-CANDIDATE','mode':args.mode,'candidate_contacts':0,'author_contacts':0,'children':0,'extra_independent_replications':0,'source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'pin_sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'reused_graph_sha256':hashlib.sha256(BASE.read_bytes()).hexdigest(),'fixtures':[],'all_main_milestones':'OPEN'}
 try:
  result['planted_controls']=plants(pin,c);result['planted_checks_before_fixtures']=len(c.rows)
  fs=[f for f in pin['cases'] if args.mode=='battery' or f['id'] in pin['limits']['pilot_ids']]
  for f in fs:result['fixtures'].append(fixture(f,pin,c))
  assert time.monotonic()-start<pin['limits']['battery_seconds'];result['verdict']='PASS-FROZEN-BLIND-DEPTH-ONE-CONTROLS'
 except Exception as e:rc=1;result['verdict']='OPEN-CONTROL-OR-PIN-FAILURE';result['error']=repr(e);result['traceback']=traceback.format_exc()
 result['checks']=c.rows;result['literal_checks']=len(c.rows);result['mismatches_rejected']=sum(x['mismatched_expectation_rejected'] for x in c.rows);result['seconds']=time.monotonic()-start;result['original_edges_tested']=sum(len(x['edge_checks']) for x in result['fixtures']);result['one_two_partitions_tested']=sum(len(x['one_two_partitions']) for x in result['fixtures']);result['all_partitions_tested']=sum(x.get('all_partition_denominator',0) for x in result['fixtures'])
 out=Path(args.output);out.parent.mkdir(parents=True,exist_ok=True);out.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({k:result[k] for k in ['verdict','mode','literal_checks','mismatches_rejected','seconds','original_edges_tested','one_two_partitions_tested','all_partitions_tested']}));return rc
if __name__=='__main__':raise SystemExit(main())
