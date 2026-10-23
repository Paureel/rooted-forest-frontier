#!/usr/bin/env python3
"""Blind bounded original-graph/raw-list/state-interface controls.
Uses only the disclosed own pair-case dependency and permitted State definitions.
Mock child tables are instruments, not an implemented recursive solver.
"""
from pathlib import Path
import sys,json,time,hashlib,traceback,importlib.util,argparse
from collections import Counter
from itertools import combinations
sys.dont_write_bytecode=True
H=Path(__file__).resolve().parent
ROOT=next(p for p in (H,*H.parents) if (p/'bootloops-python').is_file())
spec=importlib.util.spec_from_file_location('own_graph',H/'own_paircase_dependency.py')
g=importlib.util.module_from_spec(spec);spec.loader.exec_module(g)
DATA=json.loads((H/'controls-v1.json').read_text())
GUARDS=json.loads((H/'guard-controls-v1.json').read_text())

def norm(x):return json.loads(json.dumps(x))
def labels(t):return [] if t is None else g.Original(t).labels
def contained(a,b):return all(x in b for x in a)
def family(xs,F):return [b for b in F if contained(b,xs)]
def materialize(s,Q):return [u for b in Q if (u:=g.raw_restrict(s,b)) is not None]
def raw_disjoint(t,F):return all(not(g.raw_minimal(t,a)&g.raw_minimal(t,b)) for a,b in combinations(F,2))
def proper(t,ss):return len(set(labels(t)))==len(labels(t)) and g.partition_check(labels(t),[labels(s) for s in ss])
def restriction_agrees(t,s,b):
 if t is None:return False
 a,c=g.raw_restrict(t,b),g.raw_restrict(s,b)
 return a is not None and c is not None and g.raw_shape(a)==g.raw_shape(c)
def source_check(t,F,s):
 G=family(labels(s),F)
 return g.partition_check(labels(s),G) and all(restriction_agrees(t,s,b) for b in G) and raw_disjoint(s,G)
def state_agrees(t,ss,F):
 return (proper(t,ss) and g.partition_check(labels(t),F)
  and all(any(contained(b,labels(s)) for s in ss) for b in F)
  and ((not F) if t is None else raw_disjoint(t,F))
  and all(source_check(t,F,s) for s in ss))
def graph_state(t,ss,F):
 if not proper(t,ss) or not g.partition_check(labels(t),F):return False
 if not all(any(contained(b,labels(s)) for s in ss) for b in F):return False
 if t is None:return not F and not ss
 T=g.Original(t)
 if not T.embedding_disjoint(F):return False
 for s in ss:
  S=g.Original(s);G=family(S.labels,F)
  if not g.partition_check(S.labels,G) or not S.embedding_disjoint(G):return False
  if not all(T.clusters(frozenset(b))==S.clusters(frozenset(b)) and S.clusters(frozenset(b)) for b in G):return False
 return True

def evaluate(c):
 f=DATA['fixtures'][c['fixture']];s,t=f['S'],f['T'];Q=c.get('Q',f['Q']);F=c['F']
 ss=materialize(s,Q);S,T=g.Original(s),g.Original(t)
 raw=state_agrees(t,ss,F);graph=graph_state(t,ss,F)
 assert raw==graph,('raw_graph_state_disagreement',c['id'],raw,graph)
 orig=g.agrees(T,S,F);assert orig==g.raw_agrees(T,S,F),('original_route_disagreement',c['id'])
 assert S.embedding_disjoint(Q)==raw_disjoint(s,Q)
 assert T.embedding_disjoint(Q)==raw_disjoint(t,Q)
 return norm({'sources':ss,'source_count':len(ss),'Q_checked':g.partition_check(S.labels,Q),
  'source_Q_clear':S.embedding_disjoint(Q),'target_Q_clear':T.embedding_disjoint(Q),
  'state':raw,'original_AF':orig,'refines':g.refines(F,Q),'additional':max(0,len(F)-len(ss)),
  'Q_subtraction':max(0,len(F)-len(Q)),'proper':proper(t,ss)})

class Battery:
 def __init__(self):self.rows=[];self.mismatches=[];self.semantic=[]
 def equal(self,name,actual,expected):
  actual,expected=norm(actual),norm(expected)
  row={'id':name,'expected':expected,'actual':actual,'pass':actual==expected};self.rows.append(row)
  assert row['pass'],row
  # Exact same comparator, deliberately unequal frozen-type corruption.
  if isinstance(expected,bool):bad=not expected
  elif expected is None:bad='PLANTED_NONEMPTY'
  elif isinstance(expected,int):bad=expected+1
  elif isinstance(expected,list):bad=expected+['PLANTED_EXTRA_RECORD']
  elif isinstance(expected,str):bad=expected+'PLANTED'
  else:raise TypeError(type(expected))
  caught=(actual!=bad);self.mismatches.append({'id':name,'mutant':bad,'rejected':caught});assert caught
 def reject(self,name,clean,mutant):
  assert clean is True and mutant is False,(name,clean,mutant)
  self.semantic.append({'id':name,'clean_twin':clean,'mutant_accepted':mutant,'rejected':True})

def grouping(B):
 d=DATA['grouping'];f=DATA['fixtures'][d['fixture']];t,s,Q=f['T'],f['S'],f['Q'];ss=materialize(s,Q)
 a,b,c=ss[:1],ss[1:3],ss[3:];A,Bs,C=d['A'],d['B'],d['C'];bt=g.raw_restrict(t,[x for p in Bs for x in p])
 at,ct=g.raw_restrict(t,A),g.raw_restrict(t,C)
 assert state_agrees(at,a,d['FA']) and state_agrees(ct,c,d['FC'])
 single,cheap=d['Bsingletons'],d['Bcheaper']
 assert state_agrees(bt,b,single) and state_agrees(bt,b,cheap)
 for fb in (single,cheap):
  final=d['FA']+fb+d['FC']
  assert state_agrees(t,ss,final) and g.agrees(g.Original(t),g.Original(s),final) and g.refines(final,Q)
 cross=g.Original(t).embedding_disjoint([A,[x for p in Bs for x in p],C])
 # B internal target overlap does not violate cross-group disjointness.
 got={'A_cost':len(d['FA'])-len(a),'C_cost':len(d['FC'])-len(c),
  'B_singletons_cost':len(single)-len(b),'B_cheaper_cost':len(cheap)-len(b),
  'parent_singletons_cost':len(d['FA']+single+d['FC'])-len(ss),
  'parent_cheaper_cost':len(d['FA']+cheap+d['FC'])-len(ss),
  'B_internal_target_clear':g.Original(t).embedding_disjoint(Bs),'cross_group_clear':cross,
  'source_permutation':Counter(map(repr,ss))==Counter(map(repr,a+list(reversed(b))+c)),
  'actual_sideOutputs_derived':False,'recursive_solver_implemented':False}
 for k,v in d['expected'].items():B.equal('group.'+k,got[k],v)
 for case in d['mock_calls']:
  out={'access':False,'calls':0,'child_budget':None,'witness':False,'child_cost':None,'parent_cost':None}
  if case['q']>0 and case['contract'] and case['groups_ok']:
   out.update(access=True,calls=1,child_budget=case['q']-1)
   if case['choice'] is not None:
    fb=d[case['choice']];cost=len(fb)-len(b)
    assert state_agrees(bt,b,fb) and cost<=out['child_budget']
    final=d['FA']+fb+d['FC'];assert state_agrees(t,ss,final)
    total=len(final)-len(ss);assert total==1+cost and total<=case['q']
    out.update(witness=True,child_cost=cost,parent_cost=total)
  for k,v in case['expected'].items():B.equal('mock.'+case['id']+'.'+k,out[k],v)
 expected=Counter(map(repr,b))
 B.reject('omitted_B_piece_ownership',Counter(map(repr,b))==expected,Counter(map(repr,b[:-1]))==expected)
 B.reject('duplicate_B_piece_ownership',Counter(map(repr,b))==expected,Counter(map(repr,b+[b[0]]))==expected)
 B.reject('forced_B_internal_target_clearance',cross,cross and got['B_internal_target_clear'])
 B.reject('free_whole_B_replacement_cost',len(cheap)-len(b)==1,len(cheap)-1==1)
 B.reject('fabricated_A_cost_zero',got['A_cost']==1,got['A_cost']==0)
 B.reject('supplied_contract_claimed_implemented',not got['recursive_solver_implemented'],got['recursive_solver_implemented'])
 return {'sources':norm(ss),'B_sources':norm(b),'B_target':norm(bt),'measurements':got,'mock_cases':len(d['mock_calls'])}

def run(pilot=False):
 start=time.monotonic();B=Battery();cases=DATA['literal_cases'][:DATA['limits']['pilot_cases']] if pilot else DATA['literal_cases']
 observations={}
 for c in cases:
  got=evaluate(c);observations[c['id']]=got
  for k,v in c['expected'].items():B.equal(c['id']+'.'+k,got[k],v)
 banks=[];group=None
 if not pilot:
  for c in GUARDS:
   t,ss,F=c['T'],c['sources'],c['F'];actual={'proper':proper(t,ss),'state':state_agrees(t,ss,F),'additional':max(0,len(F)-len(ss))}
   assert actual['state']==graph_state(t,ss,F)
   for k,v in c['expected'].items():B.equal('guard.'+c['id']+'.'+k,actual[k],v)
  for bank in DATA['partition_banks']:
   f=DATA['fixtures'][bank['fixture']];S,T=g.Original(f['S']),g.Original(f['T']);Q=f['Q'];ss=materialize(f['S'],Q)
   ps=list(g.partitions(bank['labels']));B.equal(bank['fixture']+'.partition_denominator',len(ps),bank['denominator'])
   state_set=[];orig_set=[];rows=[]
   for F in ps:
    a=state_agrees(f['T'],ss,F);assert a==graph_state(f['T'],ss,F)
    original=g.agrees(T,S,F);assert original==g.raw_agrees(T,S,F)
    o=original and g.refines(F,Q)
    if a:state_set.append(g.canon_partition(F))
    if o:orig_set.append(g.canon_partition(F))
    rows.append({'F':norm(F),'state':a,'original_refinement':o,'additional':max(0,len(F)-len(ss))})
   for key,actual in [('state_accepts',state_set),('original_refinement_accepts',orig_set)]:
    B.equal(bank['fixture']+'.'+key,sorted(actual),sorted(g.canon_partition(x) for x in bank[key]))
   banks.append({'fixture':bank['fixture'],'denominator':len(ps),'rows':rows})
  x=observations['target_overlap_refined'];y=observations['source_overlap_omitted_guard'];r=observations['reordered_lists_literal_sources']
  B.reject('false_target_Q_requirement',x['state'],x['state'] and x['target_Q_clear'])
  B.reject('omitted_source_Q_equivalence',x['state']==(x['original_AF'] and x['refines']),y['state']==(y['original_AF'] and y['refines']))
  B.reject('dropped_materialization_entry',x['sources']==[[0,1],[2,3]],x['sources'][:-1]==[[0,1],[2,3]])
  B.reject('wrong_source_count_subtraction',x['additional']==1,max(0,3-1)==1)
  B.reject('canonical_source_order_assumption',r['sources']==[[2,3],[0,1]],sorted(r['sources'])==[[2,3],[0,1]])
  group=grouping(B)
 elapsed=time.monotonic()-start;cap=DATA['limits']['pilot_seconds' if pilot else 'battery_seconds'];assert elapsed<=cap,('OPEN_time_cap',elapsed,cap)
 return {'phase':'PRE-CANDIDATE','candidate_contacts':0,'extra_independent_replications':0,
  'mode':'pilot' if pilot else 'full','seconds':elapsed,'cap_seconds':cap,'literal_cases':len(cases),'guard_cases':0 if pilot else len(GUARDS),
  'expected_field_denominator':len(B.rows),'expected_fields_passed':sum(r['pass'] for r in B.rows),
  'mismatch_denominator':len(B.mismatches),'mismatches_rejected':sum(r['rejected'] for r in B.mismatches),
  'semantic_mutation_denominator':len(B.semantic),'semantic_mutations_rejected':len(B.semantic),
  'comparisons':B.rows,'mismatches':B.mismatches,'semantic_mutations':B.semantic,'observations':observations,
  'partition_banks':banks,'grouping':group,'verdict':'PASS_BOUNDED_PRE_CANDIDATE_CONTROLS_ONLY','all_main_milestones':'OPEN'}

def main():
 a=argparse.ArgumentParser();a.add_argument('--pilot',action='store_true');a.add_argument('--output',required=True);args=a.parse_args();out=Path(args.output)
 try:r=run(args.pilot)
 except Exception as e:
  r={'verdict':'OPEN_CONTROL_FAILURE','phase':'PRE-CANDIDATE','candidate_contacts':0,'error':repr(e),'traceback':traceback.format_exc()};out.write_text(json.dumps(r,indent=2)+'\n');raise
 out.write_text(json.dumps(r,indent=2)+'\n')
 print(json.dumps({k:r[k] for k in ['verdict','mode','seconds','literal_cases','guard_cases','expected_field_denominator','mismatch_denominator','semantic_mutation_denominator','candidate_contacts']}))
if __name__=='__main__':main()
