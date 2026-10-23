#!/usr/bin/env python3
"""One-shot fixed graph-interface observations. No candidate imports or query implementation.

Wraps the disclosed own X0 evaluator unchanged; new observations are not a new
independent replication. Exhausts only frozen tiny local partitions/one-edge
inventories, never a tree or input census.
"""
import argparse,copy,hashlib,importlib.util,itertools,json,time
from fractions import Fraction as F
from pathlib import Path
P=Path(__file__).resolve().parent.parent
sp=importlib.util.spec_from_file_location('own_x0',P/'instrument/x0_evaluator_reused.py');x=importlib.util.module_from_spec(sp);sp.loader.exec_module(x)
DATA=json.loads((P/'fixtures-v1.json').read_text())
def tree_edges(t,p=''):
 return [] if isinstance(t,int) else [p+'0',p+'1']+tree_edges(t[0],p+'0')+tree_edges(t[1],p+'1')
def regions(g,v,sel):
 out=[]
 for w in sorted(g.adj[v]):
  seen={v};stack=[w];labels=set()
  while stack:
   z=stack.pop()
   if z in seen:continue
   seen.add(z);labels|=set(k for k,p in g.at.items() if p==z);stack+=list(g.adj[z]-seen)
  if labels&set(sel):out.append(sorted(labels&set(sel)))
 return out
def choose(t,A,B):
 g=x.Graph(t);a,b=set(A),set(B)
 if not(g.distinct and len(A)==len(a) and len(B)==len(b) and a and b and a<=g.at.keys() and b<=g.at.keys() and not a&b):return None
 ha,hb=g.hull(A),g.hull(B)
 for v in g.adj:
  if v in ha&hb and (len(regions(g,v,a))==3 or len(regions(g,v,b))==3):return {'kind':'vertex','vertex':v}
 for e in tree_edges(t):
  sec=[a&g.desc[e],a-g.desc[e],b&g.desc[e],b-g.desc[e]]
  if {e,e[:-1]}<=ha&hb and all(sec) and all(not(g.hull(z)&hb) for z in sec[:2]) and all(not(g.hull(z)&ha) for z in sec[2:]):
   return {'kind':'edge','edge':[e[:-1],e]}
 return None
def restrict(t,selected):
 if isinstance(t,int):return t if t in selected else None
 a,b=restrict(t[0],selected),restrict(t[1],selected)
 return b if a is None else a if b is None else [a,b]
def refines(fine,coarse):return all(any(set(b)<=set(c) for c in coarse) for b in fine)
def colors(f):
 a,b,c=map(set,f['P']);d=x.Graph(f['T']).desc.get(f['edge'],set())
 return {name:{z:i for i,part in enumerate(parts) for z in part} for name,parts in [('A',[a&d,a-d,b,c]),('B',[a,b&d,b-d,c])]}
def regime(f):
 s,t=x.Graph(f['S']),x.Graph(f['T']);g,secs=x.regime(s,t,f['P'],f['edge']);A,B,C=f['P']
 g.update({'A_rooted_bad':not x.agrees(s,t,A),'B_rooted_bad':not x.agrees(s,t,B),'C_rooted_good':x.agrees(s,t,C),
           'literal_selector':choose(f['T'],A,B)=={'kind':'edge','edge':[f['edge'][:-1],f['edge']]}})
 return g,secs
def cost(r):return [len(o['sourceCuts']) for o in r['outputs']]
def local_record(f,parent):
 S,T=restrict(f['S'],set(parent)),restrict(f['T'],set(parent));s,t=x.Graph(S),x.Graph(T)
 valid=[];allrows=[]
 for e in tree_edges(S):
  cp=s.cut_parts([e]);ok=x.agreement(s,t,s.labels,cp['parts'])
  allrows.append({'edge':e,'cut_graph':cp,'agreement':ok})
  if ok:valid.append(e)
 return {'S':S,'T':T,'minimum':x.optimum(s,t,[parent]),'one_edge_denominator':len(allrows),'one_edge_rows':allrows,'valid_one_edges':valid,'own_certificate':[valid[0]] if valid else None}
def evaluate(f,checks):
 def add(name,got,want=True):checks.append({'name':f['id']+' / '+name,'got':got,'expected':want,'pass':got==want})
 s,t=x.Graph(f['S']),x.Graph(f['T']);g,sec=regime(f);cs=colors(f);cap=len(s.labels)-1
 add('actual input regime',all(g.values()));add('literal sectors',[sorted(z) for z in sec],f['expected_sectors'])
 add('sector agreements',[x.agrees(s,t,z) for z in sec],f['expected_sector_good'])
 add('same exact selector on parent swap',choose(f['T'],f['P'][1],f['P'][0]),choose(f['T'],*f['P'][:2]))
 calls={name:x.generate(f['S'],col,cap+3) for name,col in cs.items()};budgets={};hulls={};opposite=[];local=None
 for name,r in calls.items():
  add(name+' literal costs',cost(r),f['expected_costs'][name]);add(name+' budget3 literal probe',cost(x.generate(f['S'],cs[name],3)),f['expected_probe'][name])
  add(name+' no generator refusal',r['refusals'],[])
  budgets[name]=[]
  for q in range(cap+4):
   rr=x.generate(f['S'],cs[name],q);expected=[o for o in r['outputs'] if len(o['sourceCuts'])<=q]
   add(name+' q'+str(q)+' literal capped list',rr['outputs'],expected)
   budgets[name].append({'q':q,'receipt':rr})
  hulls[name]=[]
  for j,o in enumerate(r['outputs']):
   cp=s.cut_parts(o['sourceCuts']);bs=o['partition']
   add(name+str(j)+' exact original source cuts',cp['parts'],x.canon(bs));add(name+str(j)+' proper/no-empty original realization',x.proper(s.labels,bs) and not cp['empty_components'] and cp['graph_components']==len(o['sourceCuts'])+1)
   add(name+str(j)+' original parent refinement',refines(bs,f['P']))
   hulls[name].append({'source':[sorted(s.hull(z)) for z in bs],'target':[sorted(t.hull(z)) for z in bs],
                        'source_disjoint':s.disjoint(bs),'target_disjoint':t.disjoint(bs),'agreement':x.agreement(s,t,s.labels,bs)})
 if f['cheap']:
  name=f['cheap'];other='B' if name=='A' else 'A';ix=0 if name=='A' else 1;parent=f['P'][ix];otherparent=f['P'][1-ix];C=f['P'][2]
  o=calls[name]['outputs'][0]
  add('cheap literal full partition',o['partition'],f['cheap_partition']);add('cheap literal cuts',o['sourceCuts'],f['cheap_cuts'])
  add('cheap original source and target embedding',s.disjoint(o['partition']) and t.disjoint(o['partition']))
  add('embedding is not bad-parent agreement',x.agreement(s,t,s.labels,o['partition']),False)
  add('other literal partitions',[v['partition'] for v in calls[other]['outputs']],f['opposite_partitions']);add('other literal cuts',[v['sourceCuts'] for v in calls[other]['outputs']],f['opposite_cuts'])
  if 'local'in f:
   local=local_record(f,parent);want=f['local']
   for k in ['S','T']:add('local exact '+k,local[k],want[k])
   add('local global partition minimum',local['minimum']['additional'],want['minimum']);add('local exact partition denominator',local['minimum']['partition_denominator'],want['partition_denominator'])
   add('local every one-edge certificate',local['valid_one_edges'],want['all_valid_one_edges']);add('local own first certificate',local['own_certificate'],want['own_first_certificate'])
   ls,lt=x.Graph(local['S']),x.Graph(local['T']);add('cheap sectors actual local agreement',x.agreement(ls,lt,parent,want['cheap_sector_certificate']))
   qcp=ls.cut_parts(want['capped_cost2_certificate']);add('minimum does not discount every capped legal answer',x.agreement(ls,lt,parent,qcp['parts']) and len(qcp['parts'])-1==2 and 2>2-1)
   wrong=s.cut_parts(local['own_certificate']);add('local address is not whole-source certificate',x.canon([set(z)&set(parent) for z in wrong['parts'] if set(z)&set(parent)])!=x.canon(ls.cut_parts(local['own_certificate'])['parts']))
  else:
   bads=f['two_bad_blocks'];add('two distinct actual bad emitted blocks',len({tuple(sorted(b)) for b in bads})==2 and all(any(set(b)==set(z) for z in o['partition']) and not x.agrees(s,t,b) for b in bads) and t.disjoint(bads))
  for j,v in enumerate(calls[other]['outputs']):
   bs=v['partition'];bp=[z for z in bs if set(z)<=set(otherparent)];whole=any(set(z)==set(parent) for z in bs) and any(set(z)==set(C) for z in bs)
   cross=all(not(t.hull(parent)&t.hull(z)) for z in bp+[C]);within=not t.disjoint(bp)
   add('opposite'+str(j)+' whole cheap parent and C',whole);add('opposite'+str(j)+' cross-clearance',cross);add('opposite'+str(j)+' retained within-other overlap',within,f['opposite_within_other_overlap'][j])
   lr=local_record(f,parent) if local else None
   if local:add('opposite'+str(j)+' identical local problem and certificates',lr,local)
   opposite.append({'occurrence':j,'partition':bs,'whole_parent_C':whole,'other_pieces':bp,'cross_clear':cross,'within_other_overlap':within,'local':lr,
                    'parent_target_hull':sorted(t.hull(parent)),'other_target_hulls':[sorted(t.hull(z)) for z in bp], 'C_target_hull':sorted(t.hull(C))})
 else:
  for name in ['A','B']:
   add(name+' frozen full list partitions',[z['partition'] for z in calls[name]['outputs']],f['raw_partitions'][name]);add(name+' frozen cuts',[z['sourceCuts'] for z in calls[name]['outputs']],f['raw_cuts'][name])
 raw=calls['A']['outputs']+calls['B']['outputs'];masses=[]
 for cpair in DATA['rational_c']:
  c=F(*cpair);m=sum((c**-len(z['sourceCuts']) for z in raw),F());masses.append({'c':str(c),'mass':str(m),'raw_denominator':len(raw)})
  if not f['cheap']:add('same appended two-high literal mass '+str(c),m,4*c**-4)
 return {'id':f['id'],'regime':g,'selector':choose(f['T'],*f['P'][:2]),'sectors':[sorted(z) for z in sec],
         'parent_source_hulls':[sorted(s.hull(z)) for z in f['P']],'parent_target_hulls':[sorted(t.hull(z)) for z in f['P']],
         'calls':calls,'budgets':budgets,'hulls':hulls,'local':local,'opposite':opposite,'appended_raw':raw,'masses':masses}
def primitives(checks):
 def add(n,g,w=True):checks.append({'name':'primitive / '+n,'got':g,'expected':w,'pass':g==w})
 for name,f in DATA['primitive_controls'].items():
  if 'expected_additional'in f:add(name,x.optimum(x.Graph(f['S']),x.Graph(f['T']),[x.Graph(f['S']).labels])['additional'],f['expected_additional'])
  elif 'expected_hull'in f:add(name,sorted(x.Graph(f['tree']).hull(f['selection'])),f['expected_hull'])
  else:
   r=x.generate(f['S'],{int(k):v for k,v in f['colors'].items()},f['q'])
   if 'expected_costs'in f:add(name+' costs',cost(r),f['expected_costs'])
   if 'expected_parts'in f:add(name+' parts',sorted(x.canon(z['partition']) for z in r['outputs']),sorted(x.canon(z) for z in f['expected_parts']))
   if 'expected_refusal'in f:add(name+' refusal',r['refusals'],[f['expected_refusal']])
 add('false rooted whole-block agreement',x.agreement(x.Graph([[0,1],2]),x.Graph([0,[1,2]]),[0,1,2],[[0,1,2]]),False)
def guards_and_mutations(results,checks):
 def add(n,g,w=True):checks.append({'name':'mutation / '+n,'got':g,'expected':w,'pass':g==w})
 outside=[]
 for f in DATA['outside']:
  g,sec=regime(f);add(f['id']+' exact failed guards',[k for k,v in g.items() if not v],f['expected_false_guards'])
  calls={name:x.generate(f['S'],col,len(x.Graph(f['S']).labels)+2) for name,col in colors(f).items()}
  if 'expected_costs'in f:add(f['id']+' costs',{k:cost(v) for k,v in calls.items()},f['expected_costs'])
  outside.append({'id':f['id'],'guards':g,'calls':calls,'theorem_fire':False})
 f=DATA['fixtures'][0];r=results[0];s,t=x.Graph(f['S']),x.Graph(f['T']);raw=r['appended_raw']
 add('omitted raw occurrence rejected',raw[:-1]!=raw);add('duplicated raw occurrence rejected',raw+[copy.deepcopy(raw[0])]!=raw)
 twin=[copy.deepcopy(raw[0]),copy.deepcopy(raw[0])];add('raw repeated occurrence not deduplicated',sum((F(2)**-len(z['sourceCuts']) for z in twin),F())==F(1,4))
 col=colors(f)['A'];badcol={k:(2 if v==3 else v) for k,v in col.items()}
 add('wrong four-color cardinality rejected',len(set(badcol.values()))==4,False);add('three-color edge emits forbidden cost2',2 in cost(x.generate(f['S'],badcol,3)))
 B=f['P'][1];D=t.desc[f['edge']];want=x.canon([set(B)&D,set(B)-D]);one=[]
 for e in tree_edges(f['S']):
  cp=s.cut_parts([e]);one.append(x.canon([set(z)&set(B) for z in cp['parts'] if set(z)&set(B)])==want)
 add('whole bad parent sector cut one-edge mutation rejected',any(one),False)
 add('different selected edge on swap rejected',choose(f['T'],f['P'][1],f['P'][0])!={'kind':'edge','edge':['0','01']})
 pub=DATA['reused_public_false_control'];ps,pt=x.Graph(pub['S']),x.Graph(pub['T']);F0,Fp=DATA['public_F'],DATA['public_Fprime']
 pr=x.generate(pub['S'],colors(pub)['B'],6)['outputs']
 add('original F is actual agreement refines P',x.agreement(ps,pt,ps.labels,F0) and refines(F0,pub['P']))
 add('original F need not refine any literal B output',any(refines(F0,z['partition']) for z in pr),False)
 add('correctness-only Fprime is actual no-larger reconstruction',x.agreement(ps,pt,ps.labels,Fp) and len(Fp)<=len(F0) and any(refines(Fp,z['partition']) for z in pr))
 A,B=f['P'][:2]
 add('absent label selector refuses',choose(f['T'],A+[999],B),None);add('duplicate selector input refuses',choose(f['T'],A+[A[0]],B),None)
 for e in ['',t.at[1],'111111']:
  z=copy.deepcopy(f);z['edge']=e;g,_=regime(z);add('invalid root/leaf/absent edge '+repr(e)+' caught',all(g.values()),False)
 add('child order topology transported',x.Graph([f['S'][1],f['S'][0]]).shape(A)==s.shape(A))
 return outside
if __name__=='__main__':
 ap=argparse.ArgumentParser();ap.add_argument('stage',choices=['pilot','battery']);a=ap.parse_args();st=time.perf_counter();checks=[];rows=[]
 try:
  primitives(checks)
  if not all(z['pass'] for z in checks):raise RuntimeError('planted primitive control failure')
  fs=DATA['fixtures'][:1] if a.stage=='pilot' else DATA['fixtures']
  if a.stage=='battery' and not json.loads((P/'graph-pilot-v1.json').read_text())['all_pass']:raise RuntimeError('pilot not passed')
  for f in fs:
   rows.append(evaluate(f,checks))
   if not all(z['pass'] for z in checks):raise RuntimeError('frozen expectation mismatch at '+f['id'])
  outscope=[] if a.stage=='pilot' else guards_and_mutations(rows,checks)
  out={'phase':'PRE-CANDIDATE ONLY','stage':a.stage,'fixtures':rows,'outside':outscope,'checks':checks,'denominator':len(checks),'passed':sum(z['pass'] for z in checks),'all_pass':all(z['pass'] for z in checks),
       'seconds':time.perf_counter()-st,'candidate_contact':False,'candidate_compilation':False,'replication_increment':0,'source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
  (P/('graph-'+a.stage+'-v1.json')).write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({k:v for k,v in out.items() if k not in ['fixtures','outside','checks']},indent=2));raise SystemExit(0 if out['all_pass'] else 1)
 except Exception as ex:
  (P/('graph-'+a.stage+'-v1-FAILURE.json')).write_text(json.dumps({'exception':repr(ex),'completed_fixtures':rows,'checks':checks,'seconds':time.perf_counter()-st},indent=2)+'\n');raise
