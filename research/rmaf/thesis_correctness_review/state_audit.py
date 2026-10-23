"""Post-unblinding active-state audit with frozen independent graph/cut arithmetic.
Candidate import obtains states only; all cut solutions and exchange checks here
use the independently authored Graph.cut. No author oracle/helper imports.
"""
import argparse, copy, json, random, time
from pathlib import Path
from independent import Graph,trees
from replay_candidate import candidate
HERE=Path(__file__).parent

def convert(f):
 g=object.__new__(Graph);g.child=copy.deepcopy(f.child);g.parent={v:u for u,vs in g.child.items() for v in vs}
 g.roots=[v for v in g.child if v not in g.parent]
 g.label={v:','.join(sorted(block)) for v,block in f.label.items()};g.bylabel={x:v for v,x in g.label.items()};g.labels=tuple(sorted(g.bylabel));g.edges=tuple(sorted(g.parent));return g

def descend(g,v):return ([g.label[v]] if v in g.label else [])+[x for w in g.child[v] for x in descend(g,w)]

def audit(state,corrupt=False):
 f1,f2,av,cv,a,c,case=state;g,h=convert(f1),convert(f2);gm=g.allcuts();hm=h.allcuts();common=set(gm)&set(hm)
 d=min(hm[F][0] for F in common);opts=[E for F in common if hm[F][0]==d for E in hm[F][1]]
 path=h.path(a,c)
 if path is None:return {'case':case,'d':d,'optima':len(opts),'normalization_checks':0,'root_safe_checks':0,'raw_cover_counterexamples':0}
 ps=set(path);P={v for v in path if h.parent.get(v) in ps};B={w for v in path[1:-1] for w in h.child[v] if w not in ps}
 u=next(v for v in path if h.parent.get(v) not in ps)
 count=0;rootcount=0;failures=[];badcover=[]
 if len(B)==2:
  for E in opts:
   if not(a in E or c in E or B<=E):badcover.append(sorted(E))
   for z in (a,c):
    if z in E and E&B:
     added=set(E)|B; removed=added&P; normalized=added if corrupt else added-P
     if len(removed)>=2 and u in h.parent:normalized.add(u)
     count+=1;rootcount+=int(len(removed)>=2 and u not in h.parent)
     if h.cut(normalized) not in gm or len(normalized)>d or not B<=normalized:
      failures.append({'E':sorted(E),'normalized':sorted(normalized),'d':d,'endpoint':z})
 x1=g.parent.get(av);x1=next((w for w in g.child.get(g.parent.get(x1),[]) if w!=x1),None)
 x2=None
 if x1 is not None:
  block=descend(g,x1)
  x2=next((v for v in h.child if sorted(descend(h,v))==sorted(block) and g.restricted(block)==h.restricted(block)),None)
 root_second=case=='2B' and x2 is not None and h.parent.get(x2) not in h.parent
 bcy_bad=[]
 if case=='BCY':
  assert x2 is not None
  y=next(w for w in h.child[h.parent[x2]] if w!=x2)
  bcy_bad=[sorted(E) for E in opts if not(x2 in E or B<=E or {c,y}<=E)]
 return {'case':case,'d':d,'optima':len(opts),'normalization_checks':count,'root_safe_checks':rootcount,'normalization_failures':failures,'raw_cover_counterexamples':len(badcover),'bcy_raw_cover_counterexamples':len(bcy_bad),'second_2B_normalization_root_parent_absent':root_second,'witness':{'F1_child':g.child,'F1_label':g.label,'F2_child':h.child,'F2_label':h.label,'a':a,'c':c,'B':sorted(B),'bad_Cover_E':badcover[:1],'bad_BCY_E':bcy_bad[:1]} if badcover or bcy_bad or root_second or failures else None}

def collect(limit):
 states=[];seen=set();old=candidate.branches
 def capture(f1,f2,av,cv,a,c):
  case,opts=old(f1,f2,av,cv,a,c)
  key=repr((f1.child,f1.label,f1.protected,f2.child,f2.label,f2.protected,a,c))
  if key not in seen and len(states)<limit:
   seen.add(key);states.append((copy.deepcopy(f1),copy.deepcopy(f2),av,cv,a,c,case))
  return case,opts
 candidate.branches=capture
 try:
  # Source-file witnesses provide rare branch coverage; independent sampler adds states.
  w=json.loads((HERE.parent/'results'/'thesis-correctness-sweep-n6-limit3000-seed613.json').read_text())['branch_witnesses']
  for case in ['BCY','A2BC-protected-c','2B','A3BC','A2BC','RB*','RB','B','AC']:
   z=w[case]
   for q in range(z['oracle_cuts']+2):candidate.decide(z['t1'],z['t2'],q)
  if len(states)<limit:
   ts=trees(list('abcdef'));rng=random.Random(6142026)
   for _ in range(150):
    t1,t2=rng.choice(ts),rng.choice(ts)
    for q in range(4):candidate.decide(t1,t2,q)
    if len(states)>=limit:break
 finally:candidate.branches=old
 return states

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--limit',type=int,default=10);args=ap.parse_args();start=time.perf_counter()
 f1=candidate.Forest.tree(('a',('b',('c','d'))));f2=candidate.Forest.tree(((('a','c'),'b'),'d'))
 ids=lambda f,x:next(v for v,b in f.label.items() if b==frozenset([x]))
 plant=(f1,f2,ids(f1,'c'),ids(f1,'d'),ids(f2,'c'),ids(f2,'d'),'A2BC')
 clean=audit(plant);broken=audit(plant,True)
 assert clean['normalization_checks']>0 and not clean['normalization_failures'] and broken['normalization_failures']
 states=collect(args.limit);rows=[audit(s) for s in states]
 totals={k:sum(r.get(k,0) for r in rows) for k in ['normalization_checks','root_safe_checks','raw_cover_counterexamples','bcy_raw_cover_counterexamples','second_2B_normalization_root_parent_absent']}
 totals['normalization_failures']=sum(len(r.get('normalization_failures',[])) for r in rows)
 report={'states':len(states),'state_cap':args.limit,'controls':{'timing':'post-unblinding controls, after initial 10-state pilot; not claimed blinded','clean_normalization_checks':clean['normalization_checks'],'omitted_removal_mutant_failures':len(broken['normalization_failures'])},'scope':'finite actual candidate snapshots, fresh exact cut arithmetic; every-optimum Cover deliberately attacked','seconds':time.perf_counter()-start,'totals':totals,'rows':rows}
 p=HERE/f'state-audit-{args.limit}.json';p.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps({k:v for k,v in report.items() if k!='rows'}));assert not totals['normalization_failures']
if __name__=='__main__':main()
