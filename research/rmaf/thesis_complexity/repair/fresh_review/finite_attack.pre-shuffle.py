#!/usr/bin/env python3
"""One-shot fresh local attack; imports only this review's fresh checker.
Enumerates labelled rooted binary F2 trees, labels input lineage explicitly.
"""
from fresh_checker import *
from functools import lru_cache
from itertools import combinations
import argparse
@lru_cache(None)
def trees(labels):
    if len(labels)==1:return (labels[0],)
    first,*rest=labels;out=[]
    for size in range(len(rest)):
        for add in combinations(rest,size):
            left=tuple(sorted((first,)+add));right=tuple(x for x in labels if x not in left)
            for l in trees(left):
                for r in trees(right):out.append((l,r))
    return tuple(out)
def tonode(t):return N(t) if isinstance(t,str) else N(ch=[tonode(x) for x in t])
def atoms(key):return set(re.findall(r'[A-Za-z0-9_]+',key))
def prefix(st,k,local,rootk):
    if k<0:return (1,0,F(0))
    st=normalize(st)
    if st.active()<=2:return (1,0,F(0))
    possibilities=[]
    for pair in choices(st):
        if not set.union(*(atoms(x) for x in pair))<=local:
            possibilities.append((0,1,F(2)**(k-rootk)));continue
        info=classify(st,pair);v=1;l=0;m=F(0)
        for b in info['branches']:
            if b['legal']:
                # preserve negative-budget failure precedence
                if k-len(b['cuts'])<0:q=(1,0,F(0))
                else:q=prefix(apply(st,b),k-len(b['cuts']),local,rootk)
                v+=q[0];l+=q[1];m+=q[2]
        possibilities.append((v,l,m))
    return max(possibilities,key=lambda q:F(128)*F(2)**rootk*q[2]+q[0]-3*q[1])
def run(limit,stage):
    started=time.perf_counter();checked=0;admissible=0;tests=0;fires=[];examples=[];shape_checks=0
    for size,labels,f1 in [
      (3,('a','p','q','x','y','z'),'((a,((x,y),z)),(p,q))'),
      (4,('a','p','q','u','v','x','y'),'((a,((x,y),(u,v))),(p,q))')]:
        for tx in trees(labels)[:limit]:
            checked+=1;st=State(parse(f1),[N('rho',[tonode(tx)])]);b,p,d,comp=index(st.f);a=b['a'];bs=sibling(a,p)
            if bs is None:continue
            set_prot(st,['a'],['a',bs.key()])
            for pair in [('x','y'),('y','x')]:
                if pair[0] in bs.labels():continue
                try:info=classify(st,pair)
                except AssertionError:continue
                # Shape check applies to every source-legal branch, even non-target cases.
                for br in info['branches']:
                    if br['legal']:
                        parents=[p[b[x]] for x in br['cuts']];shape_checks+=1
                        if len(parents)!=len(set(parents)):
                            fires.append({'step':'source-cut-shape','scope':'local','instance':repr(tx),'branch':br,'lhs':len(parents),'rhs':len(set(parents)),'residual':len(parents)-len(set(parents))})
                if info['case']!='A3BC' or len(info['pendants'])!=3 or not all(br['legal'] for br in info['branches']):continue
                admissible+=1;C=apply(st,next(br for br in info['branches'] if br['name']=='C'))
                if len(examples)<8:examples.append({'size':size,'F2':repr(tx),'pair':pair,'pendants':info['pendants']})
                if size==4:
                    # After y removal, if u/v have common root or B merges them, x cannot be its sibling.
                    _,(by,pa,_,co)=C.idx();x=by[pair[0]]
                    if 'u' in by and 'v' in by and co[by['u']] is co[by['v']]:
                        r,_=path_info(C,'u','v')
                        if sibling(r,pa) is x:
                            fires.append({'step':'four-root-no-free-B-merge','scope':'local H1/H2/H3','instance':repr(tx),'pair':pair,'lhs':1,'rhs':0,'residual':1})
                local={'a','x','y','z'} if size==3 else {'a','x','y','u','v'}
                for K in range(0,8):
                    V,L,M=prefix(C,K-1,local,K-1);lhs=F(128)*F(2)**(K-1)*M+V-3*L;rhs=F(128)*F(2)**(K-3)-1;tests+=1
                    if lhs>rhs:fires.append({'step':'geometry-frontier-bound','scope':'local; not source-reachable certificate','instance':repr(tx),'pair':pair,'K':K,'V':V,'L':L,'M':str(M),'lhs':str(lhs),'rhs':str(rhs),'residual':str(lhs-rhs)})
    result=dict(stage=stage,scope='finite connected local states only; outside-b assumption enforced; no source-history certification',input_trees=checked,admissible_orientations=admissible,frontier_budget_tests=tests,source_shape_checks=shape_checks,fires=fires,examples=examples,elapsed_seconds=time.perf_counter()-started)
    path=ROOT/f'results/thesis-runtime-repair-fresh-review-{stage}.json';path.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({k:v for k,v in result.items() if k not in ('examples','fires')}));print('fires',len(fires))
    assert not fires
if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('--limit',type=int,default=200);ap.add_argument('--stage',default='pilot');a=ap.parse_args();run(a.limit,a.stage)
