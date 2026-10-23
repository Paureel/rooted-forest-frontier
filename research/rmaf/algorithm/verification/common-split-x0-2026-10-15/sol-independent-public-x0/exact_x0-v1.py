#!/usr/bin/env python3
"""One-shot public-target-only X0 instrument, freshly authored 2026-10-15.
Not a registered or independently certified toolkit oracle. No third-party
phylogenetic code, prior enumerator, author implementation or proof is imported.
Scientific integers use original graph BFS hulls, set partitions, induced clades.
"""
import argparse
import collections
import functools
import hashlib
import itertools
import json
import pathlib
import signal
import time

HERE = pathlib.Path(__file__).resolve().parent

def emit(path, obj):
    path.write_text(json.dumps(obj, indent=2, sort_keys=True) + '\n')

def tree(t):
    if type(t) is int:
        if t < 0: raise ValueError('negative label')
        return t
    if not isinstance(t, (list,tuple)) or len(t) != 2:
        raise ValueError('not a binary tree')
    return (tree(t[0]),tree(t[1]))

def leaves(t):
    return (t,) if type(t) is int else leaves(t[0])+leaves(t[1])

def normalize_blocks(p):
    return tuple(sorted(tuple(sorted(b)) for b in p))

def family(*ps):
    return tuple(sorted(normalize_blocks(p) for p in ps))

def parts(xs):
    # Insert the last label into every existing block, or its own new block.
    if not xs:
        yield ()
        return
    for p in parts(xs[:-1]):
        x=xs[-1]
        for i in range(len(p)):
            yield p[:i]+(p[i]+(x,),)+p[i+1:]
        yield p+((x,),)

class Graph:
    def __init__(self,t):
        self.t=tree(t)
        self.labels=tuple(sorted(leaves(self.t)))
        if len(set(self.labels))!=len(self.labels): raise ValueError('duplicate label')
        self.adj={}; self.leaf={}; self.desc={}; self.edges=[]
        def build(a,p=''):
            self.adj[p]=[]
            if type(a) is int:
                self.leaf[a]=p; self.desc[p]=frozenset((a,))
            else:
                for i,b in enumerate(a):
                    q=p+str(i); build(b,q)
                    self.adj[p].append(q);self.adj[q].append(p);self.edges.append((p,q))
                self.desc[p]=self.desc[p+'0']|self.desc[p+'1']
        build(self.t)
        self.vertices=tuple(sorted(self.adj));self.vertex_index={v:i for i,v in enumerate(self.vertices)}
        self.features={}
        for size in range(1,len(self.labels)+1):
            for b in itertools.combinations(self.labels,size):
                bs=frozenset(b); h=set()
                for a,c in itertools.combinations_with_replacement(b,2):
                    h.update(self.path(self.leaf[a],self.leaf[c]))
                bits=sum(1<<self.vertex_index[v] for v in h)
                clades=frozenset(self.desc[v]&bs for v in self.vertices if len(self.desc[v]&bs)>=2)
                self.features[bs]=(bits,clades,tuple(sorted(h)))
    def path(self,a,b):
        queue=collections.deque((a,)); prev={a:None}
        while queue:
            v=queue.popleft()
            if v==b: break
            for w in self.adj[v]:
                if w not in prev: prev[w]=v;queue.append(w)
        path=[];v=b
        while v is not None: path.append(v);v=prev[v]
        return tuple(path)
    def hull(self,b):
        return self.features[frozenset(b)][2]
    def cut_components(self,cuts):
        removed=frozenset(tuple(sorted(e)) for e in cuts)
        unseen=set(self.vertices);comps=[]
        while unseen:
            first=min(unseen); stack=[first]; unseen.remove(first);vs=[]
            while stack:
                v=stack.pop();vs.append(v)
                for w in self.adj[v]:
                    if w in unseen and tuple(sorted((v,w))) not in removed:
                        unseen.remove(w);stack.append(w)
            ls=tuple(sorted(x for x,p in self.leaf.items() if p in vs))
            comps.append({'vertices':sorted(vs),'labels':ls})
        return comps
    def cut_witness(self,p):
        wanted=normalize_blocks(p)
        for chosen in itertools.combinations(self.edges,len(p)-1):
            cs=self.cut_components(chosen)
            got=normalize_blocks(c['labels'] for c in cs if c['labels'])
            if got==wanted and len(cs)==len(p):
                return {'cuts':chosen,'components':cs,'cost':len(chosen)}
        raise AssertionError('no exact original cut realization')
    def literal(self):
        return {'tree':self.t,'vertices':self.vertices,'edges':self.edges,'leaves':self.leaf}

@functools.lru_cache(None)
def graph(t): return Graph(t)

def restriction(t,selected):
    if type(t) is int: return t if t in selected else None
    a=restriction(t[0],selected); b=restriction(t[1],selected)
    if a is None:return b
    if b is None:return a
    return (a,b)

def rename(t,old,new):
    if type(t) is int:return new if t==old else t
    return tuple(rename(a,old,new) for a in t)

def canonical(t):
    if type(t) is int:return ('L',t)
    return ('N',)+tuple(sorted((canonical(t[0]),canonical(t[1]))))

def agrees(g,h,p):
    if not p or any(not b for b in p):return False
    flat=tuple(x for b in p for x in b)
    if sorted(flat)!=list(g.labels) or sorted(flat)!=list(h.labels):return False
    usedg=0;usedh=0
    for b in p:
        k=frozenset(b)
        gb,gc,_=g.features[k];hb,hc,_=h.features[k]
        if gc!=hc or usedg&gb or usedh&hb:return False
        usedg|=gb;usedh|=hb
    return True

@functools.lru_cache(None)
def exact(t,s):
    g=graph(t); h=graph(s)
    if g.labels!=h.labels:raise ValueError('label mismatch')
    afs=tuple(sorted(normalize_blocks(p) for p in parts(g.labels) if agrees(g,h,p)))
    if not afs:raise AssertionError('zero AF families')
    best=min(len(p)-1 for p in afs)
    mins=tuple(p for p in afs if len(p)-1==best)
    return {'cost':best,'minima':mins,'afs':afs}

def split_edges(g,x,y):
    return tuple((p,q,'X' if g.desc[q]==x else 'Y') for p,q in g.edges if g.desc[q]==x or g.desc[q]==y)

def guard(t,s,x,y,xrep,yrep,rho,gamma):
    g=graph(t);h=graph(s);x=frozenset(x);y=frozenset(y)
    if g.labels!=h.labels:raise ValueError('label mismatch')
    if not x or not y or x&y or x|y!=set(g.labels):raise ValueError('invalid split')
    if xrep not in x or yrep not in y:raise ValueError('absent representative')
    if type(rho)is not int or type(gamma)is not int or rho<0 or gamma<0 or rho==gamma or rho in g.labels or gamma in g.labels:raise ValueError('marker collision')
    et=split_edges(g,x,y);es=split_edges(h,x,y)
    if not et or not es:raise ValueError('missing common edge')
    return g,h,x,y,et,es

def evaluate(t,s,x,y,xrep,yrep,rho=100,gamma=101):
    g,h,x,y,et,es=guard(t,s,x,y,xrep,yrep,rho,gamma)
    tx=restriction(t,x);sx=restriction(s,x);ty=restriction(t,y);sy=restriction(s,y)
    txr=rename(restriction(t,x|{yrep}),yrep,rho);sxr=rename(restriction(s,x|{yrep}),yrep,rho)
    tyg=rename(restriction(t,y|{xrep}),xrep,gamma);syg=rename(restriction(s,y|{xrep}),xrep,gamma)
    v=[exact(t,s),exact(tx,sx),exact(ty,sy),exact(txr,sxr),exact(tyg,syg)]
    glob,a,b,ar,bg=[q['cost'] for q in v]
    dx=ar-a;dy=bg-b
    predicted=a+b+(0 if dx==dy==0 else 1)
    fires=[]
    if glob!=predicted:fires.append('global_identity')
    if dx not in (0,1):fires.append('X_marker_inequality')
    if dy not in (0,1):fires.append('Y_marker_inequality')
    crosscounts=[sum(bool(set(B)&x) and bool(set(B)&y) for B in p) for p in v[0]['afs']]
    if any(c>1 for c in crosscounts):fires.append('multiple_crossing_blocks')
    mx=sum(1 for p in v[3]['minima'] for B in p if rho in B and len(B)==1)
    my=sum(1 for p in v[4]['minima'] for B in p if gamma in B and len(B)==1)
    if dx==0 and mx:fires.append('X_stable_singleton_marker')
    if dy==0 and my:fires.append('Y_stable_singleton_marker')
    return {'T':t,'S':s,'X':sorted(x),'Y':sorted(y),'reps':[xrep,yrep],'markers':[rho,gamma],
      'edges_T':et,'edges_S':es,'marked_trees':[txr,sxr,tyg,syg],
      'costs':[glob,a,b,ar,bg],'flags':[dx,dy],'identity_rhs':predicted,
      'all_af_count':len(v[0]['afs']),'crossing_distribution':dict(collections.Counter(crosscounts)),
      'marked_minimum_counts':[len(v[3]['minima']),len(v[4]['minima'])],
      'marker_singleton_minimum_counts':[mx,my], 'fires':fires,
      'minima':[q['minima'] for q in v]}


def controls():
    tA=tree([[0,1],[2,3]]); tB=tree([[0,1],2]); sB=tree([0,[1,2]])
    tC=tree([0,[1,[2,3]]]);sC=tree([2,[3,[0,1]]])
    tD=tree([[[0,1],2],3]);sD=tree([[0,[1,2]],3])
    full=lambda xs: family([xs])
    trip=lambda a,b,c: family([[a],[b,c]],[[b],[a,c]],[[c],[a,b]])
    cases=[
      ('A',tA,tA,[0,1],[2,3],0,2,100,101,[0,0,0,0,0],
       [full([0,1,2,3]),full([0,1]),full([2,3]),full([0,1,100]),full([2,3,101])],
       [tree([[0,1],100]),tree([[0,1],100]),tree([101,[2,3]]),tree([101,[2,3]])]),
      ('B',tB,sB,[0,1],[2],0,2,100,101,[1,0,0,1,0],
       [trip(0,1,2),full([0,1]),full([2]),trip(0,1,100),full([2,101])],
       [tree([[0,1],100]),tree([0,[1,100]]),tree([101,2]),tree([101,2])]),
      ('Bswap',tB,sB,[2],[0,1],2,0,100,101,[1,0,0,0,1],
       [trip(0,1,2),full([2]),full([0,1]),full([2,100]),trip(0,1,101)],
       [tree([100,2]),tree([100,2]),tree([[0,1],101]),tree([0,[1,101]])]),
      ('C',tC,sC,[0,1],[2,3],0,2,100,101,[1,0,0,1,1],
       [family([[0,1],[2,3]]),full([0,1]),full([2,3]),trip(0,1,100),trip(2,3,101)],
       [tree([0,[1,100]]),tree([100,[0,1]]),tree([101,[2,3]]),tree([2,[3,101]])]),
      ('D',tD,sD,[0,1,2],[3],0,3,100,101,[1,1,0,1,0],
       [family([[0],[1,2,3]],[[1],[0,2,3]],[[2],[0,1,3]]),trip(0,1,2),full([3]),
        family([[0],[1,2,100]],[[1],[0,2,100]],[[2],[0,1,100]]),full([3,101])],
       [tree([[[0,1],2],100]),tree([[0,[1,2]],100]),tree([101,3]),tree([101,3])]),
      ('E',tree([8,10000]),tree([8,10000]),[8],[10000],8,10000,1000003,1000033,[0,0,0,0,0],
       [full([8,10000]),full([8]),full([10000]),full([8,1000003]),full([10000,1000033])],
       [tree([8,1000003]),tree([8,1000003]),tree([1000033,10000]),tree([1000033,10000])])]
    reports=[]
    for name,t,s,x,y,xr,yr,r,g,cs,mins,marks in cases:
        got=evaluate(t,s,x,y,xr,yr,r,g)
        assert got['costs']==cs,(name,'costs',got['costs'],cs)
        assert got['minima']==mins,(name,'minima',got['minima'],mins)
        assert got['marked_trees']==marks,(name,'marked trees',got['marked_trees'],marks)
        assert not got['fires'],(name,'public control unexpected fire',got['fires'])
        cuts=[]
        for p in mins[0]:
            cuts.append({'partition':p,'T':graph(t).cut_witness(p),'S':graph(s).cut_witness(p)})
        reports.append({'name':name,'result':got,'graphs':[graph(t).literal(),graph(s).literal()],'cut_realizations':cuts})
    caught=[]
    def reject(name,fn):
        try:fn()
        except (ValueError,AssertionError) as e:
            caught.append({'name':name,'caught':str(e)});return
        raise AssertionError(('corruption escaped',name))
    def demand(cond,msg):
        if not cond:raise AssertionError(msg)
    reject('incorrect_marker_attachment',lambda:demand(canonical(reports[3]['result']['marked_trees'][0])==canonical(tree([[0,1],100])),'literal marked attachment mismatch'))
    reject('marker_collision',lambda:evaluate(tA,tA,[0,1],[2,3],0,2,0,101))
    reject('absent_representative',lambda:evaluate(tA,tA,[0,1],[2,3],0,99))
    reject('missing_common_edge',lambda:evaluate(tA,tA,[0,2],[1,3],0,1))
    reject('invalid_original_target_embedding',lambda:demand(agrees(graph(tA),graph(tA),((0,2),(1,3))),'crossing original hulls'))
    literal_hull=('', '0','00','1','10')
    assert graph(tA).hull([0,2])==literal_hull
    reject('discarded_suppressed_vertex',lambda:demand(tuple(v for v in literal_hull if v!='0')==graph(tA).hull([0,2]),'original unary path vertex discarded'))
    emptycuts=graph(tA).cut_components(())
    assert len(emptycuts)==1 and len(emptycuts[0]['labels'])==4
    reject('off_by_one_null_cuts',lambda:demand(len(emptycuts)==0+0,'components falsely used as cuts'))
    leafless=graph(tA).cut_components((('', '0'),('','1')))
    assert len(leafless)==3 and sum(not c['labels'] for c in leafless)==1
    reject('discarded_leafless_component',lambda:demand(len(leafless)==sum(bool(c['labels']) for c in leafless),'leafless root component lost'))
    reject('off_by_one_nonzero_cuts',lambda:demand(reports[3]['result']['costs'][0]==2,'two components falsely claimed two cuts'))
    reject('falsely_favorable_flag',lambda:demand(reports[3]['result']['flags']==[0,0],'C actual flags [1,1], false [0,0]'))
    reject('falsely_favorable_identity',lambda:demand(reports[3]['result']['costs'][0]==0,'C global1, false stable-stable predicts0'))
    reject('empty_side_invalid',lambda:evaluate(tA,tA,[],[0,1,2,3],0,2))
    reject('duplicate_original_label',lambda:graph(tree([[0,0],[2,3]])))
    reject('different_original_labels',lambda:evaluate(tA,tree([[0,1],[2,4]]),[0,1],[2,3],0,2))
    # Frozen label/order variants transform literal hand expectations, never computed expected costs.
    variants=[]
    def swapall(t):return t if type(t)is int else (swapall(t[1]),swapall(t[0]))
    mapping={0:17,1:103,2:1009,3:10007,8:99991,10000:999983,100:1000003,101:1000033,1000003:1000037,1000033:1000039}
    def relabel(t):return mapping[t] if type(t)is int else tuple(relabel(a) for a in t)
    for name,t,s,x,y,xr,yr,r,g,cs,mins,marks in cases:
        for mode in ('child_swaps','reverse_inputs','arbitrary_Nat_labels'):
            if mode=='child_swaps':ts,ss=swapall(t),swapall(s);args=(x,y,xr,yr,r,g);expected=mins
            elif mode=='reverse_inputs':ts,ss=s,t;args=(x,y,xr,yr,r,g);expected=mins
            else:
                ts,ss=relabel(t),relabel(s);args=([mapping[a] for a in x],[mapping[a] for a in y],mapping[xr],mapping[yr],mapping[r],mapping[g])
                expected=[family(*[[[mapping[a] for a in B] for B in p] for p in fs]) for fs in mins]
            got=evaluate(ts,ss,*args)
            assert got['costs']==cs and got['minima']==expected and not got['fires'],(name,mode)
            variants.append({'control':name,'mode':mode,'result':got})
    return {'positive_controls':reports,'caught_corruptions':caught,'variant_controls':variants,'clean_count':len(reports),'corruption_count':len(caught),'variant_count':len(variants)}

@functools.lru_cache(None)
def all_trees(labels):
    if len(labels)==1:return (labels[0],)
    first=labels[0]; tail=labels[1:];out=[]
    # The smallest label belongs to the first child, removing sibling duplication.
    for k in range(len(tail)):
        for rest in itertools.combinations(tail,k):
            a=(first,)+rest;b=tuple(x for x in tail if x not in rest)
            out.extend((l,r) for l in all_trees(a) for r in all_trees(b))
    return tuple(out)

def scientific_cases(n):
    ts=all_trees(tuple(range(n)))
    for i,t in enumerate(ts):
        for j,s in enumerate(ts):
            if n==5 and not ((17*i+31*j)%97==0 or i==j or j==104-i):continue
            gt=graph(t);gs=graph(s);labs=frozenset(range(n))
            seen=set()
            for p,q in gt.edges:
                for x in (gt.desc[q],labs-gt.desc[q]):
                    if x in seen:continue
                    seen.add(x);y=labs-x
                    et=split_edges(gt,x,y);es=split_edges(gs,x,y)
                    if es:yield i,j,t,s,tuple(sorted(x)),tuple(sorted(y)),et,es

def run_bank(args):
    start=time.perf_counter();rows=0;shape_cases=0;flags=collections.Counter();orient=collections.Counter();joint=collections.Counter();fires=[];reps_eligible=0;crosschecks=0;markedchecks=0;rep_groups=0
    out=HERE/args.output
    if out.exists():raise ValueError('output exists; preserve receipts')
    eligible=0;coverage=[]
    with out.open('w') as f:
        for index,(i,j,t,s,x,y,et,es) in enumerate(scientific_cases(args.n)):
            eligible+=1
            if index<args.offset:continue
            if shape_cases>=args.limit:break
            if time.perf_counter()-start>args.seconds:break
            shape_cases+=1;values=[];minmap=[]
            for xr in x:
                for yr in y:
                    got=evaluate(t,s,x,y,xr,yr)
                    got.update({'case_index':index,'tree_indices':[i,j],'n':args.n})
                    values.append(tuple(got['costs'][3:]));minmap.append(got['minima'][3:])
                    flags[tuple(got['flags'])]+=len(et)*len(es)
                    for a,b in itertools.product(et,es):
                        orient[a[2]+b[2]]+=1;joint[(tuple(got['flags']),a[2]+b[2])]+=1
                    reps_eligible+=len(et)*len(es);crosschecks+=got['all_af_count'];markedchecks+=sum(got['marked_minimum_counts'])
                    if got['fires']:
                        got['original_graphs']=[graph(t).literal(),graph(s).literal()]
                        got['global_cut_witnesses']=[{'partition':p,'T':graph(t).cut_witness(p),'S':graph(s).cut_witness(p)} for p in got['minima'][0]]
                        fires.append(got)
                    f.write(json.dumps(got,sort_keys=True)+'\n');f.flush();rows+=1
            rep_groups+=1
            if len(set(values))!=1:
                fire={'property':'representative_invariance','case_index':index,'T':t,'S':s,'X':x,'Y':y,'marked_costs':values}
                fires.append(fire)
            coverage.append({'case_index':index,'tree_indices':[i,j],'split':[x,y],'representative_options':len(x)*len(y),'edge_pairs':len(et)*len(es),'orientation_options':sorted({a[2]+b[2] for a,b in itertools.product(et,es)})})
    elapsed=time.perf_counter()-start
    summary={'n':args.n,'offset':args.offset,'requested_limit':args.limit,'shape_split_cases':shape_cases,'rows':rows,'edge_pair_representative_records':reps_eligible,'elapsed_seconds':elapsed,'flags':{str(k):v for k,v in sorted(flags.items())},'orientations':dict(orient),'joint_flags_orientations':{str(k):v for k,v in sorted(joint.items())},'global_AF_crossing_checks_per_representative':crosschecks,'marked_minimum_marker_checks':markedchecks,'representative_invariance_groups':rep_groups,'fires':fires,'coverage':coverage,'next_offset':args.offset+shape_cases,'fully_exhausted':eligible<=args.offset+shape_cases,'deadline_seconds':args.seconds,'criterion':'exact integer mismatch; any subsidiary violation also preserved'}
    emit(out.with_suffix('.summary.json'),summary)
    print(json.dumps({k:v for k,v in summary.items() if k not in ('coverage','fires')},sort_keys=True))
    if fires:print('FIRE_COUNT',len(fires))

if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('mode',choices=['controls','bank']);ap.add_argument('--n',type=int,default=4);ap.add_argument('--offset',type=int,default=0);ap.add_argument('--limit',type=int,default=12);ap.add_argument('--seconds',type=float,default=50);ap.add_argument('--output',default='controls.json');args=ap.parse_args()
    if args.seconds>50 or args.n>5:raise ValueError('preregistered cap exceeded')
    signal.signal(signal.SIGALRM,lambda *_:(_ for _ in ()).throw(TimeoutError('hard 59-second cap')));signal.alarm(59)
    if args.mode=='controls':
        start=time.perf_counter();result=controls();result['elapsed_seconds']=time.perf_counter()-start;emit(HERE/args.output,result)
        print(json.dumps({k:v for k,v in result.items() if k in ('clean_count','corruption_count','variant_count','elapsed_seconds')},sort_keys=True))
    else:run_bank(args)
