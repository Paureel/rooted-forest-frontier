"""One-shot Case322 public-spec controls; own frozen graph layer reused by pin.
Finite fixture evidence only, zero additional independent replication credit.
No Case322 candidate code is imported. General nested cuts retain all vertices.
"""
import argparse, copy, hashlib, importlib.util, itertools, json, pathlib, time, traceback
from fractions import Fraction

H=pathlib.Path(__file__).resolve().parent
ROOT=next(p for p in H.parents if (p/'bootloops-python').exists())
OLD=ROOT/'research/rmaf/algorithm/verification/rule4-2026-10-15/sol-independent/original_graph.py'
assert hashlib.sha256(OLD.read_bytes()).hexdigest()=='ae0a8d87583b99e8c6ce26bc19574ebc564518fb3e6c53c72f6355a3926de110'
spec=importlib.util.spec_from_file_location('own_pinned_graph',OLD)
og=importlib.util.module_from_spec(spec);spec.loader.exec_module(og)
A,B,C=11,23,47

def mirror(t):return t if type(t)is int else [mirror(t[1]),mirror(t[0])]
def orient(bit,l,r):return [r,l]if bit else[l,r]
def bottom(bits,X):
    sa,sc,sb=bits
    return orient(sb,orient(sc,orient(sa,A,X),C),B)
def fixture(name,bits=(0,0,0),cherry_order=0,target_mirror=0,source_context_side=0):
    core=[B,A]if cherry_order else[A,B]
    extra={'cside2':[],'fallback':[],'allbside-d3':[307],
           'allbside-d4':[307,401],'allbside-d5':[307,401,503]}[name]
    for x in reversed(extra):core=[x,core]
    X=[101,[157,211]]if name=='cside2'else[101,157]
    T=[101,[core,[157,[211,C]]]]if name=='cside2'else[101,[[157,core],C]]
    if name=='fallback':T=[101,[core,[157,C]]]
    S=bottom(bits,X);w=''
    for x in reversed(extra):S=orient(source_context_side,x,S)
    w=('0'if source_context_side else'1')*len(extra)
    if target_mirror:T=mirror(T)
    return dict(name=name,T=T,S=S,X=X,w=w,bits=list(bits),cherry_order=cherry_order,
                target_mirror=target_mirror,source_context_side=source_context_side,
                costs=[2,1,2,2]if name=='cside2'else[2,1,int(name[-1])]if name.startswith('allbside')else[2,1,2])

def desc(g,v):return [x for x in g.labels if g.vertex(x)in descendant_vertices(g,v)]
def descendant_vertices(g,v):
    out=set();queue=[v]
    for w in queue:out.add(w);queue.extend(g.children[w])
    return out
def pendant(g,a,b):
    hull=g.hull([a,b]);return [v for v in g.adj if v!=g.root and g.parent[v]in hull and v not in hull]
def lca(g,a,b):
    u,v=g.address[g.vertex(a)],g.address[g.vertex(b)];i=0
    while i<min(len(u),len(v))and u[i]==v[i]:i+=1
    return u[:i]
def residual(g,heads):
    if len(heads)!=len(set(heads))or any(v==g.root or v not in g.adj for v in heads):raise ValueError('invalid original arcs')
    cuts={frozenset((h,g.parent[h]))for h in heads};pending=set(g.adj);regions=[]
    while pending:
        seed=min(pending);pending.remove(seed);vs={seed};queue=[seed]
        for v in queue:
            for w in g.adj[v]:
                if w in pending and frozenset((v,w))not in cuts:pending.remove(w);vs.add(w);queue.append(w)
        labels=[x for x in g.labels if g.vertex(x)in vs]
        regions.append(dict(vertices=[g.address[v]for v in sorted(vs)],labels=labels,
                            retained_endpoint_labels=labels[:1]))
    return regions
def split_partition(g,heads):
    P=[g.labels[:]]
    for v in heads:
        selected=set(desc(g,v));P=[b for U in P for b in [[x for x in U if x in selected],[x for x in U if x not in selected]]if b]
    return P
def physical_restrict(t,labels):
    if type(t)is int:return t if t in labels else None
    l,r=[physical_restrict(x,labels)for x in t]
    return r if l is None else l if r is None else[l,r]
def source_forest(g,P):return [s for p in P if (s:=physical_restrict(g.tree,p))is not None]
def branch(g,role,heads,P=None):
    return dict(role=role,originalCuts=[g.address[v]for v in heads],
                partition=split_partition(g,heads)if P is None else P,paid=len(heads))
def guard(t,s,b):
    g=s if b['role']=='source'else t;qs=b['originalCuts'];P=b['partition']
    if len(qs)!=len(set(qs))or any(not q or q not in g.by_address for q in qs):return False
    return og.partition_ok(g.labels,P)and og.separated(g,P)and len(P)==len(qs)+1 and P==split_partition(g,[g.by_address[q]for q in qs])
def geometry(f):
    t,s=og.Graph(f['T']),og.Graph(f['S']);xl=og.Graph(f['X']).labels
    if not t.proper or not s.proper or set(t.labels)!=set(s.labels):return False,{}
    if f['w']not in s.by_address:return False,{}
    v=s.by_address[f['w']]
    if physical_subtree(s.tree,f['w'])!=bottom(f['bits'],f['X']):return False,{}
    if (A,B)not in t.cherries():return False,{}
    hs=pendant(s,A,B)
    corelabels=set(t.labels)-set(xl)-{C}
    rs=[v for v in t.adj if set(desc(t,v))==corelabels]
    if len(hs)!=2 or len(rs)!=1:return False,{}
    r=rs[0];uc=t.vertex(C);hull=t.hull(xl)
    frontier=[v for v in t.adj if v!=t.root and ((v in hull)!=(t.parent[v]in hull))]
    ok=len(frontier)==2 and set(frontier)=={r,uc}and all(t.parent[v]in hull and v not in hull for v in[r,uc])
    return ok,dict(r=t.address[r],uc=t.address[uc],qa=t.address[t.vertex(A)],ub=t.address[t.vertex(B)],
                   frontier=[t.address[v]for v in frontier],frontier_order='r,uc'if frontier==[r,uc]else'uc,r',
                   hull=[t.address[v]for v in sorted(hull)],source_pendants=[s.address[v]for v in hs],
                   source_bottom_address=f['w'],core_labels=sorted(corelabels))
def physical_subtree(t,address):
    for bit in address:
        if type(t)is int:return None
        t=t[int(bit)]
    return t
def plan(f):
    t,s=og.Graph(f['T']),og.Graph(f['S']);path=pendant(t,B,C)
    cs=[v for v in path if C in desc(t,t.parent[v])and B not in desc(t,t.parent[v])]
    bs=[v for v in path if B in desc(t,t.parent[v])and C not in desc(t,t.parent[v])and A not in desc(t,v)]
    hs=pendant(s,A,B);detached=[desc(s,v)for v in hs]
    P=detached+[[x for x in s.labels if all(x not in p for p in detached)]]
    qb=f['w']+str(1-int(f['bits'][2]));qa=t.vertex(A)
    branches=[branch(s,'source',hs,P),branch(s,'source',[s.by_address[qb]],[[B],[x for x in s.labels if x!=B]])]
    selected=[[qa,cs[0]],[qa,cs[1]]]if len(cs)>=2 else[[qa]+(bs if bs else[t.by_address[lca(t,B,C)]])]
    branches +=[branch(t,'target',qs)for qs in selected]
    return branches,dict(cside=[t.address[v]for v in cs],bside_without_a=[t.address[v]for v in bs],lca=lca(t,B,C))

def check(name,condition,records):
    records.append(dict(name=name,passed=bool(condition)))
    if not condition:raise AssertionError(name)
def catches(fn):
    try:fn()
    except (ValueError,KeyError,AssertionError):return True
    return False
def known_controls():
    checks=[];T=[101,[[A,B],C]];S=[[[A,101],C],B]
    t,s=og.Graph(T),og.Graph(S);afs=[F for F in og.partitions(t.labels)if og.agreement(t,s,F)]
    check('fresh quartet known minimum3',min(map(len,afs))==3,checks)
    check('fresh quartet cannot have full tree AF',not og.agreement(t,s,[t.labels]),checks)
    check('quartet singletons',og.agreement(t,s,[[x]for x in t.labels]),checks)
    f=fixture('fallback');t,s=og.Graph(f['T']),og.Graph(f['S']);bs,details=plan(f);ok,geom=geometry(f)
    check('fallback exact geometry',ok,checks);check('nested fallback valid',bs[-1]['originalCuts']==['100','1']and guard(t,s,bs[-1]),checks)
    check('fallback original retained regions',all(r['labels']for r in residual(t,[t.by_address[q]for q in bs[-1]['originalCuts']])),checks)
    for label,qs in [('duplicate',['100','100']),('root',['']),('absent',['999'])]:
        bad=copy.deepcopy(bs[-1]);bad['originalCuts']=qs;bad['paid']=len(qs)
        check(label+' guard rejects',not guard(t,s,bad),checks)
    bad=copy.deepcopy(bs[1]);bad['originalCuts']=[s.address[s.vertex(A)]]
    check('wrong source terminal binding rejects',not guard(t,s,bad),checks)
    # Cutting both children below a common parent creates a leafless original region.
    bad=branch(t,'target',[t.by_address['10'],t.by_address['100'],t.by_address['101']])
    check('redundant arc cost rejects',not guard(t,s,bad)and any(not r['labels']for r in residual(t,[t.by_address[q]for q in bad['originalCuts']])),checks)
    altered=copy.deepcopy(bs[-1]);altered['partition'].reverse()
    check('ordered partition corruption catches',not guard(t,s,altered),checks)
    reordered=copy.deepcopy(bs[-1]);reordered['originalCuts'].reverse();reordered['partition']=split_partition(t,[t.by_address[q]for q in reordered['originalCuts']])
    check('nested sequential split order recorded',guard(t,s,reordered)and reordered!=bs[-1],checks)
    check('same unordered split semantics',og.canon(reordered['partition'])==og.canon(bs[-1]['partition']),checks)
    for label,mut in [('labels',lambda f:f.update(S=[f['S'],11])),('topology',lambda f:f.update(T=[101,[157,[[A,B],C]]])),('core terminal',lambda f:f.update(X=[101,47]))]:
        bad=copy.deepcopy(f);mut(bad);check('geometry '+label+' corruption',not geometry(bad)[0],checks)
    # Weak pendant-X shape has raw fallback root metadata, outside exact geometry.
    weak=copy.deepcopy(f);weak['T']=[[A,B],[C,[101,157]]]
    wb,wd=plan(weak);wt,ws=og.Graph(weak['T']),og.Graph(weak['S'])
    check('weakened pendant-X root outside geometry',not geometry(weak)[0]and wd['lca']==''and not guard(wt,ws,wb[-1]),checks)
    for name in ['allbside-d3','allbside-d4','allbside-d5']:
        fs=fixture(name);bb,_=plan(fs);check(name+' full expected cost',[b['paid']for b in bb]==fs['costs'],checks)
        mutant=copy.deepcopy(bb);mutant[-1]['paid']=2
        check(name+' cost to2 catches',[b['paid']for b in mutant]!=fs['costs'],checks)
    mass=sum(Fraction(2)**(-b['paid'])for b in bs)
    doubled=bs+[bs[-1]]
    check('duplicate branch retained list mass',sum(Fraction(2)**(-b['paid'])for b in doubled)==mass+Fraction(1,4),checks)
    return dict(checks=checks,quartet_afs=afs,weak_plant=weak,weak_branches=wb)

def enumerate_family(name):
    start=time.perf_counter();f=fixture(name);t,s=og.Graph(f['T']),og.Graph(f['S']);bs,details=plan(f)
    allF=[];afs=[]
    for F in og.partitions(sorted(t.labels)):
        if len(allF)>=4140:raise ValueError('partition cap4140')
        allF.append(F)
        if og.agreement(t,s,F):afs.append(F)
        if time.perf_counter()-start>5:raise TimeoutError('fixture5s cap')
    assert min(map(len,afs))==3,'predeclared minimum mismatch'
    tables=[[F for F in afs if og.refines(F,b['partition'])]for b in bs]
    assert all(any(len(G)<=len(F)for tab in tables for G in tab)for F in afs),'finite cover fire'
    queries=[]
    for q in range(len(t.labels)):
        affordable=[i for i,b in enumerate(bs)if b['paid']<=q]
        feasible=[[F for F in tables[i]if len(F)-len(bs[i]['partition'])<=q-bs[i]['paid']]for i in affordable]
        parent=[F for F in afs if len(F)-1<=q]
        decision=any(feasible)
        assert decision==bool(parent)
        for i,tab in zip(affordable,feasible):
            assert q-bs[i]['paid']<q
            assert all(bs[i]['paid']+(len(F)-len(bs[i]['partition']))==len(F)-1 for F in tab)
        least=min((len(F)for tab in feasible for F in tab),default=None)
        assert least==min(map(len,parent),default=None)
        queries.append(dict(q=q,affordable_requests=[dict(index=i,residual=q-bs[i]['paid'])for i in affordable],
                            feasible=decision,minimum_components=least,
                            first_success=next((i for i,tab in zip(affordable,feasible)if tab),None)))
    return dict(fixture=f,partition_count=len(allF),agreements=afs,minimum_components=3,branches=bs,
                child_tables=tables,queries=queries,elapsed_seconds=time.perf_counter()-start)

def orientations(name):
    records=[];orders=set();sides=range(2)if name.startswith('allbside')else range(1)
    for bits,co,tm,ss in itertools.product(itertools.product([0,1],repeat=3),range(2),range(2),sides):
        f=fixture(name,bits,co,tm,ss);ok,geom=geometry(f);assert ok,(name,bits,co,tm,ss)
        t,s=og.Graph(f['T']),og.Graph(f['S']);bs,details=plan(f)
        assert [b['paid']for b in bs]==f['costs']
        assert all(guard(t,s,b)for b in bs)
        assert bs[0]['partition']==split_partition(s,[s.by_address[q]for q in bs[0]['originalCuts']])
        for b in bs:
            g=s if b['role']=='source'else t;rr=residual(g,[g.by_address[q]for q in b['originalCuts']])
            assert len(rr)==b['paid']+1 and all(r['labels']for r in rr)
            assert og.canon([r['labels']for r in rr])==og.canon(b['partition'])
            b['sourceForest']=source_forest(g,b['partition']);b['original_regions']=rr
            b['current_tree']=g.tree
            # Operational metadata swap changes role while physical current tree stays fixed.
            swapped_role='target'if b['role']=='source'else'source'
            swapped_current=t if swapped_role=='source'else s
            assert swapped_current.tree==g.tree
            b['swapped_role']=swapped_role
        orders.add(geom['frontier_order']);records.append(dict(fixture=f,geometry=geom,details=details,branches=bs))
    assert orders=={'r,uc','uc,r'}
    return dict(name=name,rows=records,row_count=len(records),frontier_orders=sorted(orders))

def main():
    p=argparse.ArgumentParser();p.add_argument('--mode',choices=['pilot','family','orientations'],required=True);p.add_argument('--name',default='fallback');a=p.parse_args()
    stamp=time.perf_counter()
    if a.mode=='pilot':out=known_controls();out['family']=enumerate_family('fallback')
    elif a.mode=='family':out=enumerate_family(a.name)
    else:out=orientations(a.name)
    out['total_elapsed_seconds']=time.perf_counter()-stamp
    path=H/(a.mode+'-'+a.name+'-v1.json')
    if path.exists():raise ValueError('preserve existing receipt')
    path.write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps(dict(mode=a.mode,name=a.name,path=str(path),seconds=out['total_elapsed_seconds'])))
if __name__=='__main__':
    try:main()
    except Exception:
        with(H/'graph-failures-v1.log').open('a')as f:f.write(traceback.format_exc()+'\n')
        raise
