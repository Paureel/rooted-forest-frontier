"""Problem-specific independent partition/span oracle; not a certified general toolkit.
No code reused from other route. Exact integers and canonical rooted topologies only.
Run controls before any candidate instances; retain every exact killer in results.
"""
from __future__ import annotations
import argparse, functools, itertools, json, pathlib, time
ROOT=pathlib.Path(__file__).resolve().parents[3]
HERE=pathlib.Path(__file__).resolve().parent
RESULT=ROOT/'research/rmaf/results/decomposition-search.json'
PROGRESS=ROOT/'research/rmaf/progress/decomposition.json'
def freeze(t):
    if isinstance(t,str): return t
    a,b=map(freeze,t)
    return tuple(sorted((a,b),key=repr))
@functools.cache
def labels(t):
    return frozenset([t]) if isinstance(t,str) else labels(t[0])|labels(t[1])
@functools.cache
def restrict(t, block):
    if isinstance(t,str): return t if t in block else None
    a,b=restrict(t[0],block),restrict(t[1],block)
    if a is None:return b
    if b is None:return a
    return freeze((a,b))
@functools.cache
def leafpaths(t):
    out={}
    def walk(s,p):
        if isinstance(s,str):out[s]=p
        else:
            walk(s[0],p+(0,));walk(s[1],p+(1,))
    walk(t,())
    return out
@functools.cache
def span(t,block):
    paths=[leafpaths(t)[x] for x in block]
    common=0
    while all(len(p)>common for p in paths) and len({p[common] for p in paths})==1:common+=1
    return frozenset(p[:i] for p in paths for i in range(common,len(p)+1))
def valid(a,b,forest):
    forest=tuple(frozenset(s) for s in forest)
    if not forest or any(not s for s in forest):return False
    seen=frozenset()
    for s in forest:
        if seen&s:return False
        seen|=s
    if seen!=labels(a) or seen!=labels(b):return False
    sa,sb=[],[]
    for s in forest:
        if restrict(a,s)!=restrict(b,s):return False
        x,y=span(a,s),span(b,s)
        if any(x&p for p in sa) or any(y&p for p in sb):return False
        sa.append(x);sb.append(y)
    return True
@functools.cache
def partitions(xs):
    if not xs:return ((),)
    first,*tail=xs
    out=[]
    for p in partitions(tuple(tail)):
        out.append((frozenset([first]),)+p)
        for i in range(len(p)):
            out.append(p[:i]+(p[i]|{first},)+p[i+1:])
    return tuple(sorted(out,key=len))
@functools.cache
def optimum(a,b):
    if repr(a)>repr(b):a,b=b,a
    for p in partitions(tuple(sorted(labels(a)))):
        if valid(a,b,p):return len(p),p
    raise AssertionError('singleton partition must succeed')
@functools.cache
def trees(xs):
    if len(xs)==1:return (xs[0],)
    out=[]
    first=xs[0]
    for z in range(1,len(xs)):
        for left in itertools.combinations(xs,z):
            if first not in left:continue
            right=tuple(x for x in xs if x not in left)
            for a in trees(left):
                for b in trees(right):out.append(freeze((a,b)))
    return tuple(out)
@functools.cache
def clusters(t):
    if isinstance(t,str):return frozenset()
    return frozenset([labels(t)])|clusters(t[0])|clusters(t[1])
def collapse(t,c):
    if labels(t)==c:return '@'
    if isinstance(t,str):return t
    return freeze(tuple(collapse(s,c) for s in t))
def chains(t):
    paths=leafpaths(t)
    out=set()
    for x,y,z in itertools.permutations(sorted(paths),3):
        px,py,pz=paths[x][:-1],paths[y][:-1],paths[z][:-1]
        if (px==py or (len(px)==len(py)+1 and px[:-1]==py)) and len(py)==len(pz)+1 and py[:-1]==pz:
            out.add((x,y,z))
    return out

def clean_json(value):
    if isinstance(value,(set,frozenset)):return sorted(value)
    raise TypeError(type(value).__name__)
def atomic(path,obj):
    tmp=path.with_suffix('.tmp');tmp.write_text(json.dumps(obj,indent=2,default=clean_json)+'\n');tmp.replace(path)
def progress(result,status='active'):
    witnesses=result['witnesses']
    claims=[{'id':q,'label':label,'status':'refuted' if q in witnesses else 'open','detail':witnesses[q]['mechanism'] if q in witnesses else 'Finite search only; universal statement remains open.'} for q,label in [('common-cluster-naive','Cluster additivity'),('chain-3-to-2','Shorten chain to 2')]]
    data={'id':'decomposition','title':'Decomposition','status':status,'summary':f"{result['pairs_checked']} exact pairs; {len(witnesses)} failed formulations.",'metrics':{'controls':result['controls'],'pairs_checked':result['pairs_checked'],'candidate_instances':result['candidate_instances'],'counterexamples':len(witnesses)},'claims':claims,'lemmas':[{'id':'boundary-state','label':'Boundary attachment lemma','status':'open','detail':'Determine the optimum from detached and extendible attachment states; naive cluster sum can lose root compatibility.','depends_on':[]}],'artifacts':['research/rmaf/decomposition/journal.md','research/rmaf/decomposition/search.py',str(RESULT.relative_to(ROOT))],'sources':[{'title':'Split-or-decompose v2','url':'https://arxiv.org/abs/2409.18634','locator':'Section2; Section4; Section6 Case3.1'},{'title':'Cyclic generators kernel','url':'https://arxiv.org/abs/2202.09904','locator':'Accepted manuscript Section5–6'}]}
    if witnesses:
        w=next(iter(witnesses.values()));data['example']={'tree_a':w['a'],'tree_b':w['b'],'forest':w['forest'],'k':w['k'],'caption':w['mechanism']}
    atomic(PROGRESS,data);atomic(RESULT,result)
def controls():
    frozen=json.loads((HERE/'controls.json').read_text())
    recovered=0;rejections=0
    for c in frozen['controls']:
        a,b=freeze(c['a']),freeze(c['b'])
        actual=optimum(a,b)[0]
        assert actual==c['k'],(c['id'],actual,c['k']);recovered+=1
        if 'valid' in c:assert valid(a,b,c['valid']);recovered+=1
        if 'invalid' in c:assert not valid(a,b,c['invalid']);rejections+=1
    # Deliberately false expected optimum caught, clean twin accepted.
    caught=False
    c=frozen['controls'][1]
    try:assert optimum(freeze(c['a']),freeze(c['b']))[0]==1
    except AssertionError:caught=True
    assert caught
    return {'constructed_optima':4,'positive_forests':2,'invalid_forests_caught':3,'false_optimum_caught':1,'checks':recovered+rejections+1}
def main():
    global RESULT
    p=argparse.ArgumentParser();p.add_argument('--limit',type=int,default=0);p.add_argument('--labels',default='abcde');p.add_argument('--candidate-only',action='store_true');args=p.parse_args()
    RESULT=ROOT/f'research/rmaf/results/decomposition-n{len(args.labels)}-{args.limit or "full"}.json'
    start=time.monotonic();battery=controls()
    result={'status':'running','convention':'ordinary unaugmented rooted MAF; vertex-disjoint embeddings','controls':battery['checks'],'control_details':battery,'pairs_checked':0,'candidate_instances':{'common-cluster-naive':0,'chain-3-to-2':0},'witnesses':{},'n':len(args.labels)}
    progress(result)
    ts=trees(tuple(args.labels))
    print(f"controls PASS {battery['checks']}; rooted trees {len(ts)}",flush=True)
    for a,b in itertools.combinations_with_replacement(ts,2):
        result['pairs_checked']+=1
        cs=(clusters(a)&clusters(b))-{labels(a)};chs=chains(a)&chains(b)
        if args.candidate_only and not cs and not chs:
            if result['pairs_checked']%1000==0:progress(result)
            if args.limit and result['pairs_checked']>=args.limit:break
            continue
        k,f=optimum(a,b)
        for c in clusters(a)&clusters(b):
            if c==labels(a):continue
            result['candidate_instances']['common-cluster-naive']+=1
            inside=optimum(restrict(a,c),restrict(b,c))[0]
            outside=optimum(collapse(a,c),collapse(b,c))[0]
            predicted=inside+outside-1
            if k!=predicted and 'common-cluster-naive' not in result['witnesses']:
                result['witnesses']['common-cluster-naive']={'a':a,'b':b,'cluster':c,'k':k,'forest':f,'inside_k':inside,'collapsed_outside_k':outside,'predicted_k':predicted,'mechanism':'A locally optimal cluster component may not be attachable to the outside component at the root.'}
                print('KILL common-cluster-naive',json.dumps(result['witnesses']['common-cluster-naive'],default=clean_json),flush=True)
        for chain in chains(a)&chains(b):
            result['candidate_instances']['chain-3-to-2']+=1
            reduced=labels(a)-{chain[2]};kr,fr=optimum(restrict(a,reduced),restrict(b,reduced))
            if k!=kr and 'chain-3-to-2' not in result['witnesses']:
                result['witnesses']['chain-3-to-2']={'a':a,'b':b,'chain':chain,'deleted':chain[2],'k':k,'forest':f,'reduced_a':restrict(a,reduced),'reduced_b':restrict(b,reduced),'reduced_k':kr,'reduced_forest':fr,'mechanism':'Deleting the top chain leaf removes an attachment constraint and falsely reduces the optimum.'}
                print('KILL chain-3-to-2',json.dumps(result['witnesses']['chain-3-to-2'],default=clean_json),flush=True)
        if result['pairs_checked']%100==0:progress(result)
        if args.limit and result['pairs_checked']>=args.limit:break
    result['seconds']=round(time.monotonic()-start,6);result['status']='complete';progress(result,'review')
    print(json.dumps({k:v for k,v in result.items() if k not in ['witnesses','candidate_instances']}),flush=True)
    print(json.dumps(result['candidate_instances']),flush=True)
if __name__=='__main__':main()
