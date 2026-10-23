"""One-shot independently constructed common-chain family, no general proof."""
import argparse,itertools,json,time
from search import freeze,labels,restrict,trees,optimum,valid,chains,controls,atomic,ROOT
def graft(t,core):
    if t=='@':return core
    if isinstance(t,str):return t
    return freeze((graft(t[0],core),graft(t[1],core)))
def family(spares):
    out=set()
    for n in range(len(spares)+1):
        for below in itertools.combinations(spares,n):
            above=tuple(x for x in spares if x not in below)
            bases=trees(below) if below else (None,)
            for base in bases:
                core=freeze(('a','b')) if base is None else freeze((freeze((base,'a')),'b'))
                core=freeze((core,'c'))
                for outer in trees(tuple(sorted(above+('@',)))):out.add(graft(outer,core))
    assert all(('a','b','c') in chains(t) for t in out)
    return sorted(out,key=repr)
def main():
    p=argparse.ArgumentParser();p.add_argument('--limit',type=int,default=0);p.add_argument('--spare',default='defg');args=p.parse_args();controls()
    t0=time.monotonic();ts=family(tuple(args.spare));tested=0;killer=None;maxk=0
    print('family trees',len(ts),flush=True)
    for a,b in itertools.combinations_with_replacement(ts,2):
        k,f=optimum(a,b);keep=labels(a)-{'c'};kr,fr=optimum(restrict(a,keep),restrict(b,keep));tested+=1;maxk=max(maxk,k)
        if k!=kr:
            killer={'a':a,'b':b,'chain':['a','b','c'],'deleted':'c','k':k,'forest':[sorted(s) for s in f],'reduced_k':kr,'reduced_forest':[sorted(s) for s in fr],'reduced_a':restrict(a,keep),'reduced_b':restrict(b,keep),'mechanism':'A common chain can be shattered into singletons; deleting a chain leaf removes a unit of optimum cost.'};print('KILL',json.dumps(killer),flush=True);break
        if args.limit and tested>=args.limit:break
    r={'status':'refuted' if killer else 'screened-open','trees':len(ts),'n':len(args.spare)+3,'pairs_checked':tested,'max_k_seen':maxk,'killer':killer,'seconds':time.monotonic()-t0}
    atomic(ROOT/f'research/rmaf/results/decomposition-chain-n{len(args.spare)+3}-{args.limit or "full"}.json',r);print(json.dumps(r),flush=True)

if __name__=='__main__':main()
