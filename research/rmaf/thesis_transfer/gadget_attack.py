#!/usr/bin/env python3
"""One-task adversary for the pinned opposite-caterpillar transfer construction.
Shares only this audit's oracle.py; never imports another research solver.
"""
import argparse, hashlib, json, time
from pathlib import Path
from oracle import Tree, RHO, trees, profiles, common, normal, write_json
ALPHA, BETA = '@alpha', '@beta'
SPECIAL = {RHO, ALPHA, BETA}

def graft(a,b,mutate=False):
    return (BETA,(ALPHA,a)), ((BETA,(ALPHA,b)) if mutate else (ALPHA,(BETA,b)))

def erase(part):
    return normal(tuple(tuple(x for x in b if x not in SPECIAL) for b in part
                        if any(x not in SPECIAL for x in b)))

def scan(n, mutate=False):
    start=time.perf_counter(); ts=trees(tuple('abcdefghi'[:n]))
    ps=[profiles(Tree(t)) for t in ts]
    aa=[profiles(Tree(graft(t,t,mutate)[0],True)) for t in ts]
    bb=[profiles(Tree(graft(t,t,mutate)[1],True)) for t in ts]
    prep=time.perf_counter()-start
    checked=0; ordinary=0; pairs=0
    for i,a in enumerate(ts):
        for j in range(i,len(ts)):
            old=common(ps[i],ps[j]); new=common(aa[i],bb[j])
            k=min(map(len,old)); kg=min(map(len,new))
            assert kg == k+1, {'kind':'optimum','a':a,'b':ts[j],'K':k,'Kgadget':kg}
            oldset=set(old); newset=set(new)
            for p in old:
                assert normal(p+(tuple(sorted(SPECIAL)),)) in newset
                ordinary+=1
            for p in new:
                assert erase(p) in oldset, ('erase',a,ts[j],p)
                assert len(erase(p)) < len(p), ('no lost component',a,ts[j],p)
                checked+=1
            pairs+=1
    return {'n':n,'trees':len(ts),'unordered_pairs':pairs,
            'upper_maps_checked':ordinary,'lower_maps_checked':checked,
            'profile_seconds':prep,'seconds':time.perf_counter()-start}

if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('--n',type=int,nargs='+',default=[1,2,3]);
    ap.add_argument('--mutate',action='store_true');ap.add_argument('--out',required=True);args=ap.parse_args()
    data={'scope':'finite attack only, not universal proof','mutated':args.mutate,
          'code_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'scans':[]}
    for n in args.n:
        data['scans'].append(scan(n,args.mutate));write_json(args.out,data)
        print(json.dumps(data['scans'][-1]),flush=True)
