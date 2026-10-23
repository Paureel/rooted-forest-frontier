"""One-shot finite exact synthesis of chain-state penalties, not a theorem."""
import functools,itertools,json,time
from search import freeze,labels,restrict,trees,optimum,partitions,valid,chains,controls,atomic,ROOT
import argparse,random
p=argparse.ArgumentParser();p.add_argument('--family',action='store_true');p.add_argument('--random-eight',type=int,default=0);args=p.parse_args()
controls();t0=time.monotonic()
@functools.cache
def features(a,b,x,y):
    out=[None,None,None]
    for p in partitions(tuple(sorted(labels(a)))):
        if not valid(a,b,p):continue
        if any(x in s and y in s for s in p):category=0
        elif frozenset([x]) in p and frozenset([y]) in p:category=1
        else:category=2
        if out[category] is None or len(p)<out[category]:out[category]=len(p)
    return tuple(out)
def row(a,b,chain):
    x,y,z=chain;keep=labels(a)-{z}
    return {'a':a,'b':b,'chain':chain,'k':optimum(a,b)[0],'features':features(restrict(a,keep),restrict(b,keep),x,y)}
rows=[]
for a,b in itertools.combinations_with_replacement(trees(tuple('abcde')),2):
    for chain in chains(a)&chains(b):rows.append(row(a,b,chain))
w=json.loads((ROOT/'research/rmaf/results/decomposition-chain-n7-full.json').read_text())['killer']
pinned_killer_row=row(freeze(w['a']),freeze(w['b']),tuple(w['chain']));rows.append(pinned_killer_row)
if args.family or args.random_eight:
    from chain_family import family
    if args.family:
        for a,b in itertools.combinations_with_replacement(family(tuple('defg')),2):rows.append(row(a,b,('a','b','c')))
    if args.random_eight:
        rng=random.Random(20261014);ts=family(tuple('defgh'))
        for _ in range(args.random_eight):rows.append(row(rng.choice(ts),rng.choice(ts),('a','b','c')))
survivors=[];rejected=[]
for penalties in itertools.product((0,1,2,None),repeat=3):
    killer=None
    for i,r in enumerate(rows):
        predictions=[v+p for v,p in zip(r['features'],penalties) if v is not None and p is not None]
        prediction=min(predictions) if predictions else None
        if prediction!=r['k']:
            killer={'index':i,'prediction':prediction,'actual':r['k'],'features':r['features'],'chain':r['chain']};break
    if killer is None:survivors.append(penalties)
    else:rejected.append({'penalties':penalties,'killer':killer})
r={'status':'screened-open' if survivors else 'no-survivors','rows':len(rows),'candidate_tables':64,'survivors':survivors,'rejected':rejected,'killer_features':pinned_killer_row,'seconds':time.monotonic()-t0,'category_order':['a,b together','a,b singleton','mixed']}
atomic(ROOT/f'research/rmaf/results/decomposition-penalty-synthesis-family{int(args.family)}-eight{args.random_eight}.json',r)
print(json.dumps({k:v for k,v in r.items() if k!='rejected'}))
