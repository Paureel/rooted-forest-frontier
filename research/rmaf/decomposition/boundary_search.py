"""One-shot screened two-state cluster identity; structural proof remains open."""
import itertools,json,time
from search import freeze,labels,restrict,clusters,collapse,optimum,trees,controls,atomic,ROOT
controls()
t0=time.monotonic();tested=0;killers=[];counts={}
for a,b in itertools.combinations_with_replacement(trees(tuple('abcde')),2):
    for c in (clusters(a)&clusters(b))-{labels(a)}:
        innera,innerb=restrict(a,c),restrict(b,c)
        ia=optimum(innera,innerb)[0]
        iaug=optimum(freeze(('rho',innera)),freeze(('rho',innerb)))[0]
        rest=labels(a)-c
        ob=optimum(restrict(a,rest),restrict(b,rest))[0]
        ocoll=optimum(collapse(a,c),collapse(b,c))[0]
        k,f=optimum(a,b)
        predicted=min(ia+ob,iaug+ocoll-1)
        tested+=1
        state=f'{iaug-ia},{ocoll-ob}';counts[state]=counts.get(state,0)+1
        if predicted!=k:
            killers.append({'a':a,'b':b,'cluster':sorted(c),'k':k,'predicted':predicted,'A':ia,'A_aug':iaug,'B':ob,'B_collapsed':ocoll})
            break
    if killers:break
r={'status':'refuted' if killers else 'screened-open','tested':tested,'state_counts':counts,'killers':killers,'seconds':time.monotonic()-t0,'convention':'ordinary unaugmented rooted MAF; marker rho adjoined only inside local signature'}
atomic(ROOT/'research/rmaf/results/decomposition-boundary.json',r)
print(json.dumps(r))
# Pin killer's exact boundary signature, after generic screen only.
a=freeze(['a',['b',['c',['d','e']]]]);b=freeze(['a',['e',['d',['b','c']]]]);c=frozenset('bcde')
print(json.dumps({'pinned_killer_signature':{'A':optimum(restrict(a,c),restrict(b,c))[0],'A_aug':optimum(freeze(('rho',restrict(a,c))),freeze(('rho',restrict(b,c))))[0],'B':optimum(restrict(a,labels(a)-c),restrict(b,labels(b)-c))[0],'B_collapsed':optimum(collapse(a,c),collapse(b,c))[0]}}))
