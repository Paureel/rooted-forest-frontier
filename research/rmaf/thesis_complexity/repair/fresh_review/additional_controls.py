"""Additional explicitly post-candidate structural and boundary controls."""
from fresh_checker import *
extra=[]
def put(id,observed,expected):
    assert observed==expected,(id,observed,expected)
    extra.append(dict(id=id,observed=observed,expected=expected,passed=True,scope='post-candidate targeted control'))
# A non-rho component root with a protected child forbids cutting its sibling.
comp=N(ch=[N('a'),N('b',protected=True)])
try:cut_batch([comp],['a'])
except AssertionError as exc:put('root-sibling-exclusion',str(exc),'protected root sibling')
else:raise AssertionError('root-sibling restriction missed')
# Remove the retained-sibling condition on a copy: both descendant cuts erase b.
st=set_prot(State(parse('(a,(p,q))'),[parse('(a,(p,q))')]),['a'],['a','p,q'])
after=cut_batch(st.f,['p','q']);by,pa,_,_=index(after)
put('arbitrary-double-cut-erases-sibling',sibling(by['a'],pa) is None,True)
after_single=cut_batch(st.f,['p']);by,pa,_,_=index(after_single)
put('single-cut-retains-protected-sibling',sibling(by['a'],pa).protected,True)
# Replay initial trees and full legal branch history at actual budget 2.
r=json.loads((ROOT/'results/thesis-complexity-three-credit-trace.json').read_text());st=State(parse(r['trace'][0]['F1']),[parse(r['trace'][0]['F2'])]);k=2
for pair,name in [(('a','c'),'C'),(('d','a'),'A')]:
    inf=classify(st,pair);br=next(b for b in inf['branches'] if b['name']==name);assert br['legal'];k-=len(br['cuts']);st=apply(st,br)
inf=classify(st,('x','y'));br=next(b for b in inf['branches'] if b['name']=='B');assert br['legal'];k-=len(br['cuts'])
put('actual-budget-after-reachable-B',k,-4);put('negative-before-normalization-count',1 if k<0 else None,1)
# Pin the precise arbitrary-induction misuse with saturated abstract allowances.
X=F(128);A_generic=X/2-3;A_needed=X/4-2;B=X/8-3;C=X/8+2;lhs=1+A_generic+B+C;rhs=X/2-2
put('generic-A-does-not-imply-credited-A',A_generic>A_needed,True)
fire=dict(failing_step='replace credited A allowance by empty-credit induction at same child budget',scope='abstract allowance countermodel; actual A runtime not asserted',instance={'X':'128','A_generic':str(A_generic),'A_needed':str(A_needed),'B':str(B),'C':str(C)},lhs=str(lhs),rhs=str(rhs),residual=str(lhs-rhs))
assert lhs-rhs==31
# Compare every exposed protection and legal-branch snapshot after replaying from initial trees.
for filename in ['thesis-complexity-reachable-trace.json','thesis-complexity-three-credit-trace.json']:
    fixture=json.loads((ROOT/'results'/filename).read_text())
    st=State(parse(fixture['trace'][0]['F1']),[parse(fixture['trace'][0]['F2'])])
    for i,r in enumerate(fixture['trace']):
        (b1,_,_,_),(b2,_,_,_)=st.idx()
        observed=[sorted(k for k,n in b1.items() if n.protected),sorted(k for k,n in b2.items() if n.protected)]
        put(filename+'-protection-'+str(i),observed,[sorted(r['protected_F1']),sorted(r['protected_F2'])])
        inf=classify(st,r['pair'])
        put(filename+'-branches-'+str(i),[(b['name'],b['cuts'],b['legal']) for b in inf['branches']],[(b['name'],b['cuts'],b['legal']) for b in r['branches']])
        if 'chosen_branch' in r:st=apply(st,next(b for b in inf['branches'] if b['name']==r['chosen_branch']))
(ROOT/'results/thesis-runtime-repair-fresh-review-additional.json').write_text(json.dumps({'controls':extra,'abstract_import_fire':fire},indent=2)+'\n');print('additional controls',len(extra),'abstract import residual',lhs-rhs)
