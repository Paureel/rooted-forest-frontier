"""Fresh exact source-use-site arithmetic; candidate implementations not imported."""
from fractions import Fraction as F
from pathlib import Path
import json
BASE=Path(__file__).resolve().parent;ROOT=BASE.parents[2]
def orig(p,q):return F(2)**(-p)+q*F(2)**(-p-1)
def mul(p,q):return F(1,2)**(p-q)*F(3,4)**q
rows=[]
def row(name,page,p,q,cs,w=orig,scope='conditional source use site'):
    mass=sum(F(2)**(-d)*w(a,b) for d,a,b in cs);bound=w(p,q)
    off=1+sum(a-3 for _,a,_ in cs);cap=p-3
    r=dict(id=name,printed_page=page,parent=[p,q],children=cs,lhs_mass=str(mass),rhs_mass=str(bound),mass_residual=str(mass-bound),lhs_offset=off,rhs_offset=cap,offset_residual=off-cap,passes=mass<=bound and off<=cap,scope=scope)
    rows.append(r);return r
row('generic-two',117,0,0,[(1,0,0),(1,0,0)])
row('G1-A2',118,0,0,[(1,0,0),(2,0,0),(1,1,0)])
row('G1-A3',118,0,0,[(1,0,0),(3,0,0),(1,1,1)])
for q in [0,1]:
 for group,page in [('G2',119),('G4',122)]:
    row(group+'-unary-'+str(q),page,1,q,[(1,0,0)])
    row(group+'-BCY-'+str(q),page,1,q,[(2,0,0),(2,0,0)])
    row(group+'-binary-retain-'+str(q),page,1,q,[(1,1,q),(1,1,q)])
 row('G2-A2-'+str(q),119,1,q,[(1,1,q),(2,1,q),(1,2,q)])
 row('G2-A3-'+str(q),119,1,q,[(1,1,q),(3,1,q),(1,2,q+1)])
 for group,page in [('G3',120),('G5',125)]:row(group+'-unary-'+str(q),page,1,q,[(1,0,0)])
for group,page in [('G3',120),('G5',125)]:row(group+'-soft-two-reset',page,1,1,[(1,0,0),(2,0,0)])
row('G3-hard-A2',120,1,0,[(1,1,0),(2,0,0)])
row('G3-hard-A3',120,1,0,[(1,1,1),(3,0,0)])
for q in range(3):
 row('G3-two-credits-'+str(q),121,2,q,[(2,0,0)])
 row('G5-two-credits-'+str(q),126,2,q,[(2,0,0)])
row('G4.1-A3-hard-exception',123,1,0,[(1,1,0),(3,0,0),(1,2,1)])
row('G4.1-A3-soft-original',123,1,1,[(1,1,1),(3,0,0),(1,2,2)])
assert [r['id'] for r in rows if not r['passes']]==['G4.1-A3-hard-exception']
# Rebuild the advertised 37 multiplicative schemas directly from contracts.
mult=[]
def mrow(*a):r=row(*a,w=mul,scope='finite abstract row; structural coverage unproved');mult.append(r)
for r in range(3):
 for t in range(r+1):
    mrow('lift-A2-'+str((r,t)),123,r,t,[(1,r,t),(2,r,t),(1,r+1,t)])
    mrow('lift-A3-'+str((r,t)),123,r,t,[(1,r,t),(3,r,t),(1,r+1,t+1)])
for r in range(2):
 for t in range(r+1):
    specs=[(r+1,t,[(1,r,t)]),(r+1,t+1,[(1,r,t)]),(r+2,t,[(2,r,t)]),(r+2,t+1,[(2,r,t)]),(r+1,t+1,[(1,r,t),(2,r,t)]),(r+1,t,[(1,r+1,t),(2,r,t)]),(r+1,t,[(1,r+1,t+1),(3,r,t)])]
    for i,(p,q,cs) in enumerate(specs):mrow('discharge-'+str((r,t,i)),123,p,q,cs)
for q in [0,1]:
 for s in [3,4]:mrow('G4.1-mul-'+str((q,s)),123,1,q,[(1,1,q),(s,0,0),(1,2,q+1)])
assert len(mult)==37 and sum(r['passes'] for r in mult)==35
# Hostile abstract table extensions, explicitly not source reachability assertions.
for name,p,q,cs in [('three-credit-retain',3,2,[(1,3,2),(1,3,2)]),('three-hard-2B',3,0,[(2,0,0)]),('three-one-soft-2B',3,1,[(2,0,0)])]:
    assert not row(name,123,p,q,cs,w=mul,scope='hypothetical abstract transition; no legal source history established')['passes']
row('literal-additive-two-soft-gap',123,2,2,[(1,1,1),(2,1,1)],scope='abstract lifted discharge; reachability unestablished')
row('reachable-three-credit-discharge',123,3,2,[(2,1,0)],scope='specific thirteen-leaf trace under displayed Q assignment')
# Exact full use-site compositions, all invocation constants retained.
compositions=[]
for X in [F(128)*2**k for k in range(8)]:
    A=X/4-2;B=X/8-3;target=X/2-2
    for C,label,slack in [(X/8+2,'weak-C',F(0)),(X/8-1,'strong-C',F(3))]:
        lhs=1+A+B+C;assert target-lhs==slack
        compositions.append(dict(X=str(X),kind=label,A=str(A),B=str(B),C=str(C),lhs=str(lhs),rhs=str(target),slack=str(slack)))
    # A bound cannot be replaced by generic induction at K-1.
    genericA=X/2-3;lhs=1+genericA+B+(X/8+2)
    assert lhs>target
# Every integer negative budget at k=-4..-1 and all ten states.
neg=[]
for k in range(-4,0):
 for p in range(4):
  for q in range(p+1):
    cap=128*F(2)**k*mul(p,q)+p-3;assert cap>=1;neg.append([k,p,q,str(cap)])
negative_fire={'failing_step':'unrestricted negative-budget formula','scope':'abstract arithmetic misuse; actual negative invocation is directly terminal','K':-10,'p':0,'q':0,'lhs':'1','rhs':str(128*F(2)**-10-3),'residual':str(1-(128*F(2)**-10-3))}
# Reachable thirteen-leaf C,A path can start at initial budget 2; J budget=0;
# its legal four-edge B child is called with actual budget -4 and returns 1.
actual_negative={'source':'thirteen-leaf replay C,A,B','initial_budget':2,'at_J':0,'B_cost':4,'child_budget':-4,'actual_count':1,'original_p117_base_covers':False,'extended_128_empty_cap':'5','scope':'reachable full-call-tree trace, failure precedes success'}
out=dict(rows=rows,multiplicative_rows=len(mult),multiplicative_passing=sum(r['passes'] for r in mult),compositions=compositions,negative_boundary=neg,negative_formula_fire=negative_fire,actual_negative_budget=actual_negative)
(ROOT/'results/thesis-runtime-repair-fresh-review-interface.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({'source_and_abstract_rows':len(rows),'multiplicative_pass':sum(r['passes'] for r in mult),'multiplicative_total':len(mult),'compositions':len(compositions),'negative_boundary_states':len(neg),'actual_reachable_negative_budget':-4}))
