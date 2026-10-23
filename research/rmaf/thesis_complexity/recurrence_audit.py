#!/usr/bin/env python3
"""One-shot thesis credit-recurrence audit; not a rooted-tree reachability verifier.
Toolkit capability index checked: no branching-credit/reachability package applies.
"""
from fractions import Fraction as F
import json, hashlib, time
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
HERE=Path(__file__).resolve().parent

def w(p,q): return F(2+q, 2**(p+1))
def audit(parent,children):
    p,q=parent
    mass=sum((w(pc,qc)/2**d for d,pc,qc in children),F(0))
    return {'parent_mass':str(w(p,q)), 'child_mass':str(mass),
            'mass_slack':str(w(p,q)-mass), 'mass_ok':mass<=w(p,q),
            'offset_slack':p-3-(1+sum(pc-3 for _,pc,_ in children)),
            'states_valid':q<=p<=2 and all(qc<=pc<=2 for _,pc,qc in children)}
def main():
    start=time.monotonic()
    raw=(HERE/'controls-frozen.json').read_bytes(); controls=json.loads(raw)
    checks=[]
    for c in controls['cases']:
        a=audit(c['parent'],c['children'])
        assert a['child_mass']==c['expected_mass'], (c,a)
        assert a['mass_ok']==c['expected_ok'], (c,a)
        checks.append({'id':c['id'],'caught_or_recovered':True,**a})
    for c in controls['state_controls']:
        actual=0<=c['q']<=c['p']<=2
        assert actual==c['expected_ok'],c
        checks.append({'id':c['id'],'caught_or_recovered':True,'valid':actual})
    result={'kind':'exact-rational-arithmetic-only','controls_sha256':hashlib.sha256(raw).hexdigest(),
            'control_results':checks,'control_count':len(checks),'transitions':[]}
    def row(name,loc,p,q,ch,status='source claimed'):
        result['transitions'].append({'id':name,'source_printed_page':loc,'parent':[p,q],
                                      'children':ch,'reachability':status,**audit((p,q),ch)})
    row('G1-simple',117,0,0,[(1,0,0),(1,0,0)])
    row('G1-A2BC',118,0,0,[(1,0,0),(2,0,0),(1,1,0)])
    row('G1-A3BC',118,0,0,[(1,0,0),(3,0,0),(1,1,1)])
    for q in (0,1):
        row(f'G2-one-q{q}',118,1,q,[(1,0,0)])
        row(f'G2-BCY-q{q}',119,1,q,[(2,0,0),(2,0,0)])
        row(f'G2-two-q{q}',119,1,q,[(1,1,q),(1,1,q)])
        row(f'G2-A2BC-q{q}',119,1,q,[(1,1,q),(2,1,q),(1,2,q)])
        row(f'G2-A3BC-q{q}',119,1,q,[(1,1,q),(3,1,q),(1,2,q+1)])
        row(f'G3-one-q{q}',120,1,q,[(1,0,0)])
    row('G3-reset-after-A3',120,1,1,[(1,0,0),(2,0,0)])
    row('G3-after-A2-A2',120,1,0,[(1,1,0),(2,0,0)])
    row('G3-after-A2-A3',120,1,0,[(1,1,1),(3,0,0)])
    for q in (0,1,2): row(f'G3-double-protected-q{q}',121,2,q,[(2,0,0)])
    for q in (0,1):
        row(f'G4-one-q{q}',122,1,q,[(1,0,0)])
        row(f'G4-BCY-q{q}',122,1,q,[(2,0,0),(2,0,0)])
        row(f'G4-two-q{q}',122,1,q,[(1,1,q),(1,1,q)])
        row(f'G4.1-A2BC-q{q}',123,1,q,[(1,1,q),(2,1,q),(1,2,q)])
        row(f'G4.1-A3BC-exception-q{q}',123,1,q,[(1,1,q),(3,0,0),(1,2,q+1)],'reachability of q=0 requires examination')
        row(f'G4-2B-reset-q{q}',123,1,q,[(2,0,0)])
        row(f'G5-one-q{q}',125,1,q,[(1,0,0)])
    row('G5-Q-nonempty-reset',125,1,1,[(1,0,0),(2,0,0)])
    row('G5-Q-empty-forbidden-two',125,1,0,[(1,0,0),(2,0,0)],'source explicitly excludes; NOT an allowed transition')
    for q in (0,1,2):
        row(f'G5-double-protected-q{q}',126,2,q,[(2,0,0)])
    # G4.2 has outer P={a}, local P={a_prime}; union lift of G2.
    for q in (0,1):
        row(f'G4.2-union-A2BC-q{q}',123,2,q,[(1,2,q),(2,2,q),(1,3,q)],'unrestricted union arithmetic; requires reachable cardinality check')
        row(f'G4.2-union-A3BC-q{q}',123,2,q,[(1,2,q),(3,2,q),(1,3,q+1)],'unrestricted union arithmetic; requires reachable cardinality check')
    result['elapsed_seconds']=time.monotonic()-start
    result['mass_failures']=[r['id'] for r in result['transitions'] if not r['mass_ok']]
    result['invalid_state_rows']=[r['id'] for r in result['transitions'] if not r['states_valid']]
    (ROOT/'results/thesis-complexity-arithmetic.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:result[k] for k in ['control_count','mass_failures','invalid_state_rows','elapsed_seconds']},sort_keys=True))
if __name__=='__main__':main()
