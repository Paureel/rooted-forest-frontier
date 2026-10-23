"""One-shot exact arithmetic and Lean-log reviewer; no producer code imported."""
import hashlib,json,re,time
from fractions import Fraction
from pathlib import Path

BASE=Path(__file__).resolve().parents[1];OUT=BASE/'results';start=time.perf_counter()
data=json.loads((OUT/'thesis-complexity-arithmetic.json').read_text())
checks=[]
for row in data['transitions']:
    p,r=row['parent']
    parent=Fraction(1,2**p)+Fraction(r,2**(p+1))
    mass=sum((Fraction(1,2**(d+pp))+Fraction(rr,2**(d+pp+1)) for d,pp,rr in row['children']),Fraction())
    offset=(p-3)-(1+sum(pp-3 for d,pp,rr in row['children']))
    valid=0<=r<=p<=2 and all(0<=rr<=pp<=2 for d,pp,rr in row['children'])
    assert parent==Fraction(row['parent_mass'])
    assert mass==Fraction(row['child_mass'])
    assert parent-mass==Fraction(row['mass_slack'])
    assert offset==row['offset_slack']
    assert (mass<=parent)==row['mass_ok']
    assert valid==row['states_valid']
    checks.append({'id':row['id'],'parent':str(parent),'children':str(mass),'offset_slack':offset,'source_cap_valid':valid,'mass_passes':mass<=parent})
assert len(checks)==44

fresh=json.loads((OUT/'thesis-complexity-review-replay.json').read_text());trace_comparisons=[]
for key,name in [('nine','reachable'),('thirteen','three-credit')]:
    old=json.loads((OUT/f'thesis-complexity-{name}-trace.json').read_text())['trace']
    for i,record in enumerate(old):
        new=fresh[key][i]
        assert new['pair']==record['pair'] and new['case']==record['case']
        assert new['pendants']==record['pendants']
        assert new['F1']['protected']==record['protected_F1']
        assert new['F2']['protected']==record['protected_F2']
        for nb,ob in zip(new['branches'],record['branches'],strict=True):
            assert nb==ob,(key,i,nb,ob)
        trace_comparisons.append({'witness':key,'state':i,'pair_case_pendants_protection_branches_agree':True})

allowed={'propext','Classical.choice','Quot.sound'};axioms=[]
for suffix in ['credit','trace']:
    log=(OUT/f'thesis-complexity-review-{suffix}-lean.log').read_text()
    assert 'error:' not in log and 'sorryAx' not in log
    for line in log.splitlines():
        if 'axioms' not in line:continue
        name=line.split("'")[1]
        used=[] if 'does not depend' in line else [x.strip() for x in line.split('[')[1].split(']')[0].split(',')]
        assert set(used)<=allowed,(name,used)
        axioms.append({'declaration':name,'axioms':used})
assert len(axioms)==28
negative=(OUT/'thesis-complexity-review-negative-lean.log').read_text()
assert 'Tactic `decide` proved that the proposition' in negative and '9 ≤ 8' in negative and 'is false' in negative
positive=(OUT/'thesis-complexity-review-positive-lean.log').read_text()
assert "'trueTwin' does not depend on any axioms" in positive and "'affineTwin' does not depend on any axioms" in positive

hashes={}
for name in ['Credit.lean','Trace.lean']:
    original=BASE/'thesis_complexity'/name;copied=BASE/'thesis_complexity_review'/'lean-clean'/name
    assert original.read_bytes()==copied.read_bytes()
    txt=original.read_text()
    assert not re.search(r'(?m)^\s*axiom\b|\b(?:sorry|admit|native_decide)\b',txt)
    assert [s.strip() for s in txt.splitlines() if s.startswith('import ')]==['import Std']
    hashes[str(original.relative_to(BASE))]=hashlib.sha256(original.read_bytes()).hexdigest()
hashes['sources/baseline/whidden-thesis-2013.pdf']=hashlib.sha256((BASE/'sources/baseline/whidden-thesis-2013.pdf').read_bytes()).hexdigest()
result={'diagnostic_rows_recomputed':checks,'diagnostic_count':len(checks),'trace_comparisons':trace_comparisons,'kernel_axiom_audits':axioms,'kernel_axiom_audit_count':len(axioms),
        'false_proposition_diagnostic_confirmed':True,'true_twin_confirmed':True,'clean_sources_byte_identical':True,'hashes':hashes,
        'scope':'Data-only arithmetic recomputation plus clean producer Lean replay, not an independent universal formalization of source algorithm.',
        'elapsed_seconds':time.perf_counter()-start}
(OUT/'thesis-complexity-review-receipt-audit.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({'diagnostic_rows':len(checks),'axiom_audits':len(axioms),'false_plant_rejected':True,'true_twin_accepted':True,'elapsed_seconds':result['elapsed_seconds']}))
