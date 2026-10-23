"""Freeze COPY mutations and compare charges/masses to independent graph truth."""
import copy,itertools,json,sys
from fractions import Fraction
from pathlib import Path
from independent_graph import Graph,exact_forest,valid_forest
from review_paid import cp,refines,cli
HERE=Path(__file__).resolve().parent; CAMPAIGN=HERE.parents[1]; OUT=CAMPAIGN/'results'
def write(path,x): path.write_text(json.dumps(x,indent=2)+'\n')
actual=json.loads((HERE/'paid-five-witness-stdout.json').read_text())
witness=[[0,1,4],[2],[3]]
bad=copy.deepcopy(actual)
bad['cover']['states']=[s for s in bad['cover']['states'] if not refines(witness,s['partition'])]
assert bad['cover']['states'] and not any(refines(witness,s['partition']) for s in bad['cover']['states'])
write(HERE/'COPY-paid-omitted-necessary.json',bad)
charge=copy.deepcopy(actual)
necessary=next(s for s in charge['cover']['states'] if refines(witness,s['partition']))
necessary['charge']-=1
assert necessary['charge'] != len(necessary['partition'])-1
write(HERE/'COPY-paid-false-charge.json',charge)
rec=copy.deepcopy(actual)
rec['cover']['paid_vector'][-1]+=1
recomputed=sum((Fraction(100,231)**q for q in rec['cover']['paid_vector']),Fraction())
assert str(recomputed)!=rec['cover']['exact_mass']
write(HERE/'COPY-paid-false-recurrence.json',rec)
write(OUT/'algorithm-review-copy-bugreports.json',{'reports':[
 {'failing_step':'B3 coverage after necessary entries omitted','copy':'COPY-paid-omitted-necessary.json','nonempty_remaining':len(bad['cover']['states']),'exact_lost_parent_q':2,'exact_best_remaining_total':3,'lost_witness':witness,'caught':True},
 {'failing_step':'B3 claimed cut payment','copy':'COPY-paid-false-charge.json','claimed':necessary['charge'],'actual':len(necessary['partition'])-1,'residual':-1,'caught':True},
 {'failing_step':'B3 recurrence term/mass consistency','copy':'COPY-paid-false-recurrence.json','claimed_mass':rec['cover']['exact_mass'],'mass_from_mutated_terms':str(recomputed),'difference':str(recomputed-Fraction(rec['cover']['exact_mass'])),'caught':True}],'clean_twin':'paid-five-witness-stdout.json'})

frozen=json.loads((CAMPAIGN/'algorithm/x0/frozen-controls-v1.json').read_text())
rows=[]
for name,case in frozen['sources']['branching-recurrences.json']['recurrences'].items():
    v=case['vector']; mass=lambda c:sum((c**(-q) for q in v),Fraction())
    value=mass(Fraction(231,100)); bracket=case['exact_root_bracket']
    lo,hi=Fraction(bracket['lower']),Fraction(bracket['upper'])
    assert str(value)==case['mass_at_231_100'] and (value<=1)==case['certificate'] and mass(lo)>1 and mass(hi)<=1
    rows.append({'name':name,'vector':v,'mass':str(value),'certificate':value<=1,'lower_mass':str(mass(lo)),'upper_mass':str(mass(hi)),'root_bracket_verified':True})
four=[1,1,4,4,4,4]; baseline=[1,1,3,4,4]
at=lambda v,c:sum((c**(-q) for q in v),Fraction())
assert at([1,1],Fraction(2))==1 and at([1,1],Fraction(1))==2
v231=at(four,Fraction(231,100)); v233=at(four,Fraction(233,100)); b233=at(baseline,Fraction(233,100))
assert v231>1 and v233<=1 and b233>1 and Fraction(233,100)<Fraction(23391,10000)
assert str(v233)=='2929867400/2947295521'
write(OUT/'algorithm-review-exact-arithmetic.json',{'X0_nine_recurrences':rows,'retarget':{'positive_control_base2':'1','negative_control_base1':'2','vector':four,'mass_231':str(v231),'mass_233':str(v233),'baseline_vector':baseline,'baseline_mass_233':str(b233),'strict_below_benchmark':True,'scope':'ARITHMETIC ONLY; sourcecore/generation/fullalgorithm debts unchanged'}})

spec=json.loads((CAMPAIGN/'algorithm/paid_cover/core-control-spec-v1.json').read_text())
core_rows=[]
for name in ['two_color','three_color']:
    raw=spec[name]; independently=exact_forest(raw['target'],raw['source']); assert independently['residual']==raw['minimum_additional_cuts']
    code,ans,sec=cli({'target':raw['target'],'source':raw['source'],'budget':raw['minimum_additional_cuts']},'paid-multicolor-'+name)
    assert code==0 and ans['feasible'] and valid_forest(raw['target'],raw['source'],ans['partition']) and ans['additional_cuts']==independently['residual']
    code,low,sec=cli({'target':raw['target'],'source':raw['source'],'budget':raw['minimum_additional_cuts']-1},'paid-multicolor-low-'+name)
    assert code==0 and not low['feasible']
    core_rows.append({'name':name,'exact_current_forest':independently,'actual_cli_witness':ans['partition'],'lower_budget_rejected':True})
origin=[ [spec['three_color']['source'][0],spec['three_color']['source'][1]],spec['three_color']['source'][2]]
g=Graph(origin); blocks=[set(Graph(s).labels) for s in spec['three_color']['source']]; actualcut=None
for cut in itertools.combinations(g.edges,2):
    if cp(g.cut_partition(cut))==cp(blocks): actualcut=cut;break
assert actualcut is not None
write(OUT/'algorithm-review-multicolor-supplementary.json',{'scope':'two supplementary synthetic development states; no hard2e reachability inferred','rows':core_rows,'three_color_original_source':origin,'actual_two_cut_certificate':actualcut})
print(json.dumps({'candidate_copy_mutations_caught':3,'X0_arithmetic_rows':9,'retarget_mass233':str(v233),'multicolor_cli_controls':2}))
