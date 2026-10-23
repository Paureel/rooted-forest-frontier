"""Explicit prerequisite/list/payment controls, frozen before execution."""
import json,copy,hashlib,time
from fractions import Fraction
from pathlib import Path
import instrument as I
HERE=Path(__file__).resolve().parent;ROOT=I.ROOT

def main():
    f=json.loads((HERE/'ADDENDUM-FREEZE-v1.json').read_text())
    for r in f['files']:assert hashlib.sha256((ROOT/r['path']).read_bytes()).hexdigest()==r['sha256']
    C=json.loads((HERE/'CONTROL-ADDENDUM-v1.json').read_text());start=time.perf_counter();rows=[];negative=[]
    P=C['proper_but_crossing_source_parents'];g=I.base.OriginalGraph(P['source'])
    actual={'proper_labels':I.base.proper_partition(g,P['parents']),
      'source_embeddings_disjoint':I.base.convex_partition(g,P['parents']),
      'valid_three_parent_source':I.parent_check(P['source'],P['parents'])}
    assert all(actual[k]==P[k] for k in actual);rows.append({'id':'proper-but-source-crossing','actual':actual})
    negative.append({'id':'proper-labels-do-not-imply-source-disjointness','caught':not actual['source_embeddings_disjoint']})
    T=C['clique_target_parent_hulls'];g=I.base.OriginalGraph(T['target'])
    proper=I.base.proper_partition(g,T['parents']);disjoint=I.base.convex_partition(g,T['parents'])
    common=g.at[tuple(T['common_vertex'])]
    assert proper and not disjoint and all(common in g.span(p) for p in T['parents'])
    rows.append({'id':'source-parents-may-overlap-in-target','proper_labels':proper,'target_embeddings_disjoint':disjoint,'common_vertex':T['common_vertex']})
    for r in C['wrong_extra_hard_cut_inequalities']:
        for c in [Fraction(2),Fraction(233,100)]:
            actual=sum((c**(-d) for d in r['costs']),Fraction(0))
            wrong=sum((c**(-d) for d in r['wrong_costs']),Fraction(0))
            assert (actual<=wrong)==r['actual_le_wrong_mass']
            negative.append({'id':r['id']+'-false-extra-discount-inequality','c':[c.numerator,c.denominator],
              'actual_mass':[actual.numerator,actual.denominator],'wrong_rhs':[wrong.numerator,wrong.denominator],'caught':actual>wrong})
    R=C['legal_raw_duplicate_output'];row=I.receipt(R['id'],[copy.deepcopy(R['output']),copy.deepcopy(R['output'])])
    assert I.validate_receipts([row],[R['id']]) and row['costs']==R['costs']
    actual=I.raw_mass(row['outputs'],2);assert actual==Fraction(*R['mass_at_2'])
    negative.append({'id':'legal-raw-duplicate-must-remain-in-mass','caught':actual!=Fraction(*R['false_deduplicated_mass_at_2'])})
    rows.append({'id':'legal-raw-duplicate','receipt_accepted':True,'costs':row['costs'],'mass_at_2':[actual.numerator,actual.denominator]})
    wrong=I.receipt(R['id'],[R['output']]);wrong['costs']=[C['forged_actual_cost']['forged_recorded_cost']]
    caught=False
    try:I.validate_receipts([wrong],[R['id']])
    except ValueError:caught=True
    assert caught;negative.append({'id':'forged-actual-whole-source-cost','caught':caught})
    assert all(r['caught'] for r in negative)
    report={'status':'PASS_PRERELEASE_ADDENDUM','candidate_contact':False,'replication_count_added':0,
      'rows':rows,'negative':negative,'negative_count':len(negative),'elapsed_seconds':time.perf_counter()-start}
    (ROOT/'research/rmaf/results/algorithm-assembly-prerelease-review-addendum-v1.json').write_text(json.dumps(report,indent=2)+'\n')
    print(report['status'],len(rows),'positive groups;',len(negative),'false catches;',report['elapsed_seconds'],'seconds')

if __name__=='__main__':main()
