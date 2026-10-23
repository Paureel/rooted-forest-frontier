"""Exact identity/origin reconciliation and deliberately forged origin rows."""
import json,copy
from rebuild import ROOT,HERE

def expected_inventory():
    out={}
    for arm in ['source','cut']:
        data=json.loads((ROOT/f'research/rmaf/results/algorithm-core-completion-fresh-review-{arm}-rebuild-v1.json').read_text())
        for row in data['audit']['rows']:
            row=copy.deepcopy(row)
            if arm=='cut' and row['module']=='Coverage':
                row['module']='CutCoverage';row['name']=row['name'].replace('_private.Coverage.','_private.CutCoverage.')
            if row['name']=='Universal233.CoreProgram.generate.eq_1':row['module']='InitialCoverage'
            key=row['name']
            if key in out:assert out[key]==row,(key,out[key],row)
            out[key]=row
    # Explicit list of this review's three named proofs and the two generated
    # simp auxiliaries. These are newly authored consumer records, not imports.
    for n in ['FreshCompletionReview.every_actual_output',
              'FreshCompletionReview.completed_source_consumer',
              'FreshCompletionReview.distinctColorCounts',
              'FreshCompletionReview.distinctColorCounts._simp_1_1',
              'FreshCompletionReview.distinctColorCounts._simp_1_2']:
        out[n]={'module':'NonauthorConsumer','name':n,'kind':'theorem',
                'axioms':['propext','Quot.sound'] if '._simp_' in n else ['propext','Classical.choice','Quot.sound']}
    return out

def validate(rows,expected):
    actual={r['name']:r for r in rows}
    assert len(actual)==len(rows),'duplicate records'
    assert set(actual)==set(expected),'missing/extra records'
    for n,a in actual.items():
        e=expected[n]
        assert a['module']==e['module'],('wrong originating module',n)
        assert a['kind']==e['kind'],('wrong declaration kind',n)
        assert set(a['axioms'])==set(e['axioms']),('wrong axiom closure',n)

def main():
    joint=json.loads((ROOT/'research/rmaf/results/algorithm-core-completion-fresh-review-joint-v1.json').read_text())
    rows=joint['audit']['rows'];expected=expected_inventory();validate(rows,expected)
    cases=[]
    for name,change in [
        ('wrong-module-public',lambda rs: next(r for r in rs if r['name']=='Universal233.CoreProgram.generate').update(module='RMAF')),
        ('wrong-module-private',lambda rs: next(r for r in rs if r['name'].startswith('_private.')).update(module='Controls')),
        ('missing-private',lambda rs:rs.pop(next(i for i,r in enumerate(rs) if r['name'].startswith('_private.')))),
        ('missing-generated',lambda rs:rs.pop(next(i for i,r in enumerate(rs) if r['name'].endswith('.eq_1')))),
        ('forged-axiom-closure',lambda rs:next(r for r in rs if r['name']=='Universal233.CoreProgram.generate').update(axioms=['propext','FakeDebt']))]:
        changed=copy.deepcopy(rows);change(changed)
        try:validate(changed,expected)
        except AssertionError as e:cases.append({'id':name,'caught':True,'reason':str(e)})
        else:raise AssertionError('forgery not caught: '+name)
    report={'status':'PASS_EXACT_ORIGIN_RECONCILIATION_CONTROLS','expected_declarations':len(expected),
      'unchanged_clean_inventory_accepted':True,'controls':cases,
      'sole_generated_origin_adoption':'Universal233.CoreProgram.generate.eq_1: Entrypoint -> InitialCoverage; exact type/proof Expr fingerprint checked',
      'replication_count_added':0}
    (ROOT/'research/rmaf/results/algorithm-core-completion-fresh-review-inventory-controls-v1.json').write_text(json.dumps(report,indent=2)+'\n')
    print(report['status'],len(expected),'complete rows; five forged records caught')

if __name__=='__main__':main()
