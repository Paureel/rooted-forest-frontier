#!/usr/bin/env python3
"""Compare compiled adapter to unchanged READY bank and independent graph checks.
One preserved frozen q4 callback-table error is reported, never silently passed.
"""
import collections,fractions,importlib.util,json,pathlib,sys
sys.dont_write_bytecode=True
HERE=pathlib.Path(__file__).resolve().parent
loader=importlib.util.spec_from_file_location('ownfrozen',HERE.parent/'instrument-v2.py')
m=importlib.util.module_from_spec(loader);loader.loader.exec_module(m)

def main():
    lines=(HERE/'compiled-controls-bank-v1.json').read_text().splitlines()
    payloads=[json.loads(x) for x in lines if x.startswith('{"cases"')]
    assert len(payloads)==1
    actual=payloads[0]
    frozen=json.loads((HERE.parent/'bank-v2.json').read_text())
    references={x['name']:x for x in frozen['cases']}
    tables=json.loads((HERE.parent/'CALLBACK-TABLES-v1.json').read_text())
    assert len(actual['cases'])==len(references)==25
    summary={'status':'PASS_WITH_PRESERVED_FROZEN_CONTROL_ERRATUM','case_count':25,
        'core_receipt_comparisons':0,'plan_comparisons':0,'execution_comparisons':0,
        'independent_return_checks':0,'actual_callback_occurrences':0,
        'frozen_callback_mismatches':[],'mass_comparisons':0,'c4_outside_domain':[],
        'cases':[]}
    for row in actual['cases']:
        name=row['name']; ref=references[name]
        assert row['selector']==ref['selector'],name
        if ':' in name:
            base,variant=name.split(':'); spec=m.transform(m.CASES[base],variant)
        else: spec=m.CASES[name]
        s,t=m.Original(spec['s']),m.Original(spec['t'])
        for k,v in row['cores'].items():
            assert v==ref['cores'][k],(name,k)
            summary['core_receipt_comparisons']+=1
        if row['selector'][0]=='vertex':
            assert row['cores']=={} and row['plans']==[] and row['executions']==[]
            summary['cases'].append({'name':name,'scope':'selector-boundary'});continue
        pa,pb=ref['cores']['splitA-q3']['outputs'],ref['cores']['splitB-q3']['outputs']
        ca,cb=ref['cores']['splitA-q5']['outputs'],ref['cores']['splitB-q5']['outputs']
        if pa: cheap_idx,cheap,opposite=0,pa,cb
        elif pb: cheap_idx,cheap,opposite=1,pb,ca
        else:cheap_idx,cheap,opposite=None,[],[]
        expected_outputs=[]
        for planned in row['plans']:
            q=planned['q']; expected=[]
            if q>=3:
                if cheap_idx is None:
                    candidates=[(o,'full',0) for o in ca+cb]
                else:
                    both_good=all(ref['sector_good'][cheap_idx])
                    candidates=[(o,'ordinary',0) for o in cheap]+[(o,'retained' if both_good else 'full',1 if both_good else 0) for o in opposite]
                for out,mode,extra in candidates:
                    d=len(out['cuts'])+extra
                    if d<=q:expected.append((out,mode,q-d))
            assert len(planned['entries'])==len(expected),(name,q,'entry count')
            for entry,(out,mode,budget) in zip(planned['entries'],expected):
                actualmode=entry['mode'] if isinstance(entry['mode'],str) else entry['mode']['mode']
                assert entry['output']==out and actualmode==mode and entry['budget']==budget,(name,q,'entry')
                if mode=='retained':
                    md=entry['mode']; a=spec['p'][cheap_idx]; b=spec['p'][1-cheap_idx]
                    assert md['parent']==a and md['residual']==b and md['completed']==spec['p'][2]
                    # Known completion is checked against original restricted
                    # trees using independent clades/hulls, not copied expected digits.
                    known=md['known']
                    assert m.partition(a,known) and len(known)==2
                    assert all(s.restriction_equal(t,k) for k in known)
                    assert s.disjoint(known) and t.disjoint(known)
            assert planned['budgets']==[e['budget'] for e in planned['entries']]
            assert planned['charged']==[q-e['budget'] for e in planned['entries']]
            summary['plan_comparisons']+=1
        for ex in row['executions']:
            q=ex['q']; result=json.loads(ex['result']); calls=result['reported_calls']
            assert calls==ex['observed_calls'],(name,q,ex['oracle'],'reported vs observed')
            assert all(c['budget']+3<=q for c in calls)
            summary['execution_comparisons']+=1
            summary['actual_callback_occurrences']+=len(calls)
            answer=result['answer']
            if answer is not None:
                assert m.agreement(s,t,answer) and len(answer)-1<=q,(name,q,'original returned check')
                summary['independent_return_checks']+=1
            for c in [fractions.Fraction(2),fractions.Fraction(233,100),fractions.Fraction(3)]:
                mass=sum((c**(-(q-x['budget'])) for x in calls),fractions.Fraction())
                assert mass<=4*c**-4,(name,q,ex['oracle'],str(c),str(mass))
                summary['mass_comparisons']+=1
            c=fractions.Fraction(4)
            mass=sum((c**(-(q-x['budget'])) for x in calls),fractions.Fraction())
            if mass>4*c**-4:summary['c4_outside_domain'].append([name,q,ex['oracle'],str(mass)])
            if name=='S11' and q in [4,5,6]:
                table=tables['S11'][f'q{q}'];bs=[c['budget'] for c in calls]
                if bs!=table['budgets']:
                    mismatch={'case':name,'q':q,'oracle':ex['oracle'],'frozen_expected_callbacks':table['budgets'],'actual_callbacks':bs}
                    summary['frozen_callback_mismatches'].append(mismatch)
                    assert q==4 and bs==[],mismatch
                if q in [5,6]:
                    assert bs==table['budgets']
                    assert [c['target'] for c in calls]==[tables['S11']['T_B']]*3
                    assert [c['sources'] for c in calls]==[[tables['S11']['B_whole']],tables['S11']['B_forest_opposite0'],tables['S11']['B_forest_opposite1']]
                if ex['oracle']==3:
                    if q in [4,5]:assert answer is None
                    else:assert answer is not None and len(answer)==table['returned_block_minimum']
        summary['cases'].append({'name':name,'selector':row['selector'],'original_minimum_blocks':ref['minimum_blocks']})
    assert len(summary['frozen_callback_mismatches'])==4
    expected={'empty':[],'failed':[0],'duplicate':[0,0],'early_failure':[0,1]}
    for row in actual['scheduler']:
        result=json.loads(row['result']);trace=[p[0] for p in result['queries']]
        assert trace==row['observed']==expected[result['label']]
    summary['scheduler_controls']=4
    summary['expected_internal_B_overlap_retained']=True
    m.dump(HERE/'COMPILED-CONTROL-COMPARISON-v1.json',summary)
    print(json.dumps({k:v for k,v in summary.items() if k not in ['cases','c4_outside_domain']},indent=2))

if __name__=='__main__':main()
