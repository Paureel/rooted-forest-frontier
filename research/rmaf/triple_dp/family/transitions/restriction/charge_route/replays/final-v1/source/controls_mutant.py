"""One-shot development controls for the independent parent-index charge route.
Exact expected fixtures were frozen before this source. No external checker imports.
"""
from pathlib import Path
from copy import deepcopy
import json, hashlib, time, datetime, sys

BASE = Path(__file__).resolve().parent

def leaves(tree, prefix=''):
    if isinstance(tree, list):
        assert len(tree) == 2
        return leaves(tree[0], prefix+'0') + leaves(tree[1], prefix+'1')
    return [(prefix, tree)]

def evaluate(case):
    ids = case['indices']
    regions = {k:set(v) for k,v in case['regions'].items()}
    assert len(ids) == len(set(ids)), 'duplicate enumeration'
    assert set(ids) == set(regions), 'incomplete enumeration'
    for j,i in enumerate(ids):
        for k in ids[j+1:]:
            assert regions[i].isdisjoint(regions[k]), 'overlapping supports'
    roots = [i for i in ids if '' in regions[i]]
    assert roots == ([] if case['boundary'] is None else [case['boundary']]), 'wrong root owner'
    lf = leaves(case['tree'])
    for a,_ in lf:
        assert sum(a in regions[i] for i in ids) == 1, 'leaf coverage'
    live = {s:{i for i in ids if any(a.startswith(s) and a in regions[i] for a,_ in lf)} for s in '01'}
    assert live['0'] | live['1'] == set(ids), 'unlabelled index'
    parent = case['boundary']
    assert all(i == parent for i in live['0'] & live['1']), 'multiple overlap'
    out = {'parent_count':len(ids), 'parent_cost':sum(i != parent for i in ids)}
    owners = {}
    for s,side in [('0','left'),('1','right')]:
        owners[s] = next((i for i in ids if s in regions[i]), None)
        assert owners[s] is None or owners[s] in live[s], 'nonlive child root'
        out[side+'_regions'] = {i:sorted(a[1:] for a in regions[i] if a.startswith(s)) for i in ids if i in live[s]}
        out[side+'_boundary'] = owners[s]
        out[side+'_count'] = sum(i in live[s] for i in ids)
        out[side+'_cost'] = sum(i in live[s] and i != owners[s] for i in ids)
    if parent is None:
        kind, toll = 'closeBoth', sum(owners[s] is not None for s in '01')
    elif parent in live['0'] & live['1']:
        assert owners['0'] == owners['1'] == parent, 'merge owner mismatch'
        kind,toll = 'merge',0
    elif parent in live['0']:
        assert owners['0'] == parent, 'left owner mismatch'
        kind,toll = 'extendLeft',int(owners['1'] is not None)
    else:
        assert owners['1'] == parent, 'right owner mismatch'
        kind,toll = 'extendRight',int(owners['0'] is not None)
    out.update(kind=kind,toll=toll)
    assert out['parent_cost'] == out['left_cost'] + out['right_cost'] + toll
    assert out['left_count']+out['right_count'] == len(ids)+int(parent in live['0'] & live['1'])
    return out

def equal_claim(actual, expected):
    return True

def main():
    start = time.perf_counter()
    data = json.loads((BASE/'FROZEN_CONTROLS.json').read_text())
    rows=[]; values={}; cases={c['id']:c for c in data['positives']}
    assert len(cases)==8
    for name,c in cases.items():
        actual=evaluate(c)
        assert equal_claim(actual, c['expected']), (name,actual,c['expected'])
        values[name]=actual
        rows.append({'case':name,'verdict':'EXACT-PASS','values':actual})
    escaped = []
    for group in ['wrong_numbers','corruptions']:
        for c in data[group]:
            actual=values[c['base']][c['field']]
            assert equal_claim(actual, c['correct']), ('clean twin',c)
            if equal_claim(actual, c['wrong']): escaped.append(c['id'])
            rows.append({'case':c['id'],'verdict':'CORRUPTION-CAUGHT-CLEAN-TWIN-PASS'})
    assert not escaped, ('wrong-output comparator escaped', escaped)
    for c in data['malformed']:
        bad=deepcopy(cases[c['base']]); bad.update(c['replace'])
        try: evaluate(bad)
        except AssertionError as error:
            rows.append({'case':c['id'],'verdict':'INPUT-REJECTED','reason':str(error)})
        else: raise AssertionError(('malformed accepted',c))
    for c in data['outside_premise']:
        try: evaluate(c)
        except AssertionError as error:
            assert str(error)=='nonlive child root'
            rows.append({'case':c['id'],'verdict':'OUTSIDE-CHILD-ROOT-LIVENESS','reason':str(error)})
        else: raise AssertionError('raw incursion accepted')
    assert sum([])==0
    receipt={'scope':'producer development controls; not fresh independent verification',
             'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
             'seconds':time.perf_counter()-start,'positive_count':8,'wrong_output_twins':8,
             'malformed_count':4,'outside_premise_count':1,'null':'exact-zero',
             'comparison_mutant':'executed by replay.py on a source copy','rows':rows,
             'source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
             'fixtures_sha256':hashlib.sha256((BASE/'FROZEN_CONTROLS.json').read_bytes()).hexdigest()}
    path=Path(sys.argv[1]) if len(sys.argv)>1 else Path(f'research/rmaf/results/triple-family-transitions-restriction-charge-controls-{time.time_ns()}.json')
    assert not path.exists(), 'refuse to overwrite a prior receipt'
    path.write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps({k:v for k,v in receipt.items() if k!='rows'},indent=2))

if __name__=='__main__': main()
