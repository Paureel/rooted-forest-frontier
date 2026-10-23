"""Supplementary one-shot actual-chain missing-branch control, post-development."""
from chain import *

spec=json.loads((HERE/'CHAIN-PLANT-PIN-v1.json').read_text())
source=json.loads((ROOT/'results/algorithm-macro-chain-minimize-v2.json').read_text())
raw=source['smallest_refuter'];out=run({'T':raw['T'],'Tprime':raw['Tprime'],'cherry':[9,10]})
f=out['fixture'];opt=f['reduced_optimum']
assert opt['optimal_partitions']==[spec['expected_unique_reduced_optimum']]
assert f['residual_optimum']==spec['expected_residual']
rows=[]
for r in out['edge_pairs']:
    bad=[c for c in r['children'] if c['assignment']!='BB']
    assert bad
    badcost=min(c['total_residual'] for c in bad)
    goodcost=min(c['total_residual'] for c in r['children'])
    missed=spec['expected_unique_reduced_optimum']
    def survives(c):return all(any(set(b)<=set(q) for q in c['blocks']) for b in missed)
    assert not any(survives(c) for c in bad)
    assert any(survives(c) for c in r['children'])
    assert badcost==spec['expected_bad_cover_residual']
    assert goodcost==spec['expected_clean_cover_residual']
    try:
        assert badcost==f['residual_optimum']
        raise RuntimeError('corrupted cover comparator did not reject missing BB')
    except AssertionError:
        caught=True
    rows.append({'edges':[r['AB_edge'],r['BC_edge']],
                 'bad_nonempty_assignments':[c['assignment'] for c in bad],
                 'missed_optimum':missed,'bad_residual':badcost,'clean_residual':goodcost,
                 'missing_branch_and_comparator_caught':caught})
record={'scope':spec['registration'],'controls':rows,'passed':len(rows),'total':2,
        'pin_sha256':hashlib.sha256((HERE/'CHAIN-PLANT-PIN-v1.json').read_bytes()).hexdigest(),
        'code_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        'fresh_development_replay':out}
assert record['passed']==record['total']
(ROOT/'results/algorithm-macro-chain-plant-v1.json').write_text(json.dumps(record,indent=2)+'\n')
print('PASS supplementary actual-chain missing-BB/comparator controls:',len(rows),'/ 2')
