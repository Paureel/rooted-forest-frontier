"""Problem-specific supplemental held-out six-leaf verification.

The independent oracle is unchanged from its pre-production freeze. The plan
and hand controls were fixed before any six-leaf oracle results were inspected.
"""
import argparse
import copy
import hashlib
import importlib.util
import json
from pathlib import Path
import random
import sys
import time
from datetime import datetime, timezone
from itertools import product

HERE = Path(__file__).resolve().parent
RMAF_ROOT = HERE.parents[1]
RESULTS = RMAF_ROOT / 'results'
sys.path.insert(0, str(HERE))
from partition_oracle import Instance, trees
from run_verification import controls, digest

ORACLE_HASH = 'cd7c672033890df4a8f6d730603f4299295351b08179a0ff47fd9d07ad0b027d'
SOLVER_HASH = '4b0fed6b9a1e76454820a911f21a29d263c110e58bb4575b52a086e751c2174d'


def load_solver():
    path = HERE.parent / 'solver.py'
    assert digest(path) == SOLVER_HASH, 'solver changed; stop held-out campaign'
    spec = importlib.util.spec_from_file_location('triple_solver_n6_under_test', path)
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module.solve


def supplemental_controls(plan, solve):
    for fixture in plan['controls']:
        ins = Instance(fixture['input'])
        exact = ins.exact(check_characterization=True)
        assert exact['components'] == fixture['components']
        assert exact['additional_cuts'] == fixture['additional_cuts']
        ins.verify_result(fixture, exact)
        ins.verify_result(solve(copy.deepcopy(fixture['input'])), exact)
    fixture = next(x for x in plan['controls'] if x['id'] == plan['mutant']['fixture'])
    ins = Instance(fixture['input'])
    try:
        ins.verify_result(plan['mutant'])
    except (ValueError, AssertionError):
        caught = True
    else:
        raise AssertionError('two-bad-triple mutant survived')
    ins.verify_result(fixture)
    return {'positive':len(plan['controls']), 'mutants_caught':int(caught), 'clean_twins':1}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--mode', choices=['pilot','full','fallback'], required=True)
    args = ap.parse_args()
    output = RESULTS / ('triple-dp-verification-n6-' + args.mode + '.json')
    if output.exists():
        raise FileExistsError('preserve existing receipt: '+str(output))
    plan = json.loads((HERE/'supplement-n6-plan.json').read_text())
    assert digest(HERE/'partition_oracle.py') == ORACLE_HASH
    started = time.perf_counter()
    receipt = {'utc':datetime.now(timezone.utc).isoformat(), 'mode':args.mode,
        'plan_sha256':digest(HERE/'supplement-n6-plan.json'),
        'oracle_sha256':ORACLE_HASH,'solver_sha256':SOLVER_HASH,
        'script_sha256':digest(Path(__file__)), 'original_controls_sha256':digest(HERE/'controls.json'),
        'original_controls':controls(), 'theorem_verdict':'OPEN', 'failures':[]}
    try:
        solve = load_solver()
        receipt['production_original_controls'] = controls(solve)
        receipt['supplemental_controls'] = supplemental_controls(plan, solve)
        targets = trees(tuple(plan['target_labels']))
        source_choices = [trees(tuple(x)) for x in plan['source_leaf_sets']]
        case_tuples = [(target, source) for target in targets for source in product(*source_choices)]
        assert len(targets) == plan['target_count']
        assert len(case_tuples) == plan['full_case_count']
        if args.mode == 'pilot':
            indices = random.Random(plan['pilot']['sample_seed']).sample(range(len(case_tuples)),plan['pilot']['count'])
        elif args.mode == 'fallback':
            indices = random.Random(2140626).sample(range(len(case_tuples)),200)
        else:
            pilot_path = RESULTS/'triple-dp-verification-n6-pilot.json'
            pilot = json.loads(pilot_path.read_text())
            assert pilot['plan_sha256'] == receipt['plan_sha256']
            assert pilot['oracle_sha256'] == ORACLE_HASH and pilot['solver_sha256'] == SOLVER_HASH
            assert pilot['projected_full_seconds'] < 60, 'projection requires fixed fallback'
            receipt['pilot_receipt_sha256'] = digest(pilot_path)
            indices = list(range(len(case_tuples)))
        receipt['sample_indices'] = indices if args.mode != 'full' else 'all indices 0..8504'
        count = partition_count = 0
        histogram = {'0':0,'1':0,'2':0}
        loop_started = time.perf_counter()
        for index in indices:
            target, source = case_tuples[index]
            data = json.loads(json.dumps({'target':target,'source':source}))
            ins = Instance(data)
            assert ins.in_regime
            try:
                exact = ins.exact(check_characterization=True)
                actual = solve(copy.deepcopy(data))
                ins.verify_result(actual, exact)
                assert exact['partitions_checked'] == plan['monochromatic_partitions_per_case']
            except Exception as exc:
                receipt['failures'].append({'index':index,'input':data,'exception':repr(exc)})
                raise
            count += 1
            partition_count += exact['partitions_checked']
            histogram[str(len(ins.bad))] += 1
        receipt['comparison_seconds'] = time.perf_counter()-loop_started
        receipt['case_count'] = count
        receipt['characterization_partitions'] = partition_count
        receipt['bad_color_histogram'] = histogram
        receipt['projected_full_seconds'] = receipt['comparison_seconds'] / count * plan['full_case_count']
        expected = {'pilot':40,'full':8505,'fallback':200}[args.mode]
        assert count == expected
        if args.mode == 'full':
            assert partition_count == plan['full_characterization_partition_count']
            assert histogram == plan['expected_full_bad_color_histogram']
        assert digest(HERE/'partition_oracle.py') == ORACLE_HASH
        assert digest(HERE.parent/'solver.py') == SOLVER_HASH
        receipt['finite_verdict'] = 'PASS'
    except Exception as exc:
        receipt['finite_verdict'] = 'FAIL'
        receipt['error'] = repr(exc)
        raise
    finally:
        receipt['seconds'] = time.perf_counter()-started
        output.write_text(json.dumps(receipt,indent=2,sort_keys=True)+'\n')
        print(json.dumps({k:receipt.get(k) for k in ['mode','finite_verdict','case_count',
             'characterization_partitions','bad_color_histogram','comparison_seconds',
             'projected_full_seconds','seconds']}),flush=True)


if __name__ == '__main__':
    main()
