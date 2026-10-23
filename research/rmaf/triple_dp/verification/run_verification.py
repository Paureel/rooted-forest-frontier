"""One-shot replay harness. Run oracle controls before importing production."""
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

HERE = Path(__file__).resolve().parent
RMAF_ROOT = HERE.parents[1]
RESULTS = RMAF_ROOT / "results"
WORKSPACE_ROOT = HERE.parents[3]
sys.path.insert(0, str(HERE))
from partition_oracle import Instance, instances


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def controls(solve=None):
    frozen = json.loads((HERE/'controls.json').read_text())
    count = {'positive':0,'malformed':0,'wrong_result':0,'mutants_caught':0,'clean_twins':0}
    fixtures = {x['id']:x for x in frozen['positive']}
    for f in frozen['positive']:
        ins = Instance(f['input'])
        expected = ins.exact(check_characterization=True)
        assert expected['components'] == f['components'], f['id']
        assert expected['additional_cuts'] == f['additional_cuts'], f['id']
        ins.verify_result(f, expected)
        if solve:
            ins.verify_result(solve(copy.deepcopy(f['input'])), expected)
        count['positive'] += 1
    for f in frozen['malformed']:
        try:
            (solve if solve else Instance)(copy.deepcopy(f['input']))
        except ValueError:
            count['malformed'] += 1
        else:
            raise AssertionError('malformed control survived: ' + f['id'])
    for f in frozen['wrong_result']:
        clean = fixtures[f['fixture']]
        ins = Instance(clean['input'])
        try:
            ins.verify_result(f['result'])
        except (AssertionError, ValueError):
            count['wrong_result'] += 1
        else:
            raise AssertionError('wrong result survived: '+f['reason'])
        if 'mutant' in f['reason']:
            count['mutants_caught'] += 1
            ins.verify_result(clean)
            count['clean_twins'] += 1
    assert count == {'positive':6,'malformed':5,'wrong_result':5,'mutants_caught':2,'clean_twins':2}
    return count


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--mode', choices=['controls','pilot','full'], required=True)
    ap.add_argument('--output', required=True)
    args = ap.parse_args()
    output = Path(args.output)
    if not output.is_absolute():
        output = WORKSPACE_ROOT / output
    if output.parent.resolve() != RESULTS.resolve():
        raise ValueError("receipt output must be inside research/rmaf/results")
    if output.exists():
        raise FileExistsError("preserve prior receipt; select a fresh output name")
    start = time.perf_counter()
    receipt = {'mode':args.mode,'utc':datetime.now(timezone.utc).isoformat(),
               'oracle_sha256':digest(HERE/'partition_oracle.py'),
               'controls_sha256':digest(HERE/'controls.json'),
               'harness_sha256':digest(Path(__file__)), 'theorem_verdict':'OPEN',
               'method':'set partitions; rooted triples; direct vertex paths',
               'oracle_controls':controls(), 'cases':{}, 'failures':[]}
    try:
        if args.mode != 'controls':
            solver_path = HERE.parent/'solver.py'
            receipt['solver_sha256'] = digest(solver_path)
            spec = importlib.util.spec_from_file_location('triple_solver_under_test', solver_path)
            module = importlib.util.module_from_spec(spec)
            sys.modules[spec.name] = module
            spec.loader.exec_module(module)
            receipt['production_controls'] = controls(module.solve)
            for n in range(1, 6):
                all_cases = list(instances(n))
                expected_count = {1:1,2:2,3:21,4:345,5:9660}[n]
                assert len(all_cases) == expected_count, (n,len(all_cases),expected_count)
                if args.mode == 'pilot' and n == 5:
                    all_cases = random.Random(140526).sample(all_cases, 20)
                stage = time.perf_counter()
                comparisons = parts = bad_cases = large_compatible = 0
                for data_tuple in all_cases:
                    data = json.loads(json.dumps(data_tuple))
                    ins = Instance(data)
                    assert ins.in_regime
                    try:
                        exact = ins.exact(check_characterization=True)
                        actual = module.solve(copy.deepcopy(data))
                        ins.verify_result(actual, exact)
                    except Exception as exc:
                        receipt['failures'].append({'n':n,'input':data,'exception':repr(exc)})
                        raise
                    comparisons += 1
                    parts += exact['partitions_checked']
                    bad_cases += bool(ins.bad)
                    large_compatible += any(len(s.labels) >= 4 for s in ins.source)
                receipt['cases'][str(n)] = {'count':comparisons,'characterization_partitions':parts,
                       'cases_with_bad_triple':bad_cases,'cases_with_large_compatible':large_compatible,
                       'seconds':time.perf_counter()-stage}
                print(json.dumps({'n':n, **receipt['cases'][str(n)]}), flush=True)
            assert sum(v['count'] for v in receipt['cases'].values()) == (10029 if args.mode == 'full' else 389)
        receipt['finite_verdict'] = 'PASS'
    except Exception as exc:
        receipt['finite_verdict'] = 'FAIL'
        receipt['error'] = repr(exc)
        raise
    finally:
        receipt['seconds'] = time.perf_counter()-start
        output.write_text(json.dumps(receipt, indent=2, sort_keys=True)+'\n')
        print(json.dumps({'finite_verdict':receipt.get('finite_verdict'),'seconds':receipt['seconds'],
                          'output':args.output}), flush=True)


if __name__ == '__main__':
    main()
