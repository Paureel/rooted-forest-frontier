"""Problem-specific post-hoc adversary for good size-four plus bad triples."""
import argparse
import hashlib
import json
import pathlib
import random
import time
import check
import cut_oracle
import solver

HERE = pathlib.Path(__file__).resolve().parent


def run(pilot=False):
    check.controls()
    plan = json.loads((HERE/'mixed-plan.json').read_text())
    start = time.perf_counter()
    all_targets = check.trees(tuple('abcdefg'))
    indices = random.Random(plan['seed']).sample(range(len(all_targets)), plan['target_count'])
    if pilot:
        indices = indices[:plan['pilot_targets']]
    rows = []
    for idx in indices:
        target = all_targets[idx]
        restrictions = {frozenset(block): check.raw_shape(shape)
                        for forest in cut_oracle.cut_forests(target) for block, shape in forest}
        good = restrictions[frozenset(plan['good_labels'])]
        target_triple = restrictions[frozenset(plan['bad_labels'])]
        target_shape = next(f for f in cut_oracle.cut_forests(target_triple) if len(f) == 1)
        for triple in check.trees(tuple(plan['bad_labels'])):
            source_shape = next(f for f in cut_oracle.cut_forests(triple) if len(f) == 1)
            if source_shape == target_shape:
                continue
            case = dict(target=target, source=[good, triple])
            answer = check.check_case(case)
            assert answer['bad_components'] == plan['expected_bad_components']
            rows.append(dict(target_index=idx, case=case, answer=answer))
    assert len(rows) == (plan['pilot_targets']*2 if pilot else plan['expected_case_count'])
    result = dict(status='passed', cases=len(rows), seconds=time.perf_counter()-start,
                  plan=plan, pilot=pilot, rows=rows,
                  hashes={p.name:hashlib.sha256(p.read_bytes()).hexdigest()
                          for p in [HERE/'mixed_checks.py',HERE/'mixed-plan.json',HERE/'solver.py',HERE/'cut_oracle.py',HERE/'check.py']})
    name = 'triple-dp-mixed-pilot.json' if pilot else 'triple-dp-mixed-sample.json'
    check.atomic(HERE.parent/'results'/name, result)
    print(json.dumps({k:result[k] for k in ['status','cases','seconds','pilot']}))


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--pilot', action='store_true')
    run(parser.parse_args().pilot)
