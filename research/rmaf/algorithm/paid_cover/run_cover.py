#!/usr/bin/env python3
"""One-shot controls and measured candidate failures. See PIN-v1.md."""
import argparse
import hashlib
import json
from pathlib import Path
import time
from cover_solver import (Tree, solve, valid_partition, source_realization,
                          membership, mass, canon_parts)

ROOT = Path(__file__).resolve().parents[2]
OUT = ROOT/'results'


def controls():
    checks = []
    catches = []
    def check(name, condition):
        if not condition:
            raise AssertionError(name)
        checks.append(name)
    def catch(name, f):
        try:
            f()
        except (AssertionError, ValueError, TypeError):
            catches.append(name)
        else:
            raise AssertionError('corruption survived: '+name)
    def insist(x):
        if not x:
            raise AssertionError('planted assertion fired')
    check('empty', solve(None, [], 0)['partition'] == [])
    check('singleton', solve(0, [0], 0)['additional_cuts'] == 0)
    t = ((0,1),2)
    u = ((0,2),1)
    check('identical', solve(t, [t], 0)['additional_cuts'] == 0)
    check('conflicting-triple-zero', not solve(t, [u], 0)['feasible'])
    answer = solve(t, [u], 1)
    check('conflicting-triple-one', answer['feasible'] and len(answer['partition']) == 2)
    a,b = Tree(t),Tree(u)
    check('wrong-full-topology-reject', not valid_partition(a,[b],[[0,1,2]]))
    check('two-block-clean-twin', valid_partition(a,[b],[[0],[1,2]]))
    t = ((0,1),(2,3))
    check('cross-pairs-zero', not solve(t, [(0,2),(1,3)], 0)['feasible'])
    check('cross-pairs-one', solve(t, [(0,2),(1,3)], 1)['additional_cuts'] == 1)
    check('cross-pairs-overlap-reject', not valid_partition(Tree(t),[Tree((0,2)),Tree((1,3))],[[0,2],[1,3]]))
    catch('duplicate-tree', lambda: solve((0,0), [(0,1)], 1))
    catch('duplicate-forest', lambda: solve((0,1), [0,0], 1))
    catch('missing-forest', lambda: solve((0,1), [0], 1))
    catch('empty-component', lambda: solve((0,1), [None], 1))
    catch('negative-budget', lambda: solve(0, [0], -1))
    check('suppression', Tree(t).shape([0,2,3]) == ((2,3),0))
    triple = Tree(((0,1),2))
    v = next(v for v in triple.adj if triple.span([0,1]) == {v, triple.labels[0], triple.labels[1]})
    regions,_ = triple.leaf_regions({v})
    check('degree-three-region-count', len(regions) == 3)
    check('degree-three-two-cut-realization', source_realization(triple,regions,2) is not None)
    catch('degree-three-false-one-cut', lambda: insist(source_realization(triple,regions,1) is not None))
    cross = Tree(((0,2),(1,3)))
    parts = [[0,1],[2,3]]
    check('bad-one-cut-realization-reject', source_realization(cross,parts,1) is None)
    check('source-span-overlap', bool(cross.span(parts[0]) & cross.span(parts[1])))
    check('one-cut-clean-twin', source_realization(Tree(t),parts,1) is not None)
    check('mass-1-2', str(mass([1,2])) == '33100/53361')
    catch('unpaid-branch-false-mass', lambda: insist(mass([0,1,2]) < 1))
    catch('wrong-count-comparator', lambda: insist(len(answer['partition']) == 1))
    clean_cover = [[[0],[1,2]], [[1],[0,2]], [[2],[0,1]]]
    bad_cover = [[[0,1,2]]]
    literal = canon_parts([[0],[1,2]])
    check('clean-cover-literal', literal in [canon_parts(p) for p in clean_cover])
    catch('missing-branch-literal', lambda: insist(literal in [canon_parts(p) for p in bad_cover]))
    return dict(passed=len(checks)+len(catches), total=27,
                positive=checks, corruptions_caught=catches)


def pilot():
    # Frozen synthetic input; not selected from any execution output.
    target = ((0,1),(2,3))
    source = ((0,2),(1,3))
    rows = []
    for q in (0,1,2):
        start = time.perf_counter()
        ans = solve(target,[source],q)
        rows.append(dict(q=q, elapsed_seconds=time.perf_counter()-start, result=ans))
    failed = rows[-1]['result']
    assert failed['feasible'] and failed['additional_cuts'] == 2
    assert failed['stats']['core_states'] == 0
    site = failed['ledger'][0]
    assert site['membership']['pure'] and not site['membership']['triple']
    query = site['hypothetical_queries'][0]
    assert query['labels'] == [0,1,2,3] and query['additional_cut_budget'] == 2
    return dict(status='candidate-improved-bound-rejected', target=target, source=[source],
                rows=rows, mechanism='one color has no inter-color core; unmarked query is identical to original input at full q',
                same_budget_cover=[0], cover_mass=str(mass([0])),
                finite_scope='Smallest leaf count outside the compatible/triple class: incompatible components require at least four labels. No universal algorithm theorem certified.')


def main():
    p = argparse.ArgumentParser()
    p.add_argument('--stage', choices=['controls','pilot'], required=True)
    args = p.parse_args()
    started = time.perf_counter()
    ans = controls() if args.stage == 'controls' else pilot()
    if args.stage == 'controls':
        assert ans['passed'] == ans['total'], ans
    report = dict(stage=args.stage, result=ans, elapsed_seconds=time.perf_counter()-started,
                  hashes={f.name:hashlib.sha256(f.read_bytes()).hexdigest() for f in
                          [Path(__file__),Path(__file__).with_name('cover_solver.py'),Path(__file__).with_name('PIN-v1.md')]},
                  provenance='Same-author development wrapper around pure_bridge/check_geometry.py graph primitives; no independent certification.')
    dest = OUT/f'algorithm-cover-{args.stage}-v1.json'
    if dest.exists():
        raise FileExistsError('Preserve existing receipt: '+str(dest))
    dest.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(dict(output=str(dest), stage=args.stage, elapsed_seconds=report['elapsed_seconds'],
                          passed=ans.get('passed'), status=ans.get('status'))))


if __name__ == '__main__':
    main()
