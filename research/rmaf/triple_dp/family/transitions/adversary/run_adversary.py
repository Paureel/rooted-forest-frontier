"""One-shot independent geometric merge adversary; no old code imports.

Controls, mutation audit, pilot and bounded run each emit retained receipts.
"""
import argparse
import copy
import hashlib
import importlib.util
import itertools
import json
from pathlib import Path
import platform
import sys
import time
from datetime import datetime, timezone
import prefix_oracle as P

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[5]
FROZEN = HERE.parent / 'controls.json'
SUPPLEMENTAL = HERE / 'supplemental-controls.json'


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def load_checker(path):
    spec = importlib.util.spec_from_file_location('selected_graph_checker', path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def control_battery(G):
    controls = json.loads(FROZEN.read_text())
    supplemental = json.loads(SUPPLEMENTAL.read_text())
    report = []
    fixtures = {f['id']: f for f in controls['positive']}
    def event(group, ident, ok, **data):
        report.append({'group': group, 'id': ident, 'passed': bool(ok), **data})
    def positive(group, f):
        out = G.candidate(f['left'], f['right'])
        ge = G.transition_errors(f['left'], f['right'], out)
        pe = P.errors(out)
        expected = P.expected(f['left'], f['right'])
        mismatches = {k: {'frozen': v, 'prefix': expected[k]}
                      for k, v in f['expected'].items() if v != expected[k]}
        claims = G.claim_errors(out, f['expected'])
        ok = not (ge or pe or mismatches or claims) and G.facts(out) == expected
        event(group, f['id'], ok, graph_errors=ge + claims, prefix_errors=pe,
              frozen_prefix_mismatches=mismatches, actual=G.facts(out))
    for f in controls['positive']:
        positive('positive', f)
    for f in controls['malformed']:
        ge = G.input_errors(f['left'], f['right'])
        pe = P.errors(f['left']) + P.errors(f['right'])
        if f['left']['boundary'] is None or f['right']['boundary'] is None:
            pe.append('merge-boundary-absent')
        event('malformed', f['id'], bool(ge) and bool(pe),
              graph_errors=ge, prefix_errors=pe)
    for wrong in controls['wrong_results']:
        f = fixtures[wrong['fixture']]
        out = G.candidate(f['left'], f['right'])
        field = wrong['field']
        bad = G.claim_errors(out, {field: wrong['wrong']})
        clean = G.claim_errors(out, {field: wrong['clean']})
        other = P.expected(f['left'], f['right'])[field]
        event('wrong_result', wrong['id'], bool(bad) and not clean and
              other == wrong['clean'] and other != wrong['wrong'],
              wrong_diagnostics=bad, clean_diagnostics=clean,
              prefix_actual=other, clean_twin_passed=not clean)
    for corrupt in controls['support_corruptions']:
        f = fixtures[corrupt['fixture']]
        clean = G.candidate(f['left'], f['right'])
        damaged = copy.deepcopy(clean)
        damaged['regions'][corrupt['region']].remove(corrupt['remove'])
        ge = G.transition_errors(f['left'], f['right'], damaged)
        pe = P.errors(damaged)
        twin = G.transition_errors(f['left'], f['right'], clean) + P.errors(clean)
        event('support_corruption', corrupt['id'], bool(ge) and bool(pe) and not twin,
              graph_errors=ge, prefix_errors=pe, clean_twin_passed=not twin,
              exact_corrupt_output=damaged)
    for f in supplemental['malformed_family']:
        ge, pe = G.family_errors(f['family']), P.errors(f['family'])
        event('supplemental_malformed', f['id'], bool(ge) and bool(pe),
              graph_errors=ge, prefix_errors=pe)
    for f in supplemental['valid_merge']:
        positive('supplemental_positive', f)
    for corrupt in supplemental['valid_but_wrong_output']:
        f = fixtures[corrupt['fixture']]
        clean = G.candidate(f['left'], f['right'])
        damaged = copy.deepcopy(clean)
        if 'add' in corrupt:
            damaged['regions'][corrupt['region']].append(corrupt['add'])
        else:
            damaged['regions'][corrupt['new']] = damaged['regions'].pop(corrupt['old'])
            damaged['indices'] = list(damaged['regions'])
        structural = G.family_errors(damaged) + P.errors(damaged)
        ge = G.transition_errors(f['left'], f['right'], damaged)
        prefix_mismatch = G.facts(damaged) != P.expected(f['left'], f['right'])
        twin = G.transition_errors(f['left'], f['right'], clean)
        event('supplemental_retention', corrupt['id'], not structural and bool(ge)
              and prefix_mismatch and not twin, structural_errors=structural,
              graph_errors=ge, clean_twin_passed=not twin,
              exact_corrupt_output=damaged)
    counts = {group: {'total': sum(r['group'] == group for r in report),
                      'passed': sum(r['group'] == group and r['passed'] for r in report)}
              for group in sorted({r['group'] for r in report})}
    return {'passed': all(r['passed'] for r in report), 'counts': counts, 'items': report}


SHAPES = [('leaf', 'x', 1), ('cherry', ['x', 'x'], 2),
          ('left-comb3', [['x', 'x'], 'x'], 3),
          ('right-comb3', ['x', ['x', 'x']], 3)]


def candidates(tree):
    """Restricted-growth partitions with an optional unowned internal class.

    Root owner fixed to i0; each further new block gets its first-use name.
    No family validity assumptions except leaves owned and root live.
    """
    vertices, leaflabels = P.table(tree)
    assert vertices[0] == ''
    def assign(pos, assignment, largest):
        if pos == len(vertices):
            regions = {f'i{i}': [] for i in range(largest + 1)}
            for address, owner in zip(vertices, assignment):
                if owner >= 0:
                    regions[f'i{owner}'].append(address)
            yield {'tree': tree, 'regions': regions,
                   'indices': list(regions), 'boundary': 'i0'}
            return
        options = list(range(largest + 2))
        if vertices[pos] not in leaflabels:
            options.insert(0, -1)
        for owner in options:
            yield from assign(pos + 1, assignment + [owner], max(owner, largest))
    yield from assign(1, [0], 0)


def search(G, pilot):
    all_families, enum_rows = {}, []
    for name, tree, leaves in SHAPES:
        began = time.perf_counter()
        accepted = []
        count = 0
        for f in candidates(tree):
            count += 1
            ge, pe = G.family_errors(f), P.errors(f)
            if bool(ge) != bool(pe):
                return {'verdict': 'CHECKER-DISAGREEMENT', 'stage': 'input-enumeration',
                        'witness': f, 'graph_errors': ge, 'prefix_errors': pe,
                        'enumeration': enum_rows, 'attempts_current': count}
            if not ge:
                accepted.append(f)
        all_families[name] = accepted
        enum_rows.append({'shape': name, 'vertices': len(P.table(tree)[0]),
                         'leaves': leaves, 'candidate_partitions': count,
                         'valid_live_families': len(accepted),
                         'seconds': time.perf_counter() - began})
    rows, checked, windows = [], 0, []
    for lname, _, ll in SHAPES:
        for rname, _, rl in SHAPES:
            if ll + rl > 5:
                continue
            lefts, rights = all_families[lname], all_families[rname]
            all_pairs = list(itertools.product(lefts, rights))
            if pilot and len(all_pairs) > 16:
                chosen = sorted({i * (len(all_pairs) - 1) // 15 for i in range(16)})
                pairs = [all_pairs[i] for i in chosen]
            else:
                pairs = all_pairs
            began = time.perf_counter()
            per_case = []
            for left, right in pairs:
                tick = time.perf_counter()
                out = G.candidate(left, right)
                ge = G.transition_errors(left, right, out)
                pe = P.errors(out)
                expected = P.expected(left, right)
                mismatch = G.facts(out) != expected
                checked += 1
                if ge or pe or mismatch:
                    return {'verdict': 'FIRE', 'stage': 'valid-input-merge',
                            'checked_pairs_through_failure': checked,
                            'witness': {'left': left, 'right': right, 'output': out,
                                        'graph_errors': ge, 'prefix_errors': pe,
                                        'prefix_expected': expected},
                            'enumeration': enum_rows, 'pair_rows': rows}
                per_case.append(time.perf_counter() - tick)
            elapsed = time.perf_counter() - began
            row = {'left_shape': lname, 'right_shape': rname,
                   'available_pairs': len(all_pairs), 'checked_pairs': len(pairs),
                   'seconds': elapsed, 'case_seconds': per_case}
            rows.append(row)
            windows.extend(per_case)
    return {'verdict': 'NO-FIRE-BOUNDED', 'pilot': pilot,
            'checked_pairs': checked, 'available_pairs': sum(r['available_pairs'] for r in rows),
            'enumeration': enum_rows, 'pair_rows': rows,
            'timing': {'first_case_warmup_seconds': windows[0],
                       'post_first_mean_seconds': sum(windows[1:]) / len(windows[1:]),
                       'post_first_max_seconds': max(windows[1:])},
            'label_convention': 'Every enumerated leaf has label x; address identity retained',
            'coverage_scope': 'Canonical vertex partitions; root live; child leaves <=3; total <=5; no color admissibility; no universal conclusion'}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--mode', choices=['controls', 'pilot', 'bounded'], required=True)
    parser.add_argument('--checker', type=Path, default=HERE / 'graph_checker.py')
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--gate', type=Path)
    args = parser.parse_args()
    G = load_checker(args.checker)
    started = time.perf_counter()
    hashpaths = [args.checker, HERE / 'prefix_oracle.py', Path(__file__), FROZEN,
                 SUPPLEMENTAL, HERE / 'SPEC.md', HERE.parent / 'TARGET.md',
                 HERE.parent.parent / 'NEXT.md']
    result = {'started_utc': datetime.now(timezone.utc).isoformat(),
              'mode': args.mode, 'command': sys.argv, 'python': sys.version,
              'platform': platform.platform(),
              'source_sha256': {str(p): sha(p) for p in hashpaths}}
    result['controls'] = control_battery(G)
    if not result['controls']['passed']:
        result['verdict'] = 'CONTROL-FAILURE'
    elif args.mode == 'bounded':
        if args.gate is None:
            raise ValueError('bounded search requires recorded pilot gate')
        gate = json.loads(args.gate.read_text())
        assert gate['pilot_and_controls_passed'] and gate['checker_plant_caught']
        assert gate['projected_seconds'] < 7200
        assert gate['source_sha256'] == result['source_sha256']
        result['pilot_gate_sha256'] = sha(args.gate)
        result['search'] = search(G, False)
        result['verdict'] = result['search']['verdict']
    elif args.mode == 'pilot':
        result['search'] = search(G, True)
        result['verdict'] = result['search']['verdict']
    else:
        result['verdict'] = 'CONTROLS-PASS'
    result['elapsed_seconds'] = time.perf_counter() - started
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2, sort_keys=True) + '\n')
    print(json.dumps({'verdict': result['verdict'], 'receipt': str(args.output),
                      'controls': result['controls']['counts'],
                      'checked_pairs': result.get('search', {}).get('checked_pairs'),
                      'elapsed_seconds': result['elapsed_seconds']}, sort_keys=True))
    return 0 if result['verdict'] in ['CONTROLS-PASS', 'NO-FIRE-BOUNDED'] else 1


if __name__ == '__main__':
    raise SystemExit(main())
