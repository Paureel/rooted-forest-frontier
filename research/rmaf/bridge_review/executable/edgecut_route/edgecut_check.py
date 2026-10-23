#!/usr/bin/env python3
"""One-shot exact rMAF review: finite graph edge cuts versus imported Lean source.

This fresh checker implements no rootedSpan/minimalVertices recursion. It builds
the entire input tree graph, deletes edges, and searches their components. Frozen
manual plants and corruption tests precede Lean comparisons. No external packages.
Use ./bootloops-python PATH/edgecut_check.py graph|lean from the workspace root.
Outputs in this directory are exact receipts, not a universal formal proof.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import time
from datetime import datetime, timezone

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[4]
SOURCE = ROOT / 'research/rmaf/lean/RMAF.lean'
PIN = '4960d5be9a5f1eb6b15d11c76130bee5263125631314a4eb2d43d500d5b513a9'
CONTROL_PIN = 'd4f251ce0cdf7de4984b44a4024629c1be3d08518f84c79691eab977504f838b'


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def save(name, obj):
    (HERE / name).write_text(json.dumps(obj, indent=2, sort_keys=True) + '\n')


def controls():
    path = HERE / 'frozen-controls.json'
    assert digest(path) == CONTROL_PIN, 'frozen controls changed'
    return json.loads(path.read_text())


def graph(tree):
    vertices, edges, leaves = set(), set(), {}
    stack = [('', tree)]
    while stack:
        at, branch = stack.pop()
        vertices.add(at)
        if isinstance(branch, int):
            leaves[at] = branch
        else:
            assert len(branch) == 2
            for side in (0, 1):
                child = at + str(side)
                edges.add((at, child))
                stack.append((child, branch[side]))
    return vertices, edges, leaves


def reached(start, vertices, edges):
    adjacent = {v: set() for v in vertices}
    for a, b in edges:
        if a in adjacent and b in adjacent:
            adjacent[a].add(b)
            adjacent[b].add(a)
    seen, todo = {start}, [start]
    while todo:
        vertex = todo.pop()
        for other in adjacent[vertex] - seen:
            seen.add(other)
            todo.append(other)
    return seen


def cut_hull(tree, selected):
    vertices, edges, leaves = graph(tree)
    terminals = {v for v, label in leaves.items() if label in selected}
    support, cut_edges, cuts = set(terminals), set(), []
    for edge in sorted(edges):
        side = reached(edge[0], vertices, edges - {edge})
        left, right = terminals & side, terminals - side
        keep = bool(left) and bool(right)
        cuts.append({'edge': edge, 'side_terminals': sorted(left),
                     'other_terminals': sorted(right), 'keep': keep})
        if keep:
            cut_edges.add(edge)
            support.update(edge)
    return support, cut_edges, terminals, cuts


def is_connected(vertices, edges):
    return not vertices or reached(min(vertices), vertices, edges) == vertices


def assert_equal(actual, expected):
    assert actual == expected, {'missing': sorted(expected - actual),
                                'extra': sorted(actual - expected)}


def graph_stage():
    frozen = controls()
    rows, caught = [], []
    started = time.perf_counter()
    for case in frozen['cases']:
        before = time.perf_counter()
        support, edges, terminals, cuts = cut_hull(case['tree'], case['selected'])
        assert_equal(support, set(case['support']))
        assert is_connected(support, edges)
        rows.append({'id': case['id'], 'support': sorted(support),
                     'terminals': sorted(terminals), 'cuts': cuts,
                     'seconds': time.perf_counter() - before})
    by_id = {c['id']: c for c in frozen['cases']}
    for corruption in frozen['corruptions']:
        case = by_id[corruption['source']]
        good = set(case['support'])
        bad = set(corruption.get('replace', good))
        bad.difference_update(corruption.get('delete', []))
        bad.update(corruption.get('add', []))
        try:
            assert_equal(bad, good)
        except AssertionError as error:
            mismatch = error.args[0]
        else:
            raise AssertionError('corruption escaped equality comparator')
        _, tree_edges, _ = graph(case['tree'])
        connected = is_connected(bad, tree_edges)
        if 'expected_connected' in corruption:
            assert connected is corruption['expected_connected']
        caught.append({'id': corruption['id'], 'bad_support': sorted(bad),
                       'mismatch': mismatch, 'connected': connected,
                       'exact_mismatch_caught': True})
    assert len(rows) == 12 and len(caught) == 3
    receipt = {'stage': 'graph_plants_before_actual_comparison',
               'utc': datetime.now(timezone.utc).isoformat(),
               'control_sha256': CONTROL_PIN, 'code_sha256': digest(Path(__file__)),
               'cases': rows, 'corruptions': caught,
               'case_count': len(rows), 'corruptions_caught': len(caught),
               'seconds': time.perf_counter() - started}
    save('graph-results.json', receipt)
    print(json.dumps({k: receipt[k] for k in ['stage', 'case_count', 'corruptions_caught', 'seconds']}), flush=True)


def lean_tree(tree):
    if isinstance(tree, int):
        return f'(.leaf {tree})'
    return f'(.node {lean_tree(tree[0])} {lean_tree(tree[1])})'


def lean_vertex(vertex):
    return '[' + ', '.join('false' if b == '0' else 'true' for b in vertex) + ']'


def lean_support(vertices):
    return '[' + ', '.join(map(lean_vertex, vertices)) + ']'


PRELUDE = '''import RMAF
open RMAF
namespace FreshEdgeCutControls
def sameSupport (a b : List Vertex) : Bool :=
  a.all (fun v => b.contains v) && b.all (fun v => a.contains v)
def encode (v : Vertex) : String :=
  String.ofList (v.map (fun b => if b then '1' else '0'))
'''


def emit_lean(name, cases, expected_override=None):
    lines = [PRELUDE]
    for case in cases:
        tree = lean_tree(case['tree'])
        selected = repr(case['selected'])
        expected = lean_support(expected_override if expected_override is not None else case['support'])
        identifier = case['id']
        lines.append(f'def {identifier} : Tree := {tree}\n')
        lines.append(f'example : sameSupport (minimalVertices {selected} {identifier}) {expected} = true := by decide\n')
        if expected_override is None:
            lines.append(f'#eval IO.println ("{identifier}\\t" ++ reprStr ((minimalVertices {selected} {identifier}).map encode))\n')
    lines.append('end FreshEdgeCutControls\n')
    path = HERE / name
    path.write_text(''.join(lines))
    return path


def run_lean(label, args, expected_success=True):
    start = time.perf_counter()
    env = dict(os.environ, LEAN_PATH=str(HERE))
    completed = subprocess.run([str(ROOT / 'bootloops-lean'), *map(str, args)],
                               cwd=ROOT, env=env, capture_output=True, text=True,
                               timeout=60)
    seconds = time.perf_counter() - start
    output = completed.stdout + completed.stderr
    (HERE / f'{label}.log').write_text(output)
    result = {'label': label, 'exit_code': completed.returncode, 'seconds': seconds,
              'command': ['bootloops-lean', *map(str, args)], 'log': f'{label}.log'}
    save(f'{label}-timing.json', result)
    print(json.dumps(result), flush=True)
    assert (completed.returncode == 0) is expected_success, output
    if not expected_success:
        assert ('Tactic `decide` proved that the proposition' in output
                and '\nis false' in output), 'failure was not an audited semantic falsehood'
        assert 'unknown identifier' not in output and 'type mismatch' not in output
    return output, result


def lean_stage():
    frozen = controls()
    planted = json.loads((HERE / 'graph-results.json').read_text())
    assert planted['case_count'] == 12 and planted['corruptions_caught'] == 3
    assert digest(SOURCE) == PIN, 'source changed after definition inspection'
    runs = []
    _, version = run_lean('lean-version', ['--version'])
    runs.append(version)
    _, build = run_lean('rmaf-fresh-build', ['-o', HERE / 'RMAF.olean', SOURCE])
    runs.append(build)
    root_case = [c for c in frozen['cases'] if c['id'] == 'root_leaf']
    pilot = emit_lean('Pilot.lean', root_case)
    _, result = run_lean('pilot', [pilot])
    runs.append(result)
    # Single imported leaf case is the startup pilot. Full batch is bounded at
    # 12 hand cases, no enumeration. No numerical extrapolation is asserted.
    save('launch-plan.json', {'pilot_seconds': result['seconds'],
                              'pilot_cases': 1, 'full_cases': 12,
                              'full_timeout_seconds': 60,
                              'enumeration': False,
                              'progress_unit': 'kernel-checked exact support example'})
    complete = emit_lean('ExactControls.lean', frozen['cases'])
    output, result = run_lean('exact-controls', [complete])
    runs.append(result)
    actual = {}
    for line in output.splitlines():
        if '\t' in line:
            identifier, data = line.split('\t', 1)
            actual[identifier] = set(json.loads(data))
    expected_ids = {c['id'] for c in frozen['cases']}
    assert set(actual) == expected_ids, 'actual output case denominator mismatch'
    comparisons = []
    for case in frozen['cases']:
        hull, edges, terminals, _ = cut_hull(case['tree'], case['selected'])
        assert_equal(actual[case['id']], hull)
        assert is_connected(hull, edges)
        comparisons.append({'id': case['id'], 'actual': sorted(actual[case['id']]),
                            'edgecut': sorted(hull), 'exact_equal': True,
                            'nonempty_iff_selected_occurrence': bool(hull) == bool(terminals)})
    by_id = {c['id']: c for c in frozen['cases']}
    for corruption in frozen['corruptions']:
        case = by_id[corruption['source']]
        bad = set(corruption.get('replace', case['support']))
        bad.difference_update(corruption.get('delete', []))
        bad.update(corruption.get('add', []))
        path = emit_lean('False_' + corruption['id'] + '.lean', [case], sorted(bad))
        _, result = run_lean('false-' + corruption['id'], [path], expected_success=False)
        runs.append(result)
    assert digest(SOURCE) == PIN
    save('lean-results.json', {'source_sha256': PIN, 'control_sha256': CONTROL_PIN,
                               'utc': datetime.now(timezone.utc).isoformat(),
                               'cases': comparisons, 'case_count': len(comparisons),
                               'semantic_false_corruptions': 3, 'runs': runs,
                               'source_unchanged': True})
    print('PASS: 12/12 exact edge-cut/source support matches; 3/3 semantic false controls rejected.', flush=True)


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('stage', choices=['graph', 'lean'])
    stage = parser.parse_args().stage
    graph_stage() if stage == 'graph' else lean_stage()
