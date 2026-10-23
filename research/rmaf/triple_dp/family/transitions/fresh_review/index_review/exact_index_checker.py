#!/usr/bin/env python3
"""One-shot fresh index review: tagged equivalence classes, no author imports.
Known-answer JSON tests exact output order/counts. Deliberate survivor coalescing
must fail the class validator; a clean twin must pass. No geometry is modeled.
"""
import argparse
import hashlib
import json
from pathlib import Path
import time

HERE = Path(__file__).resolve().parent
CONTROLS = HERE.parents[1] / 'index_route/controls.json'


def input_errors(case):
    errors = []
    for side in ['left', 'right']:
        values = case[side]
        if len(set(values)) != len(values): errors.append(side + ':duplicate')
        if case[side + '_boundary'] not in values: errors.append(side + ':boundary-absent')
    return errors


def atoms(case):
    return [('L', value) for value in case['left']] + [('R', value) for value in case['right']]


def quotient(case):
    assert not input_errors(case), input_errors(case)
    components = [{atom} for atom in atoms(case)]
    boundary_atoms = {('L', case['left_boundary']), ('R', case['right_boundary'])}
    # Unite exactly one left atom and one right atom. All remaining classes
    # retain source traversal order, independently of source boundary position.
    merged = set()
    survivors = []
    for component in components:
        if component & boundary_atoms:
            merged |= component
        else:
            survivors.append(component)
    return [merged] + survivors


def partition_errors(case, components):
    errors = []
    original = set(atoms(case))
    flattened = [atom for component in components for atom in component]
    if set(flattened) != original: errors.append('incomplete or foreign source atoms')
    if len(flattened) != len(set(flattened)): errors.append('duplicate source atom ownership')
    boundary_atoms = {('L', case['left_boundary']), ('R', case['right_boundary'])}
    if not components or components[0] != boundary_atoms: errors.append('wrong boundary class')
    for component in components[1:]:
        if len(component) != 1: errors.append('survivor class is not singleton')
        if component & boundary_atoms: errors.append('boundary duplicated among survivors')
    return errors


def names(components):
    assert len(components[0]) == 2
    output = ['M']
    for component in components[1:]:
        assert len(component) == 1
        side, value = next(iter(component))
        output.append(side + ':' + value)
    return output


def counts(components):
    return {'blocks': len(components), 'closed': sum(1 for component in components[1:])}


def check_positive(case):
    components = quotient(case)
    assert not partition_errors(case, components), partition_errors(case, components)
    actual = counts(components)
    assert names(components) == case['expected'], (names(components), case['expected'])
    assert len(names(components)) == len(set(names(components)))
    assert actual['blocks'] == case['blocks']
    assert actual['closed'] == case['closed']
    assert actual['blocks'] == len(case['left']) + len(case['right']) - 1
    assert actual['closed'] == (len(case['left']) - 1) + (len(case['right']) - 1)
    return {'names': names(components), **actual, 'components': [sorted(component) for component in components]}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--pilot', action='store_true')
    parser.add_argument('--false-proposition', action='store_true')
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    start = time.perf_counter()
    data = json.loads(CONTROLS.read_text())
    assert [len(data[key]) for key in ['positive', 'malformed', 'wrong_results', 'lean_controls']] == [5, 3, 4, 3]
    fixtures = {case['id']: case for case in data['positive']}
    rows = []
    for case in data['positive'][:1] if args.pilot else data['positive']:
        rows.append({'kind': 'positive', 'id': case['id'], 'actual': check_positive(case), 'accepted': True})
    if not args.pilot:
        for case in data['malformed']:
            errors = input_errors(case)
            assert errors, case['id']
            clean = check_positive(fixtures[case['clean_twin']])
            rows.append({'kind': 'malformed', 'id': case['id'], 'caught': errors, 'clean_twin': case['clean_twin'], 'clean_actual': clean})
        for case in data['wrong_results']:
            actual = check_positive(fixtures[case['fixture']])[case['field']]
            assert actual != case['wrong']
            assert actual == case['clean']
            rows.append({'kind': 'wrong_number', 'id': case['id'], 'actual': actual, 'wrong_rejected': case['wrong'], 'clean_accepted': case['clean']})
        case = fixtures['same-name-collision']
        clean = quotient(case)
        assert not partition_errors(case, clean)
        # On a copy, replace the two survivor classes by their union.
        bad = [set(clean[0]), set(clean[1]) | set(clean[2])]
        errors = partition_errors(case, bad)
        assert errors == ['survivor class is not singleton'], errors
        rows.append({'kind': 'known_corruption', 'id': 'cross-side-survivor-coalescing', 'caught': errors, 'clean_accepted': True})
        if args.false_proposition:
            assert not partition_errors(case, bad), 'FALSE PROPOSITION: coalescing retained left/right c preserves the required index partition; actual=' + repr(errors)
            raise RuntimeError('false proposition unexpectedly accepted')
    result = {'scope': 'finite index quotient only', 'pilot': args.pilot, 'rows': rows, 'elapsed_seconds': time.perf_counter() - start, 'checker_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(), 'controls_sha256': hashlib.sha256(CONTROLS.read_bytes()).hexdigest()}
    if args.output: args.output.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({'pilot': args.pilot, 'rows': len(rows), 'elapsed_seconds': result['elapsed_seconds'], 'passed': True}))


if __name__ == '__main__': main()
