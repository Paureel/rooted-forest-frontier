#!/usr/bin/env python3
"""One-shot literal fixture writer; no checker/candidate imports or evaluations."""
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
T = [[[0, 1], 2], [3, 4]]
U = [[[0, 2], 1], [3, 4]]
S = [[0, 1], 2]
C = [0, 0, 1, 1, 1]
M = [0, 1, 0, 1, 1]
rows = []

def add(name, op, data, expected, field, wrong):
    rows.append(dict(id=name, op=op, input=data, expected=expected,
                     false_expectation=dict(field=field, value=wrong)))

add('empty-partition-null', 'partition', {'labels': [], 'blocks': []},
    {'partition': True}, 'partition', False)
add('proper-partition-order-invariant', 'partition',
    {'labels': [0, 1, 2, 3, 4], 'blocks': [[4, 3], [2], [1, 0]]},
    {'partition': True}, 'partition', False)
for name, blocks in [
    ('empty-block', [[0, 1, 2, 3, 4], []]),
    ('duplicate-inside', [[0, 0], [1, 2, 3, 4]]),
    ('duplicate-across', [[0, 1], [1, 2, 3, 4]]),
    ('missing-label', [[0, 1], [2, 3]]),
    ('foreign-label', [[0, 1], [2, 3, 4, 8]])]:
    add(name, 'partition', {'labels': [0, 1, 2, 3, 4], 'blocks': blocks},
        {'partition': False}, 'partition', True)
add('embedding-clean-clades', 'embedding', {'tree': T, 'blocks': [[0, 1, 2], [3, 4]]},
    {'embeddings': True}, 'embeddings', False)
add('embedding-overlap-despite-disjoint-labels', 'embedding',
    {'tree': T, 'blocks': [[0, 2], [1, 3, 4]]},
    {'embeddings': False}, 'embeddings', True)
add('swapped-children-agreement', 'agreement',
    {'left': T, 'right': [[4, 3], [2, [1, 0]]], 'blocks': [[0, 1, 2, 3, 4]]},
    {'proper_inputs': True, 'agreement': True}, 'agreement', False)
add('topology-mismatch-with-disjoint-clades', 'agreement',
    {'left': T, 'right': U, 'blocks': [[0, 1, 2], [3, 4]]},
    {'proper_inputs': True, 'agreement': False}, 'agreement', True)
add('singleton-agreement-clean', 'agreement',
    {'left': T, 'right': U, 'blocks': [[0], [1], [2], [3], [4]]},
    {'proper_inputs': True, 'agreement': True}, 'agreement', False)
add('duplicate-tree-labels-raw-boolean-is-not-instance', 'agreement',
    {'left': [0, 0], 'right': [0, 0], 'blocks': [[0]]},
    {'proper_inputs': False, 'agreement': True}, 'proper_inputs', True)
add('normalization-all-homogeneous-root', 'normalize', {'tree': T, 'colors': [7, 7, 7, 7, 7]},
    {'root_origin': '', 'groups': [['', [0, 1, 2, 3, 4], 7]], 'idempotent': True},
    'idempotent', False)
add('normalization-homogeneous-clades', 'normalize', {'tree': T, 'colors': C},
    {'root_origin': '', 'groups': [['00', [0, 1], 0], ['01', [2], 1], ['1', [3, 4], 1]],
     'idempotent': True}, 'root_origin', '0')
add('normalization-does-not-preserve-every-fine-owner', 'owners',
    {'tree': T, 'colors': C, 'blocks': [[0], [1], [2], [3], [4]]},
    {'monochromatic_groups': True, 'each_group_has_one_owner': False,
     'group_owner_ids': [None, 2, None]}, 'each_group_has_one_owner', True)
add('normalization-owner-transport-clean', 'owners',
    {'tree': T, 'colors': C, 'blocks': [[0, 1], [2], [3, 4]]},
    {'monochromatic_groups': True, 'each_group_has_one_owner': True,
     'group_owner_ids': [0, 1, 2]}, 'each_group_has_one_owner', False)
add('refinement-direction', 'refinement',
    {'F': [[0], [1], [2], [3, 4]], 'Q': [[0, 1], [2], [3, 4]]},
    {'F_refines_Q': True, 'Q_refines_F': False}, 'Q_refines_F', True)
add('refinement-overlap-is-not-containment', 'refinement',
    {'F': [[0, 2], [1], [3, 4]], 'Q': [[0, 1], [2], [3, 4]]},
    {'F_refines_Q': False, 'Q_refines_F': False}, 'F_refines_Q', True)

GOOD = {'actual': True, 'terminal_exact': True, 'connected': True, 'disjoint': True,
        'valid': True, 'leafless_support': False, 'monochromatic': True}
add('mixed-cherry-left-singleton-clean', 'source_partition',
    {'tree': T, 'colors': M, 'blocks': [[0], [1, 3, 4], [2]],
     'supports': 'minimal', 'chosen': [0, 1]},
    {**GOOD, 'chosen_singletons': [True, False]}, 'valid', False)
add('mixed-cherry-right-singleton-clean', 'source_partition',
    {'tree': T, 'colors': M, 'blocks': [[0, 2], [1], [3, 4]],
     'supports': 'minimal', 'chosen': [0, 1]},
    {**GOOD, 'chosen_singletons': [False, True]}, 'valid', False)
add('mixed-alternative-needs-disjoint-supports', 'source_partition',
    {'tree': T, 'colors': M, 'blocks': [[0, 2], [1, 3, 4]],
     'supports': 'minimal', 'chosen': [0, 1]},
    {**GOOD, 'disjoint': False, 'valid': False, 'chosen_singletons': [False, False]},
    'valid', True)
add('leafless-support-satisfies-weak-structure', 'source_partition',
    {'tree': [0, 1], 'colors': [0, 1], 'blocks': [[0], [1]],
     'supports': [['0'], ['1'], ['']], 'chosen': [0, 1]},
    {**GOOD, 'leafless_support': True, 'chosen_singletons': [True, True]},
    'leafless_support', False)
add('support-missing-terminal', 'source_partition',
    {'tree': [0, 1], 'colors': [0, 1], 'blocks': [[0], [1]],
     'supports': [[], ['1']], 'chosen': [0, 1]},
    {**GOOD, 'terminal_exact': False, 'valid': False, 'chosen_singletons': [True, True]},
    'valid', True)
add('support-nonactual-address', 'source_partition',
    {'tree': [0, 1], 'colors': [0, 1], 'blocks': [[0], [1]],
     'supports': [['0', '00'], ['1']], 'chosen': [0, 1]},
    {**GOOD, 'actual': False, 'connected': False, 'valid': False,
     'chosen_singletons': [True, True]}, 'actual', True)
add('support-disconnected', 'source_partition',
    {'tree': T, 'colors': M, 'blocks': [[0, 2], [1], [3, 4]],
     'supports': [['000', '01'], ['001'], ['1', '10', '11']], 'chosen': [0, 1]},
    {**GOOD, 'connected': False, 'valid': False, 'chosen_singletons': [False, True]},
    'connected', True)
add('original-edge-vs-suppressed-edge', 'edges',
    {'tree': S, 'pairs': [['', '01'], ['0', '01'], ['', '1'], ['', '']]},
    {'actual': [False, True, True, False]}, 'actual', [True, True, True, False])
add('cut-one-clade-clean', 'cuts',
    {'tree': S, 'cuts': ['0'], 'partition': [[0, 1], [2]]},
    {'actual_edges': True, 'distinct': True, 'components': 2, 'leafless_components': 0,
     'leaf_regions': [[0, 1], [2]], 'cut_count': 1, 'exact_partition_and_cost': True},
    'exact_partition_and_cost', False)
add('distinct-actual-cuts-leafless-root-trap', 'cuts',
    {'tree': S, 'cuts': ['0', '1'], 'partition': [[0, 1], [2]]},
    {'actual_edges': True, 'distinct': True, 'components': 3, 'leafless_components': 1,
     'leaf_regions': [[0, 1], [2]], 'cut_count': 2, 'exact_partition_and_cost': False},
    'exact_partition_and_cost', True)
add('duplicate-cut-name-trap', 'cuts',
    {'tree': S, 'cuts': ['00', '00'], 'partition': [[0], [1, 2]]},
    {'actual_edges': True, 'distinct': False, 'components': 2, 'leafless_components': 0,
     'leaf_regions': [[0], [1, 2]], 'cut_count': 2, 'exact_partition_and_cost': False},
    'distinct', True)
add('original-root-is-not-edge', 'cuts',
    {'tree': S, 'cuts': [''], 'partition': [[0, 1, 2]]},
    {'actual_edges': False, 'distinct': True, 'components': 1, 'leafless_components': 0,
     'leaf_regions': [[0, 1, 2]], 'cut_count': 1, 'exact_partition_and_cost': False},
    'actual_edges', True)
add('stale-cut-origin-trap', 'cuts',
    {'tree': S, 'cuts': ['000'], 'partition': [[0, 1, 2]]},
    {'actual_edges': False, 'distinct': True, 'components': 1, 'leafless_components': 0,
     'leaf_regions': [[0, 1, 2]], 'cut_count': 1, 'exact_partition_and_cost': False},
    'actual_edges', True)
add('erase-root-entire', 'erase', {'tree': S, 'colors': [0, 0, 1], 'chosen': ''},
    {'root_origin': None, 'groups': []}, 'root_origin', '')
add('erase-unary-retains-surviving-original-origin', 'erase',
    {'tree': S, 'colors': [0, 0, 1], 'chosen': '0'},
    {'root_origin': '1', 'groups': [['1', [2], 1]]}, 'root_origin', '')
add('surviving-owner-not-erased-owner', 'surviving_owner',
    {'tree': S, 'colors': [0, 0, 1], 'chosen': '0', 'blocks': [[0, 1], [2]]},
    {'root_origin': '1', 'surviving_owner': 1, 'original_root_survives': False},
    'surviving_owner', 0)
add('choose-unique-color-before-mixed-cherry', 'choose', {'tree': T, 'colors': C},
    {'kind': 'one', 'origins': ['00']}, 'kind', 'two')
add('choose-mixed-when-no-unique-color', 'choose', {'tree': T, 'colors': M},
    {'kind': 'two', 'origins': ['000', '001']}, 'kind', 'finish')
add('choose-homogeneous-finish', 'choose', {'tree': T, 'colors': [0, 0, 0, 0, 0]},
    {'kind': 'finish', 'origins': []}, 'kind', 'two')
add('choose-unnormalized-homogeneous-cherry-refusal', 'choose',
    {'tree': [[0, 1], [2, 3]], 'colors': [0, 0, 1, 1], 'normalize': False},
    {'kind': 'refuse-unnormalized', 'origins': []}, 'kind', 'two')

def att(name, data, outcome, called, member, unique, edge, next_root, next_groups, patch, wrong):
    add(name, 'attempt', data, {'guard_outcome': outcome, 'child_attempts': 1,
        'continuation_called': called, 'chosen_is_current_group': member,
        'current_origins_unique': unique, 'chosen_origin_is_actual_edge': edge,
        'next_root': next_root, 'next_groups': next_groups}, patch, wrong)

BASE = {'tree': S, 'colors': [0, 0, 1], 'cuts': []}
att('attempt-root-guard', {**BASE, 'group': ['', [0, 1, 2], 0]},
    'root', False, False, True, False, None, [], 'continuation_called', True)
att('attempt-duplicate-guard', {**BASE, 'cuts': ['0'], 'group': ['0', [0, 1], 0]},
    'duplicate', False, True, True, True, None, [], 'continuation_called', True)
att('attempt-whole-current-guard',
    {**BASE, 'current': ['g', '1', [2], 1], 'group': ['1', [2], 1]},
    'entire', False, True, True, True, None, [], 'continuation_called', True)
att('attempt-clean-original-cut', {**BASE, 'group': ['0', [0, 1], 0]},
    'continued', True, True, True, True, '1', [['1', [2], 1]],
    'chosen_is_current_group', False)
att('attempt-stale-valid-edge-not-a-current-group', {**BASE, 'group': ['00', [0], 0]},
    'continued', True, False, True, True, '', [['0', [0, 1], 0], ['1', [2], 1]],
    'chosen_is_current_group', True)
att('attempt-forged-group-metadata-not-guarded', {**BASE, 'group': ['0', [0], 0]},
    'continued', True, False, True, True, '1', [['1', [2], 1]],
    'chosen_is_current_group', True)
att('attempt-duplicate-origin-state',
    {**BASE, 'current': ['n', '', ['g', '0', [0], 0], ['g', '0', [2], 1]],
     'group': ['0', [0], 0]},
    'entire', False, True, False, True, None, [], 'current_origins_unique', True)

add('single-leaf-original-root-agreement', 'agreement',
    {'left': 0, 'right': 0, 'blocks': [[0]]},
    {'proper_inputs': True, 'agreement': True}, 'agreement', False)
add('unique-color-singleton-clean', 'source_partition',
    {'tree': T, 'colors': [0, 1, 2, 1, 1], 'blocks': [[0], [1, 3, 4], [2]],
     'supports': 'minimal', 'chosen': [2, 0]},
    {**GOOD, 'chosen_singletons': [True, True]}, 'chosen_singletons', [False, True])
add('mixed-alternative-needs-monochromatic-partition', 'source_partition',
    {'tree': T, 'colors': M, 'blocks': [[0, 1, 2, 3, 4]],
     'supports': 'minimal', 'chosen': [0, 1]},
    {**GOOD, 'monochromatic': False, 'chosen_singletons': [False, False]},
    'monochromatic', True)

payload = {'scope': 'literal finite controls before integration candidate content',
           'lineage': 'same reviewer, zero additional independent replications',
           'expected_source': 'construction and graph inspection; no checker output used',
           'count': len(rows), 'controls': rows}
dest = HERE / 'CONTROL-PIN.json'
assert not dest.exists()
dest.write_text(json.dumps(payload, indent=2) + '\n')
print(json.dumps({'literal_controls_written': len(rows), 'checker_executed': False}))
