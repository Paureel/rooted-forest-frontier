"""One-shot independent X0 instrument for the pinned geometric merge target.

No old author checker or proof code is imported. Exact undirected BFS paths.
"""
from collections import deque
from itertools import combinations


def decode(tree):
    graph, leaves = {}, {}
    def visit(t, p):
        graph[p] = set()
        if isinstance(t, str):
            leaves[p] = t
        elif isinstance(t, list) and len(t) == 2:
            for bit, child in zip('01', t):
                q = p + bit
                visit(child, q)
                graph[p].add(q)
                graph[q].add(p)
        else:
            raise ValueError('invalid tree')
    visit(tree, '')
    return graph, leaves


def path(graph, source, target):
    queue = deque([source])
    previous = {source: None}
    while queue:
        node = queue.popleft()
        if node == target:
            result = []
            while node is not None:
                result.append(node)
                node = previous[node]
            return result
        for neighbor in sorted(graph[node]):
            if neighbor not in previous:
                previous[neighbor] = node
                queue.append(neighbor)
    raise ValueError('tree disconnected')


def family_errors(f):
    graph, leaves = decode(f['tree'])
    regions = f['regions']
    indices = f.get('indices', list(regions))
    boundary = f.get('boundary')
    errors = []
    if len(indices) != len(set(indices)):
        errors.append({'rule': 'duplicate-index', 'indices': indices})
    if set(indices) != set(regions):
        errors.append({'rule': 'incomplete-indexing', 'indices': indices,
                       'supports': list(regions)})
    if boundary is not None and boundary not in regions:
        errors.append({'rule': 'boundary-index-missing', 'boundary': boundary})
    owners = {v: [] for v in graph}
    for index, raw_support in regions.items():
        support = set(raw_support)
        if not support <= set(graph):
            errors.append({'rule': 'unbounded', 'index': index,
                           'outside': sorted(support - set(graph))})
        if not support & set(leaves):
            errors.append({'rule': 'leafless', 'index': index})
        for node in support & set(graph):
            owners[node].append(index)
        if ('' in support) != (boundary == index):
            errors.append({'rule': 'root-boundary', 'index': index,
                           'owns_root': '' in support, 'boundary': boundary})
        for a, b in combinations(sorted(support & set(graph)), 2):
            required = set(path(graph, a, b))
            if not required <= support:
                errors.append({'rule': 'nonconvex', 'index': index,
                               'endpoints': [a, b],
                               'missing_path': sorted(required - support)})
                break
    for node, indices_at_node in owners.items():
        if len(indices_at_node) > 1:
            errors.append({'rule': 'overlap', 'vertex': node,
                           'indices': indices_at_node})
        if node in leaves and len(indices_at_node) != 1:
            errors.append({'rule': 'leaf-coverage', 'vertex': node,
                           'owners': indices_at_node})
    return errors


def input_errors(left, right):
    errors = []
    for side, f in [('left', left), ('right', right)]:
        errors.extend({'side': side, **e} for e in family_errors(f))
        if f.get('boundary') is None:
            errors.append({'rule': 'merge-boundary-absent', 'side': side})
    return errors


def candidate(left, right):
    """Literal support construction under test, without using expected data."""
    regions = {'M': ['']}
    for tag, bit, f in [('L:', '0', left), ('R:', '1', right)]:
        for index in f.get('indices', list(f['regions'])):
            name = 'M' if index == f['boundary'] else tag + index
            regions.setdefault(name, []).extend(bit + p for p in f['regions'][index])
    return {'tree': [left['tree'], right['tree']], 'regions': regions,
            'indices': list(regions), 'boundary': 'M'}


def facts(f):
    graph, leaves = decode(f['tree'])
    regions = f['regions']
    indices = f.get('indices', list(regions))
    occupied = set().union(*(set(s) for s in regions.values()))
    return {'regions': {k: sorted(set(v)) for k, v in regions.items()},
            'boundary': f['boundary'], 'blocks': len(indices),
            'cost': sum(i != f['boundary'] for i in indices),
            'merged_labels': sorted({leaves[v] for v in regions.get('M', []) if v in leaves}),
            'unused_vertices': sorted(set(graph) - occupied)}


def claim_errors(f, claimed):
    measured = facts(f)
    errors = []
    for field in ['regions', 'boundary', 'blocks', 'cost', 'merged_labels', 'unused_vertices']:
        if field not in claimed:
            continue
        if claimed[field] != measured[field]:
            error = {'rule': 'wrong-claim', 'field': field,
                     'claimed': claimed[field], 'actual': measured[field]}
            if field in ['blocks', 'cost']:
                error['residual_claim_minus_actual'] = claimed[field] - measured[field]
            errors.append(error)
    return errors


def transition_errors(left, right, output):
    errors = input_errors(left, right)
    if errors:
        return errors
    errors = family_errors(output)
    expected_indices = {'M'}
    expected_merged = {''}
    expected_merged_leaves = set()
    _, parent_leaves = decode(output['tree'])
    for bit, tag, f in [('0', 'L:', left), ('1', 'R:', right)]:
        _, child_leaves = decode(f['tree'])
        for index, support in f['regions'].items():
            lifted = {bit + p for p in support}
            lifted_leaves = {bit + p for p in support if p in child_leaves}
            if index == f['boundary']:
                expected_merged |= lifted
                expected_merged_leaves |= lifted_leaves
            else:
                name = tag + index
                expected_indices.add(name)
                actual = set(output['regions'].get(name, []))
                if actual != lifted:
                    errors.append({'rule': 'survivor-support', 'index': name,
                                   'expected': sorted(lifted), 'actual': sorted(actual)})
                if actual & set(parent_leaves) != lifted_leaves:
                    errors.append({'rule': 'survivor-leaves', 'index': name})
    actual_merged = set(output['regions'].get('M', []))
    if actual_merged != expected_merged:
        errors.append({'rule': 'merged-support', 'expected': sorted(expected_merged),
                       'actual': sorted(actual_merged)})
    if actual_merged & set(parent_leaves) != expected_merged_leaves:
        errors.append({'rule': 'merged-leaves'})
    if set(output.get('indices', list(output['regions']))) != expected_indices:
        errors.append({'rule': 'index-retention', 'expected': sorted(expected_indices),
                       'actual': output.get('indices', list(output['regions']))})
    errors.extend(claim_errors(output, {
        'blocks': facts(left)['blocks'] + facts(right)['blocks'] - 1,
        'cost': facts(left)['cost'] + facts(right)['cost'], 'boundary': 'M'}))
    return errors
