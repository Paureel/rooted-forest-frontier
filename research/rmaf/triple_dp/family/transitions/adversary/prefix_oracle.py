"""One-shot separately implemented prefix/owner route; never imports graph_checker.

Shared author and input convention preclude fresh-author certification.
"""
from itertools import combinations


def table(t):
    pending = [('', t)]
    vertices, labels = [], {}
    while pending:
        address, subtree = pending.pop()
        vertices.append(address)
        if type(subtree) is str:
            labels[address] = subtree
        else:
            if type(subtree) is not list or len(subtree) != 2:
                raise ValueError('not a binary string tree')
            pending.append((address + '1', subtree[1]))
            pending.append((address + '0', subtree[0]))
    return vertices, labels


def errors(f):
    vertices, labels = table(f['tree'])
    regions = f['regions']
    ids = f.get('indices', list(regions.keys()))
    failures = []
    if sorted(ids) != sorted(regions):
        failures.append('index-list')
    if f['boundary'] is not None and f['boundary'] not in ids:
        failures.append('boundary-index')
    counts = {a: 0 for a in vertices}
    for i, entries in regions.items():
        nodes = frozenset(entries)
        if any(a not in vertices for a in nodes):
            failures.append('outside')
        if not any(a in labels for a in nodes):
            failures.append('no-leaf')
        if (i == f['boundary']) != ('' in nodes):
            failures.append('root-owner')
        for a in nodes:
            if a in counts:
                counts[a] += 1
        for a, b in combinations(nodes, 2):
            common = 0
            while common < min(len(a), len(b)) and a[common] == b[common]:
                common += 1
            if any(a[:k] not in nodes for k in range(common, len(a) + 1)):
                failures.append('prefix-gap')
            if any(b[:k] not in nodes for k in range(common, len(b) + 1)):
                failures.append('prefix-gap')
    if any(n > 1 for n in counts.values()):
        failures.append('multiple-owners')
    if any(counts[a] != 1 for a in labels):
        failures.append('leaf-unowned-or-overlap')
    return sorted(set(failures))


def expected(left, right):
    """Scan parent nodes, pull back owners; no lifted support concatenation."""
    if errors(left) or errors(right) or left['boundary'] is None or right['boundary'] is None:
        raise ValueError('invalid merge inputs')
    vertices, labels = table([left['tree'], right['tree']])
    ownership = {'': 'M'}
    for node in vertices:
        if not node:
            continue
        child = left if node[0] == '0' else right
        tag = 'L:' if node[0] == '0' else 'R:'
        names = [i for i, support in child['regions'].items() if node[1:] in support]
        if names:
            i = names[0]
            ownership[node] = 'M' if i == child['boundary'] else tag + i
    partition = {}
    for node, name in ownership.items():
        partition.setdefault(name, []).append(node)
    leaf_classes = {ownership[node] for node in labels}
    return {'regions': {i: sorted(nodes) for i, nodes in partition.items()},
            'boundary': ownership[''], 'blocks': len(leaf_classes),
            'cost': len({name for name in leaf_classes if name != ownership['']}),
            'merged_labels': sorted({label for node, label in labels.items()
                                      if ownership[node] == ownership['']}),
            'unused_vertices': sorted(node for node in vertices if node not in ownership)}
