"""Independent-core, problem-specific oracle: exhaustive graph edge cuts.

No imports from solver.py, existing partition/span code, or previous-work code.
The direct cut-forest semantics and rooted component pruning are separate from
the DP. This oracle is slow and intended only for small discovery comparisons.
"""
from functools import lru_cache
from itertools import product


def freeze(x):
    return tuple(map(freeze, x)) if isinstance(x, list) else x


def graph(raw):
    children, names, edges = [], {}, []

    def add(t):
        v = len(children)
        children.append([])
        if isinstance(t, str) and t:
            if t in names.values():
                raise ValueError('duplicate oracle label')
            names[v] = t
        elif isinstance(t, (tuple, list)) and len(t) == 2:
            for child in t:
                w = add(child)
                children[v].append(w)
                edges.append((v, w))
        else:
            raise ValueError('binary oracle input required')
        return v

    add(raw)
    return children, names, edges


@lru_cache(maxsize=None)
def cut_forests(raw):
    children, names, edges = graph(raw)
    out = {}
    for cut in range(1 << len(edges)):
        adjacency = [set() for _ in children]
        for e, (v, w) in enumerate(edges):
            if not (cut >> e) & 1:
                adjacency[v].add(w)
                adjacency[w].add(v)
        unseen = set(range(len(children)))
        blocks = []
        while unseen:
            v = min(unseen)
            region, stack = set(), [v]
            while stack:
                w = stack.pop()
                if w in region:
                    continue
                region.add(w)
                stack.extend(adjacency[w] - region)
            unseen -= region
            labels = tuple(sorted(names[w] for w in region if w in names))
            if not labels:
                continue
            # Preorder numbering: minimum is this region's highest vertex.
            def shape(w):
                if w in names:
                    return ('leaf', names[w])
                pieces = [shape(z) for z in children[w] if z in region]
                pieces = [p for p in pieces if p is not None]
                if not pieces:
                    return None
                if len(pieces) == 1:
                    return pieces[0]
                return ('branch',) + tuple(sorted(pieces))
            blocks.append((labels, shape(min(region))))
        signature = tuple(sorted(blocks))
        out.setdefault(signature, cut)
    return out


def common_forests(raw):
    target = cut_forests(freeze(raw['target']))
    factors = [cut_forests(freeze(t)) for t in raw['source']]
    source = {tuple(sorted(b for part in combo for b in part))
              for combo in product(*factors)}
    return {sig for sig in target if sig in source}


def solve(raw):
    fs = common_forests(raw)
    if not fs:
        raise ValueError('no common forest')
    return min(map(len, fs))


def partitions(raw):
    return {tuple(sorted(block for block, _ in f)) for f in common_forests(raw)}


def proposed_characterization(raw):
    # Build color labels and identify bad colors independently using whole
    # source topology and the matching target block restriction from cut tables.
    groups = []
    for t in raw['source']:
        _, names, _ = graph(t)
        groups.append(frozenset(names.values()))
    target = cut_forests(freeze(raw['target']))
    bad = set()
    for i, (t, labels) in enumerate(zip(raw['source'], groups)):
        full = next(f[0][1] for f in cut_forests(freeze(t)) if len(f) == 1)
        restricted = {shape for f in target for block, shape in f
                      if frozenset(block) == labels}
        assert len(restricted) == 1
        if full not in restricted:
            assert len(labels) == 3
            bad.add(i)
    accepted = set()
    for f in target:
        valid = True
        for block, _ in f:
            bs = frozenset(block)
            colors = [i for i, ls in enumerate(groups) if bs <= ls]
            if len(colors) != 1 or (colors[0] in bad and len(bs) == 3):
                valid = False
                break
        if valid:
            accepted.add(tuple(sorted(block for block, _ in f)))
    return accepted


def check_witness(raw, blocks):
    """Witness-only direct graph check; never an optimum certificate.

    Computes undirected simple paths and a component's rooted shape separately
    from the DP, without enumerating exponential edge-cut sets.
    """
    def inspect(tree, selected_blocks):
        children, names, edges = graph(tree)
        parent = {w: v for v, w in edges}
        vertex = {label: v for v, label in names.items()}
        used, forms = set(), {}
        for labels in selected_blocks:
            leaves = [vertex[x] for x in labels]
            region = {leaves[0]}
            for endpoint in leaves[1:]:
                first = []
                cursor = leaves[0]
                while True:
                    first.append(cursor)
                    if cursor not in parent:
                        break
                    cursor = parent[cursor]
                second = []
                cursor = endpoint
                while cursor not in first:
                    second.append(cursor)
                    cursor = parent[cursor]
                region.update(second)
                region.update(first[:first.index(cursor)+1])
            if used & region:
                raise ValueError('overlapping witness embeddings')
            used |= region
            def shape(v):
                if v in names:
                    return ('leaf', names[v])
                forms = [shape(w) for w in children[v] if w in region]
                if len(forms) == 1:
                    return forms[0]
                assert len(forms) == 2
                return ('branch',) + tuple(sorted(forms))
            forms[tuple(sorted(labels))] = shape(min(region))
        return forms

    target_labels = set(graph(raw['target'])[1].values())
    flat = [x for block in blocks for x in block]
    if any(not b for b in blocks) or len(flat) != len(set(flat)) or set(flat) != target_labels:
        raise ValueError('invalid witness leaf partition')
    target_forms = inspect(raw['target'], blocks)
    source_forms = {}
    for component in raw['source']:
        labels = set(graph(component)[1].values())
        local = [b for b in blocks if set(b) <= labels]
        if set(x for b in local for x in b) != labels:
            raise ValueError('witness not monochromatic')
        source_forms.update(inspect(component, local))
    if source_forms != target_forms:
        raise ValueError('witness topology mismatch')
    return True
