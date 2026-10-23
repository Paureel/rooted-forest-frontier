"""One-campaign independent reference: leaf partitions and minimal embeddings.
No edge-cut algorithm, protected-edge code, or existing campaign oracle imported.
"""
from itertools import combinations


def normalize(t):
    if isinstance(t, str):
        if t == 'rho':
            raise ValueError('rho is reserved for labelled root')
        return t
    if not isinstance(t, (list, tuple)) or len(t) != 2:
        raise ValueError('binary input required')
    return tuple(normalize(x) for x in t)


def labels(t):
    if isinstance(t, str):
        return [t]
    return labels(t[0]) + labels(t[1])


def validate_pair(t1, t2):
    t1, t2 = normalize(t1), normalize(t2)
    x, y = labels(t1), labels(t2)
    if len(set(x)) != len(x) or len(set(y)) != len(y):
        raise ValueError('duplicate label')
    if set(x) != set(y):
        raise ValueError('different label sets')
    return t1, t2


def partitions(xs):
    if not xs:
        yield ()
        return
    head, *tail = xs
    for p in partitions(tail):
        yield (frozenset([head]),) + p
        for i, block in enumerate(p):
            yield p[:i] + (block | {head},) + p[i+1:]


def index(t):
    """Tree vertices are addresses, with rho at R and original root at ''."""
    parent, leaf = {'R': None, '': 'R'}, {'rho': 'R'}
    def walk(z, a):
        if isinstance(z, str):
            leaf[z] = a
            return
        for j in range(2):
            b = a + str(j)
            parent[b] = a
            walk(z[j], b)
    walk(t, '')
    return parent, leaf


def embedding(parent, leaf, block):
    paths = []
    for x in block:
        v, p = leaf[x], []
        while v is not None:
            p.append(v)
            v = parent[v]
        paths.append(p)
    common = set(paths[0]).intersection(*map(set, paths[1:]))
    top = next(v for v in paths[0] if v in common)
    nodes = set()
    for p in paths:
        nodes.update(p[:p.index(top)+1])
    return nodes


def restriction(t, block):
    def prune(z):
        if isinstance(z, str):
            return ('leaf', z) if z in block else None
        kids = [p for x in z if (p := prune(x)) is not None]
        if not kids:
            return None
        if len(kids) == 1:
            return kids[0]
        return ('fork', tuple(sorted(kids, key=repr)))
    ans = prune(t)
    if 'rho' in block:
        return ('labelled-root-rho', ans)
    return ans


def optimum(t1, t2):
    t1, t2 = validate_pair(t1, t2)
    xs = ['rho'] + sorted(labels(t1))
    idx1, idx2 = index(t1), index(t2)
    data = {}
    for r in range(1, len(xs)+1):
        for combo in combinations(xs, r):
            b = frozenset(combo)
            data[b] = (restriction(t1,b) == restriction(t2,b),
                       embedding(*idx1,b), embedding(*idx2,b))
    best, witness = len(xs), None
    for p in partitions(xs):
        if len(p) >= best:
            continue
        seen1, seen2, valid = set(), set(), True
        for b in p:
            equal, v1, v2 = data[b]
            if not equal or seen1 & v1 or seen2 & v2:
                valid = False
                break
            seen1 |= v1
            seen2 |= v2
        if valid:
            best, witness = len(p), p
    # The singleton partition always exists, including when best stays |X|.
    if witness is None:
        witness = tuple(frozenset([x]) for x in xs)
    return best-1, [sorted(b) for b in witness]
