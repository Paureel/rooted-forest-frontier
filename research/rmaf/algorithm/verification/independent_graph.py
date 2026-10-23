"""Review-specific explicit graph instrument; zero prior oracle code reuse.

Definition: source baseline v2 sec2. Minimal spans are unions of undirected
leaf-to-leaf paths. Rooted topology is a nested graph traversal with unary
vertices suppressed. Connected components after explicit directed edge cuts
generate forests; validity separately checks both original source spans.
Output is finite exact enumeration, never a universal proof.
Shared layers: mathematical definition, frozen literal controls, Python stdlib.
"""
import itertools
from functools import lru_cache


def freeze(x):
    return tuple(freeze(y) for y in x) if isinstance(x, (list, tuple)) else x


def thaw(x):
    return [thaw(y) for y in x] if isinstance(x, tuple) else x


class Graph:
    def __init__(self, tree):
        self.tree = freeze(tree)
        self.labels = {}
        self.children = {}
        self.parent = {}
        self.address = {}
        self.edges = []
        self.root = None
        def build(x, addr):
            node = len(self.children)
            self.children[node] = []
            self.address[addr] = node
            if isinstance(x, int):
                if x in self.labels:
                    raise ValueError('duplicate tree label')
                self.labels[x] = node
            elif isinstance(x, tuple) and len(x) in (1, 2):
                for i, y in enumerate(x):
                    child = build(y, addr + str(i))
                    self.children[node].append(child)
                    self.parent[child] = node
                    self.edges.append((node, child))
            else:
                raise ValueError('malformed rooted tree')
            return node
        if tree is not None:
            self.root = build(self.tree, '')
        self.vertex_label = {v: k for k, v in self.labels.items()}
        self.neighbors = {v: list(ch) for v, ch in self.children.items()}
        for v, p in self.parent.items():
            self.neighbors[v].append(p)
        self._span_cache = {}
        self._topology_cache = {}

    def path(self, a, b):
        pending = [(a, [a])]
        seen = {a}
        while pending:
            v, p = pending.pop()
            if v == b:
                return p
            for w in self.neighbors[v]:
                if w not in seen:
                    seen.add(w)
                    pending.append((w, p + [w]))
        raise ValueError('no path')

    def span(self, block):
        key = frozenset(block)
        if key not in self._span_cache:
            if not key or not key <= self.labels.keys():
                raise ValueError('empty/foreign block')
            leaves = [self.labels[x] for x in sorted(key)]
            vertices = {leaves[0]}
            for leaf in leaves[1:]:
                vertices.update(self.path(leaves[0], leaf))
            self._span_cache[key] = frozenset(vertices)
        return self._span_cache[key]

    def topology(self, block):
        key = frozenset(block)
        if key not in self._topology_cache:
            nodes = self.span(key)
            roots = [v for v in nodes if self.parent.get(v) not in nodes]
            assert len(roots) == 1
            def walk(v):
                if v in self.vertex_label:
                    return ('L', self.vertex_label[v])
                out = [walk(w) for w in self.children[v] if w in nodes]
                if len(out) == 1:
                    return out[0]
                return ('B', tuple(sorted(out, key=repr)))
            self._topology_cache[key] = walk(roots[0])
        return self._topology_cache[key]

    def restrict(self, block):
        def decode(x):
            return x[1] if x[0] == 'L' else tuple(decode(y) for y in x[1])
        return decode(self.topology(block))

    def descendant_labels(self, v):
        if v in self.vertex_label:
            return frozenset([self.vertex_label[v]])
        return frozenset().union(*(self.descendant_labels(w) for w in self.children[v]))

    def cut_partition(self, cuts):
        removed = {frozenset(e) for e in cuts}
        seen, blocks = set(), []
        for start in self.children:
            if start in seen:
                continue
            todo, labels = [start], set()
            seen.add(start)
            while todo:
                v = todo.pop()
                if v in self.vertex_label:
                    labels.add(self.vertex_label[v])
                for w in self.neighbors[v]:
                    if w not in seen and frozenset((v,w)) not in removed:
                        seen.add(w)
                        todo.append(w)
            if labels:
                blocks.append(tuple(sorted(labels)))
        return tuple(sorted(blocks))

    def cherries(self):
        return [tuple(sorted(self.vertex_label[w] for w in ch))
                for ch in self.children.values()
                if len(ch) == 2 and all(w in self.vertex_label for w in ch)]


def valid_graphs(a, b, partition):
    blocks = [tuple(x) for x in partition]
    flat = [v for block in blocks for v in block]
    if a.labels.keys() != b.labels.keys():
        return False, 'tree label mismatch'
    if len(flat) != len(set(flat)):
        return False, 'duplicate forest label'
    if set(flat) != set(a.labels):
        return False, 'missing/foreign forest label'
    if any(not block for block in blocks):
        return False, 'empty block'
    used_a, used_b = set(), set()
    for block in blocks:
        if a.topology(block) != b.topology(block):
            return False, 'wrong rooted topology'
        sa, sb = a.span(block), b.span(block)
        if used_a & sa or used_b & sb:
            return False, 'vertex overlap'
        used_a.update(sa)
        used_b.update(sb)
    return True, 'valid'


def valid(a, b, partition):
    try:
        return valid_graphs(Graph(a), Graph(b), partition)
    except ValueError as e:
        return False, str(e)


def valid_forest(target, sources, partition):
    """Independent state checker, separate source regions per component."""
    ga = Graph(target)
    gs = [Graph(s) for s in sources]
    flat_source = [x for g in gs for x in g.labels]
    if len(flat_source) != len(set(flat_source)) or set(flat_source) != set(ga.labels):
        return False
    flat = [x for block in partition for x in block]
    if len(flat) != len(set(flat)) or set(flat) != set(ga.labels) or any(not b for b in partition):
        return False
    used_t, used_s = set(), [set() for _ in gs]
    for block in partition:
        owners = [i for i,g in enumerate(gs) if set(block) <= set(g.labels)]
        if len(owners) != 1: return False
        i = owners[0]
        a,b=ga.span(block),gs[i].span(block)
        if a & used_t or b & used_s[i] or ga.topology(block)!=gs[i].topology(block): return False
        used_t.update(a); used_s[i].update(b)
    return True


def exact_forest(target, sources):
    """Finite current-forest residual from explicit edge cuts, not original oracle."""
    ga=Graph(target); gs=[Graph(s) for s in sources]
    edges=[(i,e) for i,g in enumerate(gs) for e in g.edges]
    tested=0; seen=set()
    if not gs: return {'residual':0,'optimal':[[]],'tested':1}
    for q in range(len(ga.labels)-len(gs)+1):
        winners=[]
        for cut in itertools.combinations(edges,q):
            by=[[] for _ in gs]
            for i,e in cut: by[i].append(e)
            p=tuple(sorted(block for g,es in zip(gs,by) for block in g.cut_partition(es)))
            tested+=1
            if len(p)!=len(gs)+q or p in seen: continue
            seen.add(p)
            if valid_forest(target,sources,p): winners.append(p)
        if winners: return {'residual':q,'optimal':[thaw(x) for x in winners],'tested':tested}
    raise AssertionError('no singleton forest')


def exact(a, b, containing=None, required_refinement=None):
    """Search actual edge cut components by increasing charge; collect all optima."""
    ga, gb = Graph(a), Graph(b)
    if ga.labels.keys() != gb.labels.keys():
        raise ValueError('tree label mismatch')
    if not ga.labels:
        return {'components': 0, 'cuts': 0, 'optimal': [[]], 'cutsets_tested': 1}
    seen, tested = set(), 0
    for q in range(len(gb.labels)):
        opt = []
        for cuts in itertools.combinations(gb.edges, q):
            partition = gb.cut_partition(cuts)
            tested += 1
            if len(partition) != q + 1 or partition in seen:
                continue
            seen.add(partition)
            if containing and not any(set(containing) <= set(block) for block in partition):
                continue
            if required_refinement and not all(any(set(block) <= set(outer) for outer in required_refinement) for block in partition):
                continue
            if valid_graphs(ga, gb, partition)[0]:
                opt.append(partition)
        if opt:
            return {'components': q+1, 'cuts': q, 'optimal': [thaw(x) for x in sorted(opt)], 'cutsets_tested': tested}
    raise AssertionError('singleton forest not found')


def predicate(a, b, cherry):
    ga, gb = Graph(a), Graph(b)
    path = gb.path(*(gb.labels[x] for x in cherry))
    pathnodes = set(path)
    pendants = [e for e in gb.edges if e[0] in pathnodes and e[1] not in pathnodes]
    blocks = gb.cut_partition(pendants)
    t = len(pendants)
    common = set(ga.cherries()) & set(gb.cherries())
    rule4 = t == 2 and any(len(gb.descendant_labels(v)) == 1 and any(tuple(sorted([next(iter(gb.descendant_labels(v))), x])) in gb.cherries() for x in cherry) for _,v in pendants)
    disjoint = True
    used = set()
    for block in blocks:
        span = ga.span(block)
        if used & span:
            disjoint = False
        used.update(span)
    homeo = [ga.topology(block) == gb.topology(block) for block in blocks]
    return {'t': t, 'step2a': t == 1, 'step2b': t >= 3, 'step2c': rule4,
            'step2d': t == 2 and disjoint and sum(homeo) >= 2,
            'common': sorted(common), 'blocks': thaw(blocks),
            'pendants': [sorted(gb.descendant_labels(v)) for _,v in pendants],
            'blocks_disjoint_T': disjoint, 'homeomorphic': homeo}


def priority(a, b):
    ga, gb = Graph(a), Graph(b)
    rows = [predicate(a,b,c) for c in ga.cherries()] + [predicate(b,a,c) for c in gb.cherries()]
    common = set(ga.cherries()) & set(gb.cherries())
    excluded = not common and not any(any(row[k] for k in ['step2a','step2b','step2c','step2d']) for row in rows)
    return {'common': sorted(common), 'rows': rows, 'excluded_2a_to_2d': excluded}
