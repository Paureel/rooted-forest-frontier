"""One-shot independent oracle for the triple-component completion audit.

Authored before production access. Uses set partitions, rooted-triple signatures,
and explicit unique vertex paths; never enumerates edge-cut subsets.
"""
from functools import lru_cache
from itertools import combinations, product


class Tree:
    def __init__(self, nested):
        self.nodes = set()
        self.leaves = {}
        def visit(t, p):
            self.nodes.add(p)
            if isinstance(t, str) and t:
                if t in self.leaves:
                    raise ValueError('duplicate tree label')
                self.leaves[t] = p
            elif isinstance(t, (list, tuple)) and len(t) == 2:
                visit(t[0], p + (0,))
                visit(t[1], p + (1,))
            else:
                raise ValueError('tree must be a nonempty string or binary node')
        visit(nested, ())
        self.labels = frozenset(self.leaves)
        self.embedding_cache = {}
        self.signature_cache = {}

    @staticmethod
    def meet(p, q):
        i = 0
        while i < min(len(p), len(q)) and p[i] == q[i]:
            i += 1
        return p[:i]

    def path(self, a, b):
        p, q = self.leaves[a], self.leaves[b]
        m = self.meet(p, q)
        return frozenset([p[:i] for i in range(len(m), len(p)+1)] +
                         [q[:i] for i in range(len(m), len(q)+1)])

    def embedding(self, block):
        block = tuple(sorted(block))
        if block not in self.embedding_cache:
            if len(block) == 1:
                vertices = frozenset([self.leaves[block[0]]])
            else:
                vertices = frozenset().union(*(self.path(a, b)
                                              for a, b in combinations(block, 2)))
            self.embedding_cache[block] = vertices
        return self.embedding_cache[block]

    def triples(self, block):
        block = tuple(sorted(block))
        if block not in self.signature_cache:
            signature = []
            for triple in combinations(block, 3):
                pair = max(combinations(triple, 2),
                           key=lambda ab: len(self.meet(self.leaves[ab[0]], self.leaves[ab[1]])))
                other = next(x for x in triple if x not in pair)
                signature.append((pair, other))
            self.signature_cache[block] = tuple(signature)
        return self.signature_cache[block]


@lru_cache(None)
def partitions(labels):
    """Canonical restricted-growth set partitions, independent of tree shape."""
    labels = tuple(labels)
    if not labels:
        return ((),)
    first, rest = labels[0], labels[1:]
    answer = []
    for part in partitions(rest):
        answer.append(((first,),) + part)
        for i, block in enumerate(part):
            answer.append(part[:i] + ((first,) + block,) + part[i+1:])
    return tuple(answer)


def normalize_partition(part):
    if not isinstance(part, (list, tuple)) or not part:
        raise ValueError('partition must be a nonempty list')
    if any(not isinstance(b, (list, tuple)) or not b for b in part):
        raise ValueError('partition blocks must be nonempty lists')
    flat = [x for b in part for x in b]
    if any(not isinstance(x, str) for x in flat) or len(flat) != len(set(flat)):
        raise ValueError('invalid or duplicate partition labels')
    return tuple(sorted(tuple(sorted(b)) for b in part))


class Instance:
    def __init__(self, data):
        if not isinstance(data, dict) or 'target' not in data or 'source' not in data:
            raise ValueError('missing target/source')
        self.target = Tree(data['target'])
        if not isinstance(data['source'], (list, tuple)) or not data['source']:
            raise ValueError('empty source forest')
        self.source = [Tree(t) for t in data['source']]
        self.owner = {}
        for i, tree in enumerate(self.source):
            for leaf in tree.leaves:
                if leaf in self.owner:
                    raise ValueError('duplicate source label')
                self.owner[leaf] = i
        if set(self.owner) != self.target.labels:
            raise ValueError('target/source label mismatch')
        self.labels = tuple(sorted(self.owner))
        self.bad = {i for i, s in enumerate(self.source)
                    if s.triples(s.labels) != self.target.triples(s.labels)}
        self.in_regime = all(len(self.source[i].labels) == 3 for i in self.bad)

    def monochromatic(self, part):
        return all(len({self.owner[x] for x in block}) == 1 for block in part)

    def disjoint(self, part, source=False):
        occupied = set()
        for block in part:
            i = self.owner[block[0]]
            vertices = self.source[i].embedding(block) if source else self.target.embedding(block)
            vertices = {(i, p) for p in vertices} if source else set(vertices)
            if occupied & vertices:
                return False
            occupied |= vertices
        return True

    def valid(self, part):
        flat = [x for block in part for x in block]
        if len(flat) != len(set(flat)) or set(flat) != set(self.labels):
            return False
        if not self.monochromatic(part):
            return False
        if any(self.source[self.owner[b[0]]].triples(b) != self.target.triples(b) for b in part):
            return False
        return self.disjoint(part) and self.disjoint(part, source=True)

    def candidate(self, part):
        if not self.monochromatic(part) or not self.disjoint(part):
            return False
        return not any(self.owner[b[0]] in self.bad and len(b) == 3 for b in part)

    def exact(self, check_characterization=False):
        best = len(self.labels) + 1
        optimum = None
        checked = 0
        for part in partitions(self.labels):
            if not self.monochromatic(part):
                continue
            actual = self.valid(part)
            if check_characterization:
                assert self.in_regime
                guess = self.candidate(part)
                if guess != actual:
                    raise AssertionError({'kind':'characterization','partition':part,
                                          'candidate':guess,'actual':actual})
                checked += 1
            if actual and len(part) < best:
                best, optimum = len(part), part
        assert optimum is not None
        return {'components':best, 'additional_cuts':best-len(self.source),
                'partition':optimum, 'partitions_checked':checked}

    def verify_result(self, result, expected=None):
        part = normalize_partition(result['partition'])
        if not self.valid(part):
            raise AssertionError('returned partition is not an agreement refinement')
        exact = self.exact() if expected is None else expected
        if result['components'] != len(part) or result['components'] != exact['components']:
            raise AssertionError('component optimum/count mismatch')
        if result['additional_cuts'] != len(part)-len(self.source):
            raise AssertionError('cut/component conversion mismatch')
        return True


@lru_cache(None)
def trees(labels):
    """All non-plane binary trees, rooting each split by its smallest leaf."""
    labels = tuple(sorted(labels))
    if len(labels) == 1:
        return (labels[0],)
    answer = []
    for mask in range(1 << (len(labels)-1)):
        left = (labels[0],) + tuple(x for j, x in enumerate(labels[1:]) if mask & (1 << j))
        right = tuple(x for x in labels if x not in left)
        if right:
            answer.extend((a, b) for a, b in product(trees(left), trees(right)))
    return tuple(answer)


def restrict(nested, block):
    if isinstance(nested, str):
        return nested if nested in block else None
    a, b = restrict(nested[0], block), restrict(nested[1], block)
    if a is None:
        return b
    if b is None:
        return a
    return (a, b)


def instances(n):
    labels = tuple(chr(97+i) for i in range(n))
    for target in trees(labels):
        for part in partitions(labels):
            choices = [trees(b) if len(b) <= 3 else (restrict(target, frozenset(b)),) for b in part]
            for source in product(*choices):
                yield {'target':target, 'source':source}
