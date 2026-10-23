"""One-shot reused original-address graph core; zero additional replications.
Exact class Graph/canonical extraction from the prior immutable own checker.
No partition/minimum/solver imports.
"""
class Graph:
    def __init__(self, tree):
        self.child, self.taxon, self.parent = {}, {}, {}
        def visit(t, v=()):
            if t is None: return
            if isinstance(t, int): self.taxon[v] = t; self.child[v] = []
            else:
                self.child[v] = [v+(0,), v+(1,)]
                for k, x in enumerate(t):
                    self.parent[v+(k,)] = v
                    visit(x, v+(k,))
        visit(tree)
    def labels(self): return [self.taxon[v] for v in sorted(self.taxon)]
    def selected(self, B): return [v for v, x in self.taxon.items() if x in B]
    def hull(self, B):
        vs = self.selected(B)
        if not vs: return set()
        root = vs[0]
        for v in vs[1:]:
            n = 0
            while n < min(len(root), len(v)) and root[n] == v[n]: n += 1
            root = root[:n]
        return {v[:n] for v in vs for n in range(len(root), len(v)+1)}
    def restriction(self, B):
        hull = self.hull(B)
        if not hull: return None
        root = min(hull, key=len)
        def emit(v):
            cs = [c for c in self.child[v] if c in hull]
            if not cs: return self.taxon[v]
            if len(cs) == 1: return emit(cs[0])
            return [emit(c) for c in cs]
        return emit(root)
    def cherry_parent(self, a, b):
        if a == b: return None
        va = [v for v, x in self.taxon.items() if x == a]
        vb = [v for v, x in self.taxon.items() if x == b]
        if len(va) != 1 or len(vb) != 1: return None
        if va[0] and va[0][:-1] == vb[0][:-1]: return va[0][:-1]
        return None
    def contracted(self, a, b, z):
        p = self.cherry_parent(a,b)
        def emit(v):
            if v == p: return z
            if v in self.taxon: return self.taxon[v]
            return [emit(c) for c in self.child[v]]
        return None if not self.child else emit(())

def canonical(t):
    if t is None: return ('empty',)
    if isinstance(t,int): return ('leaf',t)
    return ('node',)+tuple(sorted((canonical(x) for x in t), key=repr))
