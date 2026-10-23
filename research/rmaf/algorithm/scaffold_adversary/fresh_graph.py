"""One-shot independent scaffold falsifier. No problem evaluator imports.

Trees use immutable nested pairs and frozenset original-label leaf groups.
Graph edges retain disjoint paths of original directed edges through tidying.
"""
from __future__ import annotations
from dataclasses import dataclass
from itertools import combinations
from fractions import Fraction
from copy import deepcopy
import json, hashlib, time


def leaf(x):
    return frozenset(x) if isinstance(x, (set, frozenset, list)) else frozenset([x])


def tree(x):
    if isinstance(x, (int, str, frozenset)):
        return leaf(x)
    if len(x) != 2:
        raise ValueError("binary pair required")
    return canon((tree(x[0]), tree(x[1])))


def labels(t):
    if isinstance(t, frozenset):
        return t
    return labels(t[0]) | labels(t[1])


def key(t):
    if isinstance(t, frozenset):
        return (0, tuple(sorted(t)))
    return (1, key(t[0]), key(t[1]))


def canon(t):
    if isinstance(t, frozenset):
        return t
    a, b = map(canon, t)
    return (a, b) if key(a) <= key(b) else (b, a)


def encode(t):
    if isinstance(t, frozenset):
        return sorted(t)[0] if len(t) == 1 else {"group": sorted(t)}
    return [encode(t[0]), encode(t[1])]


def pkey(parts):
    return tuple(sorted(tuple(sorted(p)) for p in parts))


class Graph:
    def __init__(self, t):
        self.ch = {}
        self.group = {}
        self.lift = {}
        self.roots = set()
        self.cut_history = []
        self.tidy_history = []
        self.nextid = 0
        def visit(u):
            v = self.nextid
            self.nextid += 1
            self.ch[v] = []
            if isinstance(u, frozenset):
                self.group[v] = u
            else:
                for q in u:
                    w = visit(q)
                    self.ch[v].append(w)
                    self.lift[v, w] = ((v, w),)
            return v
        self.roots.add(visit(t))
        self.original_edges = tuple(sorted(self.lift))
        self.original_tree = t

    def clone(self):
        return deepcopy(self)

    def parent(self):
        return {w:v for v, cs in self.ch.items() for w in cs}

    def descendants(self, v):
        out = set()
        stack = [v]
        while stack:
            w = stack.pop()
            out.add(w)
            stack.extend(self.ch[w])
        return out

    def labs(self, v):
        return frozenset().union(*(self.group.get(w, frozenset()) for w in self.descendants(v)))

    def nested(self, v):
        if v in self.group:
            return self.group[v]
        cs = self.ch[v]
        if len(cs) == 1:
            return self.nested(cs[0])
        if len(cs) != 2:
            raise ValueError(("nonbinary live node", v, cs))
        return canon(tuple(self.nested(w) for w in cs))

    def forest(self):
        return tuple(sorted((self.nested(r) for r in self.roots), key=key))

    def partition(self):
        return pkey(self.labs(r) for r in self.roots)

    def tidy(self):
        changed = True
        while changed:
            changed = False
            pa = self.parent()
            for v in sorted(self.ch):
                if v in self.group:
                    continue
                cs = self.ch[v]
                if not cs:
                    if v in pa:
                        p = pa[v]
                        self.ch[p].remove(v)
                        self.lift.pop((p, v))
                    self.roots.discard(v)
                    del self.ch[v]
                    self.tidy_history.append({"remove_unlabelled":v})
                    changed = True
                    break
                if len(cs) == 1:
                    w = cs[0]
                    if v in pa:
                        p = pa[v]
                        paths = self.lift.pop((p,v)) + self.lift.pop((v,w))
                        self.ch[p][self.ch[p].index(v)] = w
                        self.lift[p,w] = paths
                    else:
                        self.roots.remove(v)
                        self.roots.add(w)
                        self.lift.pop((v,w))
                    del self.ch[v]
                    self.tidy_history.append({"suppress_unary":v,"child":w})
                    changed = True
                    break
        return self

    def cut(self, edge):
        v, w = edge
        path = self.lift.pop(edge)
        actual = min(path)
        self.ch[v].remove(w)
        self.roots.add(w)
        self.cut_history.append(actual)
        self.tidy()
        return actual

    def cut_original(self, edge):
        for e, path in self.lift.items():
            if edge in path:
                return self.cut(e)
        raise ValueError(("not a live source edge", edge))

    def contract(self, v):
        if v in self.group:
            return
        group = self.labs(v)
        remove = self.descendants(v) - {v}
        for w in remove:
            self.ch.pop(w)
            self.group.pop(w, None)
            self.roots.discard(w)
        self.lift = {e:p for e,p in self.lift.items() if e[0] not in remove|{v} and e[1] not in remove}
        self.ch[v] = []
        self.group[v] = group
        self.tidy_history.append({"contract":v,"labels":sorted(group)})

    def remove_component(self, root):
        remove = self.descendants(root)
        self.roots.remove(root)
        for w in remove:
            self.ch.pop(w)
            self.group.pop(w, None)
        self.lift = {e:p for e,p in self.lift.items() if e[0] not in remove and e[1] not in remove}


def restriction(g, subset, root=None):
    wanted = frozenset(subset)
    def rec(v):
        if v in g.group:
            z = g.group[v] & wanted
            return z if z else None
        a = [z for w in g.ch[v] if (z := rec(w)) is not None]
        return None if not a else a[0] if len(a)==1 else canon(tuple(a))
    if root is not None:
        return rec(root)
    vals = [z for r in sorted(g.roots) if (z:=rec(r)) is not None]
    if len(vals) > 1:
        raise ValueError("restriction crosses source components")
    return vals[0] if vals else None


def span(g, subset):
    wanted = frozenset(subset)
    pa = g.parent()
    hits = [v for v,s in g.group.items() if s & wanted]
    if not hits:
        return frozenset()
    paths = []
    for v in hits:
        q = [v]
        while q[-1] in pa:
            q.append(pa[q[-1]])
        paths.append(q)
    common = set(paths[0]).intersection(*map(set,paths[1:]))
    if not common:
        raise ValueError("span crosses forest components")
    lca = next(v for v in paths[0] if v in common)
    return frozenset(v for p in paths for v in p[:p.index(lca)+1])


def partition_af(target, source, parts, details=False):
    parts = [frozenset(p) for p in parts]
    full = frozenset().union(*(target.group.values()))
    if frozenset().union(*parts) != full or sum(map(len,parts)) != len(full):
        return (False,"label_coverage") if details else False
    occupied = [set(),set()]
    for p in parts:
        shapes = []
        for i,g in enumerate((target,source)):
            try:
                sh = restriction(g,p)
                sp = span(g,p)
            except ValueError:
                return (False,"cross_component") if details else False
            if occupied[i] & sp:
                return (False,"span_overlap") if details else False
            occupied[i].update(sp)
            shapes.append(sh)
        if shapes[0] != shapes[1]:
            return (False,"topology") if details else False
    return (True,"agreement_forest") if details else True


def terminal(target, source):
    return partition_af(target,source,[source.labs(r) for r in source.roots],details=True)


def pretest(target, source):
    attempts = []
    ok, why = terminal(target, source)
    attempts.append({"cuts":[],"terminal":ok,"reason":why})
    if ok:
        return {"solved":True,"q":0,"witness":[],"attempts":attempts}
    for e in sorted(source.lift):
        s = source.clone()
        actual = s.cut(e)
        ok,why = terminal(target,s)
        attempts.append({"cuts":[list(actual)],"terminal":ok,"reason":why,"partition":s.partition()})
        if ok:
            return {"solved":True,"q":1,"witness":[list(actual)],"attempts":attempts}
    return {"solved":False,"q":None,"witness":None,"attempts":attempts}


def monochrom(g,v,colors):
    return len({colors[a] for a in g.labs(v)}) == 1


def colored_core(source, colors, omit_second=False):
    """Source-only generator frozen before candidate-source contact."""
    if len(source.roots) != 1:
        raise ValueError("one source component required")
    out = []
    def go(g, done, cuts, history):
        # Saturated homogeneous cherry contractions.
        while True:
            cherries = [v for v,cs in g.ch.items() if len(cs)==2 and all(w in g.group for w in cs) and monochrom(g,v,colors)]
            if not cherries:
                break
            v = min(cherries,key=lambda v:tuple(sorted(g.labs(v))))
            labs = sorted(g.labs(v))
            g.contract(v)
            history = history + [{"op":"contract_homogeneous","labels":labs}]
        r = next(iter(g.roots))
        used = {colors[a] for a in g.labs(r)}
        if len(used)==1:
            out.append({"partition":pkey(done+[g.labs(r)]),"cuts":tuple(cuts),"history":history})
            return
        groups = sorted(g.group,key=lambda v:tuple(sorted(g.group[v])))
        counts = {c:sum(colors[next(iter(g.group[v]))]==c for v in groups) for c in used}
        unique = [v for v in groups if counts[colors[next(iter(g.group[v]))]]==1]
        if unique:
            choices = unique[:1]
            op = "unique_color"
        else:
            mixed = [v for v,cs in g.ch.items() if len(cs)==2 and all(w in g.group for w in cs)]
            v = min(mixed,key=lambda v:tuple(sorted(g.labs(v))))
            choices = sorted(g.ch[v],key=lambda w:tuple(sorted(g.group[w])))
            if omit_second:
                choices = choices[:1]
            op = "mixed_cherry"
        for v in choices:
            h = g.clone()
            labs = h.group[v]
            p = h.parent()[v]
            actual = h.cut((p,v))
            h.remove_component(v)
            go(h,done+[labs],cuts+[actual],history+[{"op":op,"labels":sorted(labs),"actual_edge":list(actual)}])
    go(source.clone(),[],[],[])
    dedup = {}
    for row in out:
        p = row["partition"]
        score = (len(set(row["cuts"])),tuple(sorted(set(row["cuts"]))))
        if p not in dedup or score < dedup[p][0]:
            dedup[p] = score,row
    result = []
    for p,(_,row) in sorted(dedup.items()):
        s = source.clone()
        for e in row["cuts"]:
            s.cut_original(e)
        if s.partition()!=p:
            raise AssertionError(("cut realization",p,s.partition(),row))
        row["charge"] = len(set(row["cuts"]))
        if row["charge"] != len(p)-1:
            raise AssertionError("nonredundant source cuts")
        result.append(row)
    return result


def refines(fine, coarse):
    return all(any(set(a)<=set(b) for b in coarse) for a in fine)


def mass(charges,c=Fraction(233,100)):
    return sum((c**(-d) for d in charges),Fraction())


def exact_charge(cuts, claimed):
    return len(set(tuple(e) for e in cuts)) == claimed


def jsonable(x):
    if isinstance(x,Fraction):
        return str(x)
    if isinstance(x,(set,frozenset)):
        return sorted(x)
    if isinstance(x,dict):
        return {str(k):jsonable(v) for k,v in x.items()}
    if isinstance(x,(list,tuple)):
        return [jsonable(v) for v in x]
    return x
