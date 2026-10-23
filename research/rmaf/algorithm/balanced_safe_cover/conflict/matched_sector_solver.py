#!/usr/bin/env python3
"""Exact polynomial solver for C6 only; no optimization oracle is called.

Arguments are the original unsuppressed Tree objects. Tree and agreement
primitives reside in exact_conflicts.py; importing them does not call its
cutset, partition, distance, or maximum-packing oracles.
"""
from exact_conflicts import Tree, agreement


def labels_below(tree, vertex):
    reverse = {v:a for a,v in tree.leaf.items()}
    stack, labels = [vertex], []
    while stack:
        v = stack.pop()
        if v in reverse:
            labels.append(reverse[v])
        stack.extend(tree.children[v])
    return tuple(sorted(labels))


def solve_matched_sectors(source, target, budget):
    """Return NOT_APPLICABLE, exact budget failure, or a reconstructed optimum.

    This solver recognizes the matched mixed-cherry family from the original
    pair itself. It is not a general safe-cover generator.
    """
    S,T = Tree(source),Tree(target)
    if budget < 0:
        raise ValueError('cut budget must be nonnegative')
    if S.labels != T.labels:
        raise ValueError('common distinct labels required')
    if not S.parent or len(S.labels) < 2:
        if S.t == T.t:
            return {'status':'SOLVED','optimum':0,'precuts':0,'completion':0,
                    'partition':S.cut_partition(0),'source_cuts':[],'cover_cuts':[],'tau':0}
        return {'status':'NOT_APPLICABLE'}
    Aroot,Broot = S.children[0]
    A,B = labels_below(S,Aroot),labels_below(S,Broot)
    a_set,b_set = set(A),set(B)
    reverse = {v:a for a,v in T.leaf.items()}
    pairs, covered = [], set()
    for children in T.children.values():
        if len(children)==2 and all(v in reverse for v in children):
            x,y = (reverse[v] for v in children)
            if (x in a_set)==(y in a_set):
                return {'status':'NOT_APPLICABLE'}
            pairs.append((x,y))
            covered.update((x,y))
    if covered != set(T.labels) or len(A)!=len(B) or len(pairs)!=len(A):
        return {'status':'NOT_APPLICABLE'}
    if S.restrict(A)!=T.restrict(A) or S.restrict(B)!=T.restrict(B):
        return {'status':'NOT_APPLICABLE'}
    m = len(A)
    if m==1:
        return {'status':'SOLVED','optimum':0,'precuts':0,'completion':0,
                'partition':S.cut_partition(0),'source_cuts':[],'cover_cuts':[],'tau':0}
    if budget < m:
        return {'status':'BUDGET_FAILURE','optimum':m,'lower_bound':m}
    # One original root-child edge plus m-1 original A pendant edges.
    cover_mask = 1 << S.edge[Aroot]
    final_mask = cover_mask
    for a in A[1:]:
        final_mask |= 1 << S.edge[S.leaf[a]]
    part = S.cut_partition(final_mask)
    assert final_mask.bit_count()==m and len(part)==m+1
    assert agreement(S,T,part)  # Polynomial witness validation, not optimization.
    return {'status':'SOLVED','optimum':m,'precuts':1,'completion':m-1,
            'cover_partition':S.cut_partition(cover_mask),'partition':part,
            'source_cuts':S.edge_receipt(final_mask),'cover_cuts':S.edge_receipt(cover_mask),
            'tau':0,'terminal_class':'all-compatible'}
