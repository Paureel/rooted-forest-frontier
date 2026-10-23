"""Problem-specific triple terminal DP. No imported research implementation.

Run `solver.py input.json`; exact integer counts, backpointer witness, operation
counts. Input class validation is separate from the O(nm) value calculation.
"""
import json
import sys


def parse(raw):
    if isinstance(raw, str) and raw:
        return raw, [raw]
    if not isinstance(raw, (list, tuple)) or len(raw) != 2:
        raise ValueError("binary tree required")
    a, la = parse(raw[0])
    b, lb = parse(raw[1])
    if len(set(la + lb)) != len(la + lb):
        raise ValueError("duplicate target/source label")
    return (a, b), la + lb


def topology(tree, labels):
    if isinstance(tree, str):
        return ('L', tree) if tree in labels else None
    a, b = (topology(t, labels) for t in tree)
    if a is None:
        return b
    if b is None:
        return a
    return ('N',) + tuple(sorted((a, b)))


def prepare(raw):
    target, labels = parse(raw['target'])
    if not isinstance(raw['source'], list) or not raw['source']:
        raise ValueError("nonempty source forest required")
    source = [parse(t) for t in raw['source']]
    all_source = [x for _, ls in source for x in ls]
    if len(set(all_source)) != len(all_source):
        raise ValueError("duplicate source label")
    if set(labels) != set(all_source):
        raise ValueError("source and target labels differ")
    states = [None]
    joins = []
    leaf_state = {}
    bad = []
    for color, (component, ls) in enumerate(source):
        is_bad = topology(target, set(ls)) != topology(component, set(ls))
        bad.append(is_bad)
        if is_bad and len(ls) != 3:
            raise ValueError("outside terminal class: incompatible component is not a triple")
        if is_bad:
            start = len(states)
            states.extend((color, mask) for mask in range(1, 7))
            for j, label in enumerate(sorted(ls)):
                leaf_state[label] = start + (1 << j) - 1
            # Exactly six ordered joins: two distinct singleton masks.
            for a in (1, 2, 4):
                for b in (1, 2, 4):
                    if a != b:
                        joins.append((start + a - 1, start + b - 1,
                                      start + (a | b) - 1))
        else:
            idx = len(states)
            states.append((color, 0))
            joins.append((idx, idx, idx))
            for label in ls:
                leaf_state[label] = idx
    return target, labels, source, states, joins, leaf_state, bad


def solve(raw):
    target, labels, source, states, joins, leaf_state, bad = prepare(raw)
    width = len(states)
    inf = len(labels) + 1
    nodes = []
    metrics = dict(state_width=width, states_stored=0, close_scans=0,
                   candidate_transitions=0, join_candidates_per_internal=len(joins),
                   internal_vertices=0, reconstruction_visits=0)

    def visit(t):
        if isinstance(t, str):
            vals = [inf] * width
            vals[leaf_state[t]] = 0
            backs = [None] * width
            backs[leaf_state[t]] = ('leaf', t)
            row = (vals, backs, None, None)
        else:
            left, right = visit(t[0]), visit(t[1])
            lv, rv = nodes[left][0], nodes[right][0]
            lc = min(range(width), key=lambda s: lv[s] + (s != 0))
            rc = min(range(width), key=lambda s: rv[s] + (s != 0))
            lcost, rcost = lv[lc] + (lc != 0), rv[rc] + (rc != 0)
            metrics['close_scans'] += 2 * width
            metrics['internal_vertices'] += 1
            vals, backs = [inf] * width, [None] * width

            def put(s, cost, back):
                metrics['candidate_transitions'] += 1
                if cost < vals[s]:
                    vals[s], backs[s] = cost, back

            put(0, lcost + rcost, ('none', lc, rc))
            for s in range(1, width):
                put(s, lv[s] + rcost, ('left', s, rc))
                put(s, lcost + rv[s], ('right', lc, s))
            for a, b, out in joins:
                put(out, lv[a] + rv[b], ('join', a, b))
            row = (vals, backs, left, right)
        nodes.append(row)
        metrics['states_stored'] += width
        return len(nodes) - 1

    root = visit(target)
    rv = nodes[root][0]
    winner = min(range(width), key=lambda s: rv[s] + (s != 0))
    best = rv[winner] + (winner != 0)
    blocks = []

    def new_region():
        blocks.append([])
        return len(blocks) - 1

    def recover(node, state, region=None):
        metrics['reconstruction_visits'] += 1
        if state and region is None:
            region = new_region()
        _, backs, left, right = nodes[node]
        back = backs[state]
        if back[0] == 'leaf':
            blocks[region].append(back[1])
            return
        mode, ls, rs = back
        recover(left, ls, region if mode in ('left', 'join') else None)
        recover(right, rs, region if mode in ('right', 'join') else None)

    recover(root, winner)
    assert best == len(blocks)
    assert metrics['reconstruction_visits'] == 2 * len(labels) - 1
    internal = metrics['internal_vertices']
    expected = internal * (1 + 2 * (width - 1) + len(joins))
    assert metrics['candidate_transitions'] == expected
    return dict(components=best, additional_cuts=best-len(source),
                partition=blocks, bad_components=sum(bad), metrics=metrics)


if __name__ == '__main__':
    with open(sys.argv[1]) as f:
        print(json.dumps(solve(json.load(f)), indent=2))
