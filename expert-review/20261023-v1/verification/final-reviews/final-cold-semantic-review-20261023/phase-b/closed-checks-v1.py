"""One-shot independent translation of screened CLOSED body cases only.

Not a full candidate implementation: reaching rejected pretest raises rather than
inventing its branch answer. Primitive value checks do not measure actual RAM
operations. All expected outputs are hand-written in the prior preregistration.
"""
import argparse
import copy
import json
from pathlib import Path


def leaves(t):
    return [t] if type(t) is int else leaves(t[0]) + leaves(t[1])


def vertices(t):
    return [[]] if type(t) is int else [[]] + [[False] + p for p in vertices(t[0])] + [[True] + p for p in vertices(t[1])]


def subtree(t, p):
    if not p:
        return t
    return None if type(t) is int else subtree(t[int(p[0])], p[1:])


def restrict(xs, t):
    if type(t) is int:
        return t if t in xs else None
    a, b = restrict(xs, t[0]), restrict(xs, t[1])
    return b if a is None else a if b is None else [a, b]


def shape(a, b):
    if type(a) is int or type(b) is int:
        return type(a) is int and type(b) is int and a == b
    return (shape(a[0], b[0]) and shape(a[1], b[1])) or (shape(a[0], b[1]) and shape(a[1], b[0]))


def rooted(xs, t):
    if type(t) is int:
        return [[]] if t in xs else []
    a, b = rooted(xs, t[0]), rooted(xs, t[1])
    return [] if not a and not b else [[]] + [[False] + p for p in a] + [[True] + p for p in b]


def minimal(xs, t):
    if type(t) is int:
        return [[]] if t in xs else []
    a, b = rooted(xs, t[0]), rooted(xs, t[1])
    if not a:
        return [[True] + p for p in minimal(xs, t[1])]
    if not b:
        return [[False] + p for p in minimal(xs, t[0])]
    return [[]] + [[False] + p for p in a] + [[True] + p for p in b]


def partition(xs, fs):
    flat = sum(fs, [])
    return all(fs) and all(flat.count(x) == 1 for x in xs) and all(x in xs for x in flat)


def pairwise(t, fs):
    return all(all(p not in minimal(c, t) for p in minimal(b, t)) for i, b in enumerate(fs) for c in fs[i+1:])


def agrees(t, s, fs):
    tests = []
    for b in fs:
        a, c = restrict(b, t), restrict(b, s)
        tests.append(a is not None and c is not None and shape(a, c))
    return partition(leaves(t), fs) and partition(leaves(s), fs) and all(tests) and pairwise(t, fs) and pairwise(s, fs)


def proper(t, s, trace):
    trace.append('proper')
    a, b = leaves(t), leaves(s)
    return len(set(a)) == len(a) and len(set(b)) == len(b) and sorted(a) == sorted(b)


def forest(s, cut, trace):
    trace.append('forest')
    if cut is None:
        return [leaves(s)]
    below = leaves(subtree(s, cut))
    return [below, [x for x in leaves(s) if x not in leaves(subtree(s, cut))]]


def pretest(t, s, trace):
    if not proper(t, s, trace):
        return 'refused', None
    candidates = [None] + vertices(s)[1:]

    def best(cs):
        if not cs:
            return None
        x = cs[0]
        valid = agrees(t, s, forest(s, x, trace))
        tail = best(cs[1:])
        if not valid:
            return tail
        if tail is None or int(x is not None) <= int(tail[0] is not None):
            return (x,)
        return tail

    found = best(candidates)
    return ('rejected', None) if found is None else ('found', found[0])


def query(q, t, s, trace):
    trace.append('query:' + str(q))
    if not proper(t, s, trace):
        return None
    status, cut = pretest(t, s, trace)
    if status == 'refused':
        return None
    if status == 'rejected':
        raise RuntimeError('UNIMPLEMENTED_REJECTED_PRETEST: closed scope exceeded')
    f = forest(s, cut, trace)  # intentionally before affordability
    return f if int(cut is not None) <= q else None


def groups(g):
    return [g] if g['kind'] == 'leaf' else groups(g['left']) + groups(g['right'])


def gleaf(p, xs, c):
    return {'kind': 'leaf', 'origin': p, 'labels': xs, 'color': c}


def gnode(p, a, b):
    return {'kind': 'node', 'origin': p, 'left': a, 'right': b}


def build(t, p, fs, colors):
    if type(t) is int:
        colors.append(t)
        color = next((b[0] if b else 0 for b in fs if t in b), 0)
        return gleaf(p, [t], color)
    return gnode(p, build(t[0], p + [False], fs, colors), build(t[1], p + [True], fs, colors))


def normalize(g):
    if g['kind'] == 'leaf':
        return copy.deepcopy(g)
    a, b = normalize(g['left']), normalize(g['right'])
    if a['kind'] == b['kind'] == 'leaf' and a['color'] == b['color']:
        return gleaf(g['origin'], a['labels'] + b['labels'], a['color'])
    return gnode(g['origin'], a, b)


def mixed(g):
    if g['kind'] == 'leaf':
        return None
    a, b = mixed(g['left']), mixed(g['right'])
    return (g['left'], g['right']) if g['left']['kind'] == g['right']['kind'] == 'leaf' else a if a is not None else b


def erase(g, p):
    equal = g['origin'] == p
    if g['kind'] == 'leaf':
        return None if equal else copy.deepcopy(g)
    a, b = erase(g['left'], p), erase(g['right'], p)  # eager even if equal
    return None if equal else b if a is None else a if b is None else gnode(g['origin'], a, b)


def receipt(outputs=None, refusals=None, visited=0, attempts=0, pruned=0):
    return {'outputs': outputs or [], 'refusals': refusals or [], 'visited': visited, 'attempts': attempts, 'pruned': pruned}


def run(q, g, detached, cuts):
    g = normalize(g)
    gs, m = groups(g), mixed(g)
    homogeneous = all(x['color'] == gs[0]['color'] for x in gs) if gs else False
    unique = next((x for x in gs if sum(y['color'] == x['color'] for y in gs) == 1), None)
    if not gs:
        return receipt(refusals=['empty current source'], visited=1)
    if homogeneous:
        return receipt(outputs=[{'partition': [x['labels'] for x in detached] + [sum([x['labels'] for x in gs], [])], 'cuts': cuts}], visited=1)
    choices = [unique] if unique is not None else list(m) if m is not None else []
    if not choices:
        return receipt(refusals=['no mixed cherry in multicolor source'], visited=1)
    if unique is None and m[0]['color'] == m[1]['color']:
        return receipt(refusals=['unnormalized homogeneous cherry'], visited=1)
    result = receipt(visited=1)
    for chosen in choices:
        contained = chosen['origin'] in cuts
        rest = erase(g, chosen['origin'])
        if not chosen['origin']:
            part = receipt(refusals=['attempt to cut original root'], attempts=1)
        elif contained:
            part = receipt(refusals=['duplicate original source cut'], attempts=1)
        elif rest is None:
            part = receipt(refusals=['attempt removed entire current source'], attempts=1)
        else:
            part = run(q - 1, rest, [chosen] + detached, [chosen['origin']] + cuts) if q > 0 else receipt(pruned=1)
            part['attempts'] += 1
        result['outputs'] += part['outputs']
        result['refusals'] += part['refusals']
        for key in ['visited', 'attempts', 'pruned']:
            result[key] += part[key]
    return result


def optimize(t, s):
    trace, colors, trials = [], [], []
    ok = proper(t, s, trace)
    fuel = len(leaves(t))  # retained even on malformed input
    selected, f, rec = None, None, receipt()
    if ok:
        for q in range(fuel):
            f = query(q, t, s, trace)
            trials.append([q, f is not None])
            if f is not None:
                selected = q
                trace.append('recover')
                assert partition(leaves(s), f) and pairwise(s, f) and len(set(leaves(s))) == len(leaves(s))
                built = build(s, [], f, colors)
                rec = run(min(len(f) - 1, len(leaves(s)) - 1), built, [], [])
                break
    out = rec['outputs'][0] if rec['outputs'] else None
    return {'selected': selected, 'forest': f, 'trials': trials,
            'recovery_partition': out['partition'] if out else None,
            'cuts': out['cuts'] if out else None, 'color_calls': colors,
            'visited': rec['visited'], 'attempts': rec['attempts'],
            'proper_calls': trace.count('proper'), 'forest_builds': trace.count('forest'),
            'trace': trace, 'generator': rec, 'preflight_fuel': fuel,
            'recovery_calls': trace.count('recover')}


def calibration(spec):
    t = [[0, 1], 2]
    values = {'leaves': leaves(t), 'vertices': vertices(t), 'restricted': restrict([0, 2], t),
              'minimal0': minimal([0], t), 'rooted0': rooted([0], t),
              'duplicate_partition': partition(leaves(t), [[0], [0, 1, 2]])}
    results = [{'name': k, 'actual': v, 'expected': spec['positive'][k], 'matched': v == spec['positive'][k]} for k, v in values.items()]
    negatives = {'reverse_vertices': 'EXACT_MISMATCH' if vertices(t)[::-1] != spec['positive']['vertices'] else None,
                 'unit_integer': 'EXACT_MISMATCH' if 10**80 != 10**80 + 1 else None}
    results += [{'name': k, 'actual': v, 'expected': spec['corruptions'][k], 'matched': v == spec['corruptions'][k]} for k, v in negatives.items()]
    return results


def ledger_check(spec):
    slots = [{'index': 0, 'query': ['same', 2], 'returned': None, 'live': False},
             {'index': 1, 'query': ['same', 2], 'returned': None, 'live': True}]
    cells = [(0, slots), (1, []), (2, [slots[0]])]
    labels = lambda rows: [[i, s['index']] for i, ss in rows for s in ss]
    rec, chrono = labels(cells), labels(cells[::-1])
    paid_rec = [[False, [0, 0]], [True, [0, 0]], [True, [0, 1]]]
    paid_chrono = paid_rec[1:] + paid_rec[:1]
    observed = {'recorded': rec, 'chronological': chrono, 'positions': [rec.index(x) for x in chrono],
                'live_occurrences': [[i, s['index']] for i, ss in cells for s in ss if s['live']],
                'paid_recorded': paid_rec, 'paid_chronological': paid_chrono,
                'paid_positions': [paid_rec.index(x) for x in paid_chrono],
                'query_based_collapsed_positions': [0, 0, 0],
                'collapsed_position_diagnostic': 'NOT_INJECTIVE' if len(set([0, 0, 0])) != 3 else None}
    return {'name': 'closed_ledger_helpers', 'actual': observed, 'expected': spec, 'matched': observed == spec}


def main():
    p = argparse.ArgumentParser()
    p.add_argument('--mode', choices=['calibration', 'candidate'], required=True)
    p.add_argument('--spec', type=Path, required=True)
    p.add_argument('--out', type=Path, required=True)
    a = p.parse_args()
    assert not a.out.exists()
    spec = json.loads(a.spec.read_text())
    if a.mode == 'calibration':
        results, denominator = calibration(spec['calibration']), spec['calibration']['denominator']
    else:
        results = []
        for case in spec['cases']:
            observed = optimize(case['T'], case['S'])
            expected = {k: v for k, v in case.items() if k not in ['name', 'T', 'S']}
            compared = {k: observed[k] for k in expected}
            results.append({'name': case['name'], 'actual': observed, 'expected': expected,
                            'matched': compared == expected})
        results.append(ledger_check(spec['ledger']))
        denominator = spec['candidate_denominator']
    matched = sum(r['matched'] for r in results)
    accepted = len(results) == denominator and matched == denominator
    a.out.write_text(json.dumps({'mode': a.mode, 'results': results, 'matched': matched,
                                'denominator': denominator, 'expectations_matched': accepted,
                                'scope': __doc__}, indent=2) + '\n')
    for r in results:
        print(json.dumps({'name': r['name'], 'matched': r['matched']}))
    print(f'CLOSED_CHECK_EXPECTATIONS mode={a.mode} matched={matched}/{denominator}')
    return 0 if accepted else 1


if __name__ == '__main__':
    raise SystemExit(main())
