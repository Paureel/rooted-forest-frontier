"""Problem-specific controls and bounded adversarial census; receipts on disk."""
import argparse
import hashlib
import itertools
import json
import pathlib
import time
from functools import lru_cache
import cut_oracle
import solver

HERE = pathlib.Path(__file__).resolve().parent
ROOT = HERE.parent


def atomic(path, data):
    path = pathlib.Path(path)
    temp = path.with_suffix(path.suffix + '.tmp')
    temp.write_text(json.dumps(data, indent=2) + '\n')
    temp.replace(path)


def hashes():
    return {p.name: hashlib.sha256(p.read_bytes()).hexdigest()
            for p in HERE.glob('*') if p.suffix in ('.py', '.json', '.lean')}


def same(a, b):
    if a != b:
        raise AssertionError(f'comparison mismatch: {a!r} != {b!r}')


def check_case(case):
    result = solver.solve(case)
    exact = cut_oracle.solve(case)
    same(result['components'], exact)
    valid = cut_oracle.partitions(case)
    witness = tuple(sorted(tuple(sorted(b)) for b in result['partition']))
    assert witness in valid, 'invalid reconstructed witness'
    same(cut_oracle.proposed_characterization(case), valid)
    return result


def controls():
    start = time.perf_counter()
    fixture = json.loads((HERE / 'controls.json').read_text())
    rows = []
    for case in fixture['positive']:
        result = check_case(case)
        same(result['components'], case['expected_components'])
        rows.append(dict(id=case['id'], status='passed', result=result))
    for case in fixture['malformed']:
        try:
            solver.solve(case)
        except ValueError as e:
            assert case['expected_error'] in str(e), str(e)
            rows.append(dict(id=case['id'], status='caught', reason=str(e)))
        else:
            raise AssertionError('malformed input accepted: ' + case['id'])
    base = next(c for c in fixture['positive'] if c['id'] == 'bad-triple')
    try:
        same(solver.solve(base)['components'], 1)
    except AssertionError as e:
        rows.append(dict(id='wrong-result', status='caught', reason=str(e)))
    else:
        raise AssertionError('wrong-result comparator did not fire')
    base2 = next(c for c in fixture['positive'] if c['id'] == 'good-overlap')
    wrong = (('a', 'b'), ('c', 'd'))
    assert wrong not in cut_oracle.partitions(base2)
    rows.append(dict(id='wrong-witness-overlap', status='caught'))
    merged = (('a', 'b', 'c'),)
    assert merged not in cut_oracle.partitions(base)
    rows.append(dict(id='same-color-merge-claim', status='refuted',
                     reason='One bad color has optimum two; merging gives invalid full triple.'))
    out = dict(status='passed', rows=rows, checks=len(rows), seconds=time.perf_counter()-start,
               hashes=hashes(), scope='Frozen controls only; not universal correctness.')
    atomic(ROOT / 'results/triple-dp-controls.json', out)
    print(json.dumps(dict(mode='controls', checks=len(rows), seconds=out['seconds'])))
    return out


@lru_cache(None)
def trees(labels):
    if len(labels) == 1:
        return (labels[0],)
    out = []
    first, tail = labels[0], labels[1:]
    for mask in range((1 << len(tail)) - 1):
        left = (first,) + tuple(x for i, x in enumerate(tail) if mask >> i & 1)
        right = tuple(x for i, x in enumerate(tail) if not (mask >> i & 1))
        out.extend((a, b) for a in trees(left) for b in trees(right))
    return tuple(out)


def set_partitions(labels):
    if not labels:
        yield ()
        return
    x, *rest = labels
    for p in set_partitions(tuple(rest)):
        yield ((x,),) + p
        for i in range(len(p)):
            yield p[:i] + ((x,) + p[i],) + p[i+1:]


def raw_shape(shape):
    return shape[1] if shape[0] == 'leaf' else (raw_shape(shape[1]), raw_shape(shape[2]))


def cases(n, two_triples=False):
    labels = tuple(chr(97+i) for i in range(n))
    for t in trees(labels):
        restrictions = {frozenset(block): raw_shape(shape)
                        for f in cut_oracle.cut_forests(t) for block, shape in f}
        families = [(labels[:3], labels[3:])] if two_triples else set_partitions(labels)
        for p in families:
            options = [trees(tuple(sorted(block))) if len(block) == 3 else
                       (restrictions[frozenset(block)],) for block in p]
            for source in itertools.product(*options):
                yield dict(target=t, source=list(source))


def census(n, limit=None, two_triples=False):
    controls()
    start = time.perf_counter()
    count, histogram, bad_histogram, max_metrics = 0, {}, {}, {}
    checkpoints = []
    for case in cases(n, two_triples):
        result = check_case(case)
        count += 1
        k = result['components']
        histogram[k] = histogram.get(k, 0) + 1
        b = result['bad_components']
        bad_histogram[b] = bad_histogram.get(b, 0) + 1
        for key, val in result['metrics'].items():
            max_metrics[key] = max(max_metrics.get(key, 0), val)
        if count % 100 == 0:
            checkpoints.append(dict(cases=count, seconds=time.perf_counter()-start))
        if limit and count >= limit:
            break
    assert count > 0
    if limit:
        same(count, limit)
    out = dict(status='passed', n=n, limit=limit, two_triples=two_triples,
               compared=count, histogram=histogram, bad_histogram=bad_histogram,
               seconds=time.perf_counter()-start, checkpoints=checkpoints,
               max_metrics=max_metrics, hashes=hashes(),
               scope='Finite discovery comparisons and witness checks; fresh-author proof audit pending.')
    name = f'triple-dp-census-n{n}' + ('-pilot' if limit else '')
    atomic(ROOT / f'results/{name}.json', out)
    print(json.dumps({k:out[k] for k in ('n','compared','seconds','histogram')}))


if __name__ == '__main__':
    p = argparse.ArgumentParser()
    p.add_argument('mode', choices=['controls', 'census'])
    p.add_argument('--n', type=int, default=3)
    p.add_argument('--limit', type=int)
    p.add_argument('--two-triples', action='store_true')
    args = p.parse_args()
    if args.mode == 'controls':
        controls()
    else:
        census(args.n, args.limit, args.two_triples)
