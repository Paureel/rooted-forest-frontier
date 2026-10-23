#!/usr/bin/env python3
"""One-shot leastness review instrument, written from FROZEN-SPEC before source read.
No previous checker imports. Exact rooted addresses; LCA hull versus intersection
of all connected ambient supersets. Run --max-leaves 2 for pilot, then 5.
The hand-written controls and intentionally broken supports must all be detected.
"""
import argparse, hashlib, itertools, json, time
from pathlib import Path

OUT = Path(__file__).resolve().parent

def addresses(tree):
    nodes, leaves = set(), {}
    pending = [(tree, '')]
    while pending:
        subtree, address = pending.pop()
        nodes.add(address)
        if isinstance(subtree, str):
            leaves[address] = subtree
        else:
            pending.extend([(subtree[0], address+'0'), (subtree[1], address+'1')])
    return nodes, leaves

def terminals(tree, labels):
    return {v for v, label in addresses(tree)[1].items() if label in labels}

def lca_hull(points):
    if not points:
        return set()
    smallest = min(points, key=len)
    depth = 0
    while depth < len(smallest) and len({p[depth:depth+1] for p in points}) == 1:
        depth += 1
    return {p[:i] for p in points for i in range(depth, len(p)+1)}

def connected(vertices):
    if not vertices:
        return False
    reached = {next(iter(vertices))}
    todo = list(reached)
    while todo:
        v = todo.pop()
        for w in (v[:-1], v+'0', v+'1'):
            if w in vertices and w not in reached:
                reached.add(w)
                todo.append(w)
    return reached == vertices

def feasible_supports(ambient, selected):
    optional = sorted(ambient - selected)
    for mask in range(1 << len(optional)):
        support = selected | {v for i, v in enumerate(optional) if mask >> i & 1}
        if connected(support):
            yield support

def intersection_oracle(ambient, selected):
    # No nonempty target is claimed when selected is empty; explicit null convention.
    if not selected:
        return set(), 0
    feasible = list(feasible_supports(ambient, selected))
    assert feasible
    return set.intersection(*feasible), len(feasible)

def properties(ambient, selected, support):
    return dict(ambient=support <= ambient, terminals=selected <= support,
                nonempty=bool(support), connected=connected(support),
                least=all(support <= q for q in feasible_supports(ambient, selected)))

Q = (('a','b'),('c','d'))
FIXTURES = [
 ('crossing',Q,['a','c'],{'00','10'},{'','0','00','1','10'}),
 ('singleton',Q,['a'],{'00'},{'00'}),
 ('siblings',Q,['a','b'],{'00','01'},{'0','00','01'}),
 ('empty',Q,[],set(),set()),
 ('absent',Q,['z'],set(),set()),
 ('root_leaf','a',['a'],{''},{''}),
 ('root_absent','a',['z'],set(),set()),
 ('duplicate_labels',('a','a'),['a'],{'0','1'},{'','0','1'}),
 ('duplicate_selection',Q,['a','a'],{'00'},{'00'}),
 ('duplicate_both',('a','a'),['a','a'],{'0','1'},{'','0','1'}),
 ('deep_suppression',(((('a','b'),'c'),'d'),'e'),['a','b'],{'0000','0001'},{'000','0000','0001'})
]

def controls():
    rows = []
    for name,tree,selection,expected_terminals,expected_hull in FIXTURES:
        ambient,_ = addresses(tree)
        selected = terminals(tree,selection)
        actual = lca_hull(selected)
        oracle,count = intersection_oracle(ambient,selected)
        assert selected == expected_terminals, (name,'terminals',selected)
        assert actual == expected_hull, (name,'hull',actual)
        assert oracle == expected_hull, (name,'intersection',oracle)
        if selected:
            assert all(properties(ambient, selected, actual).values())
        rows.append(dict(id=name,terminals=sorted(selected),hull=sorted(actual),feasible=count))
    corruptions = [
      ('path_deletion', Q,['a','c'],{'','00','1','10'}, {'ambient':True,'terminals':True,'connected':False,'least':True}),
      ('extra_root',Q,['a','b'],{'','0','00','01'}, {'ambient':True,'terminals':True,'connected':True,'least':False}),
      ('invalid_ambient',Q,['a','b'],{'0','00','01','000'}, {'ambient':False,'terminals':True,'connected':True,'least':False}),
      ('missing_terminal',Q,['a','b'],{'0','00'}, {'ambient':True,'terminals':False,'connected':True,'least':True}),
      ('empty_root','a',['a'],set(), {'ambient':True,'terminals':False,'connected':False,'nonempty':False,'least':True}),
      ('collapsed_label',('a','a'),['a'],{'0'}, {'ambient':True,'terminals':False,'connected':True,'least':True})
    ]
    for name,tree,selection,support,expected in corruptions:
        ambient,_ = addresses(tree)
        selected = terminals(tree,selection)
        twin = lca_hull(selected)
        assert all(properties(ambient, selected, twin).values())
        observed = properties(ambient,selected,support)
        assert all(observed[k] == v for k,v in expected.items()), (name,observed,expected)
        assert not all(observed.values()), name
        assert support != twin, (name,'comparison failed to detect mismatch')
        rows.append(dict(id=name,observed=observed,clean_twin='pass'))
    return rows

def shapes(n):
    if n == 1:
        yield None
    for k in range(1,n):
        for a in shapes(k):
            for b in shapes(n-k):
                yield (a,b)

def fill(shape, labels):
    if shape is None:
        return next(labels)
    return (fill(shape[0],labels), fill(shape[1],labels))

def run(bound):
    start = time.monotonic()
    rows = controls()
    milestones=[]
    total=0
    feasible_count=0
    for n in range(1,bound+1):
        before = time.monotonic()
        cases = 0
        for shape in shapes(n):
            for labels in itertools.product('ab',repeat=n):
                tree=fill(shape,iter(labels))
                ambient,_=addresses(tree)
                for selection in ([],['a'],['b'],['a','b'],['a','a'],['a','b','a'],['z']):
                    selected=terminals(tree,selection)
                    hull=lca_hull(selected)
                    oracle,count=intersection_oracle(ambient,selected)
                    assert hull == oracle, (tree,selection,hull,oracle)
                    if selected:
                        assert all(properties(ambient,selected,hull).values())
                    feasible_count+=count
                    cases+=1
        total+=cases
        milestones.append(dict(leaves=n,cases=cases,seconds=time.monotonic()-before))
    result=dict(status='PASS_FINITE_ONLY',max_leaves=bound,control_count=len(rows),
                controls=rows,cases=total,feasible_supports=feasible_count,
                timings=milestones,elapsed_seconds=time.monotonic()-start,
                script_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
    path=OUT/f'lca-check-{bound}.json'
    path.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k!='controls'}))

if __name__ == '__main__':
    parser=argparse.ArgumentParser()
    parser.add_argument('--max-leaves', type=int, required=True)
    run(parser.parse_args().max_leaves)
