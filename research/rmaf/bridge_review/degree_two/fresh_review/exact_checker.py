"""One-shot independent nonauthor checker: exact finite unsuppressed tree graphs.
No project imports or current implementation code were read before authoring.
CLI: ./bootloops-python this_file.py ; writes pilot_results.json next to itself.
Output is bounded exact evidence, never universal proof. Frozen fixtures and
mutations must all pass before the small adversarial pilot is considered.
"""
from pathlib import Path
import hashlib, itertools, json, time, datetime, sys
HERE = Path(__file__).resolve().parent
SPEC = json.loads((HERE / 'FROZEN_CONTROLS.json').read_text())

def graph(tree):
    adjacency, leafmap = {}, {}
    def visit(node, p):
        adjacency[p] = set()
        if isinstance(node, int):
            leafmap[p] = node
        else:
            assert isinstance(node, list) and len(node) == 2
            for direction, child in enumerate(node):
                q = p + (bool(direction),)
                visit(child, q)
                adjacency[p].add(q)
                adjacency[q].add(p)
    visit(tree, ())
    return adjacency, leafmap

def selected(tree, block):
    return {p for p, lab in graph(tree)[1].items() if lab in block}

def support(tree, block):
    terminals = selected(tree, block)
    adjacency = graph(tree)[0]
    if not terminals:
        return set()
    anchor = min(terminals)
    answer = {anchor}
    for end in terminals:
        frontier, predecessor = [anchor], {anchor: None}
        for here in frontier:
            if here == end:
                break
            for there in adjacency[here]:
                if there not in predecessor:
                    predecessor[there] = here
                    frontier.append(there)
        p = end
        while p is not None:
            answer.add(p)
            p = predecessor[p]
    return answer

def shape(tree, block):
    if isinstance(tree, int):
        return ('L', tree) if tree in block else None
    children = [shape(x, block) for x in tree]
    children = [x for x in children if x is not None]
    if not children: return None
    if len(children) == 1: return children[0]
    return ('N',) + tuple(sorted(children, key=repr))

def unique(tree):
    labs = list(graph(tree)[1].values())
    return len(labs) == len(set(labs))

def degree(tree, block, v):
    s = support(tree, block)
    return len(graph(tree)[0].get(v, set()) & s) if v in s else 0

def local_premises(t, u, block, v):
    tl, ul = set(graph(t)[1].values()), set(graph(u)[1].values())
    return (unique(t) and unique(u) and bool(block) and len(block) == len(set(block))
        and set(block) <= tl & ul and shape(t, block) == shape(u, block)
        and v in support(t, block) and degree(t, block, v) == 2)

def partition_ok(t, u, blocks, labels=None):
    if not unique(t) or not unique(u): return False
    if labels is None:
        if set(graph(t)[1].values()) != set(graph(u)[1].values()): return False
        labels = set(graph(t)[1].values())
    flat = [x for b in blocks for x in b]
    if set(flat) != set(labels) or len(flat) != len(set(flat)): return False
    if any(not b for b in blocks): return False
    if not set(labels) <= set(graph(t)[1].values()) & set(graph(u)[1].values()): return False
    if any(shape(t,b) != shape(u,b) for b in blocks): return False
    for tree in (t,u):
        spans = [support(tree,b) for b in blocks]
        if any(a & b for a,b in itertools.combinations(spans,2)): return False
    return True

def refinement_ok(t, u, block, v, pieces):
    return (len(pieces) == 2 and partition_ok(t,u,pieces,set(block))
        and all(v not in support(t,b) for b in pieces)
        and all(support(tree,b) <= support(tree,block)
                for tree in (t,u) for b in pieces))

def partitions(labels):
    labels = tuple(labels)
    if not labels:
        yield []
        return
    first, *rest = labels
    for tail in partitions(rest):
        yield [[first]] + [b[:] for b in tail]
        for i in range(len(tail)):
            yield [([first] + b if i == j else b[:]) for j,b in enumerate(tail)]

def optimal(t,u,labels,marks_t=(),marks_u=()):
    good=[]
    for p in partitions(sorted(labels)):
        if partition_ok(t,u,p,labels) and all(
            not (support(tree,b) & set(marks))
            for tree,marks in ((t,marks_t),(u,marks_u)) for b in p):
            good.append(p)
    return min(good,key=len) if good else None

def addresses(x): return sorted([list(p) for p in x])
def addrset(x): return {tuple(p) for p in x}
def trees(labels):
    labels = tuple(labels)
    if len(labels)==1:
        yield labels[0]; return
    first,*rest=labels
    for size in range(len(rest)):
        for c in itertools.combinations(rest,size):
            left=(first,)+c
            right=tuple(x for x in rest if x not in c)
            for a in trees(left):
                for b in trees(right): yield [a,b]

def run():
    start=time.perf_counter()
    results={'started_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
             'controls':[],'mutations':[],'adversary':{},'scope':'bounded exact fixtures and three-label pilot only'}
    def check(name,actual,expected):
        row={'id':name,'actual':actual,'expected':expected,'pass':actual==expected}
        results['controls'].append(row)
        assert row['pass'], row
    fs={f['id']:f for f in SPEC['fixtures']}
    for name in ('root','suppressed'):
        f=fs[name]; t,u,b,v=f['t'],f['u'],f['B'],tuple(f['v'])
        check(name+'.premises',local_premises(t,u,b,v),True)
        check(name+'.support',addresses(support(t,b)),sorted(f['support_t']))
        check(name+'.degree',degree(t,b,v),f['degree'])
        check(name+'.refinement',refinement_ok(t,u,b,v,f['split']),True)
        for side in ('t','u'):
            check(name+'.split_'+side,[addresses(support(f[side],c)) for c in f['split']],f['split_'+side])
        check(name+'.cost',len(f['split'])-1,f['cost'])
    f=fs['global']; t,u=f['t'],f['u']
    check('global.support',addresses(support(t,f['blocks'][0])),sorted(f['support_t_first']))
    check('global.before_valid',partition_ok(t,u,f['blocks']),True)
    check('global.after_valid',partition_ok(t,u,f['refined']),True)
    check('global.before',len(f['blocks']),f['before'])
    check('global.after',len(f['refined']),f['after'])
    check('global.cost',len(f['refined'])-len(f['blocks']),f['cost'])
    f=fs['degree_three']; t,u,b,v=f['t'],f['u'],f['B'],tuple(f['v'])
    check('degree_three.support',addresses(support(t,b)),sorted(f['support_t']))
    check('degree_three.degree',degree(t,b,v),3)
    p=optimal(t,u,b,[v])
    check('degree_three.min_pieces',len(p),3)
    check('degree_three.min_cost',len(p)-1,2)
    check('degree_three.two_piece_exists',any(refinement_ok(t,u,b,v,p) for p in partitions(b)),False)
    for name in ('singleton','empty','absent'):
        f=fs[name]; t,b,v=f['t'],f['B'],tuple(f['v'])
        check(name+'.support',addresses(support(t,b)),sorted(f['support_t']))
        check(name+'.degree',degree(t,b,v),f['degree'])
        check(name+'.premises',local_premises(t,t,b,v),False)
    f=fs['repeated_tree_labels']
    check('repeated_tree.unique',unique(f['t']),False)
    check('repeated_tree.premises',local_premises(f['t'],f['t'],f['B'],()),False)
    f=fs['repeated_selection']
    check('repeated_selection.unique',len(f['B'])==len(set(f['B'])),False)
    check('repeated_selection.premises',local_premises(f['t'],f['t'],f['B'],()),False)
    f=fs['joint_marks']; t,u,b=f['t'],f['u'],f['B']; marks=[tuple(p) for p in f['marks_u']]
    check('joint_marks.degrees',[degree(u,b,v) for v in marks],f['mark_degrees'])
    costs=[]; witnesses=[]
    for ms in ([],marks[:1],marks[1:],marks):
        p=optimal(t,u,b,marks_u=ms); costs.append(len(p)-1); witnesses.append(p)
    check('joint_marks.costs',costs,f['costs_none_first_second_both'])
    results['joint_mark_witnesses']=witnesses
    f=fs['different_outside_labels']; t,u,b,v=f['t'],f['u'],f['B'],tuple(f['v'])
    check('outside_labels.premises',local_premises(t,u,b,v),True)
    check('outside_labels.refinement',refinement_ok(t,u,b,v,f['split']),True)
    # Mutated statements run through the same predicates/comparators as clean twins.
    for m in SPEC['mutations']:
        f=fs[m['fixture']]; t,u,b=f['t'],f['u'],f['B']; v=tuple(f['v'])
        if m['id']=='wrong_degree': accepted=degree(t,b,v)==m['claim_degree']
        elif m['id'] in ('missing_path','wrong_root'): accepted=support(t,b)==addrset(m['claim_support_t'])
        elif m['id']=='cross_tree_address': accepted=(support(t,[0])==support(u,[0]))==m['claim_leaf0_addresses_equal']
        elif m['id']=='overlapping_blocks': accepted=refinement_ok(t,u,b,v,m['claim_split'])
        elif m['id']=='wrong_cost': accepted=len(f['split'])-1==m['claim_cost']
        else: raise AssertionError('unrecognized mutation')
        results['mutations'].append({'id':m['id'],'accepted':accepted,'caught':not accepted})
        assert not accepted, m
    assert len(results['mutations'])==6
    results['control_elapsed_seconds']=time.perf_counter()-start
    pilot_start=time.perf_counter(); considered=0; in_regime=0; failures=[]
    ts=list(trees([0,1,2]))
    for t,u in itertools.product(ts,repeat=2):
        for size in range(1,4):
            for b in itertools.combinations(range(3),size):
                for v in support(t,b):
                    considered+=1
                    if local_premises(t,u,b,v):
                        in_regime+=1
                        if not any(refinement_ok(t,u,b,v,p) for p in partitions(b)):
                            failures.append({'t':t,'u':u,'B':b,'v':v})
                            raise AssertionError(failures[-1])
    results['adversary']={'tree_count':len(ts),'considered':considered,'in_regime':in_regime,'fires':failures,
                         'elapsed_seconds':time.perf_counter()-pilot_start}
    results['status']='PASS'
    results['elapsed_seconds']=time.perf_counter()-start
    results['sha256']={p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in (HERE/'FROZEN_CONTROLS.json',Path(__file__))}
    (HERE/'pilot_results.json').write_text(json.dumps(results,indent=2)+'\n')
    print(json.dumps({'status':results['status'],'controls':len(results['controls']),
                      'mutations':len(results['mutations']),'adversary':results['adversary'],
                      'elapsed_seconds':results['elapsed_seconds']}))
if __name__=='__main__': run()
