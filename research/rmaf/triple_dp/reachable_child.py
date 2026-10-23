"""Post-hoc concrete baseline branch with overlapping incompatible triples.
No safe cover or original-instance optimality claim is made.
"""
import hashlib
import itertools
import json
import pathlib
import time
import cut_oracle
import solver

HERE = pathlib.Path(__file__).resolve().parent


def path_info(tree, a, b):
    children, names, edges = cut_oracle.graph(tree)
    parents = {w:v for v,w in edges}
    by_name = {x:v for v,x in names.items()}
    def ancestry(v):
        out = [v]
        while v in parents:
            v = parents[v]
            out.append(v)
        return out
    aa, bb = ancestry(by_name[a]), ancestry(by_name[b])
    root = next(v for v in bb if v in aa)
    path = set(aa[:aa.index(root)+1] + bb[:bb.index(root)+1])
    off = [(v,w) for v,w in edges if v in path and w not in path]
    def below(v):
        return [names[v]] if v in names else [x for w in children[v] for x in below(w)]
    return dict(vertices=path, off_edges=off, pendant_labels=[below(w) for _,w in off])


def cherries(tree):
    children, names, _ = cut_oracle.graph(tree)
    return [tuple(names[w] for w in c) for c in children if len(c)==2 and all(w in names for w in c)]


def main():
    # New path-count routine gets hand controls before the target instance.
    assert len(path_info((('a','c'),'b'),'a','b')['off_edges']) == 1
    assert len(path_info((('a','b'),'c'),'a','b')['off_edges']) == 0
    assert len(path_info((('a','c'),('b','d')),'a','b')['off_edges']) == 2
    target = (('a','b'),(('c','f'),(('d','g'),('e',('h','x')))))
    source = (('a',(('c','d'),'e')),('x',('b',(('f','g'),'h'))))
    child = dict(target=target, source=[(('c','d'),'e'), (('f','g'),'h'), 'x', ('a','b')])
    counts = [{'tree':'target', 'cherry':c, 't':len(path_info(source,*c)['off_edges'])}
              for c in cherries(target)]
    counts += [{'tree':'source','cherry':c,'t':len(path_info(target,*c)['off_edges'])}
               for c in cherries(source)]
    assert all(r['t']>=2 for r in counts), counts
    selected = path_info(source,'a','b')
    assert len(selected['off_edges']) == 3
    assert {tuple(sorted(x)) for x in selected['pendant_labels']} == {('c','d','e'),('f','g','h'),('x',)}
    start = time.perf_counter()
    answer = solver.solve(child)
    exact = cut_oracle.solve(child)
    assert answer['components'] == exact == 7
    assert answer['additional_cuts'] == 3 and answer['bad_components'] == 2
    assert cut_oracle.check_witness(child, answer['partition'])
    assert cut_oracle.proposed_characterization(child) == cut_oracle.partitions(child)
    def span(labels):
        return set().union(*(path_info(target,labels[0],x)['vertices'] for x in labels[1:]))
    overlap = span('cde') & span('fgh')
    assert overlap
    pair_intersections = [dict(first=list(a), second=list(b),
                               vertices=sorted(span(a) & span(b)))
                          for a in itertools.combinations('cde', 2)
                          for b in itertools.combinations('fgh', 2)]
    assert len(pair_intersections) == 9 and all(x['vertices'] for x in pair_intersections)
    # Original source forest signature is obtained by exactly the three
    # off-path cuts named above; membership is also independently enumerated.
    signature = tuple(sorted(next(f for f in cut_oracle.cut_forests(cut_oracle.freeze(t))
                                   if len(f)==1)[0] for t in child['source']))
    assert signature in cut_oracle.cut_forests(source)
    result = dict(status='passed', source=source, target=target, child=child, result=answer,
                  cherry_path_counts=counts, selected_branch=dict(cherry=['a','b'],t=3,
                    pendant_labels=selected['pendant_labels'],off_edges=selected['off_edges']),
                  incompatible_embedding_overlap_vertices=sorted(overlap),
                  all_nine_cross_color_pair_intersections=pair_intersections,
                  lower_bound_argument='Each bad triple needs at least one cut. With only two cuts total each keeps a pair, but every pair span of cde intersects every pair span of fgh; hence at least three additional cuts.',
                  paid_cuts=3, remaining_optimum_cuts=3, final_components=7,
                  original_instance_optimum='not computed or claimed',
                  seconds=time.perf_counter()-start,
                  locator='Baseline v2 Section 3.2 PDF pp.6–7; Figure 16 step2b p.24',
                  scope='Legal Whidden(t=3) all-pendant-cuts child, with overlapping bad triples. No safe cover or global recurrence improvement.',
                  source_hashes={name:hashlib.sha256((HERE/name).read_bytes()).hexdigest()
                                 for name in ['reachable_child.py','solver.py','cut_oracle.py']})
    (HERE.parent/'results/triple-dp-reachable-overlap-child.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:result[k] for k in ['status','paid_cuts','remaining_optimum_cuts','final_components','seconds']}))


if __name__=='__main__':
    main()
