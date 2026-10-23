"""One-shot chain ownership cover development; imports dev core and X0 tests.

Four ownership assignments are algorithmic; exact calls only falsify coverage.
Sequential current-component cores retain stage cut addresses and cost. This
is a wrapper for the missing multicore generator, not a new optimum engine.
"""
from develop import *


def signature(blocks):
    return tuple(tuple(b) for b in normalized_blocks(blocks))


def assignment_cover(t, forest, constraints):
    sources=[Tree(raw) for raw in forest]
    states=[{'blocks':[[sorted(f.labels)] for f in sources], 'paid':0,'stages':[]}]
    for source,edge in constraints:
        far=t.below[edge[1]]
        out=[]
        for s in states:
            substates=[s]
            # Splitting one old block never changes any other old block.
            for block in s['blocks'][source]:
                if not set(block)&far or not set(block)-far:
                    continue
                ft=Tree(sources[source].restriction(block))
                new=[]
                for k in core(ft,set(block)&far):
                    pieces,empty=ft.cut_blocks(k)
                    assert not empty and len(pieces)==1+len(k)
                    for prev in substates:
                        nextblocks=[list(bs) for bs in prev['blocks']]
                        nextblocks[source]=[b for b in nextblocks[source] if b!=block]+pieces
                        new.append({'blocks':nextblocks,'paid':prev['paid']+len(k),
                                    'stages':prev['stages']+[{'source':source,'T_edge':edge,
                                      'old_block':block,'old_tree':ft.raw,'cut_edges':k,'new_blocks':pieces}]})
                substates=new
            out+=substates
        states=out
    for s in states:
        s['blocks_by_source']=s['blocks']
        s['blocks']=normalized_blocks([b for bs in s['blocks'] for b in bs])
        assert s['paid']==len(s['blocks'])-len(sources)
    return states


def chain_cover(t,forest,ai,bi,ci,e,f):
    assignments=[('AB',[(bi,e),(ci,f)]),('AC',[(bi,e),(bi,f)]),
                 ('BB',[(ai,e),(ci,f)]),('BC',[(ai,e),(bi,f)])]
    out=[]
    for name,cons in assignments:
        for child in assignment_cover(t,forest,cons):
            child['assignment']=name
            out.append(child)
    return out


def run(raw):
    start=time.perf_counter()
    child=fixture(raw['T'],raw['Tprime'],raw['cherry'])
    assert child['parent_admitted'] and child['three_live'] and not child['common_edges']
    overlaps=child['overlap'];assert len(overlaps)==2
    bi=(set(overlaps[0]['sources']) & set(overlaps[1]['sources'])).pop()
    ai,ci=[i for i in range(3) if i!=bi]
    t=Tree(child['reduced']['T']);forest=child['reduced']['forest_trees']
    ref=forest_to_reference(t,forest)
    spans=[t.span(c) for c in child['reduced']['forest_blocks']]
    assert not spans[ai]&spans[ci]
    ea=span_edges(t,child['reduced']['forest_blocks'][ai]) & span_edges(t,child['reduced']['forest_blocks'][bi])
    ec=span_edges(t,child['reduced']['forest_blocks'][ci]) & span_edges(t,child['reduced']['forest_blocks'][bi])
    rows=[]
    opt=child['reduced_optimum']['optimal_partitions']
    for e,f in product(sorted(ea),sorted(ec)):
        emitted=chain_cover(t,forest,ai,bi,ci,e,f)
        # Deduplicate identical partition children. Further remove branches
        # whose partition strictly refines a cheaper emitted partition.
        unique={signature(x['blocks']):x for x in emitted}
        minimal=[x for x in unique.values() if not any(
            y['paid']<x['paid'] and all(any(set(b)<=set(c) for c in y['blocks']) for b in x['blocks'])
            for y in unique.values())]
        diagonal=[x for x in emitted if x['assignment'] in ['AC','BB']]
        missed=[p for p in opt if not any(all(any(set(b)<=set(c) for c in x['blocks']) for b in p) for x in diagonal)]
        assert all(any(all(any(set(b)<=set(c) for c in x['blocks']) for b in p) for x in minimal) for p in opt)
        for x in minimal:
            z=exact(t,ref,refinement=x['blocks'])
            x['test_only_child_optimum']=z
            x['further_residual']=z['components']-len(x['blocks'])
            x['total_residual']=x['paid']+x['further_residual']
        assert min(x['total_residual'] for x in minimal)==child['residual_optimum']
        vec=[x['paid'] for x in minimal]
        diagvec=[x['paid'] for x in diagonal]
        full=[1,1,*[2+d for d in vec]]
        rows.append({'AB_edge':e,'BC_edge':f,'endpoint_indices':[ai,ci],'middle_index':bi,
                     'raw_count':len(emitted),'unique_count':len(unique),'minimal_count':len(minimal),
                     'children':minimal,'paid_vector':vec,'full_vector':full,
                     'full_mass_at_target':str(sum(Fraction(100,231)**d for d in full)),
                     'diagonal_paid_vector':diagvec,'diagonal_missed_optima':missed,
                     'diagonal_finite_all_optima_covered':not missed})
    return {'fixture':child,'edge_pairs':rows,'elapsed_seconds':time.perf_counter()-start,
            'scope':'Development finite evidence; no universal chain coverage or improved bound proved'}


if __name__=='__main__':
    pin=json.loads((HERE/'CHAIN-PIN-v2.json').read_text())
    out=run(pin)
    out['code_sha256']=hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    out['pin_sha256']=hashlib.sha256((HERE/'CHAIN-PIN-v2.json').read_bytes()).hexdigest()
    (ROOT/'results/algorithm-macro-chain-cover-v1.json').write_text(json.dumps(out,indent=2)+'\n')
    print('Actual chain, residual optimum:',out['fixture']['residual_optimum'])
    for row in out['edge_pairs']:
        print('Edges:',row['AB_edge'],row['BC_edge'],'vector:',row['full_vector'],
              'mass:',row['full_mass_at_target'],'diagonal missed:',len(row['diagonal_missed_optima']))
    print('Elapsed seconds:',out['elapsed_seconds'])
