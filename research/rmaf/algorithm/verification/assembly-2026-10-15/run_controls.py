"""Execute only the frozen finite preparation controls, never author code."""
import argparse,copy,hashlib,json,time
from pathlib import Path
from fractions import Fraction
import instrument as I

HERE=Path(__file__).resolve().parent
ROOT=I.ROOT

def serial(v):
    if isinstance(v,Fraction):return [v.numerator,v.denominator]
    if isinstance(v,set):return sorted(v)
    if isinstance(v,tuple):return list(v)
    raise TypeError(type(v).__name__)

def main():
    parser=argparse.ArgumentParser();parser.add_argument('--stage',choices=['pilot','full'],required=True);a=parser.parse_args()
    freeze=json.loads((HERE/'FREEZE-v1.json').read_text())
    for row in freeze['before_execution_files']:
        assert hashlib.sha256((ROOT/row['path']).read_bytes()).hexdigest()==row['sha256'],row['path']
    C=json.loads((HERE/'CONTROLS-v1.json').read_text());start=time.perf_counter()
    report={'stage':a.stage,'candidate_contact':False,'replication_count_added':0,
            'positive':[],'negative':[],'failures':[]}
    def check(name,actual,expected):
        ok=actual==expected;report['positive'].append({'id':name,'actual':actual,'expected':expected,'pass':ok})
        if not ok:report['failures'].append(name)
    def false(name,actual,forged):
        caught=actual!=forged;report['negative'].append({'id':name,'actual':actual,'false_expectation':forged,'caught':caught})
        if not caught:report['failures'].append('FALSE_CONTROL_NOT_CAUGHT:'+name)
    def rejects(name,fn):
        caught=False;reason=''
        try:fn()
        except (ValueError,TypeError,KeyError) as e:caught=True;reason=str(e)
        report['negative'].append({'id':name,'caught':caught,'reason':reason})
        if not caught:report['failures'].append('CORRUPTION_NOT_CAUGHT:'+name)

    H=C['hard_parent'];route,edges=I.pendant_edges(H['source'],H['a'],H['b'])
    check('hard-original-path',route,H['path']);check('hard-fixed-edges-before-F',edges,H['pendant_cuts'])
    check('actual-target-cherry',I.cherry(H['target'],H['target_cherry'],H['a'],H['b']),True)
    false('wrong-target-cherry',I.cherry(H['target'],H['target_cherry'],0,2),True)
    r=I.base.OriginalGraph(H['source']).residual(edges)
    check('hard-three-original-components',r['leaf_partition'],H['parents'])
    check('hard-no-leafless-component',r['nonempty'],True);check('hard-components-cuts-plus-one',r['count'],3)
    chosen=H['agreement_partitions'] if a.stage=='full' else [H['agreement_partitions'][3],H['agreement_partitions'][8],H['agreement_partitions'][5]]
    valid=[]
    for j,f in enumerate(chosen):
        actual=I.agreement(H['source'],H['target'],f['F']);check('hard-agreement-'+str(j),actual,f['agreement'])
        if actual:
            facts=([H['a']] in f['F'],[H['b']] in f['F'],I.base.refines(f['F'],H['parents']))
            check('hard-alternatives-'+str(j),list(facts),[f['singleton_a'],f['singleton_b'],f['refines_P']])
            check('hard-disjunction-'+str(j),any(facts),True);valid.append(f['F'])
    false('singleton-alternatives-cannot-be-omitted',all(I.base.refines(F,H['parents']) for F in valid),True)
    false('two-hard-cuts-not-affordable-for-every-F',all(2<=len(F)-1 for F in valid),True)
    if a.stage=='full':
        check('hard-valid-forest-count',len(valid),H['valid_forest_count'])
        for label in ['mirror','inner_swap']:
            t=H[label+'_source'];_,ed=I.pendant_edges(t,H['a'],H['b'])
            check(label+'-fixed-original-edges',ed,H[label+'_cuts'])
            check(label+'-components',I.base.OriginalGraph(t).residual(ed)['leaf_partition'],H['parents'])
            check(label+'-sibling-order-agreement',[I.agreement(t,H['target'],f['F']) for f in H['agreement_partitions']],
                  [f['agreement'] for f in H['agreement_partitions']])

    macro_reports=[]
    for M in (C['macros'] if a.stage=='full' else C['macros'][:1]):
        check(M['id']+'-proper-parent-source',I.parent_check(M['source'],M['parents']),True)
        check(M['id']+'-two-hard-components',I.base.OriginalGraph(M['source']).residual(M['hard_cuts'])['leaf_partition'],M['parents'])
        region_counts=lambda v:[len({I.region_from_graph(M['target'],v,x) for x in p}) for p in M['parents']]
        check(M['id']+'-actual-regions-v',region_counts(M['v']),M['parent_region_counts_at_v'])
        if 'w' in M:
            check(M['id']+'-actual-regions-w',region_counts(M['w']),M['parent_region_counts_at_w'])
            pairs=[[I.region_from_graph(M['target'],M['v'],x),I.region_from_graph(M['target'],M['w'],x)] for x in M['parents'][1]]
            check(M['id']+'-actual-joint-pairs',pairs,M['B_joint_pairs'])
            check(M['id']+'-actual-joint-count',len(set(map(tuple,pairs))),M['B_joint_count'])
            tg=I.base.OriginalGraph(M['target'])
            check(M['id']+'-A-C-target-hulls-disjoint',not bool(tg.span(M['parents'][0])&tg.span(M['parents'][2])),True)
        rows=[];call_outputs={};call_colors={}
        calls=M['calls'] if a.stage=='full' else M['calls'][:1]
        for call in calls:
            tag=M['id']+':'+call['id']
            colors,counts=I.tagged_colors(M['source'],M['target'],M['parents'],M['v'],M.get('w'),call['modes'])
            check(tag+'-literal-tags',colors,{int(k):v for k,v in call['colors'].items()})
            check(tag+'-local-counts',counts,call['local_counts']);check(tag+'-sum-global-colors',len(set(colors.values())),call['global_count'])
            generated=I.base.generate(M['source'],colors,M['q'])
            outputs=generated['outputs'];expected=[{'partition':p,'cuts':c} for p,c in zip(call['parts'],call['cuts'],strict=True)]
            check(tag+'-literal-output-list',outputs,expected)
            check(tag+'-paid-whole-source-costs',[len(o['cuts']) for o in outputs],call['costs'])
            for o in outputs:
                check(tag+'-actual-nonredundant-original-output',I.validate_output(M['source'],colors,M['q'],o),True)
                check(tag+'-source-embeddings-disjoint',I.base.convex_partition(I.base.OriginalGraph(M['source']),o['partition']),True)
                check(tag+'-Q-refines-P',I.base.refines(o['partition'],M['parents']),True)
                check(tag+'-requested-original-target-clearing',I.requested_clear(M['target'],M['parents'],o['partition'],call['requests'],M),True)
            call_outputs[call['id']]=outputs;call_colors[call['id']]=colors;rows.append(I.receipt(call['id'],outputs))
        check(M['id']+'-clean-literal-receipts',I.validate_receipts(rows,[c['id'] for c in calls]),True)
        if a.stage=='full':
            raw=[o for row in rows for o in row['outputs']]
            check(M['id']+'-raw-cost-list',[len(o['cuts']) for o in raw],M['raw_costs'])
            check(M['id']+'-cost-sum',sum(len(o['cuts']) for o in raw),M['cost_sum'])
            for c,key in [(Fraction(2),'mass_at_2'),(Fraction(233,100),'mass_at_233_100')]:
                check(M['id']+'-'+key,I.raw_mass(raw,c),Fraction(*M[key]))
            false(M['id']+'-no-extra-c^-2-discount',I.raw_mass(raw,2),Fraction(*M['false_extra_hard_cut_mass_at_2']))
            for f in M['forests']:
                check(M['id']+f['id']+'-original-agreement',I.agreement(M['source'],M['target'],f['F']),True)
                check(M['id']+f['id']+'-F-refines-P',I.base.refines(f['F'],M['parents']),True)
                q=f.get('q',len(f['F'])-1)
                covering=[]
                for call in calls:
                    outputs=I.base.generate(M['source'],call_colors[call['id']],q)['outputs']
                    if any(I.base.refines(f['F'],o['partition']) and I.base.refines(o['partition'],M['parents']) and len(o['cuts'])<=q
                           and I.requested_clear(M['target'],M['parents'],o['partition'],call['requests'],M) for o in outputs):covering.append(call['id'])
                check(M['id']+f['id']+'-only-covering-call',covering,[f['only_covering_call']])
                false(M['id']+f['id']+'-omission-loses-cover',any(x!=f['only_covering_call'] for x in covering),True)
            # Literal call omissions/duplicates differ from legal raw duplicate
            # outputs. The latter remain legal list data and must be counted.
            omitted=rows[1:];rejects(M['id']+'-omitted-call-receipt',lambda:I.validate_receipts(omitted,[c['id'] for c in calls]))
            rejects(M['id']+'-duplicate-call-identity',lambda:I.validate_receipts(rows+[rows[0]],[c['id'] for c in calls]))
            duplicate_raw=raw+[copy.deepcopy(raw[0])]
            false(M['id']+'-raw-duplicate-cannot-be-omitted-from-mass',I.raw_mass(duplicate_raw,2),I.raw_mass(raw,2))
            false(M['id']+'-raw-duplicate-cannot-be-omitted-from-cost',sum(len(o['cuts']) for o in duplicate_raw),sum(len(o['cuts']) for o in raw))
            false(M['id']+'-duplicate-breaks-fixed-mass-bound',I.raw_mass(duplicate_raw,2)<=Fraction(*M['mass_at_2']),True)
            if M['id']=='two-joint-diagonal':
                check('diagonal-q3-pruned-list-counts',[len(I.base.generate(M['source'],call_colors[c['id']],3)['outputs']) for c in calls],M['q3_output_counts'])
            macro_reports.append({'id':M['id'],'receipts':rows,'actual_mass_2':I.raw_mass(raw,2),'actual_mass_233_100':I.raw_mass(raw,Fraction(233,100))})
        else:
            rejects('pilot-malformed-receipt',lambda:I.validate_receipts([{'id':'leave-A','outputs':[]}],['leave-A']))

    if a.stage=='full':
        E=C['clearing_not_final_agreement']
        cols,_=I.tagged_colors(E['source'],E['target'],E['parents'],E['v'],None,E['modes'])
        out=I.base.generate(E['source'],cols,E['q'])['outputs']
        check('clearing-not-agreement-exact-output',out,[{'partition':p,'cuts':c} for p,c in zip(E['parts'],E['cuts'],strict=True)])
        for o in out:
            check('clearing-not-agreement-source',I.base.convex_partition(I.base.OriginalGraph(E['source']),o['partition']),True)
            check('clearing-not-agreement-request',I.requested_clear(E['target'],E['parents'],o['partition'],E['requests'],E),True)
            check('clearing-not-agreement-false-final-agreement',I.agreement(E['source'],E['target'],o['partition']),False)
            false('do-not-infer-final-agreement-from-clearing',I.agreement(E['source'],E['target'],o['partition']),True)
        for f in C['malformed_parents']:
            check(f['id']+'-parent-rejected',I.parent_check(f['tree'],f['parents']),False)
            rejects(f['id']+'-tag-construction-rejected',lambda f=f:I.tagged_colors(f['tree'],f['tree'],f['parents'],[],None,['constant']*3))
        # Missing residue tags collide across parents, although the local
        # counts are individually correct. The sum encoding loses joint colors.
        clique=C['macros'][0];local=[I.local_value(clique['target'],clique['v'],None,x,mode) for p,mode in zip(clique['parents'],clique['calls'][0]['modes']) for x in p]
        false('missing-parent-tags-count-collision',len(set(local)),sum(clique['calls'][0]['local_counts']))
        reversed_tags={x:3*i+I.local_value(clique['target'],clique['v'],None,x,mode)
          for i,(p,mode) in enumerate(zip(clique['parents'],clique['calls'][0]['modes'])) for x in p}
        false('wrong-residue-parent-tags',all(reversed_tags[x]%3==i for i,p in enumerate(clique['parents']) for x in p),True)
        first=macro_reports[0]['receipts'][0]['outputs'][0]
        forged=copy.deepcopy(first);forged['cuts']+=clique['hard_cuts']
        colors={int(k):v for k,v in clique['calls'][0]['colors'].items()}
        false('appending-two-hard-cuts-is-not-an-output',I.validate_output(clique['source'],colors,clique['q'],forged),True)
        false('named-parent-cuts-not-required-as-literal-output-sublist',all(c in first['cuts'] for c in clique['hard_cuts']),True)
        chain=C['macros'][1];sums={sum(x) for x in chain['B_joint_pairs']}
        false('sum-is-not-an-injective-joint-color',len(sums),chain['B_joint_count'])
        # Schema omissions and forged costs are rejected even if their mass
        # would appear smaller. Legal duplicate outputs preserve multiplicity.
        one=I.receipt('x',[{'partition':[[0],[1]],'cuts':[[0]]}])
        check('toy-clean-receipt',I.validate_receipts([one],['x']),True)
        rejects('nonlist-receipt',lambda:I.validate_receipts({},['x']))
        rejects('missing-cost-field',lambda:I.validate_receipts([{'id':'x','outputs':one['outputs']}],['x']))
        rejects('omitted-emitted-cost',lambda:I.validate_receipts([{'id':'x','outputs':one['outputs'],'costs':[]}],['x']))
        rejects('forged-paid-cost',lambda:I.validate_receipts([{'id':'x','outputs':one['outputs'],'costs':[3]}],['x']))
        rejects('duplicate-receipt-id',lambda:I.validate_receipts([one,one],['x']))
        strictF=[[0],[1],[2]];strictQ=[[0,1],[2]]
        check('strict-forward-refinement',I.base.refines(strictF,strictQ),True)
        false('reverse-refinement-is-not-coverage',I.base.refines(strictQ,strictF),True)
        false('strict-refinement-is-not-equality',I.base.canonical(strictF),I.base.canonical(strictQ))
        S=C['suppression_control'];g=I.base.OriginalGraph(S['tree'])
        actual=[list(g.address[x]) for x in g.path(g.at[()],g.at[(0,1)])]
        check('original-suppression-path',actual,S['original_path'])
        false('compressed-edge-is-not-original',g.at[(0,1)] in g.adj[g.at[()]],True)
        bad=copy.deepcopy(C['macros'][0]['parents']);bad[0].append(99)
        check('selected-foreign-label-parent-exception',I.parent_check(C['macros'][0]['source'],bad),False)

    for f in C['geometry_exceptions']:
        if 'parent' in f:
            regs=sorted({I.region_from_graph(f['tree'],f['v'],x) for x in f['parent']})
            check(f['id']+'-actual-regions',regs,f['regions']);check(f['id']+'-actual-count',len(regs),f['region_count'])
            if 'clears' in f:check(f['id']+'-clears',I.target_clears(f['tree'],[f['parent']],f['v']),f['clears'])
            if f['id']=='root-has-no-up-region':false('root-not-three-regions',len(regs),3)
            if f['id']=='selected-label-is-not-cleared':false('selected-label-monochromatic-is-not-clear',I.target_clears(f['tree'],[f['parent']],f['v']),True)
        else:
            _,ed=I.pendant_edges(f['tree'],f['a'],f['b']);check(f['id']+'-pendants',ed,f['pendant_cuts'])
            false('root-cherry-does-not-have-two-hard-pendants',len(ed),2)
    report['macro_receipts']=macro_reports;report['elapsed_seconds']=time.perf_counter()-start
    report['status']='PASS_PREPARATION_CONTROLS' if not report['failures'] else 'FAIL_PREPARATION_CONTROLS'
    report['positive_count']=len(report['positive']);report['negative_count']=len(report['negative'])
    path=ROOT/f'research/rmaf/results/algorithm-assembly-prerelease-review-{a.stage}-v1.json'
    path.write_text(json.dumps(report,indent=2,default=serial)+'\n')
    print(report['status'],report['positive_count'],'positive comparisons;',report['negative_count'],'false/corruption catches;',report['elapsed_seconds'],'seconds')
    if report['failures']:print(report['failures']);raise SystemExit(1)

if __name__=='__main__':main()
