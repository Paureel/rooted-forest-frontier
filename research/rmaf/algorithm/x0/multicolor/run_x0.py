"""Retained multicolor X0 comparator; independent source reference is read-only."""
import argparse
import copy
import datetime
from fractions import Fraction
from functools import lru_cache
import hashlib
import importlib.util
from itertools import combinations
import json
from pathlib import Path
import platform
import time
from prototype import generate,key

HERE=Path(__file__).resolve().parent
RMAF=HERE.parents[2]
SPEC=json.loads((HERE/'frozen-spec-v1.json').read_text())
REFPATH=HERE.parent/'fresh_oracle.py'
module_spec=importlib.util.spec_from_file_location('prior_x0_reference',REFPATH)
REFERENCE=importlib.util.module_from_spec(module_spec)
module_spec.loader.exec_module(REFERENCE)


def color_map(vector):
    return dict(enumerate(vector))


def refined(fine,coarse):
    return all(any(set(b)<=set(c) for c in coarse) for b in fine)


def monochromatic(partition,colors):
    return all(len({colors[x] for x in b})==1 for b in partition)


def source_partitions(tree):
    result=[]
    for p in REFERENCE.partitions(tree.labels):
        v=REFERENCE.validate_partition(tree,tree,p)
        if v['valid']:
            result.append(p)
    assert result,'zero source-valid partition denominator'
    return result


def check_core(tree,colors,core):
    p=core['partition']
    v=REFERENCE.validate_partition(tree,tree,p)
    if not v['valid']:
        return {'valid':False,'reason':'invalid source partition','detail':v}
    if not monochromatic(p,colors):
        return {'valid':False,'reason':'nonmonochromatic core'}
    cuts=core['cuts']
    if len(cuts)!=len(set(tuple(e) for e in cuts)):
        return {'valid':False,'reason':'duplicate source cut'}
    try:
        blocks,empty=tree.cut_blocks(cuts)
    except ValueError as e:
        return {'valid':False,'reason':str(e)}
    if key(blocks)!=key(p) or empty:
        return {'valid':False,'reason':'cut-realization mismatch','observed_blocks':blocks,'empty_regions':empty}
    true_cost=len(cuts)
    block_cost=0 if not tree.labels else len(p)-1
    if core['cost']!=true_cost or true_cost!=block_cost:
        return {'valid':False,'reason':'wrong source cut charge','reported':core['cost'],
                'true_cut_count':true_cost,'pieces_minus_one':block_cost}
    return {'valid':True,'true_cost':true_cost,'original_cut_blocks':blocks,
            'reconstruction_partition':p,'source_span_validation':v}


def score(tree,colors,result,valid_source=None):
    cores=result['cores']
    q=result.get('budget')
    r=len(set(colors.values()))
    errors=[]
    corechecks=[check_core(tree,colors,c) for c in cores]
    errors += [{'kind':'core-realization','index':i,'detail':v} for i,v in enumerate(corechecks) if not v['valid']]
    if len({key(c['partition']) for c in cores})!=len(cores):
        errors.append({'kind':'duplicate-final-core'})
    if valid_source is None:
        valid_source=source_partitions(tree)
    colored=[p for p in valid_source if monochromatic(p,colors)]
    feasible=[p for p in colored if q is None or (0 if not p else len(p)-1)<=q]
    coverage=[]
    for p in feasible:
        hits=[i for i,c in enumerate(cores) if refined(p,c['partition'])]
        coverage.append({'source_partition':p,'covered_by_core_indices':hits})
        if not hits:
            errors.append({'kind':'missing-source-partition','partition':p,
                           'source_span_validation':REFERENCE.validate_partition(tree,tree,p)})
    if not cores and (q is None or feasible):
        errors.append({'kind':'zero-core-failure','feasible_source_partition_count':len(feasible)})
    mass=[]
    for cs in SPEC['census']['bases']:
        c=Fraction(cs)
        observed=sum((c**(-core['cost']) for core in cores),Fraction(0))
        raw=sum((c**(-core['cost']) for core in result.get('raw_cores',cores)),Fraction(0))
        bound=c**(1-r) if tree.labels else None
        if bound is not None and (observed>bound or raw>bound):
            errors.append({'kind':'mass-exceeded','base':cs,'mass':str(observed),'raw_mass':str(raw),'bound':str(bound)})
        mass.append({'base':cs,'core_mass':str(observed),'raw_emission_mass':str(raw),
                     'bound':None if bound is None else str(bound),'nonempty_hypothesis_applies':bool(tree.labels)})
    if tree.labels and any(c['cost']<r-1 for c in cores):
        errors.append({'kind':'cost-below-color-lower-bound','r':r})
    if q is not None and any(c['cost']>q for c in cores):
        errors.append({'kind':'budget-exceeded','q':q})
    return {'valid':not errors,'errors':errors,'core_realizations':corechecks,
            'source_valid_colored_partition_count':len(colored),
            'feasible_source_partition_count':len(feasible),'coverage':coverage,
            'mass':mass,'r':r,'budget':q}


def plant_controls():
    plants=[]
    for p in SPEC['plants']:
        colors=color_map(p['colors']);tree=REFERENCE.Tree(p['T'])
        generated=generate(p['T'],colors)
        s=score(tree,colors,generated)
        assert s['valid'],(p['name'],s)
        expected=p.get('expected_extremal_partitions',[p.get('expected_core_partition')])
        assert {key(c['partition']) for c in generated['cores']}=={key(x) for x in expected},(p,generated)
        assert all(c['cost']==p['expected_cost'] for c in generated['cores'])
        assert s['mass'][0]['core_mass']==p['expected_mass_at_2']
        if 'original_refining_partition' in p:
            assert any(refined(p['original_refining_partition'],c['partition']) for c in generated['cores'])
        plants.append({'name':p['name'],'input':p,'generated':generated,'score':s,'pass':True})
    base=SPEC['plants'][0]
    tree=REFERENCE.Tree(base['T']);colors=color_map(base['colors'])
    clean=generate(base['T'],colors)
    mutation=generate(base['T'],colors,omit_first_mixed_right=True)
    failed=score(tree,colors,mutation)
    missed=SPEC['mutation_controls']['omit_right_first_mixed_branch']['explicit_missed_partition']
    assert not failed['valid'] and any(e.get('partition')==missed for e in failed['errors'])
    assert REFERENCE.validate_partition(tree,tree,missed)['valid']
    mutations=[{'name':'omitted mixed branch','corrupted':mutation,'score':failed,
                'explicit_missed_partition':missed,'clean_twin':clean,'caught':True}]
    bad=copy.deepcopy(clean);bad['cores'][0]['cost']=1
    s=score(tree,colors,bad)
    assert any(e['kind']=='core-realization' and e['detail']['reason']=='wrong source cut charge' for e in s['errors'])
    mutations.append({'name':'wrong charge','corrupted':bad,'score':s,'caught':True})
    actual=Fraction(score(tree,colors,clean)['mass'][0]['core_mass'])
    claimed=Fraction(SPEC['mutation_controls']['wrong_mass']['reported_mass_at_2'])
    assert claimed!=actual
    mutations.append({'name':'wrong rational mass','reported':str(claimed),'observed':str(actual),'caught':True})
    zero={'cores':[],'raw_cores':[],'budget':None}
    s=score(tree,colors,zero)
    assert not s['valid'] and any(e['kind']=='zero-core-failure' for e in s['errors'])
    mutations.append({'name':'zero core','score':s,'caught':True})
    duplicate=copy.deepcopy(clean);duplicate['cores'].append(copy.deepcopy(clean['cores'][0]))
    s=score(tree,colors,duplicate)
    assert any(e['kind']=='duplicate-final-core' for e in s['errors'])
    mutations.append({'name':'duplicate core','score':s,'caught':True})
    for name,alter,reason in [
        ('invalid root cut',lambda c:c['cuts'].__setitem__(0,['','']),'nonexistent cut edge'),
        ('duplicate partition label',lambda c:c['partition'][0].append(c['partition'][0][0]),'invalid source partition'),
        ('missing partition label',lambda c:c['partition'].pop(),'invalid source partition')]:
        bad=copy.deepcopy(clean['cores'][0]);alter(bad)
        v=check_core(tree,colors,bad)
        assert not v['valid'] and v['reason']==reason,(name,v)
        mutations.append({'name':name,'corrupted_core':bad,'observed':v,'caught':True})
    for name,raw,cm,reason in [
        ('duplicate source label',[0,[0,1]],{0:0,1:1},'duplicate source label'),
        ('missing color label',base['T'],{0:0,1:1,2:0},'missing or foreign color label')]:
        try:
            generate(raw,cm)
            raise AssertionError('malformed input accepted')
        except ValueError as e:
            assert str(e)==reason
            mutations.append({'name':name,'observed':str(e),'caught':True})
    try:
        assert 0==SPEC['census']['pilot_expected_cases'],'zero scored denominator'
        raise RuntimeError('denominator check did not fire')
    except AssertionError as e:
        mutations.append({'name':'zero scored denominator','observed':str(e),'caught':True})
    # Legitimate budget refusal is separate from a zero unbounded core.
    refused=generate(base['T'],colors,budget=0)
    refusal_score=score(tree,colors,refused)
    assert refusal_score['valid'] and not refused['cores'] and refusal_score['feasible_source_partition_count']==0
    return {'plants':plants,'plant_count':len(plants),'mutations':mutations,
            'mutations_caught':len(mutations),'budget_refusal_clean_twin':{'generated':refused,'score':refusal_score},
            'controls_total':len(plants)+len(mutations)+1,'controls_passed':len(plants)+len(mutations)+1}


@lru_cache(None)
def trees(labels):
    if len(labels)==1:
        return (labels[0],)
    a,rest=labels[0],labels[1:]
    out=[]
    for n in range(len(rest)):
        for chosen in combinations(rest,n):
            left=tuple(sorted((a,*chosen)))
            right=tuple(x for x in rest if x not in chosen)
            for x in trees(left):
                for y in trees(right):
                    out.append([x,y])
    return tuple(out)


def color_vectors(n):
    result=[]
    def step(v):
        if len(v)==n:
            result.append(v)
            return
        for c in range(max(v,default=-1)+2):
            step(v+[c])
    step([])
    return result


EXPECTED={1:(1,1),2:(1,2),3:(3,5),4:(15,15),5:(105,52)}


def census(n):
    started=time.perf_counter()
    ts=trees(tuple(range(n)));vectors=color_vectors(n)
    assert (len(ts),len(vectors))==EXPECTED[n]
    details=[]
    counters={'cases':0,'three_color_cases':0,'source_valid_monochromatic_partitions':0,
              'covered_original_partitions':0,'emitted_cores':0,'raw_emissions':0,
              'duplicate_emissions_removed':0,'budget_queries':0,'budget_feasible_partitions':0,
              'budget_infeasible_queries':0,'nodes_visited_unbounded':0,'nodes_visited_budgeted':0,
              'budget_pruned_prefixes':0,'zero_unbounded_cores':0,'failures':0}
    for ti,raw in enumerate(ts):
        tree=REFERENCE.Tree(raw)
        valid=source_partitions(tree)
        for ci,vector in enumerate(vectors):
            colors=color_map(vector)
            generated=generate(raw,colors)
            s=score(tree,colors,generated,valid)
            counters['cases']+=1
            counters['three_color_cases']+=s['r']==3
            counters['source_valid_monochromatic_partitions']+=s['source_valid_colored_partition_count']
            counters['covered_original_partitions']+=sum(bool(x['covered_by_core_indices']) for x in s['coverage'])
            counters['emitted_cores']+=len(generated['cores'])
            counters['raw_emissions']+=generated['stats']['raw_emissions']
            counters['duplicate_emissions_removed']+=generated['stats']['duplicate_emissions_removed']
            counters['nodes_visited_unbounded']+=generated['stats']['nodes_visited']
            counters['zero_unbounded_cores']+=not generated['cores']
            budget_results=[]
            for q in range(n):
                limited=generate(raw,colors,budget=q)
                bs=score(tree,colors,limited,valid)
                expected_keys={key(c['partition']) for c in generated['cores'] if c['cost']<=q}
                actual_keys={key(c['partition']) for c in limited['cores']}
                if expected_keys!=actual_keys:
                    bs['valid']=False
                    bs['errors'].append({'kind':'budget-prefix-output-drift','q':q,
                                         'expected':list(expected_keys),'actual':list(actual_keys)})
                counters['budget_queries']+=1
                counters['budget_feasible_partitions']+=bs['feasible_source_partition_count']
                counters['budget_infeasible_queries']+=bs['feasible_source_partition_count']==0
                counters['nodes_visited_budgeted']+=limited['stats']['nodes_visited']
                counters['budget_pruned_prefixes']+=limited['stats']['budget_pruned_prefixes']
                budget_results.append({'q':q,'generated':limited,'score':bs})
            failed=not s['valid'] or any(not b['score']['valid'] for b in budget_results)
            counters['failures']+=failed
            details.append({'tree_index':ti,'color_index':ci,'T':raw,'color_vector':vector,
                            'generated':generated,'score':s,'budget_checks':budget_results})
            if failed:
                return {'n':n,'tree_count':len(ts),'color_vector_count':len(vectors),
                        'counters':counters,'cases':details,'fire_witness':details[-1],
                        'elapsed_seconds':time.perf_counter()-started,'verdict':'FIRE'}
    assert counters['cases']==len(ts)*len(vectors)>0
    assert counters['covered_original_partitions']==counters['source_valid_monochromatic_partitions']
    assert counters['failures']==0
    return {'n':n,'tree_count':len(ts),'color_vector_count':len(vectors),
            'counters':counters,'cases':details,'elapsed_seconds':time.perf_counter()-started,
            'verdict':'FINITE-NO-FIRE'}


def hashes():
    p=json.loads((HERE/'provenance-v1.json').read_text())
    for name,digest in p['source_sha256'].items():
        assert hashlib.sha256(Path(name).read_bytes()).hexdigest()==digest
    paths=[HERE/'prototype.py',HERE/'run_x0.py',HERE/'frozen-spec-v1.json',REFPATH]
    return {str(p):hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}


def main():
    parser=argparse.ArgumentParser();parser.add_argument('--stage',choices=['controls','pilot','extension'],required=True)
    args=parser.parse_args()
    record={'stage':args.stage,'started_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
            'file_sha256':hashes(),'python':platform.python_version(),'platform':platform.platform(),
            'scope':'Finite adversarial prototype checks; all universal, Lean and consuming algorithm obligations remain OPEN.'}
    started=time.perf_counter()
    if args.stage=='controls':
        record.update(plant_controls())
        record['verdict']='PASS'
    else:
        prior=json.loads((RMAF/'results/algorithm-x0-core-controls-v1.json').read_text())
        assert prior['verdict']=='PASS' and prior['controls_passed']==prior['controls_total']==19
        if args.stage=='pilot':
            record['censuses']=[census(4)]
        else:
            pilot=json.loads((RMAF/'results/algorithm-x0-core-pilot-v1.json').read_text())
            decision=json.loads((HERE/'timing-extension-decision-v1.json').read_text())
            assert pilot['verdict']=='FINITE-NO-FIRE' and decision['projected_seconds']<7200
            assert decision['pilot_sha256']==hashlib.sha256((RMAF/'results/algorithm-x0-core-pilot-v1.json').read_bytes()).hexdigest()
            record['timing_extension_decision']=decision
            record['censuses']=[census(n) for n in SPEC['census']['after_success_and_timing_n']]
        record['verdict']='FIRE' if any(c['verdict']=='FIRE' for c in record['censuses']) else 'FINITE-NO-FIRE'
    record['elapsed_seconds']=time.perf_counter()-started
    record['completed_utc']=datetime.datetime.now(datetime.timezone.utc).isoformat()
    out=RMAF/'results'/f'algorithm-x0-core-{args.stage}-v1.json'
    assert not out.exists(),'refuse to overwrite retained execution receipt'
    out.write_text(json.dumps(record,indent=2)+'\n')
    print(json.dumps({'stage':args.stage,'verdict':record['verdict'],'seconds':record['elapsed_seconds'],
                      'controls_passed':record.get('controls_passed'),
                      'census_counters':[{'n':c['n'],**c['counters']} for c in record.get('censuses',[])],
                      'receipt':str(out)}))


if __name__=='__main__':
    main()
