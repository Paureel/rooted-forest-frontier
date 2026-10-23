"""One-shot retained X0 driver. No oracle use is part of an algorithm candidate."""
from pathlib import Path
import argparse
import datetime
import hashlib
import json
import platform
import time
from fractions import Fraction
from fresh_oracle import Tree, exact, validate_partition, applicability, tidy, forest_to_reference

ROOT = Path(__file__).resolve().parents[2]
HERE = Path(__file__).resolve().parent
FROZEN = json.loads((HERE/'frozen-controls-v1.json').read_text())
SPEC = json.loads((HERE/'control-spec-v1.json').read_text())


def check_hashes():
    for name,digest in FROZEN['source_sha256'].items():
        assert hashlib.sha256((ROOT/'results'/name).read_bytes()).hexdigest() == digest


def stamp():
    return datetime.datetime.now(datetime.timezone.utc).isoformat()


def runtime_record():
    return {'python':platform.python_version(),'platform':platform.platform(),
            'code_sha256':{p.name:hashlib.sha256(p.read_bytes()).hexdigest()
                for p in [HERE/'fresh_oracle.py',HERE/'run_x0.py']},
            'freeze_sha256':hashlib.sha256((HERE/'frozen-controls-v1.json').read_bytes()).hexdigest(),
            'spec_sha256':hashlib.sha256((HERE/'control-spec-v1.json').read_bytes()).hexdigest()}


def controls():
    rows = []
    def forest(name,a,b,p,expected,reason=None):
        v = validate_partition(Tree(a),Tree(b),p)
        assert v['valid'] is expected, (name,v)
        if reason:
            assert v['reason'] == reason,(name,v)
        rows.append({'control':name,'expected_valid':expected,'observed':v,'pass':True})
    triple1,triple2 = [0,[1,2]],[[0,1],2]
    forest('wrong topology',triple1,triple2,[[0,1,2]],False,'wrong rooted topology')
    forest('wrong topology clean twin',triple1,triple1,[[0,1,2]],True)
    balanced = [[0,1],[2,3]]
    forest('vertex overlap',balanced,balanced,[[0,2],[1,3]],False,'vertex overlap')
    forest('vertex overlap clean twin',balanced,balanced,[[0,1],[2,3]],True)
    forest('duplicate labels',triple1,triple1,[[0,1],[1,2]],False,'duplicate forest label')
    forest('duplicate clean twin',triple1,triple1,[[0],[1,2]],True)
    forest('missing labels',triple1,triple1,[[0],[1]],False,'missing/foreign forest label')
    forest('missing clean twin',triple1,triple1,[[0],[1],[2]],True)
    forest('tree universe mismatch',triple1,[0,[1,3]],[[0],[1],[2]],False,'tree label mismatch')
    forest('tree universe clean twin',triple1,triple1,[[0],[1],[2]],True)
    try:
        Tree([0,[0,1]])
        raise AssertionError('duplicate malformed input went undetected')
    except ValueError as e:
        rows.append({'control':'duplicate tree labels','pass':str(e)=='duplicate tree label','observed':str(e)})
        assert rows[-1]['pass']
    assert Tree([0,[1,2]]).labels == {0,1,2}
    rows.append({'control':'duplicate tree labels clean twin','pass':True})
    for name,a,b,k in [('empty',None,None,0),('singleton',0,0,1),
                       ('identical',balanced,balanced,1),('conflicting_rooted_triple',triple1,triple2,2)]:
        out=exact(Tree(a),Tree(b))
        assert out['components']==k,(name,out)
        rows.append({'control':name,'expected_components':k,'observed':out,'pass':True})
    s=SPEC['suppression_control']
    out=Tree(s['input']).restriction(s['selected'])
    assert out == s['expected_tree']
    rows.append({'control':'suppression','expected':s['expected_tree'],'observed':out,'pass':True})
    c=SPEC['component_count_control']
    blocks,empty=Tree(c['input']).cut_blocks([c['edge']])
    assert len(blocks)==c['expected_components'] and not empty
    rows.append({'control':'component count vs paid cuts','observed_blocks':blocks,'paid_cuts':1,
                 'initial_components':1,'final_components':len(blocks),'pass':True})
    for name in ['published_bottleneck','conditional_macro_a']:
        rec=FROZEN['sources']['branching-recurrences.json']['recurrences'][name]
        mass=sum(Fraction(100,231)**d for d in rec['vector'])
        assert mass == Fraction(rec['mass_at_231_100'])
        assert (mass <= 1) is rec['certificate']
        rows.append({'control':name,'vector':rec['vector'],'exact_mass':str(mass),
                     'observed_certificate':mass<=1,'pass':True})
    bad=SPEC['rational_negative']
    mass=sum(Fraction(100,231)**d for d in bad['vector'])
    assert bad['claimed_certificate'] != (mass<=1)
    rows.append({'control':'false recurrence caught','claimed_certificate':True,
                 'exact_mass':str(mass),'observed_certificate':False,'pass':True})
    clean=SPEC['rational_clean_twin']
    mass=sum(Fraction(100,231)**d for d in clean['vector'])
    assert clean['claimed_certificate'] == (mass<=1)
    rows.append({'control':'false recurrence clean twin','exact_mass':str(mass),'pass':True})
    # Deliberately corrupt the comparator, not the calculation.
    observed=exact(Tree(triple1),Tree(triple2))['components']
    try:
        assert observed == 1
        raise RuntimeError('false optimum comparator did not fire')
    except AssertionError:
        rows.append({'control':'false optimum comparator caught','claimed':1,'observed':observed,'pass':True})
    assert observed==2
    rows.append({'control':'false optimum comparator clean twin','claimed':2,'observed':observed,'pass':True})
    assert len(rows)==24
    return {'controls':rows,'passed':sum(r['pass'] for r in rows),'total':len(rows)}


def source_pair(source,name):
    return FROZEN['sources'][source][name]


def fixtures():
    n6=source_pair('branching-search-n6.json','forced_cherry_baseline_hard_counterexample')
    n7=source_pair('branching-search-n7.json','forced_cherry_baseline_hard_counterexample')
    ep=source_pair('branching-search-n7.json','endpoint_lookahead_baseline_hard_counterexample')
    return [('n6_forced_baseline',n6,0),('n7_forced_baseline',n7,0),
            ('n7_endpoint_baseline',ep,0),
            ('n7_endpoint_baseline_after_endpoint',{'T':ep['child_T'],'Tprime':ep['child_Tprime']},1)]


def analyze_fixture(name,data,prior_paid):
    started=time.perf_counter()
    a,b=Tree(data['T']),Tree(data['Tprime'])
    app_ab,app_ba=applicability(a,b),applicability(b,a)
    assert app_ab['excluded_2a_to_2d'] and app_ba['excluded_2a_to_2d'],(name,app_ab,app_ba)
    original=exact(a,b)
    out={'fixture':name,'T':a.raw,'Tprime':b.raw,'prior_paid_cuts':prior_paid,
         'Figure16':{'forward':app_ab,'reverse':app_ba},'original_optimum':original,
         'children':[]}
    if 'optimum_components' in data:
        assert original['components']==data['optimum_components']
        retained=exact(a,b,retain_together=data['cherry'])
        assert retained['components']==data['optimum_if_cherry_retained']
        for p in data['optimal_forests']:
            assert validate_partition(a,b,p)['valid'] and len(p)==original['components']
        pendant=a.labels # do not use expected pendant sets to construct them
        matching=next(r for r in app_ab['rows'] if r['cherry']==data['cherry'])
        assert sorted(matching['pendants'][i]['labels'] for i in range(2)) == sorted(data['pendant_sets'])
        out['forced_cherry_rejection']={'original_components':original['components'],
            'retained_components':retained['components'],'retained_optimum':retained,
            'forced_rule_refuted':retained['components']>original['components']}
    for orientation,x,y,app in [('forward',a,b,app_ab),('reverse',b,a,app_ba)]:
        for row in app['rows']:
            assert row['t']==2
            cuts=[p['edge'] for p in row['pendants']]
            blocks,empty=y.cut_blocks(cuts)
            assert not empty and len(blocks)==3
            rawtrees=[y.restriction(c) for c in blocks]
            rawopt=exact(x,y,refinement=blocks)
            residual=rawopt['components']-len(blocks)
            reduced=tidy(x.raw,rawtrees)
            tx=Tree(reduced['T'])
            ty=forest_to_reference(tx,reduced['forest_trees'])
            reduced_opt=exact(tx,ty,refinement=reduced['forest_blocks'])
            reduced_residual=reduced_opt['components']-len(reduced['forest_blocks'])
            assert reduced_residual==residual
            child={'orientation':orientation,'cherry':row['cherry'],'cuts':cuts,
                'paid_cuts_here':2,'total_paid_before_residual':prior_paid+2,
                'parent_T':x.raw,'parent_Tprime':y.raw,'raw_forest_blocks':blocks,
                'raw_forest_trees':rawtrees,'raw_optimum':rawopt,'raw_residual_optimum_cuts':residual,
                'reduced':reduced,'reduced_optimum':reduced_opt,
                'reduced_residual_optimum_cuts':reduced_residual,
                'candidate_call_site_eligible':True}
            # Reconstruct the reduced optimum, then verify on the original graphs.
            expansions={int(k):v for k,v in reduced['expansion'].items()}
            rebuilt=[]
            for p in reduced_opt['optimal_partitions']:
                parts=[sorted(z for label in c for z in expansions[label]) for c in p]
                parts += reduced['closed_components']
                parts.sort(key=lambda c:min(c))
                witness=validate_partition(x,y,parts,blocks)
                assert witness['valid'] and len(parts)==rawopt['components']
                rebuilt.append({'partition':parts,'validation':witness})
            child['reconstructed_reduced_optima']=rebuilt
            out['children'].append(child)
    out['elapsed_seconds']=time.perf_counter()-started
    return out


def cover_control():
    data=source_pair('branching-search-n6.json','forced_cherry_baseline_hard_counterexample')
    a,b=Tree(data['T']),Tree(data['Tprime'])
    optimum=exact(a,b)
    row=next(r for r in applicability(a,b)['rows'] if r['cherry']==[4,5])
    cover={}
    for name,edges in [('isolate4',[[b.parent[b.leaf[4]],b.leaf[4]]]),
                       ('isolate5',[[b.parent[b.leaf[5]],b.leaf[5]]]),
                       ('cut_all_two_pendants',[p['edge'] for p in row['pendants']])]:
        blocks,empty=b.cut_blocks(edges)
        assert not empty
        child=exact(a,b,refinement=blocks)
        cover[name]={'cuts':edges,'paid':len(edges),'blocks':blocks,'child_optimum':child,
                     'residual':child['components']-len(blocks),
                     'total_initial_cuts':len(edges)+child['components']-len(blocks)}
    s=SPEC['missing_cover']
    missed=s['missed_optimum_literal']
    assert validate_partition(a,b,missed)['valid'] and len(missed)==optimum['components']
    bad=s['bad_nonempty_cover'];clean=s['clean_complete_cover']
    badvalue=min(cover[n]['total_initial_cuts'] for n in bad)
    cleanvalue=min(cover[n]['total_initial_cuts'] for n in clean)
    missed_survival={n:all(any(set(c)<=set(r) for r in cover[n]['blocks']) for c in missed) for n in cover}
    assert badvalue>optimum['components']-1
    assert not any(missed_survival[n] for n in bad)
    assert cleanvalue==optimum['components']-1 and missed_survival['isolate5']
    return {'bad_nonempty_cover':bad,'complete_cover':clean,'missed_optimum':missed,
            'missed_optimum_validation':validate_partition(a,b,missed),
            'original_optimum_cuts':optimum['components']-1,'bad_cover_cuts':badvalue,
            'complete_cover_cuts':cleanvalue,'missed_survival_by_branch':missed_survival,
            'branches':cover,'missing_cover_bug_caught':True}


def endpoint_control():
    data=source_pair('branching-search-n7.json','endpoint_lookahead_baseline_hard_counterexample')
    a,b=Tree(data['T']),Tree(data['Tprime'])
    x=data['isolated_endpoint']
    remaining=a.labels-{x}
    assert a.restriction(remaining)==Tree(data['child_T']).restriction(remaining)
    assert b.restriction(remaining)==Tree(data['child_Tprime']).restriction(remaining)
    edge=[b.parent[b.leaf[x]],b.leaf[x]]
    blocks,empty=b.cut_blocks([edge])
    assert not empty and sorted(blocks,key=len)[0]==[x]
    ca,cb=Tree(data['child_T']),Tree(data['child_Tprime'])
    apps={'parent_forward':applicability(a,b),'parent_reverse':applicability(b,a),
          'child_forward':applicability(ca,cb),'child_reverse':applicability(cb,ca)}
    assert all(app['excluded_2a_to_2d'] for app in apps.values())
    assert all(r['t']==2 for app in apps.values() for r in app['rows'])
    return {'isolated_endpoint':x,'paid_endpoint_cut':edge,'forest_blocks_before_tidying':blocks,
            'child_T':ca.raw,'child_Tprime':cb.raw,'source_applicability_checks':apps,
            'endpoint_bonus_rejected':True,
            'mechanism':'One paid endpoint cut leaves only t=2 cherries, with no Figure16 step2a-d applicable in either orientation.'}


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--stage',choices=['controls','pilot','bounded'],required=True)
    args=parser.parse_args()
    check_hashes()
    record={'stage':args.stage,'started_utc':stamp(),'runtime':runtime_record(),
            'scope':'Finite X0 adversarial checks; no complete algorithm, universal coverage, exponent, or novelty claim.'}
    started=time.perf_counter()
    if args.stage=='controls':
        record.update(controls())
    else:
        prior=json.loads((ROOT/'results/algorithm-x0-controls-v1.json').read_text())
        assert prior['passed']==prior['total']==24 and prior['verdict']=='PASS'
        if args.stage=='pilot':
            name,data,paid=fixtures()[0]
            record['fixtures']=[analyze_fixture(name,data,paid)]
            record['progress_units']={'input_states':1,'actual_children':len(record['fixtures'][0]['children'])}
            record['timing_extension_rule']='Bounded four-state expansion only after pilot <=60 seconds; no census.'
        else:
            pilot=json.loads((ROOT/'results/algorithm-x0-pilot-v1.json').read_text())
            assert pilot['verdict']=='PASS' and pilot['elapsed_seconds']<=60
            record['pilot_measurement']={'seconds':pilot['elapsed_seconds'],'input_states':1,
                                         'actual_children':pilot['progress_units']['actual_children']}
            record['projection_provenance']='Only four receipt states. Pilot code/settings/machine identical; per-state times measured, no large-census estimate.'
            record['fixtures']=[analyze_fixture(*f) for f in fixtures()]
            record['missing_cover_control']=cover_control()
            record['endpoint_control']=endpoint_control()
            record['progress_units']={'input_states':len(record['fixtures']),
                                     'actual_children':sum(len(f['children']) for f in record['fixtures'])}
    record['elapsed_seconds']=time.perf_counter()-started
    record['completed_utc']=stamp()
    record['verdict']='PASS'
    output=ROOT/'results'/f'algorithm-x0-{args.stage}-v1.json'
    output.write_text(json.dumps(record,indent=2)+'\n')
    print(json.dumps({'verdict':record['verdict'],'stage':args.stage,'seconds':record['elapsed_seconds'],
                      'passed':record.get('passed'),'total':record.get('total'),
                      'progress_units':record.get('progress_units'),'receipt':str(output)}))


if __name__=='__main__':
    main()
