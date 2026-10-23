#!/usr/bin/env python3
"""One-shot pre-candidate literal-control runner; no author/verifier imports."""
import argparse
from copy import deepcopy
from datetime import datetime,timezone
from fractions import Fraction
import hashlib
import importlib
import json
from pathlib import Path
from time import perf_counter

HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[4]


def digest(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def require(actual,expected):
    if actual!=expected:
        raise AssertionError({'actual':actual,'expected':expected})


def must_reject(actual,false_expectation):
    try:
        require(actual,false_expectation)
    except AssertionError:
        return True
    raise AssertionError('deliberate false expectation survived')


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--phase',choices=['pilot','full'],required=True)
    args=ap.parse_args()
    start=perf_counter()
    freeze=json.loads((HERE/'FREEZE-v1.json').read_text())
    for r in freeze['owned_files']:
        require(digest(ROOT/r['path']),r['sha256'])
    I=importlib.import_module('independent_instrument')
    fixtures=json.loads((HERE/'CONTROLS-v1.json').read_text())
    rows={'graph':[],'invalid_cuts':[],'program':[],'partitions':[],'proper_labels':[],'mass':[],'negative':[]}
    try:
        for f in fixtures['graph']:
            graph=I.OriginalGraph(f['tree'])
            out=graph.residual(f['cuts'])
            require(out['leaf_partition'],f['components'])
            require(out['nonempty'],f['nonempty'])
            require(out['count'],f['component_count'])
            require(out['cuts_plus_one'],True)
            assert must_reject(out['count'],f['component_count']+1)
            rows['negative'].append({'id':f['id'],'kind':'false-component-count','caught':True})
            rows['graph'].append({'id':f['id'],'result':out})
        for f in fixtures['invalid_cuts']:
            try:
                I.OriginalGraph(f['tree']).residual(f['cuts'])
            except ValueError as exc:
                rows['invalid_cuts'].append({'id':f['id'],'rejected':str(exc)})
            else:
                raise AssertionError('invalid original-cut witness accepted')
        for t in fixtures['invalid_syntax']:
            try:
                I.OriginalGraph(t)
            except ValueError:
                rows['negative'].append({'kind':'invalid-binary-Nat-syntax','tree':t,'caught':True})
            else:
                raise AssertionError('invalid syntax accepted')
        chosen=fixtures['program'][:4] if args.phase=='pilot' else fixtures['program']
        program_map={}
        for f in chosen:
            colors={int(k):v for k,v in f['colors'].items()}
            out=I.generate(f['tree'],colors,f['q'])
            require([o['partition'] for o in out['outputs']],f['parts'])
            require([o['cuts'] for o in out['outputs']],f['cuts'])
            for key in ('visited','attempts','pruned'):
                require(out[key],f[key])
            require(out['refusals'],[f['refusal']] if 'refusal' in f else [])
            require(all(I.validate_emission(f['tree'],colors,f['q'],o) for o in out['outputs']),True)
            assert must_reject(out['visited'],f['visited']+1)
            rows['negative'].append({'id':f['id'],'kind':'false-prefix-visit-count','caught':True})
            for o in out['outputs']:
                bad=deepcopy(o)
                bad['partition'][0].append(bad['partition'][0][0])
                require(I.validate_emission(f['tree'],colors,f['q'],bad),False)
                rows['negative'].append({'id':f['id'],'kind':'duplicated-emitted-label','caught':True})
            row={'id':f['id'],'receipt':out,
                 'original_graph_certificates':[I.OriginalGraph(f['tree']).residual(o['cuts']) for o in out['outputs']]}
            rows['program'].append(row)
            program_map[f['id']]=(f,out)
        for f in fixtures['proper_labels']:
            actual=I.proper_labels(f['labels'],f['n'])
            require(actual,f['expected'])
            assert must_reject(actual,not f['expected'])
            rows['proper_labels'].append({**f,'actual':actual})
            rows['negative'].append({'kind':'false-properness-expectation','caught':True})
        # These auditor controls run without compiling or inspecting candidate code.
        clean='theorem clean : True := by trivial\n'
        require(I.named_source_audit(clean),True)
        for forged in ['axiom forged : False\ntheorem broken : False := forged\n',
                       'theorem broken : False := by sorry\n',
                       'theorem broken : False := by native_decide\n']:
            require(I.named_source_audit(forged),False)
            rows['negative'].append({'kind':'planted-custom-axiom-or-proof-token','caught':True})
        registry={'CoreGraph':{'path':'frozen/CoreGraph.lean','sha256':hashlib.sha256(clean.encode()).hexdigest()}}
        require(I.origin_matches(registry,deepcopy(registry)),True)
        for field,value in [('path','shadow/CoreGraph.lean'),('sha256','0'*64)]:
            bad=deepcopy(registry);bad['CoreGraph'][field]=value
            require(I.origin_matches(registry,bad),False)
            rows['negative'].append({'kind':'forged-module-origin-'+field,'caught':True})
        if args.phase=='full':
            for f in fixtures['partitions']:
                graph=I.OriginalGraph(f['tree']);colors={int(k):v for k,v in f['colors'].items()}
                actual={'proper':I.proper_partition(graph,f['F']),
                        'convex':I.convex_partition(graph,f['F']),
                        'monochromatic':I.monochromatic(f['F'],colors),
                        'F_refines_Q':I.refines(f['F'],f['Q']),
                        'Q_refines_F':I.refines(f['Q'],f['F']),
                        'equal':I.canonical(f['F'])==I.canonical(f['Q'])}
                actual['eligible']=(actual['proper'] and actual['convex'] and actual['monochromatic']
                                    and len(f['F'])-1<=f['q'])
                for key,value in actual.items():require(value,f[key])
                if actual['eligible']:
                    generated=I.generate(f['tree'],colors,f['q'])
                    require(any(I.refines(f['F'],o['partition']) for o in generated['outputs']),True)
                rows['partitions'].append({'id':f['id'],'actual':actual})
            strict=rows['partitions'][0]['actual']
            for field in ('Q_refines_F','equal'):
                assert must_reject(strict[field],True)
                rows['negative'].append({'kind':'false-coverage-'+field,'caught':True})
            assert must_reject(rows['partitions'][1]['actual']['eligible'],True)
            rows['negative'].append({'kind':'ignore-F-budget-premise','caught':True})
            crossed=program_map['crossed-q2'][1]['outputs']
            for f in fixtures['mass']:
                raw=[deepcopy(crossed[i]) for i in f['output_refs']]
                costs=[len(o['cuts']) for o in raw]
                require(costs,f['costs']);require(sum(costs),f['cost_sum'])
                masses={}
                for key,base in [('mass_at_2',Fraction(2)),('mass_at_233_100',Fraction(233,100))]:
                    value=I.raw_mass(raw,base)
                    require([value.numerator,value.denominator],f[key])
                    masses[key]=[value.numerator,value.denominator]
                if f['id']=='duplicate-emission-list':
                    dedup=[];seen=set()
                    for o in raw:
                        key=json.dumps(I.canonical(o['partition']))
                        if key not in seen:seen.add(key);dedup.append(o)
                    assert must_reject(sum(costs),sum(len(o['cuts']) for o in dedup))
                    for base in [Fraction(2),Fraction(233,100)]:
                        assert must_reject(I.raw_mass(raw,base),I.raw_mass(dedup,base))
                    rows['negative'].append({'kind':'omit-list-duplicate-cost-and-both-masses','caught':True,'distinct_failures':3})
                rows['mass'].append({'id':f['id'],'raw_count':len(raw),'costs':costs,'cost_sum':sum(costs),**masses})
            forged=fixtures['forged_cost_lower_bound']
            costs=[len(o['cuts']) for o in program_map[forged['program_id']][1]['outputs']]
            actual=all(c>=forged['claim_minimum_cost'] for c in costs)
            require(actual,False);assert must_reject(actual,True)
            require(all(c>=2 for c in costs),True)
            rows['negative'].append({'kind':'forged-emitted-cost-lower-bound','caught':True})
            c=fixtures['suppression_control'];graph=I.OriginalGraph(c['tree'])
            event=next(e for e in program_map['distinct-colors-suppression'][1]['trace'] if e['chosen']==c['surviving_group_origin'])
            for key in ('current_parent','original_parent','original_path'):
                expected_key='original_edge_parent' if key=='original_parent' else key
                require(event[key],c[expected_key])
            a,b=c['forged_direct_original_edge']
            require(graph.at[tuple(b)] in graph.adj[graph.at[tuple(a)]],False)
            rows['negative'].append({'kind':'suppressed-link-forged-as-original-edge','caught':True})
            require(program_map['crossed-q1'][1]['outputs'],[])
            assert must_reject(program_map['crossed-q1'][1]['outputs'],crossed)
            rows['negative'].append({'kind':'ignore-q-pruning','caught':True})
        expected={'graph':6,'invalid_cuts':3,'program':4 if args.phase=='pilot' else 12,
                  'partitions':0 if args.phase=='pilot' else 4,'proper_labels':4,'mass':0 if args.phase=='pilot' else 2}
        for key,count in expected.items():require(len(rows[key]),count)
        status='PRE-CANDIDATE-CONTROLS-PASS; NO-CANDIDATE-ACCEPTANCE'
        failure=None
    except Exception as exc:
        status='FAILED-PREPARATION-CONTROL'
        failure={'type':type(exc).__name__,'detail':str(exc)}
    for r in freeze['owned_files']:require(digest(ROOT/r['path']),r['sha256'])
    result={'kind':'core-completion-independent-pre-candidate-'+args.phase,
            'status':status,'date':datetime.now(timezone.utc).isoformat(),
            'rows':rows,'failure':failure,'seconds':perf_counter()-start,
            'stage':'PRE-CANDIDATE','candidate_contact':False,'candidate_compilation':False,
            'independence':'new code; stdlib and this frozen own instrument only; prior global contacts disclosed',
            'freeze_sha256':digest(HERE/'FREEZE-v1.json'),'source_and_control_hashes':freeze['owned_files']}
    dest=ROOT/'research/rmaf/results'/('algorithm-core-completion-fresh-review-prep-'+args.phase+'-v1.json')
    dest.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({'status':status,'phase':args.phase,'rows':{k:len(v) for k,v in rows.items()},
                      'seconds':result['seconds'],'failure':failure,'receipt':str(dest)}))
    if failure:raise SystemExit(1)


if __name__=='__main__':main()
