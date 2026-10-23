"""Fixed literal kept-parent plants; hand expectations are never regenerated."""
from pathlib import Path
from copy import deepcopy
from datetime import datetime, timezone
import hashlib,json,sys,time,traceback
sys.dont_write_bytecode=True
import instrument as I
HERE=Path(__file__).resolve().parent.parent; ROOT=I.ROOT

def digest(p): return hashlib.sha256(p.read_bytes()).hexdigest()

def main():
    mode=sys.argv[1]; assert mode in ('pilot','full')
    frozen=json.loads((HERE/'CONTROL-FREEZE-v2.json').read_text())
    for row in frozen['files']: assert digest(ROOT/row['path'])==row['sha256'], row['path']
    E=json.loads((HERE/'EXPECTATIONS-v2.json').read_text())
    fixtures=[f for f in E['fixtures'] if mode=='full' or f['id'] in E['pilot_ids']]
    dest=ROOT/f'research/rmaf/results/algorithm-kept-parent-fresh-review-replay-{mode}-v1.json'
    start=time.monotonic(); checks=[]; negatives=[]; actual_rows=[]; expected_rows=[]; detail=[]
    result={'stage':'PRE_CANDIDATE_ONLY','mode':mode,'utc':datetime.now(timezone.utc).isoformat(),'candidate_contact':False,'candidate_compilation':False,'all_main_milestones':'OPEN','replication_count_added':0,'frozen_input_manifest_sha256':digest(HERE/'CONTROL-FREEZE-v2.json')}
    def check(name,truth):
        checks.append({'id':name,'pass':bool(truth)})
        assert truth, name
    def catch(name,accepts_bad):
        negatives.append({'id':name,'caught':not bool(accepts_bad)})
        assert not accepts_bad,name
    try:
        for f in fixtures:
            tree=f['tree']; P=f['parents']; colors=I.source_colors(tree,P,f['beta'])
            check(f['id']+'/proper-source',I.source_valid(tree,P)==f['proper_source'])
            check(f['id']+'/A-restriction',I.literal_restrict(tree,P[0])==f['restriction_A'])
            check(f['id']+'/C-restriction',I.literal_restrict(tree,P[2])==f['restriction_C'])
            check(f['id']+'/B-residue',all(colors[x]%3==1 for x in P[1]))
            check(f['id']+'/A-C-tag-separation',all(colors[x]==0 for x in P[0]) and all(colors[x]==2 for x in P[2]))
            for b in f['budgets']:
                r=I.graph.generate(tree,colors,b['q']); name=f['id']+f"/q{b['q']}"
                expected={'id':f['id'],'q':b['q'],'outputs':b['outputs']}; actual={'id':f['id'],'q':b['q'],'outputs':r['outputs']}
                expected_rows.append(expected);actual_rows.append(actual)
                check(name+'/exact-raw-list',I.exact_rows([expected],[actual]))
                check(name+'/all-original-emissions',all(I.graph.validate_emission(tree,colors,b['q'],o) for o in r['outputs']))
                preserves=[I.whole_membership(tree,P,o['partition']) for o in r['outputs']]
                check(name+'/every-occurrence',preserves==b['preservation'])
                check(name+'/all-root-cuts-absent',all(a for o in r['outputs'] for a in o['cuts']))
                check(name+'/unchanged-restrictions',all(I.unchanged_restrictions(tree,P,o['partition'])==p for o,p in zip(r['outputs'],preserves)))
                if f['proper_source']: check(name+'/proper-universal-preservation',all(preserves))
                if f['local_certificate']:
                    check(name+'/retained-local-certificate',all(I.local_certificate_valid(tree,f['target'],P,o['partition'],f['local_certificate']) for o in r['outputs']))
                detail.append({'id':name,'receipt':r,'colors':colors,'proper_source':f['proper_source'],'preserves':preserves})
            last=detail[-1]['receipt']
            suppressed=any(e['current_parent']!=e['original_parent'] for e in last['trace'])
            check(f['id']+'/suppressed-original-path',suppressed==f['suppressed_chosen_path_at_full_budget'])
        check('exact-all-keyed-rows',I.exact_rows(expected_rows,actual_rows))
        # Common control twins are literal hand inputs, not regenerated truth.
        F={f['id']:f for f in E['fixtures']}
        a=F['root-clade-tag22']; good=a['budgets'][2]['outputs'][0]; t=a['tree']; P=a['parents']
        cross=F['root-crossed-outside-source']; raw=cross['budgets'][1]['outputs']
        check('negative-clean/root-source',I.source_valid(t,P))
        catch('false-root-properness',I.source_valid(t,P)==False)
        catch('false-budget-nonempty',len(a['budgets'][1]['outputs'])>0)
        nc=F['root-nonclade-A']; catch('false-nonclade-split',not I.whole_membership(nc['tree'],nc['parents'],nc['budgets'][1]['outputs'][0]['partition']))
        catch('omit-convexity-on-crossed',I.source_valid(cross['tree'],cross['parents']))
        check('negative-clean/crossed-has-two-outputs',len(raw)==2 and [I.whole_membership(cross['tree'],cross['parents'],o['partition']) for o in raw]==[False,True])
        rows=[{'id':'crossed','q':3,'outputs':deepcopy(raw)}]
        filter_rows=deepcopy(rows);filter_rows[0]['outputs']=[o for o in raw if I.whole_membership(cross['tree'],cross['parents'],o['partition'])]
        catch('filter-to-favorable-output',I.exact_rows(rows,filter_rows))
        for name,index in [('omit-first-raw-output',0),('omit-last-raw-output',1)]:
            bad=deepcopy(rows);del bad[0]['outputs'][index];catch(name,I.exact_rows(rows,bad))
        bad=deepcopy(rows);bad[0]['outputs'].reverse();catch('swap-output-occurrences',I.exact_rows(rows,bad))
        bad=deepcopy(rows);bad[0]['outputs'].append(deepcopy(raw[0]));catch('duplicate-raw-output',I.exact_rows(rows,bad))
        repeated=deepcopy(rows);repeated[0]['outputs'].append(deepcopy(raw[0]))
        check('negative-clean/repeated-raw-occurrence',I.exact_rows(repeated,deepcopy(repeated)))
        catch('deduplicate-legitimate-repeated-raw-list',I.exact_rows(repeated,rows))
        bad=deepcopy(good['partition']);bad[1].append(1);catch('set-vs-list-duplicate-label',I.whole_membership(t,P,bad))
        bad=deepcopy(good['partition']);bad.append([0,1]);catch('duplicate-parent-block',I.whole_membership(t,P,bad))
        forged={'preserved':True,'partition':raw[0]['partition']}
        catch('supplied-preservation-boolean',I.whole_membership(cross['tree'],cross['parents'],forged['partition']))
        bad=deepcopy(good['partition']);bad[1]=[0];catch('replace-whole-A-by-subblock',I.whole_membership(t,P,bad))
        reordered=deepcopy(good);reordered['partition'].reverse()
        check('negative-clean/reordered-block-membership',I.whole_membership(t,P,reordered['partition']))
        catch('reorder-blocks-is-not-exact-raw-list',I.exact_rows([{'id':'x','q':2,'outputs':[good]}],[{'id':'x','q':2,'outputs':[reordered]}]))
        rp=deepcopy(P);rp[0].reverse();check('negative-clean/reordered-parent-membership',I.whole_membership(t,rp,good['partition']))
        catch('reorder-parent-labels-is-not-literal-block-equality',any(b==rp[0] for b in good['partition']))
        catch('wrong-restriction-A',I.literal_restrict(t,P[0])==0)
        catch('wrong-restriction-C',I.literal_restrict(t,P[2])==[2,3])
        for name,change in [('root-source-cut',lambda b:b['cuts'].__setitem__(0,[])),('duplicate-source-cut',lambda b:b['cuts'].__setitem__(0,deepcopy(b['cuts'][1])))]:
            bad=deepcopy(good);change(bad);catch(name,I.graph.validate_emission(t,I.source_colors(t,P,a['beta']),2,bad))
        catch('duplicate-keyed-record',I.exact_rows(rows,rows+deepcopy(rows)))
        catch('missing-keyed-record',I.exact_rows(rows,[]))
        origins=[{'name':'visible','module':'Clean','kind':'theorem','axioms':[]},{'name':'_private.Clean.0.hidden','module':'Clean','kind':'theorem','axioms':[]},{'name':'branch.eq_1','module':'Clean','kind':'theorem','axioms':[]}]
        check('negative-clean/origin-records',I.exact_origins(origins,deepcopy(origins)))
        catch('duplicate-origin-record',I.exact_origins(origins,origins+[origins[0]]))
        catch('missing-origin-record',I.exact_origins(origins,origins[:-1]))
        catch('omit-private-origin',I.exact_origins(origins,[r for r in origins if not r['name'].startswith('_private')]))
        catch('omit-generated-origin',I.exact_origins(origins,[r for r in origins if '.eq_' not in r['name']]))
        if mode=='full':
            for f in E['malformed_sources']:
                check('malformed/'+f['id'],I.source_valid(f['tree'],f['parents'])==f['proper_source'])
                if 'generator_refusal' in f:
                    colors={x:0 for x in I.graph.syntax_leaves(f['tree'])};r=I.graph.generate(f['tree'],colors,9)
                    check('malformed/duplicate-original-refusal',r['outputs']==[] and r['refusals']==[f['generator_refusal']])
            f=F['local-cert-nonhomeomorphic-A'];o=f['budgets'][0]['outputs'][0]
            check('negative-clean/local-certificate',I.local_certificate_valid(f['tree'],f['target'],f['parents'],o['partition'],f['local_certificate']))
            for name,field,value in [('wrong-nonhomeomorphism','nonhomeomorphic',False),('wrong-local-source-cut','source_local_cuts',[[0]]),('wrong-local-target-cut','target_local_cuts',[[1,0]]),('forged-local-cost','cost',0)]:
                cert=deepcopy(f['local_certificate']);cert[field]=value
                catch(name,I.local_certificate_valid(f['tree'],f['target'],f['parents'],o['partition'],cert))
            expected_negatives=set(E['negative_controls'])-{'custom-axiom-public-unused','custom-axiom-private-unused','custom-axiom-private-used'}
            check('complete-negative-denominator',{n['id'] for n in negatives}==expected_negatives)
            check('complete-fixture-denominator',len(fixtures)==E['fixed_fixture_count'] and len(actual_rows)==E['fixed_budget_count'])
        result.update(status='PASS_PREPARATION_CONTROLS',positive_checks=len(checks),negative_catches=len(negatives),fixtures=len(fixtures),budget_cases=len(actual_rows),elapsed_seconds=time.monotonic()-start,checks=checks,negatives=negatives,details=detail,exact_rows=actual_rows)
    except Exception:
        result.update(status='FAIL_RETAINED',elapsed_seconds=time.monotonic()-start,checks=checks,negatives=negatives,details=detail,exception=traceback.format_exc())
        dest.write_text(json.dumps(result,indent=2)+'\n');raise
    dest.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:result[k] for k in ('status','mode','fixtures','budget_cases','positive_checks','negative_catches','elapsed_seconds')}))
if __name__=='__main__': main()
