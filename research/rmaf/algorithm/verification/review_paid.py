"""Independent paid-route reconstruction and actual CLI-path comparison.
The original graph instrument was frozen before candidate inspection. This
consumer harness contains no imported candidate modules; invocation is CLI.
"""
import itertools, json, os, subprocess, sys, time
from fractions import Fraction
from pathlib import Path
from independent_graph import Graph, exact, valid_graphs, thaw, priority
HERE=Path(__file__).resolve().parent
CAMPAIGN=HERE.parents[1]
WORKSPACE=CAMPAIGN.parents[1]
OUT=CAMPAIGN/'results'
CLI=CAMPAIGN/'algorithm/paid_cover/state_cli.py'
BASE=Fraction(231,100)
def write(name,x):
    (OUT/name).write_text(json.dumps(x,indent=2)+'\n')
def cp(parts): return tuple(sorted(tuple(sorted(b)) for b in parts))
def refines(fine,coarse): return all(any(set(b)<=set(c) for c in coarse) for b in fine)
def cli(raw,tag):
    path=HERE/(tag+'-input.json'); path.write_text(json.dumps(raw)+'\n')
    before=time.perf_counter()
    run=subprocess.run([str(WORKSPACE/'bootloops-python'),str(CLI),str(path)],capture_output=True,text=True)
    (HERE/(tag+'-stdout.json')).write_text(run.stdout)
    (HERE/(tag+'-stderr.log')).write_text(run.stderr)
    return run.returncode, json.loads(run.stdout) if run.returncode==0 else run.stderr, time.perf_counter()-before
def frontier(t,u,q,first=False):
    a,b=Graph(t),Graph(u)
    states=[]; seen=set(); tested=0
    # Numeric vertex order is a source presentation, not a borrowed predicate.
    for d in range(q+1):
        level=[]
        for cut in itertools.combinations(sorted(b.edges),d):
            tested+=1
            p=b.cut_partition(cut)
            if len(p)!=d+1 or p in seen: continue
            if not all(len(block)==3 or a.topology(block)==b.topology(block) for block in p): continue
            seen.add(p); level.append({'charge':d,'partition':thaw(p),'cuts':thaw(cut)})
        states.extend(level)
        if level and first: break
    return {'states':states,'tested':tested}
def cover(t,u,q):
    f=frontier(t,u,q)
    retained=[]; scans=0
    for s in f['states']:
        dominated=False
        for r in f['states']:
            scans+=1
            if r['charge']<s['charge'] and refines(s['partition'],r['partition']):
                dominated=True; break
        if not dominated: retained.append(s)
    vector=[x['charge'] for x in retained]
    return {'states':retained,'tested':f['tested'],'terminals':len(f['states']),'scans':scans,'vector':vector,'mass':str(sum((BASE**(-x) for x in vector),Fraction()))}
def validate(t,u,answer):
    a,b=Graph(t),Graph(u)
    assert answer['feasible']
    p=answer['partition']
    assert valid_graphs(a,b,p)[0]
    assert answer['additional_cuts']==len(p)-1
    for record in answer.get('reconstruction',[]):
        g=Graph(record['source'])
        assert cp(g.cut_partition(record['cuts']))==cp(record['blocks'])
        assert len(record['cuts'])==len(record['blocks'])-1
    if t is not None:
        assert answer['components']==len(p)
    return True

def main():
    control_inputs=[('empty',{'target':None,'source':[]},0),('singleton',{'target':0,'source':[0]},1),('identical',{'target':[[0,1],[2,3]],'source':[[[0,1],[2,3]]]},1),('triplet',{'target':[[0,1],2],'source':[[[0,2],1]]},2),('crossed',{'target':[[0,1],[2,3]],'source':[[[0,2],[1,3]]]},3)]
    ctrl=[]
    for name,raw,k in control_inputs:
        code,ans,sec=cli(raw,'paid-control-'+name)
        assert code==0,(name,ans)
        if k: validate(raw['target'],raw['source'][0],ans)
        assert ans['components']==k
        ctrl.append({'name':name,'components':k,'seconds':sec,'pass':True})
    for name,raw in [('duplicate',{'target':[[0,1],2],'source':[[0,[1,1]]]}),('missing',{'target':[[0,1],2],'source':[[0,1]]}),('foreign',{'target':[[0,1],2],'source':[[0,[1,3]]]}),('negative-budget',{'target':[0,1],'source':[[0,1]],'budget':-1}),('bool-budget',{'target':[0,1],'source':[[0,1]],'budget':True})]:
        code,ans,sec=cli(raw,'paid-control-'+name); assert code!=0,name
        ctrl.append({'name':name,'rejected':True,'seconds':sec,'pass':True,'error':ans.splitlines()[-1]})
    write('algorithm-review-paid-cli-controls.json',ctrl)
    t=[[[[3,4],2],1],0]; u=[[[1,4],2],[0,3]]
    independent=exact(t,u); first=frontier(t,u,2,True); full=cover(t,u,2)
    first_rows=[]
    for s in first['states']:
        e=exact(t,u,required_refinement=s['partition'])
        first_rows.append({**s,'exact_total':e['cuts'],'exact_residual':e['cuts']-s['charge'],'witnesses':e['optimal']})
    assert independent['cuts']==2 and len(first_rows)==2
    assert {cp(x['partition']) for x in first_rows}=={cp([[0,3],[1,2,4]]),cp([[0,2,3],[1,4]])}
    assert all(x['charge']==1 and x['exact_residual']==2 and x['exact_total']==3 for x in first_rows)
    assert (full['tested'],full['terminals'],len(full['states']),full['scans'])==(37,17,10,180),full
    assert full['vector']==[1,1]+[2]*8 and full['mass']=='126200/53361'
    code,ans,sec=cli({'target':t,'source':[u],'budget':2},'paid-five-witness')
    assert code==0; validate(t,u,ans); assert not ans['fallback_used']
    assert {cp(x['partition']) for x in full['states']}=={cp(x['partition']) for x in ans['cover']['states']}
    assert full['vector']==ans['cover']['paid_vector'] and full['mass']==ans['cover']['exact_mass']
    child_rows=[]
    for s in full['states']:
        e=exact(t,u,required_refinement=s['partition'])
        child_rows.append({**s,'exact_total':e['cuts'],'exact_residual':e['cuts']-s['charge'],'witnesses':e['optimal']})
    necessity=[x for x in child_rows if x['exact_total']==2]
    corrupted=[x for x in child_rows if x['exact_total']!=2]
    assert necessity and corrupted and min(x['exact_total'] for x in corrupted)==3
    lost=cp([[0,1,4],[2],[3]])
    assert not any(refines(lost,x['partition']) for x in corrupted)
    assert any(refines(lost,x['partition']) for x in child_rows)
    charge_mutant={**necessity[0],'charge':necessity[0]['charge']-1}
    caught_charge=charge_mutant['charge']!=len(charge_mutant['partition'])-1
    assert caught_charge
    mutated_vector=[1,1]+[3]*8
    assert sum((BASE**(-x) for x in mutated_vector),Fraction())!=Fraction(full['mass'])
    write('algorithm-review-paid-B1-B2-B3.json',{'scope':'finite selector/recurrence checks, not existence of any safe cover','exact_parent':independent,'B2':first_rows,'B3':full,'every_emitted_child':child_rows,'actual_cli_seconds':sec,'actual_cli_output':'algorithm/verification/paid-five-witness-stdout.json','copy_mutations':{'omitted_necessary_entries':necessity,'nonempty_corrupted_cover':corrupted,'lost_optimum':thaw(lost),'corrupted_best_total':min(x['exact_total'] for x in corrupted),'clean_best_total':min(x['exact_total'] for x in child_rows),'false_charge':charge_mutant,'false_charge_caught':caught_charge,'false_recurrence_term_caught':True}})
    sample=json.loads((HERE/'RESERVED-n8-seed40871.json').read_text())
    rows=[]
    for item in sample['pairs']:
        before=time.perf_counter(); t,u=item['T'],item['Tprime']
        e=exact(t,u)
        code,ans,secs=cli({'target':t,'source':[u]},'paid-reserved-'+str(item['id']))
        assert code==0,(item['id'],ans)
        validate(t,u,ans); assert ans['additional_cuts']==e['cuts']
        c=cover(t,u,e['cuts'])
        expected_keys={cp(s['partition']) for s in c['states']}
        got_keys={cp(s['partition']) for s in ans['cover']['states']}
        assert expected_keys==got_keys and c['mass']==ans['cover']['exact_mass']
        for s in ans['cover']['states']:
            assert s['charge']==len(s['partition'])-1
            g=Graph(u)
            assert cp(g.cut_partition(s['precuts'][0]))==cp(s['partition'])
        eligible=priority(t,u)['excluded_2a_to_2d']
        rows.append({'id':item['id'],'exact':e,'cli_cuts':ans['additional_cuts'],'cover_states':len(got_keys),'vector':c['vector'],'mass':c['mass'],'query_count':len(ans['queries']),'fallback':ans['fallback_used'],'eligible_initial_2e':eligible,'seconds':time.perf_counter()-before,'cli_seconds':secs,'pass':True})
        write('algorithm-review-paid-reserved-progress.json',{'completed':len(rows),'total':16,'rows':rows})
        if len(rows)==1:
            write('algorithm-review-paid-reserved-pilot.json',{'cases':1,'measured_seconds':rows[0]['seconds'],'projected_16_seconds':16*rows[0]['seconds'],'assumption':'linear per pair only; independent graph and CLI same n8 distribution; stop/replan if material slowdown','progress_unit':'completed independent+CLI pair rows'})
    write('algorithm-review-paid-reserved-final.json',{'completed':16,'passed':16,'eligible_initial_2e':sum(x['eligible_initial_2e'] for x in rows),'rows':rows})
    print(json.dumps({'cli_controls':len(ctrl),'B2_min':3,'B3_vector':full['vector'],'B3_mass':full['mass'],'reserved_passed':16,'eligible_initial_2e':sum(x['eligible_initial_2e'] for x in rows)}))
if __name__=='__main__': main()
