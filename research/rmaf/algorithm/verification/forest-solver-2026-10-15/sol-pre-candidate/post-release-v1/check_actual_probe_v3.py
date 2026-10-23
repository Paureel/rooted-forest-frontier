#!/usr/bin/env python3
"""Fresh graph/partition comparison against actual candidate-call receipts.

The graph evaluator and literal minima were frozen before candidate contact.
This adapter is post-contact instrumentation and does not add an independent
replication count. All raw outputs and final partitions count by occurrence.
"""
from collections import Counter,defaultdict
from copy import deepcopy
from fractions import Fraction
import json
from pathlib import Path
import sys
import time
HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE.parent))
from graph_partition_v2 import Graph,State,partitions,equal
inp=json.loads((HERE/'actual-probe-inputs-v4.json').read_text())
cases={c['id']:c for c in inp['cases']}
counts=Counter();selected=[];queries=[]


def fkey(f):return tuple(sorted(tuple(sorted(b)) for b in f))


def node_check(node):
    state=State(node['T'],node['ss']);q=node['q'];out=node['actual_return']
    equal(node['proper'],state.proper,'actual proper guard')
    equal(node['current_agrees'],state.agrees([s.taxa for s in state.ss]),'literal current forest guard')
    m,valid=state.exact()
    equal(out is not None,m is not None and m<=q,'actual solver affordability')
    if out is not None:
        equal(state.agrees(out),True,'actual returned original agreement')
        equal(len(out)-len(state.ss),m,'actual returned attained minimum')
    counts['nodes']+=1;counts['case_'+node['case']]+=1
    if not state.proper:
        equal(node['case'],'improper','improper source refusal')
        return []
    if node['case']=='done':
        equal(out,[s.taxa for s in state.ss],'actual done payload')
        return []
    if node['case']=='singleton':
        equal(len(state.ss),1,'one-source callback')
        equal([node['query_target'],node['query_source'],node['query_budget']],
              [node['T'],node['ss'][0],q],'literal same-label same-q singleton query')
        equal(node['ordinary_return'],out,'checked fixture ordinary return')
        queries.append({'kind':'singleton','labels':len(state.T.taxa),'budget':q})
        return []
    if node['case']=='disjoint':
        equal(state.current_disjoint(),True,'actual disjoint route')
        jobs=node['jobs'];equal(jobs is not None,True,'proper job preparation')
        equal(len(jobs),len(state.ss),'one ordinary pair per literal current source')
        for job,s in zip(jobs,state.ss):
            equal(job['target'],state.T.restriction(s.taxa),'actual target restriction')
            equal(job['source'],s.tree,'actual ordinary source')
            local=State(job['target'],[job['source']]);lm,lv=local.exact()
            equal(local.proper,True,'ordinary proper pair')
            if len(state.ss)>=2:equal(len(local.T.taxa)<len(state.T.taxa),True,'strict label decrease multiple sources')
            if job['kind']=='resolved':
                equal([job['cost'],local.agrees(job['forest']),len(job['forest'])-1],
                      [lm,True,lm],'depth01 exact resolved result')
                equal(lm<=1,True,'depth01 cost <=1')
            else:equal(lm>=2,True,'depth01 rejected lower bound')
        equal(node['meter_answers'],node['actual_attempt_answers'],'actual schedule/meter answer identity')
        equal(node['meter_calls'],[r['budget'] for r in node['query_calls']],'literal query occurrence budget trace')
        known=sum(j['cost'] for j in jobs if j['kind']=='resolved');pending=sum(j['kind']=='hard' for j in jobs)
        equal([node['knownCost'],node['pending'],node['allocated']],
              [known,pending,max(0,q-known-2*max(0,pending-1))],'ordinary paid allocation')
        if q<known+2*pending:equal(node['query_calls'],[],'early lower-bound refusal has no ordinary query')
        for call in node['query_calls']:
            local=State(call['target'],[call['source']]);lm,_=local.exact()
            equal(call['budget'],node['allocated'],'same actual allowance for each hard query')
            equal(call['budget']<=q,True,'ordinary query budget upper bound')
            equal(call['answer'] is not None,lm<=call['budget'],'mock fixture exact answer existence')
            if call['answer'] is not None:
                equal([local.agrees(call['answer']),len(call['answer'])-1],[True,lm],'mock returned ordinary minimum')
            queries.append({'kind':'disjoint','whole_labels':len(state.T.taxa),
                'query_labels':len(local.T.taxa),'budget':call['budget'],'state_budget':q,
                'known':known,'pending':pending})
        return []
    equal(node['case'],'overlap','unhandled actual route')
    a,b=node['selected_left'],node['selected_right'];v=tuple(node['selected_vertex'])
    equal(0<=a<b<len(state.ss),True,'actual distinct selected indices')
    equal(v in state.T.hull(state.ss[a].taxa) and v in state.T.hull(state.ss[b].taxa),True,'actual original shared target vertex')
    equal(v not in state.T.at,True,'selected original vertex is not a leaf')
    expected_raw=[]
    for i,key in [(a,'left_generation'),(b,'right_generation')]:
        gen=node[key];source=state.ss[i]
        rs=state.T.regions(v,source.taxa)
        equal(len(rs) in [2,3],True,'two or three nonempty incident regions')
        colors=defaultdict(list)
        for x,c in gen['colors']:colors[c].append(x)
        equal(sorted(sorted(x) for x in colors.values()),rs,'actual colorLabel region readout')
        expected_raw.extend({'parent':i,**r} for r in gen['outputs'])
    stripped=[{k:r[k] for k in ['parent','partition','sourceCuts','d']} for r in node['raw']]
    equal(stripped,expected_raw,'both full raw lists concatenated literally by occurrence')
    children=[];child_states=[]
    for r in node['raw']:
        i=r['parent'];source=state.ss[i];d=r['d'];Q=r['partition']
        equal(d,len(r['sourceCuts']),'actual d is literal source-cut count')
        equal(len({tuple(x) for x in r['sourceCuts']}),d,'no repeated source cut address')
        equal(all(x and tuple(x) in source.adj for x in r['sourceCuts']),True,'actual original source edge addresses')
        blocks,leafless=source.cut_components(r['sourceCuts'])
        equal(fkey(blocks),fkey(Q),'actual source cut graph partition')
        equal(leafless,0,'actual emitted cuts have no leafless pieces')
        equal(len(Q)-1,d,'literal source component delta')
        equal([r['paid_guard'],1<=d<=q],[True,True],'all actual raw outputs paid before subtraction')
        expected_ss=node['ss'][:i]+[source.restriction(B) for B in Q]+node['ss'][i+1:]
        equal(r['child_sources'],expected_ss,'replace only named source by literal restrictions')
        child=State(node['T'],expected_ss);equal(child.proper,True,'every actual child proper')
        equal(len(child.ss)-len(state.ss),d,'actual additional component change')
        equal(q-d<q,True,'strict forest budget decrease')
        for F in partitions(state.T.taxa):
            ha=state.agrees(F);hb=child.agrees(F)
            ref=all(any(set(B)<=set(s.taxa) for s in child.ss) for B in F)
            if hb:
                equal([ha,ref],[True,True],'every child final forest lifts/refines')
                equal(len(F)-len(state.ss),d+len(F)-len(child.ss),'exact d+residual cost for every child forest')
                counts['lifted_forests']+=1
            if ha and ref:equal(hb,True,'every refined original final forest transports')
        children.append({'T':node['T'],'ss':expected_ss,'q':q-d});child_states.append((i,child))
        counts['raw_occurrences']+=1
    for F in valid:
        occupied=[]
        for source in state.ss:
            local=[B for B in F if set(B)<=set(source.taxa)]
            occupied.append(any(v in state.T.hull(B) for B in local))
        equal(sum(occupied[i] for i in [a,b])<=1,True,'actual two-parent ownership from final target agreement')
        if len(F)-len(state.ss)<=q:
            equal(any(c.agrees(F) for _,c in child_states),True,'every affordable original forest covered')
            for i in [a,b]:
                if not occupied[i]:equal(any(j==i and c.agrees(F) for j,c in child_states),True,'avoiding parent gives actual emitted coverage')
            counts['covered_forests']+=1
    for c in [Fraction(2),Fraction(3)]:
        total=sum((c**(-r['d']) for r in node['raw']),Fraction())
        equal(total<=2/c,True,'actual raw rational mass at test base')
    selected.append({'q':q,'ss_labels':[s.taxa for s in state.ss],
                     'vertex':list(v),'raw_costs':[r['d'] for r in node['raw']],
                     'left_generation':{k:node['left_generation'][k] for k in ['visited','childAttempts','pruned','refusals']},
                     'right_generation':{k:node['right_generation'][k] for k in ['visited','childAttempts','pruned','refusals']}})
    return children


def check_rows(rows):
    for row in rows:
        case=cases[row['id']];trace=row['trace'];q=row['budget']
        equal([trace[0]['T'],trace[0]['ss'],trace[0]['q']],
              [case['T'],case['ss'],q],'literal registered root input')
        def walk(index,expected):
            equal(index<len(trace),True,'missing raw recursive call occurrence')
            node=trace[index]
            equal([node['T'],node['ss'],node['q']],[expected['T'],expected['ss'],expected['q']],'raw recursion order/state/budget')
            children=node_check(node);index+=1
            for child in children:index=walk(index,child)
            return index
        end=walk(0,{'T':case['T'],'ss':case['ss'],'q':q})
        equal(end,len(trace),'extra/missing trace occurrence')
        root=State(case['T'],case['ss'])
        if case['proper']:
            equal(root.exact()[0],case['minimum'],'unchanged literal minimum expectation')
        counts['root_rows']+=1


result={'source':sys.argv[1],'scope':'finite actual calls versus frozen fresh graph route; mock ordinary fixtures only'}
try:
    rows=json.loads(Path(sys.argv[1]).read_text());started=time.perf_counter();check_rows(rows)
    if 'full' in sys.argv[1]:
        literal=json.loads((HERE/'ACTUAL-MASS-REALIZATION-v1.json').read_text())
        r=next(r for r in rows if r['id']==literal['id'] and r['budget']==2)['trace'][0]
        costs=[o['d'] for o in r['raw']]
        equal([r['selected_vertex'],costs],[literal['q2_selected_vertex'],literal['q2_raw_cost_occurrences']],'actual below-c2 fixture realization')
        m=sum((Fraction(3,2)**(-d) for d in costs),Fraction())
        equal(str(m),literal['q2_mass_c_three_halves'],'actual below-c2 mass')
        equal(m>Fraction(literal['false_bound_c_three_halves']),True,'actual false below-c2 bound caught')
        result['actual_below_c2_false_extension']={'caught':True,'raw_costs':costs,'mass':str(m),'bound':literal['false_bound_c_three_halves']}
    result['counts']=dict(counts);result['actual_selections']=deepcopy(selected);result['actual_queries']=deepcopy(queries)
    if 'pilot' in sys.argv[1]:
        catches=[]
        bad=deepcopy(rows);target=next(n for r in bad for n in r['trace'] if n['case']=='overlap' and n['raw']);target['raw']=target['raw'][1:]
        try:check_rows(bad)
        except AssertionError:catches.append('missing actual raw occurrence')
        else:raise AssertionError('missing raw plant survived')
        bad=deepcopy(rows);bad[0]['trace'][0]['actual_return']=[[0,1],[2,3]]
        try:check_rows(bad)
        except AssertionError:catches.append('forged original agreement')
        else:raise AssertionError('forged agreement plant survived')
        result['post_contact_adapter_false_twins']=catches
    result['seconds']=time.perf_counter()-started;result['passed']=True
except Exception as exc:
    result['passed']=False;result['failure']=repr(exc);raise
finally:Path(sys.argv[2]).write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items() if k not in ['actual_selections','actual_queries']}))
