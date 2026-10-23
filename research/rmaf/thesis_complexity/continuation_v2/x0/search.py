#!/usr/bin/env python3
"""One-shot X0 finite hostile search; see SEARCH-PIN.md. Exact Fraction algebra."""
from evaluator import *

def swap_labels(n,a,b):
    return replace(n,label=b if n.label==a else a if n.label==b else n.label,children=tuple(swap_labels(c,a,b) for c in n.children))

def local_prefix(s,local,budget0):
    """Physical diagnostic only: frontier IH is an explicit unresolved import."""
    s,p,events,term=normalize(s)
    node=dict(state=snapshot(s),normalization=events)
    if term:
        node.update(kind='terminal',reason=term,mass='0',intercept=1,V=1,L=0);return node,F(0),1,1,0
    if not set(p)<=set(local):
        m=F(2)**(s.budget-budget0);node.update(kind='conditional-frontier',pair=p,mass=str(m),intercept=-3,V=0,L=1,required_hypothesis='empty-credit smaller-budget IH for this physical state; source reset NOT asserted')
        return node,m,-3,0,1
    r=rule(s,p);m=F(0);v=1;l=0;intercept=1;node.update(kind='expanded',rule=r,children=[])
    for b in r['branches']:
        if b['legal']:
            ch,mm,ii,vv,ll=local_prefix(transition(s,r,b),local,budget0)
            m+=mm;intercept+=ii;v+=vv;l+=ll;node['children'].append(dict(branch=b['name'],tree=ch))
    node.update(mass=str(m),intercept=intercept,V=v,L=l)
    return node,m,intercept,v,l

def check_instance(st,tag):
    pairs=[('a','t'),('d0','a'),('a','c'),('d','a'),('x','y')]
    try:
        j,rows=trace(st,pairs,['C','A','C','A'])
        if not(rows[0]['rule']['case']=='A2BC' and rows[1]['rule']['case'] in ('A2BC','A3BC') and sum(b['legal'] for b in rows[1]['rule']['branches'])==1 and rows[2]['rule']['case']=='A2BC' and rows[3]['rule']['case']=='A2BC' and sum(b['legal'] for b in rows[3]['rule']['branches'])==2):return dict(tag=tag,status='rejected-credit-regime')
        r=rows[-1]['rule']
        if not (r['case']=='A3BC' and len(r['pendants'])==3 and all(b['legal'] for b in r['branches'])):return dict(tag=tag,status='rejected-exception-regime',last_rule=r)
        n2,p2,_,_=index(j.f2);b=siblings('a',n2,p2)[0];inside='x' in labels(n2[b])
        n1,p1,_,_=index((j.f1,));e=siblings('a',n1,p1)[0]
        if len(active(n1[e]))!=3:return dict(tag=tag,status='rejected-e-size')
        child_results={}
        for branch in r['branches']:
            ch=transition(j,r,branch);f=full(ch);pr,m,i,v,l=local_prefix(ch,['a','x','y','h'],ch.budget)
            target_m=F(1,2) if branch['name']=='A' else F(1,4)
            target_i=-2 if branch['name']=='A' else 2
            child_results[branch['name']]=dict(actual_count=f['count'],full_tree=f,prefix=pr,mass=str(m),intercept=i,V=v,L=l,sufficient_envelope_pass=m<=target_m and i<=target_i,point128_residual=str(F(128)*m+i-(F(128)*target_m+target_i)))
        return dict(tag=tag,status='reached',inside_b=inside,b=b,source_credits={'P':['a'],'Q':[]},trace=rows,children=child_results,H1_pass=(not inside or child_results['C']['actual_count']<=2),H2_conditional_envelope=child_results['C']['sufficient_envelope_pass'],H3_conditional_envelope=child_results['A']['sufficient_envelope_pass'])
    except (AssertionError,KeyError,StopIteration) as ex:return dict(tag=tag,status='rejected-source-path',reason=str(ex))

def main():
    controls_result=controls()
    data=json.loads((BASE/'controls-frozen.json').read_text());ins=next(c for c in data['controls'] if c['id']=='inside-b-reached')['instance']
    st=initial(ins['input_f1'],ins['input_f2'],20)
    candidates=[('identity',st)]
    labs=sorted(labels(st.f2[0])-{'rho'})
    for a,b in itertools.combinations(labs,2):candidates.append((f'swap-F2:{a}:{b}',replace(st,f2=(swap_labels(st.f2[0],a,b),))))
    assert len(candidates)<=100
    start=time.perf_counter();results=[]
    path=OUT/'thesis-runtime-continuation-v2-x0-pilot.json'
    for tag,s in candidates:
        t=time.perf_counter();res=check_instance(s,tag);res['elapsed_seconds']=time.perf_counter()-t;results.append(res)
        path.write_text(json.dumps(dict(status='running',results=results),indent=2))
    reached=[x for x in results if x['status']=='reached']
    summary=dict(status='finite-pilot-complete',attempted=len(results),reached=len(reached),inside=sum(x['inside_b'] for x in reached),elapsed_seconds=time.perf_counter()-start,H1_fires=[x['tag'] for x in reached if not x['H1_pass']],H2_conditional_fires=[x['tag'] for x in reached if not x['H2_conditional_envelope']],H3_conditional_fires=[x['tag'] for x in reached if not x['H3_conditional_envelope']],scope='finite search only; conditional prefix frontier credits not source-certified')
    path.write_text(json.dumps(dict(summary=summary,controls=dict(passed=len(controls_result['checks']),catalog=12),results=results),indent=2));print(json.dumps(summary))
if __name__=='__main__':main()
