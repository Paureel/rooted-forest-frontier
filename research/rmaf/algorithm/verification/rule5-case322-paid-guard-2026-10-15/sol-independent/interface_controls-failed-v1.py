"""One-shot pre-candidate interface controls on own fixed original fixtures.
Shared own graph code is explicit and earns no extra independent replication.
"""
import copy, hashlib, itertools, json, pathlib, time, traceback
from fractions import Fraction
import graph_controls as gc
H=pathlib.Path(__file__).resolve().parent;og=gc.og
def check(name,ok,checks):
    checks.append(dict(name=name,passed=bool(ok)))
    if not ok:raise AssertionError(name)
def canonical_state(branch,t,s):
    g=s if branch['role']=='source'else t;target=t if branch['role']=='source'else s
    return dict(target=target,source=g,P=branch['partition'],forest=[g.restricted(p)for p in branch['partition']])
def request(b,t,s,index,q):
    g=s if b['role']=='source'else t;target=t if b['role']=='source'else s
    return dict(index=index,role=b['role'],originalCuts=b['originalCuts'],partition=b['partition'],
                current_tree=g.tree,target=target.tree,sourceForest=gc.source_forest(g,b['partition']),
                paid=b['paid'],remaining=q-b['paid'])
def main():
    checks=[];families=[];allrows=[];t0=time.perf_counter();nonminimum=False;affordability=False
    for name in ['fallback','cside2','allbside-d3','allbside-d4','allbside-d5']:
        start=time.perf_counter();f=gc.fixture(name);t,s=og.Graph(f['T']),og.Graph(f['S']);bs,_=gc.plan(f)
        record=json.loads((H/('pilot-fallback-v1.json'if name=='fallback'else'family-'+name+'-v1.json')).read_text())
        if name=='fallback':record=record['family']
        allF=list(og.partitions(sorted(t.labels)));agrees=[F for F in allF if og.agreement(t,s,F)]
        check(name+' exact finite AF receipt',agrees==record['agreements']and len(allF)==record['partition_count'],checks)
        tables=[]
        for i,b in enumerate(bs):
            state=canonical_state(b,t,s);tab=[F for F in allF if og.forest_agrees(state,F)]
            expected=[F for F in agrees if og.refines(F,b['partition'])]
            check(name+f' branch{i} full ForestState equivalence',tab==expected,checks)
            check(name+f' branch{i} sourceForest no missing block',len(gc.source_forest(state['source'],b['partition']))==len(b['partition']),checks)
            tables.append(tab)
            for F in tab:assert b['paid']+len(F)-len(b['partition'])==len(F)-1
            if len({len(F)for F in tab})>1:nonminimum=True
            if name=='allbside-d4'and i==2:
                zero=[F for F in tab if len(F)-len(b['partition'])==0]
                affordability=bool(zero)and b['paid']>2 and all(len(F)-1>2 for F in zero)
        masses={str(base):str(sum(base**(-b['paid'])for b in bs))for base in [Fraction(2),Fraction(233,100),Fraction(3)]}
        for base in [Fraction(2),Fraction(233,100),Fraction(3)]:
            mass=sum(base**(-b['paid'])for b in bs);assert mass<=base**(-1)+3*base**(-2)
            if name=='cside2':assert mass==base**(-1)+3*base**(-2)
        families.append(dict(name=name,partition_count=len(allF),branch_tables=tables,raw_LIST_mass=masses,seconds=time.perf_counter()-start))
        orientation=json.loads((H/('orientations-'+name+'-v1.json')).read_text())
        for row in orientation['rows']:
            rf=row['fixture'];rt,rs=og.Graph(rf['T']),og.Graph(rf['S']);rbs,_=gc.plan(rf);queryrows=[]
            for q in range(len(rt.labels)):
                requests=[request(b,rt,rs,i,q)for i,b in enumerate(rbs)if b['paid']<=q]
                feasible=[F for F in agrees if len(F)-1<=q]
                answer=any(any(len(F)-len(b['partition'])<=q-b['paid']for F in agrees if og.refines(F,b['partition']))for b in rbs if b['paid']<=q)
                assert answer==bool(feasible)
                queryrows.append(dict(q=q,requests=requests,decision=answer,minimum_components=3 if feasible else None))
            allrows.append(dict(fixture=rf,geometry=row['geometry'],branches=row['branches'],query_expectations=queryrows))
        if time.perf_counter()-start>10:raise TimeoutError('interface family10s cap')
    check('nonminimal feasible answer does not imply least',nonminimum,checks)
    check('unaffordable d4 truncated subtraction would exceed parentbudget',affordability,checks)
    f=gc.fixture('allbside-d4');t,s=og.Graph(f['T']),og.Graph(f['S']);bs,_=gc.plan(f)
    good=request(bs[-1],t,s,2,6)
    for field,value in [('role','source'),('originalCuts',['']),('partition',list(reversed(good['partition']))),
                        ('sourceForest',good['sourceForest'][:-1]),('current_tree',s.tree),('target',t.tree),('index',0),('remaining',99),('paid',2)]:
        bad=copy.deepcopy(good);bad[field]=value
        check('request identity corruption '+field,bad!=good,checks)
    # Source-Q can overlap target hulls yet the physical forest refinement is valid.
    qt,qs=og.Graph([[0,1],[2,3]]),og.Graph([[0,2],[1,3]])
    P=[[0,2],[1,3]];state=dict(target=qt,source=qs,P=P,forest=[qs.restricted(p)for p in P])
    check('targetQ separation not needed',not og.separated(qt,P)and og.forest_agrees(state,[[0],[1],[2],[3]]),checks)
    broken=copy.copy(state);broken['forest']=state['forest'][:-1]
    check('dropped sourceForest component fails',not og.forest_agrees(broken,[[0],[1],[2],[3]]),checks)
    out=dict(checks=checks,passed=len(checks),families=families,rows=allrows,row_count=len(allrows),
             seconds=time.perf_counter()-t0,scope='fresh finite controls; own shared graph layer, zero new independent replication credit')
    dest=H/'interface-expectations-output-v1.json'
    if dest.exists():raise ValueError('preserve previous receipt')
    dest.write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(dict(passed=len(checks),rows=len(allrows),seconds=out['seconds'])))
if __name__=='__main__':
    try:main()
    except Exception:
        with(H/'interface-failures-v1.log').open('a')as f:f.write(traceback.format_exc()+'\n')
        raise
