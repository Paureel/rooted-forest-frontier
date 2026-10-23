#!/usr/bin/env python3
"""One-shot postcontact literal-remainder adaptor of the SAME own graph oracle.
No fresh replication/blind raw-multiset/order credit. Old files unchanged.
"""
import argparse,collections,copy,hashlib,importlib.util,json,sys,time
from fractions import Fraction
import continuation_v1 as c
P=c.P;PRE=c.PRE;POST=c.POST
sys.path.insert(0,str(POST));from case_inputs_v3 import cases,g

def swap(v,a,b):return b if v==a else a if v==b else v
def candidates(e,FM,FN):
    GM=[[swap(v,e['repY'],e['rho'])for v in B]for B in FM]
    GN=[[swap(v,e['repX'],e['gamma'])for v in B]for B in FN]
    out=[]
    for H in GM:
        for J in GN:
            A=copy.deepcopy(GM);A.remove(H);B=copy.deepcopy(GN);B.remove(J)
            out.append([[v for v in H if v in e['X']]+[v for v in J if v in e['Y']]]+A+B)
    return out
def literal(F):return tuple(tuple(B)for B in F)
def best(T,S,Fs):return next(iter(sorted([F for F in Fs if g.g.agreement(T,S,F)],key=len)),None)
def hulls(t,F):return [sorted(g.g.hull(t,tuple(sorted(B))))for B in F]
def actual_hulls(H):return [sorted(''.join('1'if b else'0'for b in p)for p in B)for B in H]

def controls():
    e=cases[0];FM=[[0,10]];FN=[[1],[11,3,2]]
    expected=[[[0,1],[0,3,2]],[[0,3,2],[1]]]
    assert candidates(e,FM,FN)==expected
    d=g.setup(e);assert not g.g.agreement(d['T'],d['S'],expected[0]);assert g.g.agreement(d['T'],d['S'],expected[1]);assert best(d['T'],d['S'],expected)==expected[1]
    dup=candidates(e,FM*2,FN);assert len(dup)==4 and len(set(map(literal,dup)))==2
    checks=[]
    for tag,bad in [('old unrenamed remainders',g.merge_candidates(FM,FN,e['X'],e['Y'])),('dropped invalid guess',expected[1:]),('wrong swapped representative',[[[0,1],[11,3,2]],expected[1]]),('wrong color filter',[[[0,1,0,3,2]],expected[1]]),('forgot duplicate values',list({literal(F):F for F in dup}.values()))]:
        target=dup if tag=='forgot duplicate values'else expected
        assert collections.Counter(map(literal,bad))!=collections.Counter(map(literal,target));checks.append({'control':tag,'caught':True})
    c.write('LITERAL-ADAPTOR-CONTROLS-v1.json',{'status':'PASS','postcontact':True,'blind_credit':0,'manual_FM':FM,'manual_FN':FN,'manual_full_candidates':expected,'duplicate_candidate_count':4,'controls':checks,'script_sha256':c.sha(__file__)})
    print(json.dumps({'literal_controls':'PASS','corruptions':len(checks)}))

def pretest(e,row,which,d):
    a,b=('TY','SY')if which=='outside'else('TMY','SMY');T,S=d['trees'][a],d['trees'][b]
    v=e['costs']['Y'if which=='outside'else'MY'];r=row[which]
    assert r['status']==('FOUND'+str(v)if v<=1 else'REJECT')
    if v<=1:
        F=r['forest'];assert g.g.agreement(T,S,F)and len(F)-1==v
        p=r['cut']
        if p is None:assert v==0 and F==[g.g.leaves(S)]
        else:
            q=''.join('1'if b else'0'for b in p);assert q and q in g.g.graph(S)[0]
            inside=[x for addr,x in g.g.graph(S)[1].items()if addr.startswith(q)]
            assert F==[inside,[x for x in g.g.leaves(S)if x not in inside]]

def compare():
    assert json.loads((P/'LITERAL-ADAPTOR-CONTROLS-v1.json').read_text())['status']=='PASS'
    at=time.perf_counter();read=json.loads((POST/'readouts-full-v4.json').read_text());pin=json.loads((POST/'READOUT-PINS-v3.json').read_text())
    assert read['status']=='PASS'and read['returncode']==0 and read['source_sha256']==pin['source_sha256']==c.sha(POST/'Readouts_v3.lean')
    for name,h in pin['frozen_inputs'].items():assert c.sha(PRE/name)==h
    stdout=(POST/'readouts-full-v4.stdout.log').read_text();stderr=(POST/'readouts-full-v4.stderr.log').read_text()
    assert [json.loads(l)for l in stdout.splitlines()if l.startswith('{')]==read['rows']
    assert [l.split('|')[1:]for l in stderr.splitlines()if l.startswith('TRACE|')]==read['trace']
    bank={e['id']:e for e in cases};assert len(bank)==12
    rs=[r for r in read['rows']if r.get('kind')!='WITNESS'];ws=[r for r in read['rows']if r.get('kind')=='WITNESS']
    assert len(rs)==38 and len(ws)==8
    assert {(r['id'],r['q'])for r in rs}=={(e['id'],int(q))for e in cases for q in e['answers']}
    # Frozen hand values/families checked against the same predecessor original-graph engine.
    truth=[g.check_case(e)for e in cases]
    rows=[];traces=collections.defaultdict(list)
    for tag,q,kind,budget in read['trace']:traces[(tag,int(q))].append((kind,int(budget)))
    for r in rs:
        e=bank[r['id']];q=r['q'];d=g.setup(e);ts=d['trees'];assert r['status']==e['answers'][str(q)]
        assert [g.g.tree(x)for x in r['trees']]==[ts[k]for k in ['TX','SX','TY','SY','TMX','SMX','TMY','SMY']]
        pretest(e,r,'outside',d);pretest(e,r,'marked_outside',d)
        admit=e['costs']['Y']==1
        jobs=g.jobs(d,q)if admit else[]
        assert [{'T':g.g.tree(x['T']),'S':g.g.tree(x['S']),'budget':x['budget']}for x in r['planned_jobs']]==[{k:v for k,v in j.items()if k!='kind'}for j in jobs]
        assert Fraction(r['mass'])==(Fraction(200,233)if jobs else 0)
        assert collections.Counter(traces[(e['id'],q)])==collections.Counter((j['kind'],j['budget'])for j in jobs)
        assert r['FX']==g.callback_fixture(e,'X',100)and r['FM']==g.callback_fixture(e,'MX',100)
        assert r['callback_replies']==([g.callback_fixture(e,'X',q-1),g.callback_fixture(e,'MX',q-1)]if jobs else[])
        FX,FY,FM,FN=r['FX'],r['FY'],r['FM'],r['FN']
        if admit:
            assert g.g.agreement(ts['TY'],ts['SY'],FY)and len(FY)-1==1
            assert FN is not None and g.g.agreement(ts['TMY'],ts['SMY'],FN)and len(FN)-1==e['costs']['MY']
            if r['marked_outside']['status']=='REJECT':assert FN==[[e['gamma']]]+FY and len(FN)-1==2
        cs=candidates(e,FM,FN)if FN is not None else[]
        assert r['candidate_multiset']==cs and len(cs)==(len(FM)*len(FN)if FN is not None else 0)
        valid=[F for F in cs if g.g.agreement(d['T'],d['S'],F)]
        assert r['valid_candidates']==valid
        chosen=best(d['T'],d['S'],cs);assert r['pick']==chosen
        stable=FN is not None and len(FM)==len(FX)and len(FN)==len(FY)
        recon=chosen if stable else FX+FY
        assert r['reconstructed']==recon
        assert r['concatenation_valid']==g.g.agreement(d['T'],d['S'],FX+FY)
        if FX+FY:
            assert actual_hulls(r['concatenation_hulls_T'])==hulls(d['T'],FX+FY)
            assert actual_hulls(r['concatenation_hulls_S'])==hulls(d['S'],FX+FY)
        if r['status']=='MINIMUM':assert r['result']==recon and g.g.agreement(d['T'],d['S'],recon)and len(recon)-1==e['costs']['global']<=q
        else:assert r['result']is None
        rows.append({'id':e['id'],'q':q,'status':r['status'],'candidate_count':len(cs),'invalid_guesses':len(cs)-len(valid),'duplicate_literal_values':len(cs)-len(set(map(literal,cs))),'planned_jobs':len(jobs),'actual_calls':len(traces[(e['id'],q)]),'stable_diagnostic':stable,'diagnostics_are_not_production_invocations':True})
    for r in ws:
        e=bank[r['id']];d=g.setup(e);assert r['forest']==e['hulls']['forest']and r['agreement']is True
        for k in ['T','S']:assert actual_hulls(r['hulls_'+k])==hulls(d[k],r['forest'])==[sorted(H)for H in e['hulls'][k]]
    c.write('LITERAL-ACTUAL-COMPARISON-v1.json',{'status':'PASS_WITH_RETAINED_COVERAGE_DEBTS','postcontact_literal_adaptor':True,'new_blind_raw_order_credit':0,'replication_credit':0,'semantic_rows':len(rs),'original_hull_witness_rows':len(ws),'actual_callback_observations':len(read['trace']),'rows':rows,'frozen_hand_graph_checks':truth,'six_label_complete_global_family_debts':['hard-marked-callback6','both-marked-unstable6'],'precontact_order_eagerness':'UNKNOWN; observed trace only','source_sha256':c.sha(POST/'Readouts_v3.lean'),'readout_sha256':c.sha(POST/'readouts-full-v4.json'),'stdout_sha256':c.sha(POST/'readouts-full-v4.stdout.log'),'stderr_sha256':c.sha(POST/'readouts-full-v4.stderr.log'),'seconds':time.perf_counter()-at})
    print(json.dumps({'literal_actual':'PASS_WITH_DEBTS','rows':len(rs),'witnesses':len(ws),'calls':len(read['trace']),'invalid_guesses':sum(r['invalid_guesses']for r in rows),'seconds':time.perf_counter()-at}))

if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('mode',choices=['controls','compare']);a=ap.parse_args();{'controls':controls,'compare':compare}[a.mode]()
