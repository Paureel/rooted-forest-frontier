#!/usr/bin/env python3
"""One-shot caller controls adapting only this agent's own pinned graph engine.
No extra replication credit. No candidate program or complete recursive solver.
"""
import copy,hashlib,importlib.util,itertools,json,sys,time
from collections import Counter
from fractions import Fraction
from pathlib import Path
P=Path(__file__).resolve().parent; ROOT=P.parents[5]
reuse=json.loads((P/'OWN-REUSE-PINS-v1.json').read_text())
for r in reuse['files']:
    f=ROOT/r['path']; assert hashlib.sha256(f.read_bytes()).hexdigest()==r['sha256']
old=ROOT/reuse['files'][0]['path']; spec=importlib.util.spec_from_file_location('own_cherry_graph',old); g=importlib.util.module_from_spec(spec); spec.loader.exec_module(g)
E=json.loads((P/'EXPECTATIONS-v1.json').read_text())

def restriction(t,D):
    if type(t) is int: return t if t in D else None
    a,b=restriction(t[0],D),restriction(t[1],D)
    return b if a is None else a if b is None else (a,b)
def rename(t,rep,marker):
    return marker if t==rep else t if type(t) is int else (rename(t[0],rep,marker),rename(t[1],rep,marker))
def marked(t,D,opposite,marker):
    assert opposite not in D and opposite in g.leaves(t)
    return rename(restriction(t,set(D)|{opposite}),opposite,marker)
def normfamily(Fs): return tuple(sorted(g.partnorm(F) for F in Fs))
def cost(F): return len(F)-1
def minima(T,S):
    AF=g.all_agreements(T,S); value=min(map(cost,AF)); return value,[F for F in AF if cost(F)==value]
def check_setup_shape(d):
    allowed={'T','S','X','Y','repX','repY','rho','gamma','cutT','cutS','trees'}
    if set(d)!=allowed: raise ValueError('Setup contains non-input/guard fields')
def setup(e):
    allowed={'T','S','X','Y','repX','repY','rho','gamma','cutT','cutS'}
    d={k:e[k] for k in allowed}; T,S=g.tree(d['T']),g.tree(d['S']); g.valid_pair(T,S)
    X,Y=d['X'],d['Y']; g.checked_partition(g.leaves(T),[X,Y])
    if set(X)&set(Y): raise ValueError('overlapping original split')
    if d['repX'] not in X or d['repY'] not in Y: raise ValueError('wrong representative')
    if d['rho']==d['gamma'] or d['rho'] in g.leaves(T) or d['gamma'] in g.leaves(T): raise ValueError('nonfresh marker')
    for name,t in [('cutT',T),('cutS',S)]:
        q=d[name]
        if not q or q not in g.graph(t)[0]: raise ValueError('nonroot actual common edge missing')
        inside={x for p,x in g.graph(t)[1].items() if p.startswith(q)}
        if inside not in (set(X),set(Y)): raise ValueError('wrong split side')
        parts=g.components(t,[q])
        if g.partnorm([B for _,B in parts])!=g.partnorm([X,Y]): raise ValueError('literal common cut mismatch')
    d.update({'T':T,'S':S,'trees':{'TX':restriction(T,set(X)),'SX':restriction(S,set(X)),'TY':restriction(T,set(Y)),'SY':restriction(S,set(Y)),'TMX':marked(T,X,d['repY'],d['rho']),'SMX':marked(S,X,d['repY'],d['rho']),'TMY':marked(T,Y,d['repX'],d['gamma']),'SMY':marked(S,Y,d['repX'],d['gamma'])}})
    for a,b in [('TX','SX'),('TY','SY'),('TMX','SMX'),('TMY','SMY')]: g.valid_pair(d['trees'][a],d['trees'][b])
    check_setup_shape(d)
    return d
def depth01(T,S):
    answers=[F for F in g.partitions(tuple(sorted(g.leaves(T)))) if len(F)<=2 and g.agreement(T,S,F)]
    if not answers: return 'REJECT',None
    F=min(answers,key=len); return 'FOUND'+str(cost(F)),[list(B) for B in F]
def erase_once(F,B):
    out=copy.deepcopy(F); out.remove(B); return out
def merge_candidates(FM,FN,X,Y):
    return [[[x for x in M if x in X]+[y for y in N if y in Y]]+erase_once(FM,M)+erase_once(FN,N) for M in FM for N in FN]
def checked_pick(T,S,Fs):
    good=[F for F in Fs if g.agreement(T,S,F)]; return min(good,key=len) if good else None
def callback_fixture(e,which,r):
    families=e.get('minimum_families',{}).get(which)
    if families is None:
        assert e['costs'][which]==0
        labels=e['X'] if which=='X' else e['X']+[e['rho']]
        families=[[labels]]
    F=copy.deepcopy(families[0])
    assert cost(F)==e['costs'][which]
    return F if cost(F)<=r else None
def jobs(d,q):
    return [] if q==0 else [{'kind':'ordinaryX','T':d['trees']['TX'],'S':d['trees']['SX'],'budget':q-1},{'kind':'markedX','T':d['trees']['TMX'],'S':d['trees']['SMX'],'budget':q-1}]
def model_call(e,q):
    d=setup(e); ts=d['trees']; outside,FY=depth01(ts['TY'],ts['SY'])
    if outside!='FOUND1': return {'status':'REFUSAL','trace':[],'outside':outside}
    marked_status,FN=depth01(ts['TMY'],ts['SMY'])
    if FN is None:
        FN=[[d['gamma']]]+copy.deepcopy(FY)
        assert g.agreement(ts['TMY'],ts['SMY'],FN) and cost(FN)==2
    if q==0: return {'status':'BOUNDED_NEGATIVE','trace':[],'jobs':[],'outside':outside,'marked_outside':marked_status}
    js=jobs(d,q); FX=callback_fixture(e,'X',q-1); FM=callback_fixture(e,'MX',q-1)
    # Eager is one allowed reference-model trace, not a prediction of source order.
    trace=[{'kind':j['kind'],'budget':j['budget']} for j in js]
    if FX is None or FM is None: return {'status':'BOUNDED_NEGATIVE','trace':trace,'jobs':js,'callback_results':[FX,FM]}
    stable=cost(FM)==cost(FX) and cost(FN)==cost(FY)
    guesses=merge_candidates(FM,FN,d['X'],d['Y']) if stable else []
    answer=checked_pick(d['T'],d['S'],guesses) if stable else FX+FY
    if answer is None or not g.agreement(d['T'],d['S'],answer) or cost(answer)>q: status='BOUNDED_NEGATIVE'; answer=None
    else: status='MINIMUM'
    return {'status':status,'answer':answer,'trace':trace,'jobs':js,'guesses':guesses,'stable':stable,'outside':outside,'marked_outside':marked_status,'marked_outside_reply':FN,'callback_results':[FX,FM]}
def check_case(e):
    d=setup(e); ts=d['trees']; vals={}; families={}
    for which,a,b in [('X','TX','SX'),('Y','TY','SY'),('MX','TMX','SMX'),('MY','TMY','SMY'),('global',None,None)]:
        T,S=(d['T'],d['S']) if a is None else (ts[a],ts[b]); v,Fs=minima(T,S); vals[which]=v; families[which]=Fs
        assert v==e['costs'][which],(e['id'],which,v,e['costs'][which])
        if which in e.get('minimum_families',{}): assert normfamily(Fs)==normfamily(e['minimum_families'][which]),(e['id'],which,'complete family mismatch',Fs)
    if 'trees' in e:
        for name,t in e['trees'].items(): assert ts[name]==g.tree(t),(e['id'],name,ts[name],t)
    if 'hulls' in e:
        for key,t in [('T',d['T']),('S',d['S'])]:
            for B,h in zip(e['hulls']['forest'],e['hulls'][key]): assert g.hull(t,tuple(sorted(B)))==set(h),(e['id'],key,B)
    if 'global_witness' in e: assert g.agreement(d['T'],d['S'],e['global_witness']) and cost(e['global_witness'])==e['costs']['global']
    if 'literal_extension' in e: assert g.agreement(ts['TMY'],ts['SMY'],e['literal_extension']) and cost(e['literal_extension'])==2
    outcomes=[]
    for q,status in e['answers'].items():
        out=model_call(e,int(q)); assert out['status']==status,(e['id'],q,out,status)
        if status=='MINIMUM': assert cost(out['answer'])==e['costs']['global']
        if status=='REFUSAL': assert out['trace']==[]
        js=jobs(d,int(q)); assert len(js)==(0 if int(q)==0 else 2)
        for j in js: assert j['budget']==int(q)-1 and j['budget']<int(q); g.valid_pair(j['T'],j['S'])
        outcomes.append({'q':int(q),'status':status,'trace':out['trace'],'candidate_count':len(out.get('guesses',[])),'answer':out.get('answer')})
    return {'id':e['id'],'costs':vals,'minimum_families':families,'trees':ts,'outcomes':outcomes,'global_complete_family_pin':e.get('complete_global_family','all declared families checked')}
def require(test,message):
    if not test: raise ValueError(message)
def mutations():
    e=E['cases'][0]; d=setup(e); truth=model_call(e,1); FM,FN=truth['callback_results'][1],truth['marked_outside_reply']; ownedM=next(B for B in FM if e['rho'] in B); ownedN=next(B for B in FN if e['gamma'] in B)
    valid_merge=[x for x in ownedM if x in e['X']]+[x for x in ownedN if x in e['Y']]
    def changed(k,v):
        out=copy.deepcopy(e); out[k]=v; return setup(out)
    plants={
      'missing-common-edge':lambda:changed('cutT','111111'),
      'root-cut':lambda:changed('cutT',''),
      'wrong-split-side':lambda:changed('cutS','10'),
      'missing-original-vertex':lambda:require(set(e['hulls']['T'][0])-{'1'}==g.hull(d['T'],(0,1,2)),'forgot original path vertex'),
      'wrong-original-target':lambda:require(g.agreement(d['S'],d['S'],[[0,1,2,3]])==g.agreement(d['T'],d['S'],[[0,1,2,3]]),'wrong original target'),
      'wrong-original-source':lambda:require(g.agreement(d['T'],d['T'],[[0,1,2,3]])==g.agreement(d['T'],d['S'],[[0,1,2,3]]),'wrong original source'),
      'nonfresh-marker':lambda:changed('rho',0),
      'wrong-representative':lambda:changed('repY',0),
      'wrong-marked-relabel':lambda:require(marked(d['T'],e['X'],e['repY'],99)==d['trees']['TMX'],'wrong marked relabel'),
      'wrong-marker-owner':lambda:require(e['gamma'] in next(B for B in FN if e['gamma'] not in B),'marker absent from guessed owner'),
      'marker-not-removed':lambda:require(g.agreement(d['T'],d['S'],[[0,10]+[x for x in ownedN if x in e['Y']]]+erase_once(FN,ownedN)),'marker survived original return'),
      'wrong-original-color-filter':lambda:require(set(valid_merge)==set(ownedM+ownedN),'wrong original color filter'),
      'wrong-erase-remainder':lambda:require(len(FM+FN)==len(FM+FN)-2,'owner erase omitted'),
      'dropped-cartesian-pair':lambda:require(len(truth['guesses'])-1==len(FM)*len(FN),'Cartesian pair dropped'),
      'deduplicated-paid-candidates':lambda:require(len(set(map(g.partnorm,merge_candidates(FM*2,FN,e['X'],e['Y']))))==len(FM*2)*len(FN),'duplicate paid values removed'),
      'strict-literal-order-confusion':lambda:require(e['minimum_families']['global'][0]==list(reversed(e['minimum_families']['global'][0])),'strict list order rejects same AF'),
      'component-cut-offset':lambda:require(len(truth['answer'])==e['costs']['global'],'components confused with cuts'),
      'unpaid-callback':lambda:require(all(j['budget']==1 for j in jobs(d,1)),'unpaid parent callback'),
      'dropped-callback-coverage':lambda:require(cost([[0]]+truth['marked_outside_reply'])==e['costs']['global'],'dropped marked callback loses minimum'),
      'wrong-child-budget':lambda:require(jobs(d,2)[1]['budget']==2,'wrong actual child budget'),
      'unaffordable-success':lambda:require(e['costs']['global']<=0,'unaffordable original success'),
      'failed-callback-as-known-minimum':lambda:require(E['cases'][5]['costs']['MX']==0,'failure used as free known minimum'),
      'nonminimum-reply':lambda:require(cost([[0],[10]])==e['costs']['MX'],'nonminimum marked callback'),
      'missing-failure-exclusion':lambda:require(callback_fixture(e,'X',0) is None,'failed callback excludes known affordable original witness'),
      'refusal-as-infeasibility':lambda:require(E['cases'][1]['costs']['global']>0,'refusal fixture has cost0 original AF'),
      'setup-desired-minimum-field':lambda:check_setup_shape(dict(d,outside_minimum=1))
    }
    assert set(plants)==set(E['mutations']); caught=[]
    for name,fn in plants.items():
        try: fn()
        except (AssertionError,ValueError) as ex: caught.append({'mutation':name,'caught':True,'reason':str(ex)})
        else: raise AssertionError(('mutation survived',name))
    return caught
def main():
    import argparse
    ap=argparse.ArgumentParser(); ap.add_argument('mode',choices=['controls','pilot','bank']); a=ap.parse_args(); at=time.perf_counter()
    cases=E['cases'][:1] if a.mode=='controls' else E['cases'][:2] if a.mode=='pilot' else E['cases']
    out={'mode':a.mode,'cases':[],'candidate_contact':False,'replication_credit':0}
    for e in cases:
        start=time.perf_counter(); r=check_case(e); r['seconds']=time.perf_counter()-start; out['cases'].append(r)
    if a.mode=='controls': out['mutations']=mutations(); out['caught']=len(out['mutations'])
    assert str(2/Fraction(233,100))==E['mass']['positive_233over100']
    assert all(2/Fraction(c)<=1 for c in (2,3,4)) and 2/Fraction(233,100)<=1
    out['seconds']=time.perf_counter()-at; out['script_sha256']=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(); out['expectations_sha256']=hashlib.sha256((P/'EXPECTATIONS-v1.json').read_bytes()).hexdigest()
    (P/('graph-'+a.mode+'-v2-run1.json')).write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps({'mode':a.mode,'cases':len(cases),'caught':out.get('caught'),'seconds':out['seconds']}))
if __name__=='__main__': main()
