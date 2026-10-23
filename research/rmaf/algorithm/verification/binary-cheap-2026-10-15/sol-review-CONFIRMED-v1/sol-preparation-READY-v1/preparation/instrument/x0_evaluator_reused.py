#!/usr/bin/env python3
"""One-shot independent X0 graph/partition instrument; deliberately local.

Fresh original-address graph and projected-cluster query evaluator. The source
core generator alone is transcribed from the disclosed CoreProgram.lean hash.
No optimum oracle is part of a proposed algorithm. All tests are exact.
"""
import argparse
from collections import Counter
from fractions import Fraction as F
from functools import lru_cache
import hashlib
import itertools
import json
from pathlib import Path
import time

HERE = Path(__file__).resolve().parent

def canon(parts):
    return tuple(sorted(tuple(sorted(b)) for b in parts))

def newick(t):
    return str(t) if isinstance(t, int) else '('+newick(t[0])+','+newick(t[1])+')'

class Graph:
    def __init__(self, t):
        self.tree=t; self.adj={}; self.at={}; self.desc={}; self.labels=[]
        def visit(u,p):
            self.adj[p]=set()
            if p:
                self.adj[p[:-1]].add(p); self.adj[p].add(p[:-1])
            if isinstance(u,int):
                self.labels.append(u); self.at[u]=p; self.desc[p]=frozenset([u])
            else:
                visit(u[0],p+'0'); visit(u[1],p+'1')
                self.desc[p]=self.desc[p+'0']|self.desc[p+'1']
        visit(t,'')
        self.distinct=len(self.labels)==len(set(self.labels))
    def hull(self, sel):
        sel=frozenset(sel)
        if not sel or not sel <= self.at.keys(): return frozenset()
        addresses=[self.at[x] for x in sel]
        prefix=addresses[0]
        for p in addresses[1:]:
            while not p.startswith(prefix): prefix=prefix[:-1]
        return frozenset(p[:k] for p in addresses for k in range(len(prefix),len(p)+1))
    def shape(self,sel):
        sel=frozenset(sel)
        if not sel or not sel <= self.at.keys(): return None
        return frozenset(d & sel for d in self.desc.values() if d & sel)
    def disjoint(self,bs):
        seen=set()
        for b in bs:
            h=self.hull(b)
            if seen & h: return False
            seen |= h
        return True
    def cut_parts(self,cuts):
        if len(cuts)!=len(set(cuts)) or any(not p or p not in self.adj for p in cuts):
            return None
        removed={frozenset([p,p[:-1]]) for p in cuts}; seen=set(); leafparts=[]; empty=[]
        lab_at={p:x for x,p in self.at.items()}
        for p in self.adj:
            if p in seen: continue
            stack=[p]; vs=set(); labs=[]
            while stack:
                v=stack.pop()
                if v in seen: continue
                seen.add(v); vs.add(v)
                if v in lab_at: labs.append(lab_at[v])
                stack.extend(w for w in self.adj[v] if w not in seen and frozenset([v,w]) not in removed)
            if labs: leafparts.append(labs)
            else: empty.append(sorted(vs))
        return {'parts':canon(leafparts),'empty_components':empty,'graph_components':len(leafparts)+len(empty)}

@lru_cache(None)
def partitions(xs):
    if not xs: return ((),)
    x=xs[0]; out=[]
    for p in partitions(xs[1:]):
        out.append(((x,),)+p)
        for j,b in enumerate(p): out.append(p[:j]+(tuple(sorted((x,)+b)),)+p[j+1:])
    return tuple(out)

def refinements(coarse):
    for choices in itertools.product(*(partitions(tuple(sorted(b))) for b in coarse)):
        yield tuple(b for p in choices for b in p)

def proper(selected,bs):
    flat=[x for b in bs for x in b]
    return bool(bs) and all(bs) and Counter(flat)==Counter(selected)

def agrees(s,t,b):
    return s.shape(b) is not None and s.shape(b)==t.shape(b)

def agreement(s,t,selected,bs):
    return proper(selected,bs) and all(agrees(s,t,b) for b in bs) and s.disjoint(bs) and t.disjoint(bs)

def optimum(s,t,coarse):
    selected=sorted(x for b in coarse for x in b)
    best=None; witness=None; tested=0; valid=0; hist=Counter()
    for bs in refinements(coarse):
        tested+=1
        if agreement(s,t,selected,bs):
            valid+=1; hist[len(bs)]+=1
            if best is None or len(bs)<best: best=len(bs); witness=canon(bs)
    if best is None: raise ValueError('oracle found no singleton completion')
    return {'components':best,'additional':best-len(coarse),'witness':witness,
            'partition_denominator':tested,'valid_agreements':valid,'valid_count_by_components':dict(sorted(hist.items()))}

# Literal CoreProgram transcription. Tuple tags retain every original address.
def leaf(p,xs,c): return ('L',p,tuple(xs),c)
def node(p,l,r): return ('N',p,l,r)
def from_tree(t,col,p=''):
    return leaf(p,[t],col[t]) if isinstance(t,int) else node(p,from_tree(t[0],col,p+'0'),from_tree(t[1],col,p+'1'))
def groups(t): return [t] if t[0]=='L' else groups(t[2])+groups(t[3])
def normalize(t):
    if t[0]=='L': return t
    a,b=normalize(t[2]),normalize(t[3])
    return leaf(t[1],a[2]+b[2],a[3]) if a[0]==b[0]=='L' and a[3]==b[3] else node(t[1],a,b)
def erase(t,p):
    if t[1]==p: return None
    if t[0]=='L': return t
    a,b=erase(t[2],p),erase(t[3],p)
    return b if a is None else a if b is None else node(t[1],a,b)
def mixed(t):
    if t[0]=='L': return None
    if t[2][0]==t[3][0]=='L': return t[2],t[3]
    return mixed(t[2]) or mixed(t[3])
def receipt(): return {'outputs':[],'refusals':[],'visited':0,'childAttempts':0,'pruned':0}
def generate(tree,col,q):
    gr=Graph(tree)
    if not gr.distinct:
        r=receipt(); r['refusals']=['duplicate original label']; return r
    def run(t,det,cuts,budget):
        r=receipt(); r['visited']=1
        t=normalize(t); gs=groups(t)
        if all(g[3]==gs[0][3] for g in gs):
            r['outputs']=[{'partition':[list(g[2]) for g in det]+[[x for g in gs for x in g[2]]], 'sourceCuts':list(cuts)}]
            return r
        ct=Counter(g[3] for g in gs)
        one=next((g for g in gs if ct[g[3]]==1),None)
        choice=[one] if one else list(mixed(t) or [])
        if not choice:
            r['refusals']=['no mixed cherry in multicolor source']; return r
        if len(choice)==2 and choice[0][3]==choice[1][3]:
            r['refusals']=['unnormalized homogeneous cherry']; return r
        for g in choice:
            r['childAttempts']+=1
            if not g[1]: r['refusals'].append('attempt to cut original root'); continue
            if g[1] in cuts: r['refusals'].append('duplicate original source cut'); continue
            nxt=erase(t,g[1])
            if nxt is None: r['refusals'].append('attempt removed entire current source'); continue
            if budget==0: r['pruned']+=1; continue
            rr=run(nxt,[g]+det,[g[1]]+cuts,budget-1)
            for k in r:
                if isinstance(r[k],list): r[k]+=rr[k]
                else: r[k]+=rr[k]
        return r
    return run(from_tree(tree,col),[],[],min(q,len(gr.labels)-1))

def raw_checks(r,s,col,c):
    costs=[len(o['sourceCuts']) for o in r['outputs']]
    dy=sum((F(1,2**d) for d in costs),F())
    mass=sum((c**(-d) for d in costs),F())
    checks={'four_colors':len(set(col.values()))==4,'costs_ge_3':all(d>=3 for d in costs),
            'dyadic_allowance':dy<=F(1,8),'literal_cut_realization':True,'proper_source_partition':True,
            'four_whole_colors_if_cheap':True,'cheap_singleton':True,'high_envelope':True}
    cuts=[]
    for o in r['outputs']:
        cp=s.cut_parts(o['sourceCuts']); cuts.append(cp)
        checks['literal_cut_realization'] &= cp is not None and cp['parts']==canon(o['partition']) and not cp['empty_components'] and cp['graph_components']==len(o['sourceCuts'])+1
        checks['proper_source_partition'] &= proper(s.labels,o['partition']) and s.disjoint(o['partition']) and all(len({col[x] for x in b})==1 for b in o['partition'])
    cheap=3 in costs
    if cheap:
        checks['cheap_singleton']=costs==[3]
        expected=canon([[x for x in s.labels if col[x]==v] for v in sorted(set(col.values()))])
        checks['four_whole_colors_if_cheap']=all(canon(o['partition'])==expected for o in r['outputs'])
    else:
        checks['high_envelope']=all(d>=4 for d in costs) and mass<=2/c**4
    return {'costs':costs,'dyadic':str(dy),'mass_at_c':str(mass),'cheap':cheap,'checks':checks,'cut_graphs':cuts}

def regime(s,t,P,e):
    A,B,C=map(set,P); D=t.desc.get(e,set()); sectors=[A&D,A-D,B&D,B-D]
    ha,hb,hc=map(t.hull,[A,B,C])
    guards={'same_distinct_labels':s.distinct and t.distinct and set(s.labels)==set(t.labels),
            'proper_P':proper(s.labels,P),'source_P_disjoint':s.disjoint(P),
            'A_B_target_overlap':bool(ha&hb),'C_clear':not bool(hc&(ha|hb)),
            'original_nonroot_edge':bool(e) and e in t.adj,
            'all_sectors_nonempty':all(sectors),
            'mutual_clear':all(not(t.hull(x)&hb) for x in sectors[:2]) and all(not(t.hull(x)&ha) for x in sectors[2:])}
    return guards,sectors

def analyze_fixture(f,c):
    start=time.perf_counter(); s,t=Graph(f['S']),Graph(f['T']); P=f['P']; A,B,C=map(set,P)
    guards,sectors=regime(s,t,P,f['edge']); A1,A2,B1,B2=sectors
    colA={x:i for i,b in enumerate([A1,A2,B,C]) for x in b}
    colB={x:i for i,b in enumerate([A,B1,B2,C]) for x in b}
    out={'id':f['id'],'S':newick(f['S']),'T':newick(f['T']),'P':P,'edge':f['edge'],
         'sectors':[sorted(b) for b in sectors],'source_hulls':[sorted(s.hull(b)) for b in P],
         'target_hulls':[sorted(t.hull(b)) for b in P],'guards':guards,
         'A_good':agrees(s,t,A),'B_good':agrees(s,t,B),
         'A_sectors_good':[agrees(s,t,x) for x in [A1,A2]],'lists':{}}
    for name,col in [('LA',colA),('LB',colB)]:
        r=generate(f['S'],col,f['q']); raw=raw_checks(r,s,col,c)
        queries=[]
        for o in r['outputs']:
            local=[{'block':sorted(b),'query':optimum(s,t,[b])} for b in o['partition']]
            a_parts=[b for b in o['partition'] if set(b)<=A]
            a_query=optimum(s,t,a_parts)
            queries.append({'local':local,'A_blocks':a_parts,'A_contribution':a_query,
                            'global_refining_output':optimum(s,t,o['partition'])})
        budgets=[]
        for q in range(f['q']+1):
            qq=generate(f['S'],col,q)
            expected=[o for o in r['outputs'] if len(o['sourceCuts'])<=q]
            budgets.append({'q':q,'raw_costs':[len(o['sourceCuts']) for o in qq['outputs']],
                            'prefix_matches_full_filter':qq['outputs']==expected,'pruned':qq['pruned'],
                            'visited':qq['visited'],'childAttempts':qq['childAttempts']})
        out['lists'][name]={'colors':col,'raw':r,'summary':raw,'queries':queries,'budgets':budgets}
    out['local_A']=optimum(s,t,[sorted(A)])
    out['first_A_sector']=optimum(s,t,[sorted(A1)])
    out['global_refining_P']=optimum(s,t,P)
    out['retain_A_and_clear_B']=optimum(s,t,[sorted(A),sorted(B1),sorted(B2),sorted(C)])
    out['B_sector_one_source_cut']=any(s.cut_parts([edge])['parts']==canon([B1,B2]) for edge in s.adj if edge) if set(s.labels)==B else any(s.hull(B1).isdisjoint(s.hull(B2)) and len(bs)==2 and canon(bs)==canon([B1,B2]) for bs in [])
    # Local B one-cut realizability from its original hull: partition B after any one original edge.
    out['B_sector_one_source_cut']=False
    for edge in s.adj:
        if not edge: continue
        cp=s.cut_parts([edge])
        proj=[set(b)&B for b in cp['parts'] if set(b)&B]
        if canon(proj)==canon([B1,B2]): out['B_sector_one_source_cut']=True
    out['expectation_checks']=check_expected(f,out)
    out['seconds']=time.perf_counter()-start
    return out

def check_expected(f,o):
    e=f['expected']; results={}
    for key,val in e.items():
        if key=='in_regime': got=all(o['guards'].values())
        elif key in ['A_good','B_good','A_sectors_good']: got=o[key]
        elif key in ['LA_costs','LB_costs']: got=o['lists'][key[:2]]['summary']['costs']
        elif key=='A_local_additional': got=o['local_A']['additional']
        elif key=='A_post_B_additional_each': got=[q['A_contribution']['additional'] for q in o['lists']['LB']['queries']]; val=[val]*len(got)
        elif key=='first_A_sector_additional': got=o['first_A_sector']['additional']
        elif key=='cheap_branch_additional_at_least':
            got=min(q['global_refining_output']['additional'] for q in o['lists']['LA']['queries']); results[key]={'expected_lower_bound':val,'got':got,'pass':got>=val}; continue
        elif key=='global_refining_P_components': got=o['global_refining_P']['components']
        elif key=='retain_A_and_clear_B_components': got=o['retain_A_and_clear_B']['components']
        elif key=='B_whole_sector_one_cut': got=o['B_sector_one_source_cut']
        else: raise KeyError(key)
        results[key]={'expected':val,'got':got,'pass':got==val}
    return results

def controls(data,c):
    out=[]
    def add(name,got,want):
        out.append({'name':name,'got':got,'expected':want,'pass':got==want})
    rawlists=[[3],[4,4],[],[3,4],[3,3]]
    masses=[sum((F(1,2**d) for d in ds),F()) for ds in rawlists]
    add('five exact dyadic masses',[str(v) for v in masses],data['arithmetic']['expected_dyadic'])
    add('allowance clean/corrupt split',[v<=F(1,8) for v in masses],[True,True,True,False,False])
    add('raw duplicate corruption caught',masses[-1]!=sum((F(1,2**d) for d in set(rawlists[-1])),F()),True)
    add('high sharp envelope',sum((c**(-d) for d in [4,4]),F()),2/c**4)
    add('false high single-unit bound caught',sum((c**(-d) for d in [4,4]),F())>1/c**4,True)
    add('false comparator planted mismatch caught',F(1,8)==F(3,16),False)
    add('endpoint envelope at 233/100',2/c+4/c**4<1,True)
    for name,v in data['controls'].items():
        if 'expected_additional' in v:
            s,t=Graph(v['S']),Graph(v['T']); q=optimum(s,t,[s.labels]); add(name,q['additional'],v['expected_additional'])
            if name=='identical': add('false identical positive progress caught',q['additional']>=1,False)
        elif name=='suppressed_path': add(name,sorted(Graph(v['tree']).hull(v['selection'])),v['expected_hull'])
        else:
            r=generate(v['S'],{int(k):vv for k,vv in v['colors'].items()},v['q'])
            if 'expected_costs' in v: add(name,[len(o['sourceCuts']) for o in r['outputs']],v['expected_costs'])
            if 'expected_parts' in v: add(name+' parts',sorted(canon(o['partition']) for o in r['outputs']),sorted(canon(p) for p in v['expected_parts']))
            if 'expected_refusal' in v: add(name,r['refusals'],[v['expected_refusal']])
    s=Graph([[0,1],2]); t=Graph([0,[1,2]])
    add('false whole-block agreement caught',agreement(s,t,s.labels,[s.labels]),False)
    add('false repeated-label partition caught',agreement(s,s,s.labels,[[0,1],[1,2]]),False)
    add('empty selection rejected',agrees(s,s,[]),False)
    add('absent label rejected',agrees(s,s,[99]),False)
    add('singleton zero-cut',optimum(s,t,[[1]])['additional'],0)
    add('root address cut rejected',s.cut_parts(['']),None)
    add('wrong suppression hull corruption caught',s.hull([0,2])==frozenset(['00','1']),False)
    add('capped-query monotonic outputs not unit decrease', [optimum(s,s,[s.labels])['additional']<=b for b in [0,1]], [True,True])
    return out

def main():
    ap=argparse.ArgumentParser(); ap.add_argument('stage',choices=['controls','pilot','battery']); args=ap.parse_args()
    start=time.perf_counter(); data=json.loads((HERE/'sol-fixtures-v1.json').read_text()); c=F(*data['arithmetic']['c'])
    result={'stage':args.stage,'date_utc':time.strftime('%Y-%m-%dT%H:%M:%SZ',time.gmtime()),'c':str(c),
            'instrument_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
            'fixtures_sha256':hashlib.sha256((HERE/'sol-fixtures-v1.json').read_bytes()).hexdigest()}
    if args.stage=='controls':
        result['controls']=controls(data,c); checks=[z['pass'] for z in result['controls']]
        result['denominator']=len(checks); result['passed']=sum(checks)
    else:
        selected=data['fixtures'][:1] if args.stage=='pilot' else data['fixtures'][1:]
        result['fixtures']=[]
        for f in selected:
            o=analyze_fixture(f,c); result['fixtures'].append(o)
            if not all(z['pass'] for z in o['expectation_checks'].values()): break
        result['denominator']=len(selected); result['completed']=len(result['fixtures'])
        checks=[z['pass'] for o in result['fixtures'] for z in o['expectation_checks'].values()]
        checks += [v for o in result['fixtures'] for l in o['lists'].values() for v in l['summary']['checks'].values()]
        checks += [q['prefix_matches_full_filter'] for o in result['fixtures'] for l in o['lists'].values() for q in l['budgets']]
        result['check_denominator']=len(checks); result['passed']=sum(checks)
    result['seconds']=time.perf_counter()-start
    result['all_declared_checks_pass']=all(checks) and result.get('completed',result['denominator'])==result['denominator']
    path=HERE/('sol-'+args.stage+'-v1.json'); path.write_text(json.dumps(result,indent=2,default=str)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k not in ['controls','fixtures']},indent=2))
    if not result['all_declared_checks_pass']: raise SystemExit(1)
if __name__=='__main__': main()
