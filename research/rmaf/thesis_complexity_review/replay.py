"""One-shot independent review: explicit vertices/edges, no author-runtime imports.

Input is a nested tuple tree with a labelled unary rho vertex. Detached F2
components remain present until the corresponding F1 root is moved to done.
Outputs certify finite source-semantic traces, never a universal runtime bound.
Run --controls before --witnesses; all expected controls were frozen in source-freeze.md.
"""
from __future__ import annotations
import argparse, copy, hashlib, json, time
from fractions import Fraction as F
from pathlib import Path

BASE=Path(__file__).resolve().parents[1]
OUT=BASE/'results'

class Graph:
    def __init__(self, tree):
        self.children={}; self.label={}; self.protected=set(); self.seq=0
        self.roots={self._build(('rho',tree))}
    def _build(self,t):
        v=self.seq; self.seq+=1
        if isinstance(t,str): self.label[v]=t; self.children[v]=[]
        elif t[0]=='rho': self.label[v]='rho'; self.children[v]=[self._build(t[1])]
        else: self.children[v]=[self._build(t[0]),self._build(t[1])]
        return v
    def parents(self): return {w:v for v,cs in self.children.items() for w in cs}
    def desc(self,v):
        return {v}.union(*(self.desc(w) for w in self.children[v]))
    def cluster(self,v):
        return frozenset(self.label[w] for w in self.desc(v) if not self.children[w] and self.label.get(w)!='rho')
    def key(self,v): return ','.join(sorted(self.cluster(v)))
    def locate(self,key):
        target=frozenset(key.split(','))
        found=[v for v in self.children if self.cluster(v)==target and self.label.get(v)!='rho']
        assert len(found)==1,(key,found)
        return found[0]
    def root(self,v):
        p=self.parents()
        while v in p:v=p[v]
        return v
    def depth(self,v):
        p=self.parents(); n=0
        while v in p:v=p[v];n+=1
        return n
    def sibling(self,v):
        p=self.parents().get(v)
        if p is None:return None
        rest=[w for w in self.children[p] if w!=v]
        return rest[0] if len(rest)==1 else None
    def topology(self,v):
        if not self.children[v]:return self.label[v]
        cs=sorted(self.topology(w) for w in self.children[v])
        return '('+','.join(cs)+')'+('rho' if self.label.get(v)=='rho' else '')
    def state(self):
        return {'forest':sorted(self.topology(v) for v in self.roots),
                'protected':sorted(self.key(v) for v in self.protected if v in self.parents())}
    def remove_component(self,v):
        assert v in self.roots
        gone=self.desc(v);self.roots.remove(v);self.protected-=gone
        for w in gone:self.children.pop(w);self.label.pop(w,None)
    def suppress(self,v):
        # Suppress an ordinary unary vertex, transporting protection by OR.
        while v in self.children and len(self.children[v])==1 and self.label.get(v)!='rho':
            w=self.children[v][0];p=self.parents().get(v)
            prot=v in self.protected or w in self.protected
            self.protected.discard(v);self.protected.discard(w)
            if p is None:self.roots.remove(v);self.roots.add(w)
            else:
                self.children[p]=[w if x==v else x for x in self.children[p]]
                if prot:self.protected.add(w)
            del self.children[v];self.label.pop(v,None)
            if p is None:break
            v=p
    def cut(self,v):
        p=self.parents().get(v);assert p is not None
        self.children[p].remove(v);self.roots.add(v);self.protected.discard(v)
        self.suppress(p)
    def legal(self,cut):
        pars=self.parents()
        for v in cut:
            if v not in pars or v in self.protected:return False
            if pars[v] in self.roots and self.sibling(v) in self.protected:return False
        return True
    def cherries(self):
        return [tuple(cs) for cs in self.children.values() if len(cs)==2 and all(not self.children[v] for v in cs)]
    def contract_cherry(self,keys):
        u,v=(self.locate(k) for k in keys);assert self.sibling(u)==v
        p=self.parents()[u]
        self.children[p]=[];self.label[p]='+'.join(sorted(keys))
        for w in (u,v):
            del self.children[w];del self.label[w];self.protected.discard(w)
    def lca(self,u,v):
        p=self.parents();anc=[]
        while True:
            anc.append(u)
            if u not in p:break
            u=p[u]
        while v not in anc:v=p[v]
        return v
    def pendants(self,u,v):
        assert self.root(u)==self.root(v)
        l=self.lca(u,v);pars=self.parents()
        def arm(x):
            out=[]
            while pars[x]!=l:
                out.append(self.sibling(x));x=pars[x]
            return out
        return arm(u)+list(reversed(arm(v)))

def chosen(f,g,pair):
    u,v=(f.locate(x) for x in pair);pars=f.parents()
    assert tuple((u,v)) in f.cherries() or tuple((v,u)) in f.cherries(),'not a cherry'
    top=max((pars[w] for w in f.protected),key=f.depth) if f.protected else next(iter(f.roots))
    eligible=[ij for ij in f.cherries() if all(x in f.desc(top) for x in ij)]
    def rank(ij):
        aa,cc=(g.locate(f.key(w)) for w in ij)
        return f.depth(ij[0]), int(g.root(aa)!=g.root(cc)), max(g.depth(aa),g.depth(cc))
    assert (u,v) in eligible or (v,u) in eligible,'outside protected depth domain'
    assert rank((u,v))==max(map(rank,eligible)),'not a depth-rule maximum'
    ga,gc=(g.locate(x) for x in pair)
    assert g.depth(ga)>=g.depth(gc),'wrong deeper-first orientation'
    return {'eligible':[sorted(f.key(w) for w in ij) for ij in eligible],
            'rank':rank((u,v)),'protected_top':f.key(top)}

def inspect(f,g,pair):
    selection=chosen(f,g,pair);i,j=(f.locate(x) for x in pair);a,c=(g.locate(x) for x in pair)
    assert a not in g.roots and c not in g.roots,'trivial component root'
    assert g.sibling(a)!=c,'trivial common cherry'
    pa=f.parents()[i];unc=f.sibling(pa)
    def match(v):return v is not None and unc is not None and g.topology(v)==f.topology(unc)
    ps=g.pendants(a,c) if g.root(a)==g.root(c) else []
    un2=None
    if unc is not None:
        un2=next((v for v in g.children if g.topology(v)==f.topology(unc)),None)
    rb=match(g.sibling(a)) or match(g.sibling(c))
    def chain_ok():
        if len(ps)<2 or unc is None:return False
        chain='('+','.join(sorted(g.topology(v) for v in ps[:2]))+')'
        for v in ps[2:]:chain='('+','.join(sorted([chain,g.topology(v)]))+')'
        return chain==f.topology(unc)
    rbs=bool(ps and g.parents()[c]==g.lca(a,c) and chain_ok())
    b2=len(ps)==2 and match(g.sibling(g.lca(a,c)))
    bcy=bool(len(ps)>=2 and un2 in g.protected and g.parents().get(un2)==ps[0])
    tests={'AC':g.root(a)!=g.root(c),'B':len(ps)==1,'RB':rb,'RB*':rbs,'2B':b2,'BCY':bcy,'A2BC':len(ps)==2,'A3BC':len(ps)>=3}
    case=next(k for k,b in tests.items() if b)
    branches=[]
    def add(n,cuts,p1=(),p2=()):
        branches.append({'name':n,'cuts':[g.key(w) for w in cuts],
                         'protect1':list(p1),'protect2':[g.key(w) for w in p2],
                         'legal':g.legal(cuts)})
    if case=='A2BC':
        if c in g.protected:
            add('B',ps);add('A',[a],p2=ps)
        else:
            add('A',[a]);add('B',ps);add('C',[c],p1=[pair[0]],p2=[a]+ps)
    elif case=='A3BC':
        add('A',[a]);add('B',ps);add('C',[c],p1=[pair[0]],p2=[a])
    elif case=='B':add('B',ps)
    elif case=='AC':add('A',[a]);add('C',[c])
    elif case=='2B':add('B',ps)
    elif case=='RB':add('RB',[c] if match(g.sibling(a)) else [a])
    elif case=='RB*':add('RB*',[a])
    elif case=='BCY':add('B',ps);add('CY',[c,g.sibling(un2)])
    return {'F1':f.state(),'F2':g.state(),'pair':pair,'selection':selection,
            'predicates':tests,'case':case,'pendants':[g.key(v) for v in ps],
            'uncle':None if unc is None else f.key(unc),'branches':branches}

def advance(f,g,record,branch,budget,expected_budget=None):
    b=next(b for b in record['branches'] if b['name']==branch);assert b['legal'],'illegal branch'
    q=budget-len(b['cuts'])
    if expected_budget is not None:assert q==expected_budget,'wrong budget'
    f=copy.deepcopy(f);g=copy.deepcopy(g)
    f.protected.update(f.locate(x) for x in b['protect1'])
    g.protected.update(g.locate(x) for x in b['protect2'])
    ids=[g.locate(x) for x in b['cuts']]
    assert g.legal(ids),'new protection invalidates cut'
    for v in ids:g.cut(v)
    # For these traces every chosen cut is a singleton. Step5/6 must choose
    # its cherry under the depth rule before moving that singleton to done.
    for key in b['cuts']:
        assert ',' not in key,'review trace only advances singleton cuts'
        fv=f.locate(key);sib=f.sibling(fv);assert sib is not None
        vals=[key,f.key(sib)];vals.sort(key=lambda x:g.depth(g.locate(x)),reverse=True)
        chosen(f,g,vals)
        f.cut(fv);f.remove_component(fv)
        gv=g.locate(key);g.remove_component(gv)
    return f,g,q

def W(p,r):return F(2+r,2**(p+1))
def bound(alpha,k,p,r):return F(alpha)*F(2)**k*W(p,r)+p-3

def controls():
    rows=[]
    def add(name,condition):assert condition,name;rows.append({'name':name,'passed':True})
    cg=Graph((('a','b'),'c'));cg.contract_cherry(['a','b'])
    add('common cherry contraction',cg.state()['forest']==['((a+b,c))rho'])
    g=Graph((('a','b'),'c'));b=g.locate('b');g.cut(b);g.remove_component(b)
    add('cut/suppress true twin',g.state()['forest']==['((a,c))rho'])
    add('wrong cut forest rejected',g.state()['forest']!=['((a,b))rho'])
    g=Graph(('a','b'));g.protected.add(g.locate('a'))
    add('protected-edge cut rejected',not g.legal([g.locate('a')]))
    # Use an ordinary two-child component root to isolate its sibling rule.
    rr=next(iter(g.roots));child=g.children[rr][0];g.roots={child};del g.children[rr];del g.label[rr]
    add('root-sibling protected cut rejected',not g.legal([g.locate('b')]))
    g.protected.clear();add('root-sibling true twin',g.legal([g.locate('b')]))
    f=Graph(((('a','b'),'c'),('d','e')));g=copy.deepcopy(f)
    chosen(f,g,['a','b']);add('maximum-depth true twin',True)
    try:chosen(f,g,['d','e']);raise RuntimeError('bad depth accepted')
    except AssertionError:rows.append({'name':'nonmaximum-depth trace rejected','passed':True})
    add('normalization null',bound(3,0,0,0)==0)
    add('ordinary A3 coefficient',F(1,2)+F(1,8)+F(3,8)==1)
    add('exception false inequality rejected',not F(9,16)<=F(1,2))
    add('exception true twin',F(9,16)<=F(9,16))
    # Exact same advance entry point, planted A2BC topology from construction.
    f=Graph(((('a','c'),'d'),'x'));g=Graph(((('a','d'),'x'),'c'))
    rec=inspect(f,g,['a','c'])
    # This fixture is intentionally only a budget test; take its first legal
    # singleton branch, irrespective of earlier-case identity.
    branch=next(b['name'] for b in rec['branches'] if b['legal'] and len(b['cuts'])==1)
    advance(f,g,rec,branch,5,4);add('budget true twin',True)
    try:advance(f,g,rec,branch,5,3);raise RuntimeError('wrong budget accepted')
    except AssertionError:rows.append({'name':'wrong budget trace rejected','passed':True})
    return rows

NINE1=(((('a','c'),'d'),('x','y')),(('z','w'),('t','h')))
NINE2=((('a',(('x','z'),('d',(('y','w'),'t')))),'h'),'c')
THIRTEEN1=(((('a','c'),'d'),(('x','y'),('u','v'))),(('z1','z2'),(('b2','su'),('sy','sv'))))
THIRTEEN2=((('x',((('a',('z1',('d','z2'))),'b2'),'c')),('u','su')),(('y','sy'),('v','sv')))

def witness(tree1,tree2,pairs,branches,credits):
    f=Graph(tree1);g=Graph(tree2);q=10;trace=[]
    for ix,pair in enumerate(pairs):
        row=inspect(f,g,pair);row.update(budget=q,P=credits[ix][0],Q=credits[ix][1])
        assert set(row['Q'])<=set(row['P'])
        assert set(row['P'])<=set(f.state()['protected'])
        trace.append(row)
        if ix<len(branches):
            row['selected_branch']=branches[ix]
            f,g,q=advance(f,g,row,branches[ix],q,q-1)
    return trace

def main():
    parser=argparse.ArgumentParser();parser.add_argument('--controls',action='store_true');parser.add_argument('--witnesses',action='store_true');args=parser.parse_args()
    start=time.perf_counter();result={'representation':'explicit vertex adjacency, incoming-edge protection, exact rational arithmetic','imports_from_author_runtime':False}
    if args.controls:
        result['controls']=controls();result['controls_passed']=len(result['controls']);suffix='controls'
    elif args.witnesses:
        ctl=json.loads((OUT/'thesis-complexity-review-controls.json').read_text());assert ctl['controls_passed']==14
        nine=witness(NINE1,NINE2,[['a','c'],['d','a'],['y','x'],['y','a']],['C','A','C'],[([],[]),(['a'],[]),(['a'],[]),(['a','y'],['y'])])
        thirteen=witness(THIRTEEN1,THIRTEEN2,[['a','c'],['d','a'],['x','y'],['u','v'],['u','x']],['C','A','C','C'],[([],[]),(['a'],[]),(['a'],[]),(['a','x'],['x']),(['a','x','u'],['x','u'])])
        assert [r['case'] for r in nine]==['A2BC','A2BC','A3BC','A3BC']
        assert nine[2]['pendants']==['w','t','z']
        assert sum(b['legal'] for b in nine[2]['branches'])==3
        assert not any(b['legal'] for b in nine[3]['branches'])
        assert [r['case'] for r in thirteen]==['A2BC','A2BC','A3BC','A3BC','A2BC']
        assert len(thirteen[-1]['P'])==3
        arithmetic={'parent_mass':str(W(1,0)),'child_mass':str(F(1,2)*W(1,0)+F(1,8)*W(0,0)+F(1,2)*W(2,1)),
                    'alpha':64,'K':0,'parent_affine':str(bound(64,0,1,0)),
                    'composed_affine':str(1+bound(64,-1,1,0)+bound(64,-3,0,0)+bound(64,-1,2,1))}
        assert arithmetic['parent_affine']=='30' and arithmetic['composed_affine']=='31'
        arithmetic['base_compatible_scaling']={'alpha':128,'K':0,'parent':str(bound(128,0,1,0)),
             'children':str(1+bound(128,-1,1,0)+bound(128,-3,0,0)+bound(128,-1,2,1))}
        assert arithmetic['base_compatible_scaling']['parent']=='62' and arithmetic['base_compatible_scaling']['children']=='67'
        result.update(nine=nine,thirteen=thirteen,arithmetic=arithmetic,source_cap_violated=True,nine_C_child_descendants=1,
                      limits=['full candidate recursion tree; optional short-circuit order not replayed','finite witnesses only; no asymptotic lower bound','source credit assignment applied manually with exact set records'])
        suffix='replay'
    else:parser.error('choose --controls or --witnesses')
    result['elapsed_seconds']=time.perf_counter()-start
    path=OUT/f'thesis-complexity-review-{suffix}.json';path.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({'receipt':str(path),'elapsed_seconds':result['elapsed_seconds'],'controls':result.get('controls_passed'),'witnesses':2 if args.witnesses else 0}))
if __name__=='__main__':main()
