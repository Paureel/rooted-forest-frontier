"""One-shot fresh nonauthor AF review instrument; stdlib only, no campaign imports.
Original labelled unary rho vertex; child-descendant sets identify original edges.
Outputs exact AF Booleans, partitions and optimum original-edge cut counts.
Acceptance requires frozen fixtures plus independently planted trivial cases and
rejected corruptions. Finite searches are not universal proofs.
"""
from itertools import combinations
from pathlib import Path
import json, time, hashlib

ROOT=Path('/Users/paurel/Documents/ChatGPT/bootscience/research/rmaf')
REPAIR=ROOT/'thesis_correctness/repair'

class Tree:
    def __init__(self, shape):
        self.children={0:[]}; self.parent={}; self.labels={0:'rho'}
        def visit(x,p):
            v=len(self.children);self.children[v]=[]; self.parent[v]=p;self.children[p].append(v)
            if isinstance(x,str): self.labels[v]=x
            else:
                for y in x: visit(y,v)
            return v
        visit(shape,0)
        self.at={l:v for v,l in self.labels.items()}
        def desc(v):
            ans={self.labels[v]} if v in self.labels else set()
            for c in self.children[v]: ans|=desc(c)
            return frozenset(ans)
        self.cluster={v:desc(v) for v in self.parent}
        self.edge_for={c:v for v,c in self.cluster.items()}
    def edges(self,clusters): return {self.edge_for[frozenset(c)] for c in clusters}
    def ancestors(self,v):
        a=[v]
        while v in self.parent: v=self.parent[v]; a.append(v)
        return a
    def lca(self,vs):
        paths=[self.ancestors(v) for v in vs]
        return next(v for v in paths[0] if all(v in p for p in paths[1:]))
    def hull(self,block):
        vs=[self.at[l] for l in block]; root=self.lca(vs); h={root}
        for v in vs:
            while v!=root: h.add(v);v=self.parent[v]
        return root,h
    def restriction(self,block):
        root,h=self.hull(block)
        def sig(v):
            kids=sorted((sig(c) for c in self.children[v] if c in h),key=repr)
            label=self.labels.get(v) if self.labels.get(v) in block else None
            if label is None and len(kids)==1:return kids[0]
            return (label,tuple(kids))
        return sig(root)
    def components(self,cuts):
        groups={}
        for v,l in self.labels.items():
            while v in self.parent and v not in cuts: v=self.parent[v]
            groups.setdefault(v,set()).add(l)
        return sorted((frozenset(b) for b in groups.values()),key=lambda b:sorted(b))
    def path_edges(self,x,y):
        a=self.at[x] if isinstance(x,str) else x;b=self.at[y] if isinstance(y,str) else y
        r=self.lca([a,b]); ans=set()
        for v in [a,b]:
            while v!=r:ans.add(v);v=self.parent[v]
        return ans
    def pendant_edges(self,x,y):
        path=self.path_edges(x,y); vs={self.parent[v] for v in path}|path
        endpoints={self.at[x] if isinstance(x,str) else x,self.at[y] if isinstance(y,str) else y}
        return {c for v in vs-endpoints for c in self.children[v] if c not in path}

def af_partition(t1,t2,blocks):
    hs=[]
    for block in blocks:
        if t1.restriction(block)!=t2.restriction(block):return False
        h=t1.hull(block)[1]
        if any(h & old for old in hs):return False
        hs.append(h)
    # Check disjointness in both trees even when not generated as cut components.
    hs=[]
    for block in blocks:
        h=t2.hull(block)[1]
        if any(h & old for old in hs):return False
        hs.append(h)
    return True

def af(t1,t2,cuts):return af_partition(t1,t2,t2.components(cuts))
def optimum(t1,t2,initial=frozenset()):
    available=set(t2.parent)-set(initial)
    for k in range(len(available)+1):
        good=[set(c) for c in combinations(sorted(available),k) if af(t1,t2,set(initial)|set(c))]
        if good:return k,good
    raise AssertionError('singleton partition unavailable')
def blocks_json(blocks): return [sorted(b) for b in blocks]
def scalar(t):
    base,p1,p2,p3,added,r1,removed,r2=t
    hyps=[p2<=2,p3>=1,p1+p2+p3>=2,added+p2<=2,r1<=1,p3!=1 or r1==0,
          p3!=1 or p1<=removed,p3<2 or removed>=1,r2<=1,removed>1 or r2==0,
          p3<=base+added,removed<=max(0,base+added-p3)+r1]
    out=max(0,max(0,base+added-p3)+r1-removed)+r2
    return out,hyps

def check_equal(observed,expected,name):
    if observed!=expected:raise AssertionError((name,observed,expected))

def main():
    start=time.perf_counter(); rows=[];catches=[]
    # Synthetic trivial positives precede campaign fixtures.
    t=Tree(['a','b'])
    check_equal(optimum(t,t)[0],0,'planted-identical-optimum')
    check_equal(af(t,t,set()),True,'planted-identical-AF')
    check_equal(scalar([0,0,0,0,0,0,0,0])[0],0,'scalar-null')
    for name,observed,bad in [('AF-output',af(t,t,set()),False),('optimum-output',optimum(t,t)[0],1),
                              ('partition-output',blocks_json(t.components(set())),[['a'],['b','rho']]),
                              ('scalar-output',scalar([0,0,0,0,0,0,0,0])[0],1)]:
        try:check_equal(observed,bad,name)
        except AssertionError:catches.append(name)
        else:raise AssertionError('corruption survived: '+name)
    frozen=json.loads((REPAIR/'controls.json').read_text())
    for f in frozen['controls']:
        a,b=Tree(f['T1']),Tree(f['T2']);initial=b.edges(f.get('F2_initial_cut_clusters',[]));cut=b.edges(f['cut_clusters'])
        row={'id':f['id'],'original_AF':af(a,b,initial|cut),'blocks':blocks_json(b.components(initial|cut))}
        if 'normalized_cut_clusters' in f:
            row['normalized_AF']=af(a,b,initial|b.edges(f['normalized_cut_clusters']))
        if 'F1_blocks' in f:
            row['active_containment']=all(any(set(bl)<=set(old) for old in f['F1_blocks']) for bl in b.components(initial))
        else:row['active_containment']=True
        if f['id']=='raw-cover-failure':
            opt,mins=optimum(a,b);x,y=f['pair']; ea=b.edge_for[frozenset([x])]; ec=b.edge_for[frozenset([y])];bb=b.pendant_edges(x,y)
            covered=lambda es:ea in es or ec in es or bb<=es
            row.update(optimum_cuts=opt,universal_raw_cover=all(covered(es) for es in mins),
                       existential_covered_optimum=any(covered(es) for es in mins),fixture_covered=covered(cut),
                       minimum_count=len(mins),BB_clusters=[sorted(b.cluster[e]) for e in sorted(bb)])
        if 'expected_lca_parent_exists' in f:
            r=b.lca([b.at[z] for z in f['pair']]);row['lca_parent_exists']=r in b.parent and r not in initial
            try:check_equal(row['lca_parent_exists'],True,'root-parent corruption')
            except AssertionError:catches.append('root-parent-output')
        for key,expected in f.items():
            if key.startswith('expected_'):
                name=key.removeprefix('expected_')
                actual=row[name]
                if name=='blocks': actual={frozenset(b) for b in actual};expected={frozenset(b) for b in expected}
                check_equal(actual,expected,f['id']+'/'+name)
        rows.append(row)
    f=json.loads((REPAIR/'compound-empty-hypothesis.json').read_text()); a,b=Tree(f['T1']),Tree(f['T2'])
    before=b.edges(f['E_clusters']);after=b.edges(f['E0_clusters']);op,_=optimum(a,b)
    row={'id':'compound-empty','original_AF':af(a,b,before),'normalized_AF':af(a,b,after),'active_containment':True,
         'original_cut_count':len(before),'optimum_cuts':op,'before_blocks':blocks_json(b.components(before)),
         'after_blocks':blocks_json(b.components(after))}
    for key,expected in [('original_AF',True),('normalized_AF',False),('original_cut_count',3),('optimum_cuts',1)]:check_equal(row[key],expected,key)
    rows.append(row)
    spec=json.loads((REPAIR/'two-exchange-cost-spec.json').read_text());cost=[]
    for category in ['positive_controls','negative_controls']:
        for f in spec[category]:
            value,hyp=scalar(f['tuple']);check_equal(value,f['expected_final'],f['name'])
            check_equal(all(hyp),category=='positive_controls',f['name']+'/hypotheses')
            cost.append({'name':f['name'],'tuple':f['tuple'],'value':value,'all_hypotheses':all(hyp),'failed_hypothesis_indices':[i+1 for i,h in enumerate(hyp) if not h]})
    receipt={'status':'passed','fresh_stdlib_implementation':True,'proofs_opened_before_controls':False,'controls':rows,
             'scalar_controls':cost,'planted_corruptions_caught':catches,'elapsed_seconds':time.perf_counter()-start,
             'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
    out=ROOT/'results/thesis-correctness-repair-review-controls.json';out.write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps({'status':receipt['status'],'forest_controls':len(rows),'scalar_controls':len(cost),'corruptions_caught':catches,'elapsed_seconds':receipt['elapsed_seconds']}))
if __name__=='__main__':main()
