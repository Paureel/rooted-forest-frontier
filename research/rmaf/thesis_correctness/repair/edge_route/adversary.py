#!/usr/bin/env python3
"""One-shot rooted-MAF repair adversary; independent original-edge deletion checker.
No imports from previous forest evaluators. Exact finite evidence, not a proof.
"""
from __future__ import annotations
import argparse, hashlib, itertools as it, json, time
from pathlib import Path
ROOT=Path('/Users/paurel/Documents/ChatGPT/bootscience')
HERE=ROOT/'research/rmaf/thesis_correctness/repair/edge_route'
RESULTS=ROOT/'research/rmaf/results'

def atomic(path,data):
    tmp=path.with_suffix(path.suffix+'.tmp');tmp.write_text(json.dumps(data,indent=2,sort_keys=True)+'\n');tmp.replace(path)
def powers(xs):
    xs=tuple(sorted(xs))
    for mask in range(1<<len(xs)):
        yield frozenset(x for i,x in enumerate(xs) if mask>>i&1)

class Graph:
    def __init__(self,parent,labels):
        self.parent=dict(parent);self.labels=dict(labels);self.nodes=frozenset(parent)
        self.children={v:[] for v in self.nodes}
        for v,p in parent.items():
            if p is not None:self.children[p].append(v)
        self.edges=frozenset(v for v,p in parent.items() if p is not None)
        self.bylabel={lab:v for v,lab in labels.items()}
        self.alllabels=frozenset(labels.values())
        assert len(self.bylabel)==len(self.labels)
        assert all(len(c)<=2 for c in self.children.values())
        for v in self.nodes:
            seen=set();u=v
            while u is not None:
                assert u not in seen;seen.add(u);u=parent[u]
    @classmethod
    def tree(cls,t):
        parent={0:None};labels={0:'rho'}
        def add(q,p):
            v=len(parent);parent[v]=p
            if isinstance(q,str):labels[v]=q
            else:
                for child in q:add(child,v)
            return v
        add(t,0);return cls(parent,labels)
    def cut(self,E):
        assert set(E)<=self.edges
        return Graph({v:None if v in E else p for v,p in self.parent.items()},self.labels)
    def descendants(self,v):
        ans={v};todo=[v]
        while todo:
            u=todo.pop()
            for w in self.children[u]:ans.add(w);todo.append(w)
        return frozenset(ans)
    def cluster(self,v):return frozenset(self.labels[w] for w in self.descendants(v) if w in self.labels)
    def edge_clusters(self,E):return [sorted(self.cluster(e)) for e in sorted(E)]
    def clusters_to_edges(self,clusters):
        out=[]
        for c in clusters:
            got=[e for e in self.edges if self.cluster(e)==frozenset(c)]
            assert len(got)==1,(c,got)
            out.append(got[0])
        return frozenset(out)
    def root(self,v):
        while self.parent[v] is not None:v=self.parent[v]
        return v
    def path(self,a,b):
        aa=[];u=a
        while u is not None:aa.append(u);u=self.parent[u]
        bb=[];u=b
        while u is not None:bb.append(u);u=self.parent[u]
        shared=set(aa)&set(bb)
        if not shared:return None,None
        lca=next(v for v in aa if v in shared)
        return frozenset(aa[:aa.index(lca)]+bb[:bb.index(lca)]),lca
    def restrict(self,block):
        block=frozenset(block)
        assert block and block<=self.alllabels
        vs=[self.bylabel[x] for x in block]
        if len({self.root(v) for v in vs})>1:return None
        keep={vs[0]}
        for v in vs[1:]:
            edges,lca=self.path(vs[0],v);keep|=set(edges)|{lca}
        top=next(v for v in keep if self.parent[v] not in keep)
        def walk(v):
            cc=[walk(w) for w in self.children[v] if w in keep]
            cc=tuple(sorted(cc,key=repr))
            if v in self.labels and self.labels[v] in block:return ('L',self.labels[v],cc)
            if len(cc)==1:return cc[0]
            assert len(cc)==2,(v,cc,block)
            return ('I',cc)
        return walk(top),frozenset(keep)
    def components(self):
        byroot={}
        for v,lab in self.labels.items():byroot.setdefault(self.root(v),set()).add(lab)
        return [(frozenset(b),self.restrict(b)[0]) for b in sorted(byroot.values(),key=lambda x:sorted(x))]
    def yielded_graph(self):
        """Build active reduced graph while retaining bottom-node IDs as edge IDs."""
        par={};labs={}
        def go(v):
            children=[r for w in self.children[v] if (r:=go(w)) is not None]
            if v not in self.labels:
                if not children:return None
                if len(children)==1:return children[0]
            par[v]=None
            if v in self.labels:labs[v]=self.labels[v]
            for w in children:par[w]=v
            return v
        for v,p in self.parent.items():
            if p is None:go(v)
        return Graph(par,labs)
    def json(self):
        return {'parent':{str(v):p for v,p in self.parent.items()},'labels':{str(v):x for v,x in self.labels.items()},'original_edges':[{'id':e,'parent':self.parent[e],'cluster':sorted(self.cluster(e))} for e in sorted(self.edges)]}

def blocks(G):return [sorted(b) for b,s in G.components()]
def forest_of(candidate,source):
    if candidate.alllabels!=source.alllabels:return False
    used=set()
    for b,shape in candidate.components():
        x=source.restrict(b)
        if x is None or x[0]!=shape or used&x[1]:return False
        used|=x[1]
    return True

def af(F,F1,F2):return forest_of(F,F1) and forest_of(F,F2)
def containment(F1,F2):return all(any(b<=a for a,_ in F1.components()) for b,_ in F2.components())
def cherry_after(F,a,c,E):
    if E&F.path(a,c)[0]:return False
    H=F.cut(E).yielded_graph()
    return a in H.nodes and c in H.nodes and H.parent[a] is not None and H.parent[a]==H.parent[c] and H.restrict(F.cluster(a))[0]==F.restrict(F.cluster(a))[0] and H.restrict(F.cluster(c))[0]==F.restrict(F.cluster(c))[0]
def normalization(F,a,c,E):
    path,u=F.path(a,c);assert path is not None
    removed=E&path;parent_edge=u if F.parent[u] is not None else None
    out=E-removed
    if len(removed)>=2 and parent_edge is not None:out|={parent_edge}
    return frozenset(out),removed,u,parent_edge

def controls():
    start=time.perf_counter(); spec=json.loads((HERE/'controls-frozen.json').read_text());receipts=[]
    for item in spec['controls']:
        T1=Graph.tree(item['T1']);T2=Graph.tree(item['T2']);F2=T2.cut(T2.clusters_to_edges(item.get('F2_initial_cut_clusters',[]))).yielded_graph()
        F1=T1
        if 'F1_blocks' in item:
            want=sorted(sorted(b) for b in item['F1_blocks'])
            F1=next(T1.cut(E).yielded_graph() for E in powers(T1.edges) if sorted(blocks(T1.cut(E)))==want)
        E=F2.clusters_to_edges(item['cut_clusters']); a,c=(F2.bylabel[x] for x in item['pair'])
        original=F2.cut(E);N,removed,u,pe=normalization(F2,a,c,E);normalized=F2.cut(N)
        actual={'original_AF':af(original,T1,T2),'active_original_AF':af(original,F1,F2),'active_containment':containment(F1,F2),'normalized_AF':af(normalized,T1,T2),'normalized_active_AF':af(normalized,F1,F2),'lca_parent_exists':pe is not None}
        if 'normalized_cut_clusters' in item:assert N==F2.clusters_to_edges(item['normalized_cut_clusters'])
        for key,val in item.items():
            if key.startswith('expected_') and key[9:] in actual:assert actual[key[9:]]==val,(item['id'],key,actual)
        if item['id']=='raw-cover-failure':
            opts=[]
            for cuts in powers(T2.edges):
                if af(T2.cut(cuts),T1,T2):opts.append(cuts)
            optimum=min(map(len,opts)); opts=[s for s in opts if len(s)==optimum]
            path,lca=T2.path(a,c);pendants={w for v in set(path)|{lca} if v not in (a,c) for w in T2.children[v] if w not in path}
            covers=lambda s:a in s or c in s or len(s&pendants)>=2
            actual.update(optimum_cuts=optimum,blocks=blocks(original),universal_raw_cover=all(map(covers,opts)),existential_covered_optimum=any(map(covers,opts)),all_optimal_edge_sets=[sorted(s) for s in opts])
            assert optimum==item['expected_optimum_cuts'] and sorted(actual['blocks'])==sorted([sorted(b) for b in item['expected_blocks']])
            assert not actual['universal_raw_cover'] and actual['existential_covered_optimum']
            assert optimum!=optimum+1
        if 'E2_clusters' in item:
            E2=F2.clusters_to_edges(item['E2_clusters']);assert E2<=E and cherry_after(F2,a,c,E2)
        receipts.append({'id':item['id'],'actual':actual,'T1':T1.json(),'F1':F1.json(),'F2':F2.json(),'E':sorted(E),'normalized_E':sorted(N),'removed_path_edges':sorted(removed),'lca':u,'lca_parent_edge':pe,'original_blocks':blocks(original),'normalized_blocks':blocks(normalized)})
    assert len(receipts)==4
    r={x['id']:x['actual'] for x in receipts}
    negatives={'wrong_optimum_rejected':r['raw-cover-failure']['optimum_cuts']!=3,'bad_normalization_rejected':not r['standalone-normalization-failure']['normalized_AF'],'missing_containment_admits_bad_fixture':r['standalone-normalization-failure']['original_AF'] and not r['standalone-normalization-failure']['active_containment'],'invented_root_parent_rejected':not r['root-parent-absent']['lca_parent_exists']}
    assert all(negatives.values())
    result={'status':'CONTROLS-PASS','control_count':4,'negative_checks':negatives,'controls_sha256':hashlib.sha256((HERE/'controls-frozen.json').read_bytes()).hexdigest(),'elapsed_seconds':time.perf_counter()-start,'receipts':receipts}
    atomic(RESULTS/'thesis-correctness-repair-edge-controls.json',result)
    print(json.dumps({'status':result['status'],'controls':4,'negative_checks':4,'elapsed_seconds':result['elapsed_seconds']}),flush=True)
    return result

if __name__=='__main__':controls()

# All tree representations below are generated locally, not imported.
def trees(labels):
    labels=tuple(sorted(labels))
    if len(labels)==1:return (labels[0],)
    ans=[];first=labels[0];rest=labels[1:]
    for mask in range(1<<len(rest)):
        left=(first,)+tuple(x for i,x in enumerate(rest) if mask>>i&1)
        right=tuple(x for x in labels if x not in left)
        if not right:continue
        for a in trees(left):
            for b in trees(right):ans.append((a,b))
    return tuple(ans)

def active_graph(f):
    parent={v:None for v in f.child}
    for v,cc in f.child.items():
        for w in cc:parent[w]=v
    return Graph(parent,{v:'+'.join(sorted(lab)) for v,lab in f.label.items()})

def expand_snapshot(f,source):
    """Reconstruct source vertices explicitly; no suppression transport assumed.
    Every active edge keeps its bottom ID. Expansion is checked against source.
    Completed atoms retained so original labels stay complete.
    """
    active=active_graph(f);parent=dict(active.parent);labels={}
    records=[]
    atoms=[(v,lab,False) for v,lab in f.label.items()]+[(None,lab,True) for lab in getattr(f,'completed',[])]
    occupied=set(v for v in parent if v not in f.label)
    for v,lab,done in atoms:
        restriction=source.restrict(lab);assert restriction is not None
        _,keep=restriction
        top=next(w for w in keep if source.parent[w] not in keep)
        if not done:assert top==v,(v,top,lab)
        assert not occupied&keep,(occupied&keep,lab)
        occupied|=set(keep)
        upper=None if done else parent[v]
        for w in keep:
            parent[w]=source.parent[w] if w!=top else upper
            if w in source.labels and source.labels[w] in lab:labels[w]=source.labels[w]
        records.append({'atom':sorted(lab),'active_node':v,'completed':done,'original_vertices':sorted(keep),'original_top':top})
    out=Graph(parent,labels)
    assert forest_of(out,source),'snapshot expansion does not embed in original tree'
    return out,records

def sibling_pairs(F1,F2,leaf_only=False):
    for p,cc in F1.children.items():
        if len(cc)!=2:continue
        if leaf_only and any(F1.children[v] for v in cc):continue
        roots=[]
        for v in cc:
            b=F1.cluster(v);s=F1.restrict(b)[0]
            matches=[w for w in F2.nodes if F2.cluster(w)==b and F2.restrict(b)[0]==s]
            if len(matches)!=1:break
            roots.append(matches[0])
        if len(roots)==2 and F2.path(*roots)[0] is not None:yield tuple(roots)

def check_state(F1,F2,T1,T2,meta,root_only=False,edge_domain=None,pair_domain=None):
    counts={'pairs':0,'root_pairs':0,'cuts_enumerated':0,'af_cutsets':0,'normalization_premises':0,'root_premises_ge2':0,'root_premises_ge2_nonminimal':0}
    witnesses=[];first=None
    assert containment(F1,F2),'active containment failed'
    assert forest_of(F1,T1) and forest_of(F2,T2)
    # Enumerate every original edge cutset without merging equal partitions.
    allcuts=list(powers(F2.edges if edge_domain is None else edge_domain));afs={E for E in allcuts if af(F2.cut(E),F1,F2)}
    optimum=min(map(len,afs)); counts['cuts_enumerated']=len(allcuts);counts['af_cutsets']=len(afs)
    for a,c in (sibling_pairs(F1,F2) if pair_domain is None else pair_domain):
        path,u=F2.path(a,c);root=F2.parent[u] is None
        if root_only and not root:continue
        counts['pairs']+=1;counts['root_pairs']+=root
        # E2 subset E and unchanged endpoint subtrees; every possible E2 tested.
        for E in sorted(afs,key=lambda x:(len(x),sorted(x))):
            N,removed,u,pe=normalization(F2,a,c,E)
            if not removed:continue
            E2=next((K for K in powers(E-path) if cherry_after(F2,a,c,K)),None)
            if E2 is None:continue
            counts['normalization_premises']+=1
            rootprem=root and len(removed)>=2
            counts['root_premises_ge2']+=rootprem
            counts['root_premises_ge2_nonminimal']+=rootprem and len(E)>optimum
            good=af(F2.cut(N),F1,F2) and af(F2.cut(N),T1,T2)
            cost=len(N)<=len(E); preserve=E2<=N
            if rootprem or not (good and cost and preserve):
                row={'meta':meta,'F1':F1.json(),'F2':F2.json(),'T1':T1.json(),'T2':T2.json(),'a':a,'c':c,'a_cluster':sorted(F2.cluster(a)),'c_cluster':sorted(F2.cluster(c)),'E':sorted(E),'E2':sorted(E2),'path':sorted(path),'removed_path_edges':sorted(removed),'LCA':u,'LCA_parent_edge':pe,'normalized_E':sorted(N),'original_blocks':blocks(F2.cut(E)),'normalized_blocks':blocks(F2.cut(N)),'original_AF':True,'active_containment':True,'normalized_AF':good,'cost_nonincrease':cost,'E2_preserved':preserve,'optimum_remaining_cuts':optimum}
                if first is None and rootprem:first=row
                if not (good and cost and preserve):witnesses.append(row)
    return counts,witnesses,first

def reached(n,limit,seed,root_only=True):
    import importlib.util, random
    p=ROOT/'research/rmaf/thesis_correctness/algorithm.py';spec=importlib.util.spec_from_file_location('edge_generator',p);alg=importlib.util.module_from_spec(spec)
    import sys;sys.modules[spec.name]=alg;spec.loader.exec_module(alg)
    rng=random.Random(seed);tt=trees(tuple('abcdefghi'[:n]));pairs=[(a,b) for a in tt for b in tt] if n<=5 else None
    if pairs is not None:rng.shuffle(pairs);pairs=pairs[:limit]
    else:pairs=[(rng.choice(tt),rng.choice(tt)) for _ in range(limit)]
    counts={'inputs':0,'snapshots':0,'unique_snapshots':0,'root_candidate_snapshots':0,'valid_active_snapshots_checked':0,'invalid_snapshots':0,'pairs':0,'root_pairs':0,'cuts_enumerated':0,'af_cutsets':0,'normalization_premises':0,'root_premises_ge2':0,'root_premises_ge2_nonminimal':0};failures=[];witnesses=[];first=None;timings=[];seen=set();current={}
    original_choose=alg.choose;original_remove=alg.Forest.remove_atom;original_cut=alg.Forest.cut;original_merge=alg.Forest.merge
    def remove(self,v):
        self.history=list(getattr(self,'history',[]))+[{'action':'finish','node':v,'atom':sorted(self.label[v])}]
        self.completed=list(getattr(self,'completed',[]))+[self.label[v]]
        return original_remove(self,v)
    alg.Forest.remove_atom=remove
    def cut(self,cuts):
        g=active_graph(self);out=original_cut(self,cuts)
        out.history=list(getattr(self,'history',[]))+[{'action':'cut','original_edge_ids':list(cuts),'edge_clusters':g.edge_clusters(cuts),'protected':sorted(self.protected)}]
        return out
    def merge(self,a,c):
        self.history=list(getattr(self,'history',[]))+[{'action':'merge','nodes':[a,c],'atoms':[sorted(self.label[a]),sorted(self.label[c])]}]
        return original_merge(self,a,c)
    alg.Forest.cut=cut;alg.Forest.merge=merge
    def capture(f1,f2):
        nonlocal first
        counts['snapshots']+=1
        g1=active_graph(f1);g2=active_graph(f2)
        key=repr((current['trees'],g1.parent,g1.labels,g2.parent,g2.labels,getattr(f1,'completed',[]),getattr(f2,'completed',[])))
        if key not in seen:
            seen.add(key);counts['unique_snapshots']+=1
            root_pairs=[(a,c) for a,c in sibling_pairs(g1,g2) if g2.parent[g2.path(a,c)[1]] is None]
            if root_pairs:
                counts['root_candidate_snapshots']+=1
                try:
                    X1,r1=expand_snapshot(f1,current['T1']);X2,r2=expand_snapshot(f2,current['T2'])
                    assert containment(X1,X2)
                    # Full expansion restores original labels and original edge IDs.
                    meta={'kind':'actually-reached','input_index':current['index'],'input_trees':current['trees'],'budget':current['budget'],'active_F1':g1.json(),'active_F2':g2.json(),'expansion_F1':r1,'expansion_F2':r2,'protected_F1':sorted(f1.protected),'protected_F2':sorted(f2.protected),'enumerated_active_edge_ids':sorted(g2.edges),'history_F1':getattr(f1,'history',[]),'history_F2':getattr(f2,'history',[]),'active_edge_original_segments':{str(v):sorted(current['T2'].path(g2.parent[v],v)[0]) for v in g2.edges}}
                    cc,ww,ff=check_state(X1,X2,current['T1'],current['T2'],meta,root_only=root_only,edge_domain=g2.edges,pair_domain=root_pairs)
                    counts['valid_active_snapshots_checked']+=1
                    for k,v in cc.items():counts[k]+=v
                    witnesses.extend(ww)
                    if first is None and ff is not None:first=ff
                except AssertionError as e:
                    counts['invalid_snapshots']+=1;failures.append({'input_index':current['index'],'error':str(e),'F1':g1.json(),'F2':g2.json()})
        return original_choose(f1,f2)
    alg.choose=capture
    start=time.perf_counter()
    for index,(t1,t2) in enumerate(pairs):
        before=time.perf_counter();current={'T1':Graph.tree(t1),'T2':Graph.tree(t2),'index':index,'trees':[t1,t2]}
        for budget in range(n):
            current['budget']=budget
            alg.decide(t1,t2,budget)
        counts['inputs']+=1;timings.append(time.perf_counter()-before)
        if (index+1)%10==0:print(json.dumps({'completed_inputs':index+1,'elapsed_seconds':time.perf_counter()-start,'root_premises_ge2':counts['root_premises_ge2']}),flush=True)
        if witnesses:break
    result={'status':'FIRE' if witnesses else 'NO-FIRE','scope':'actually reached expanded snapshots; root candidate filter; all original-edge cutsets in each checked snapshot; finite evidence only','n':n,'limit':limit,'seed':seed,'counts':counts,'elapsed_seconds':time.perf_counter()-start,'per_input_seconds':timings,'invalid_snapshot_details':failures,'counterexamples':witnesses,'first_reached_root_witness':first,'generator_sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'checker_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
    atomic(RESULTS/f'thesis-correctness-repair-edge-reached-n{n}-limit{limit}.json',result)
    print(json.dumps({'status':result['status'],'counts':counts,'elapsed_seconds':result['elapsed_seconds']}),flush=True)
    return result
