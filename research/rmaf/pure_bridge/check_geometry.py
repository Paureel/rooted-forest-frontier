#!/usr/bin/env python3
"""Problem-specific exact adversarial instrument; see README.md.
No imports from existing RMAF oracles. Discovery only, not independent certification.
Enumerate removed edges of source trees, then compare explicit graph embeddings.
"""
import argparse, hashlib, itertools, json, random, time
from pathlib import Path
CAMPAIGN = Path(__file__).resolve().parents[1]
OUT = CAMPAIGN / 'results'

def freeze(t):
    return tuple(map(freeze,t)) if isinstance(t,list) else t

class Tree:
    def __init__(self, syntax):
        self.syntax = freeze(syntax)
        self.adj, self.child, self.labels, self.depth = {}, {}, {}, {}
        def build(t, parent=None, depth=0):
            v=len(self.adj); self.adj[v]=set(); self.depth[v]=depth
            if parent is not None: self.adj[v].add(parent); self.adj[parent].add(v)
            if isinstance(t,int):
                if t in self.labels: raise ValueError('duplicate label')
                self.labels[t]=v; self.child[v]=[]
            else:
                if len(t)!=2: raise ValueError('nonbinary tree')
                self.child[v]=[build(x,v,depth+1) for x in t]
            return v
        build(self.syntax)
        self.edges=tuple((u,v) for u in self.adj for v in self.adj[u] if u<v)
        self._spans={}; self._shapes={}; self._cutparts=None
    def path(self,a,b):
        todo=[a]; prev={a:None}
        for u in todo:
            if u==b: break
            for v in self.adj[u]:
                if v not in prev: prev[v]=u; todo.append(v)
        result={b}
        while b!=a: b=prev[b]; result.add(b)
        return result
    def span(self, labels):
        key=frozenset(labels)
        if not key: raise ValueError('empty block')
        if key not in self._spans:
            vs=[self.labels[x] for x in key]; result={vs[0]}
            for v in vs[1:]: result.update(self.path(vs[0],v))
            self._spans[key]=frozenset(result)
        return self._spans[key]
    def shape(self, labels):
        key=frozenset(labels)
        if key not in self._shapes:
            embedding=self.span(key); root=min(embedding,key=self.depth.get)
            rev={v:x for x,v in self.labels.items()}
            def visit(v):
                if v in rev: return rev[v]
                parts=[visit(c) for c in self.child[v] if c in embedding]
                if len(parts)==1: return parts[0]
                return tuple(sorted(parts,key=repr))
            self._shapes[key]=visit(root)
        return self._shapes[key]
    def degree(self,v,embedding): return len(self.adj[v]&embedding)
    def leaf_regions(self,marks,subset=None):
        selected=set(self.labels) if subset is None else set(subset)
        embedding=set(self.span(selected)); unseen=embedding-set(marks); regions=[]; empty=0
        while unseen:
            seed=next(iter(unseen)); seen={seed}; todo=[seed]; unseen.remove(seed)
            for u in todo:
                for v in self.adj[u]&unseen: unseen.remove(v); seen.add(v); todo.append(v)
            labels=frozenset(x for x in selected if self.labels[x] in seen)
            if labels: regions.append(labels)
            else: empty+=1
        return tuple(regions),empty
    def cut_partitions(self):
        if self._cutparts is None:
            answers=set()
            for mask in range(1<<len(self.edges)):
                cuts={self.edges[i] for i in range(len(self.edges)) if mask>>i&1}
                unseen=set(self.adj); parts=[]
                while unseen:
                    seed=next(iter(unseen)); todo=[seed]; seen={seed}; unseen.remove(seed)
                    for u in todo:
                        for v in self.adj[u]&unseen:
                            if tuple(sorted((u,v))) not in cuts: unseen.remove(v); seen.add(v); todo.append(v)
                    lab=tuple(sorted(x for x,v in self.labels.items() if v in seen))
                    if lab: parts.append(lab)
                answers.add(tuple(sorted(parts)))
            self._cutparts=tuple(sorted(answers,key=lambda p:(len(p),p)))
        return self._cutparts

def disjoint(sets):
    seen=set()
    for s in sets:
        if seen&s:return False
        seen.update(s)
    return True

def local_candidates(target,source):
    result=[]
    for p in source.cut_partitions():
        spans=[target.span(b) for b in p]
        if disjoint(spans) and all(target.shape(b)==source.shape(b) for b in p):
            # Source embeddings checked explicitly too, independent of cut enumeration claim.
            if not disjoint([source.span(b) for b in p]):raise AssertionError('cut enumeration source overlap')
            result.append({'cost':len(p)-1,'blocks':p,'used':frozenset().union(*spans)})
    return result

def opt(candidates,marks=frozenset()):
    for c in candidates:
        if not c['used']&set(marks):return c
    raise ValueError('infeasible marks')

def brute_completion(target,sources):
    candidates=[local_candidates(target,s) for s in sources]; winner=None
    for chosen in itertools.product(*candidates):
        if disjoint([c['used'] for c in chosen]):
            cost=sum(c['cost'] for c in chosen)
            if winner is None or cost<winner[0]:winner=(cost,chosen)
    assert winner is not None
    return winner

def eliminate(target,sources,require_pure=True):
    spans=[target.span(s.labels) for s in sources]
    pure=all(all(target.degree(v,spans[i])==target.degree(v,spans[j])==2 for v in spans[i]&spans[j]) for i in range(len(sources)) for j in range(i))
    if not pure and require_pure:return None
    candidates=[local_candidates(target,s) for s in sources]
    marks=[set() for s in sources]; remaining=set(range(len(sources))); chosen=[]; steps=[]
    while remaining:
        roots={i:min(spans[i],key=target.depth.get) for i in remaining}
        a=max(remaining,key=lambda i:(target.depth[roots[i]],-i)); v=roots[a]
        neigh=[i for i in remaining if i!=a and spans[i]&spans[a]]
        assert all(v in spans[i] for i in neigh),'deepest-root failure'
        base=opt(candidates[a],marks[a]); avoid=opt(candidates[a],marks[a]|{v}) if neigh else base
        if neigh and avoid['cost']>base['cost']:
            assert avoid['cost']==base['cost']+1,'one-cut failure'
            for i in neigh:marks[i].add(v)
            witness=base
        else:witness=avoid
        steps.append({'component':a,'root':v,'neighbors':len(neigh),'cost':witness['cost'],'marks':sorted(marks[a])})
        chosen.append(witness); remaining.remove(a)
    assert disjoint([c['used'] for c in chosen]),'elimination output overlap'
    return sum(c['cost'] for c in chosen),steps

def assert_equal(actual,expected):
    if actual!=expected:raise AssertionError({'actual':actual,'expected':expected})

def controls():
    fixture=json.loads((Path(__file__).parent/'controls.json').read_text()); vals={}; caught=[]
    t=Tree(((0,1),2)); vals['equal-triple']=opt(local_candidates(t,t))['cost']; d=Tree(((0,2),1))
    vals['incompatible-triple']=opt(local_candidates(t,d))['cost']
    cross=Tree(((0,1),(2,3))); pair=Tree((0,2)); cs=local_candidates(cross,pair)
    roots=sorted(v for v in cross.span(pair.labels) if v not in cross.labels.values()); center=min(roots,key=cross.depth.get)
    children=set(roots)-{center}
    vals['one-mark-cross-pair']=opt(cs,{center})['cost']; vals['two-marks-cross-pair']=opt(cs,children)['cost']
    regions,empty=cross.leaf_regions(children,pair.labels); assert empty==1
    vals['empty-center-region-count']=len(regions)
    vals['cross-pairs-completion']=brute_completion(cross,[pair,Tree((1,3))])[0]
    clique=Tree(((0,(1,2)),(3,(4,5)))); sources=[Tree((i,i+3)) for i in range(3)]
    vals['cross-triple-clique-completion']=brute_completion(clique,sources)[0]
    for c in fixture['cases']:assert_equal(vals[c['id']],c['expected'])
    for name,fn in [('wrong expected cost rejected',lambda:assert_equal(vals['equal-triple'],1)),('overlapping pairs rejected',lambda:assert_equal(disjoint([cross.span((0,2)),cross.span((1,3))]),True)),('marked leaf rejected',lambda:opt(cs,{cross.labels[0]}))]:
        try:fn()
        except (ValueError,AssertionError):caught.append(name)
        else:raise AssertionError('negative control survived: '+name)
    assert caught==fixture['negative_controls']
    for tar,src in [(cross,[pair,Tree((1,3))]),(clique,sources)]:assert_equal(eliminate(tar,src)[0],brute_completion(tar,src)[0])
    return {'positive_controls':vals,'negative_controls_caught':caught,'nonadditivity':{'tree':cross.syntax,'component':pair.syntax,'marks':sorted(children),'single_penalties':[1,1],'joint_penalty':1,'empty_regions':empty}}

def random_tree(labels,rng):
    labels=list(labels)
    if len(labels)==1:return labels[0]
    rng.shuffle(labels); k=rng.randrange(1,len(labels))
    return (random_tree(labels[:k],rng),random_tree(labels[k:],rng))

def powerset(items):
    xs=list(items)
    for mask in range(1<<len(xs)):yield frozenset(xs[i] for i in range(len(xs)) if mask>>i&1)

def run(count,seed):
    rng=random.Random(seed); checks={'local_mark_queries':0,'role_swap_cases':0,'empty_region_cases':0,'one_cut_inequalities':0,'pure_completions':0,'nonpure_completions_skipped':0,'whole_overlap_checks':0,'root_mark_cases':0,'clique3_cases':0}; examples=[]
    started=time.monotonic(); control=controls(); control_secs=time.monotonic()-started
    for index in range(count):
        n=4+index%4; target=Tree(random_tree(range(n),rng)); size=min(n,2+index%3); labels=rng.sample(range(n),size); source=Tree(random_tree(labels,rng))
        span=target.span(labels); degree2=[v for v in span if target.degree(v,span)==2]; local=local_candidates(target,source); ordinary=opt(local)['cost']
        # Mark sets include roots, adjacent path marks and empty central regions.
        marksets=list(powerset(degree2))
        for marks in marksets:
            h=opt(local,marks)['cost']; checks['local_mark_queries']+=1
            if min(span,key=target.depth.get) in marks:checks['root_mark_cases']+=1
            for v in degree2:
                hv=opt(local,marks|{v})['cost']; assert h<=hv<=h+1; checks['one_cut_inequalities']+=1
            regions,empty=target.leaf_regions(marks,labels); r=len(regions); assert 0<=h-(r-1)<=ordinary
            checks['empty_region_cases']+=bool(empty)
            region_sources=[Tree(target.shape(reg)) for reg in regions]
            swapped=brute_completion(source,region_sources)[0]
            assert_equal(swapped,h-(r-1)); checks['role_swap_cases']+=1
        # Random color class sizes <=3 keep exact joint Cartesian products bounded.
        shuffled=list(range(n)); rng.shuffle(shuffled); groups=[]
        while shuffled:
            k=min(len(shuffled),rng.choice([1,2,2,3]));groups.append(shuffled[:k]);shuffled=shuffled[k:]
        sources=[Tree(random_tree(g,rng)) for g in groups]; result=eliminate(target,sources)
        if result is None:checks['nonpure_completions_skipped']+=1
        else:
            checks['pure_completions']+=1; assert_equal(result[0],brute_completion(target,sources)[0])
            spans=[target.span(s.labels) for s in sources]
            if any(step['neighbors']>=2 for step in result[1]):checks['clique3_cases']+=1
            for i in range(len(sources)):
                for j in range(i):
                    overlap=spans[i]&spans[j]
                    if overlap:
                        for block in powerset(sources[i].labels):
                            if block:
                                used=target.span(block); assert not used&overlap or overlap<=used
                                checks['whole_overlap_checks']+=1
            if len(examples)<3:examples.append({'target':target.syntax,'sources':[s.syntax for s in sources],'cost':result[0],'steps':result[1]})
    return {'status':'tested','seed':seed,'generated_instances':count,'controls':control,'checks':checks,'examples':examples,'timing':{'controls_seconds':control_secs,'total_seconds':time.monotonic()-started},'scope':'Exact finite discovery checks. Shared implementation primitives preclude independent certification. No universal geometry theorem or unrestricted bound certified.'}

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--count',type=int,default=20);p.add_argument('--seed',type=int,default=141026);p.add_argument('--output',default='pure-bridge-pilot.json');a=p.parse_args()
    report=run(a.count,a.seed);report['source_sha256']=hashlib.sha256(Path(__file__).read_bytes()).hexdigest();report['controls_sha256']=hashlib.sha256((Path(__file__).parent/'controls.json').read_bytes()).hexdigest()
    dest=OUT/a.output;dest.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps({'output':str(dest),'generated_instances':a.count,'checks':report['checks'],'timing':report['timing']}))
