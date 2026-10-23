"""Problem-specific reconstruction of Whidden 2013 Figure 6.5.
Direct labelled rho-root model. No oracle or earlier campaign code imported.
Sources/interpretations are itemized in SEMANTICS.md. Unexpected structural
conditions raise SemanticHole; they never silently choose a fallback branch.
"""
from dataclasses import dataclass
from copy import deepcopy

class SemanticHole(RuntimeError):
    pass

@dataclass
class Forest:
    child: dict
    label: dict
    protected: set

    @classmethod
    def tree(cls, t):
        ch, lab = {}, {}
        def rec(z):
            i = len(ch)
            ch[i] = []
            if isinstance(z,str):
                if z == 'rho': raise ValueError('rho reserved')
                lab[i] = frozenset([z])
            else:
                if not isinstance(z,(tuple,list)) or len(z)!=2:
                    raise ValueError('binary input required')
                ch[i] = [rec(w) for w in z]
            return i
        ch[0] = []
        lab[0] = frozenset(['rho'])
        ch[0] = [rec(t)]
        flat=[x for v in lab.values() for x in v]
        if len(flat)!=len(set(flat)): raise ValueError('duplicate label')
        return cls(ch,lab,set())

    def parent(self):
        return {v:u for u,cs in self.child.items() for v in cs}

    def roots(self):
        return set(self.child)-set(self.parent())

    def atom(self, block):
        hits=[v for v,s in self.label.items() if s==block]
        if len(hits)!=1: raise SemanticHole('missing/duplicate common Rt atom')
        return hits[0]

    def shape(self,v):
        cs=tuple(sorted((self.shape(w) for w in self.child[v]),key=repr))
        return (tuple(sorted(self.label.get(v,()))),cs)

    def match(self,other,v):
        s=other.shape(v)
        hits=[w for w in self.child if self.shape(w)==s]
        if len(hits)>1: raise SemanticHole('nonunique matching labelled subtree')
        return hits[0] if hits else None

    def depth(self,v):
        p=self.parent(); n=0
        while v in p: n+=1; v=p[v]
        return n

    def root(self,v):
        p=self.parent()
        while v in p: v=p[v]
        return v

    def ancestors(self,v):
        p=self.parent(); a=[v]
        while v in p: v=p[v]; a.append(v)
        return a

    def below(self,v,ancestor):
        return ancestor in self.ancestors(v)

    def sibling(self,v):
        p=self.parent()
        if v not in p: return None
        cs=self.child[p[v]]
        return next((w for w in cs if w!=v),None)

    def pendants(self,a,c):
        aa,cc=self.ancestors(a),self.ancestors(c)
        if aa[-1]!=cc[-1]: return None,None
        u=next(v for v in aa if v in cc)
        path=aa[:aa.index(u)+1]+list(reversed(cc[:cc.index(u)]))
        on=set(path)
        bs=[w for v in path[1:-1] for w in self.child[v] if w not in on]
        return bs,u

    def reduce(self):
        while True:
            p=self.parent()
            v=next((v for v,cs in self.child.items() if v not in self.label and len(cs)<2),None)
            if v is None: break
            cs=self.child[v]
            if v in p:
                u=p[v]; ix=self.child[u].index(v)
                self.child[u][ix:ix+1]=cs
                if cs and v in self.protected: self.protected.add(cs[0])
            # At an unlabelled root, the sole remaining edge disappears.
            # Legal cuts refuse protected sibling root edges before this point.
            elif cs:
                self.protected.discard(cs[0])
            self.protected.discard(v)
            del self.child[v]
        self.protected.intersection_update(self.parent())

    def legal(self, cuts):
        p=self.parent()
        for v in cuts:
            if v not in p: raise SemanticHole('requested cut has no parent edge')
            if v in self.protected: return False
            if p[v] not in p:
                sib=self.sibling(v)
                if sib in self.protected: return False
        return True

    def cut(self,cuts):
        f=deepcopy(self); p=f.parent()
        if len(set(cuts))!=len(cuts): raise SemanticHole('duplicate cut request')
        for v in cuts:
            if v not in p: raise SemanticHole('cut edge vanished before simultaneous cut')
            f.child[p[v]].remove(v)
            f.protected.discard(v)
        f.reduce()
        return f

    def remove_atom(self,v):
        if self.child[v]: raise SemanticHole('finished atom not a contracted leaf')
        p=self.parent()
        if v in p: self.child[p[v]].remove(v)
        del self.child[v]; del self.label[v]; self.protected.discard(v)
        self.reduce()

    def merge(self,a,c):
        p=self.parent()
        if a not in p or c not in p or p[a]!=p[c]:
            raise SemanticHole('contracting non-siblings')
        u=p[a]
        if self.child[a] or self.child[c] or u in self.label:
            raise SemanticHole('contracting a non-atomic cherry')
        self.label[u]=self.label.pop(a)|self.label.pop(c)
        self.child[u]=[]
        del self.child[a]; del self.child[c]
        self.protected.difference_update([a,c])


def choose(f1,f2):
    p1=f1.parent()
    eligible=[]
    protected_parents=[p1[v] for v in f1.protected]
    x=max(protected_parents,key=f1.depth) if protected_parents else None
    if x is not None:
        if not all(f1.below(x,w) for w in protected_parents):
            raise SemanticHole('protected F1 edge tops are not on one path')
        if not all(v in f1.label and not f1.child[v] for v in f1.protected):
            raise SemanticHole('protected F1 edge bottom not in Rt')
    for u,cs in f1.child.items():
        if len(cs)==2 and all(v in f1.label and not f1.child[v] for v in cs):
            if x is not None and not f1.below(u,x): continue
            av,cv=cs
            a,c=f2.atom(f1.label[av]),f2.atom(f1.label[cv])
            # Source pp.120-121 uses a at least as deep as c.
            if (f2.depth(a),repr(sorted(f2.label[a]))) < (f2.depth(c),repr(sorted(f2.label[c]))):
                av,cv,a,c=cv,av,c,a
            key=(f1.depth(av),f2.root(a)!=f2.root(c),max(f2.depth(a),f2.depth(c)),repr(sorted(f1.label[av])))
            eligible.append((key,av,cv,a,c))
    if not eligible: raise SemanticHole('no eligible sibling pair with |Rt|>2')
    return max(eligible)[1:]


def branches(f1,f2,av,cv,a,c):
    """Return source case and ordered (cut bottoms, protect F1, protect F2)."""
    if f2.root(a)!=f2.root(c): return 'AC',[([a],[],[]),([c],[],[])]
    bs,u=f2.pendants(a,c)
    if len(bs)==1: return 'B',[(bs,[],[])]
    if len(bs)<2: raise SemanticHole('nontrivial connected pair has no pendants')
    p1=f1.parent(); pa=p1[av]; x1=f1.sibling(pa)
    sa,sc=f2.sibling(a),f2.sibling(c)
    if x1 is not None:
        if sa is not None and f1.shape(x1)==f2.shape(sa): return 'RB',[([c],[],[])]
        if sc is not None and f1.shape(x1)==f2.shape(sc): return 'RB',[([a],[],[])]
        # RB*: source's entire caterpillar test, not merely its b1,b2 consequence.
        if f2.parent().get(c)==u:
            shapes=[f2.shape(b) for b in bs]
            chain=((),tuple(sorted(shapes[:2],key=repr)))
            for sh in shapes[2:]: chain=((),tuple(sorted([chain,sh],key=repr)))
            if f1.shape(x1)==chain: return 'RB*',[([a],[],[])]
        x2=f2.match(f1,x1)
        if x2 is not None:
            if len(bs)==2 and f2.sibling(u)==x2: return '2B',[(bs,[],[])]
            if x2 in f2.protected and f2.parent().get(x2)==bs[0]:
                y=f2.sibling(x2)
                if y is None: raise SemanticHole('BCY x has no sibling')
                return 'BCY',[(bs,[],[]),([c,y],[],[])]
    if len(bs)==2:
        if c in f2.protected:
            return 'A2BC-protected-c',[(bs,[],[]),([a],[],bs)]
        return 'A2BC',[([a],[],[]),(bs,[],[]),([c],[av],[a]+bs)]
    return 'A3BC',[([a],[],[]),(bs,[],[]),([c],[av],[a])]


def decide(t1,t2,budget,stats=None,trace=None,protection=True):
    f1,f2=Forest.tree(t1),Forest.tree(t2)
    if set(f1.label.values()) != set(f2.label.values()): raise ValueError('different label sets')
    stats={} if stats is None else stats
    def rec(g1,g2,q):
        stats['calls']=stats.get('calls',0)+1
        if q<0: return False
        while len(g1.label)>2:
            av,cv,a,c=choose(g1,g2)
            p2=g2.parent()
            if a in p2 and c in p2 and p2[a]==p2[c]:
                g1.merge(av,cv); g2.merge(a,c)
                stats['contract']=stats.get('contract',0)+1
                continue
            if a not in p2:
                g1.remove_atom(av); g2.remove_atom(a)
                stats['finish']=stats.get('finish',0)+1
                continue
            if c not in p2:
                g1.remove_atom(cv); g2.remove_atom(c)
                stats['finish']=stats.get('finish',0)+1
                continue
            case,opts=branches(g1,g2,av,cv,a,c)
            stats[case]=stats.get(case,0)+1
            if trace is not None:
                trace.append({'case':case,'budget':q,'a':sorted(g2.label[a]),'c':sorted(g2.label[c]),'branches':len(opts)})
            for cut,pf1,pf2 in opts:
                h2=deepcopy(g2)
                if protection: h2.protected.update(pf2)
                if protection and not h2.legal(cut):
                    stats['refused']=stats.get('refused',0)+1
                    continue
                h1=deepcopy(g1)
                if protection: h1.protected.update(pf1)
                if rec(h1,h2.cut(cut),q-len(cut)): return True
            return False
        return True
    return rec(f1,f2,budget)
