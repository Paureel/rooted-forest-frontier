"""One-shot blind Rule4 verifier, written from public specification on 2026-10-15.

Original graphs use integer vertices, undirected adjacency and BFS paths. Only
topology canonicalization suppresses unary vertices. No candidate code is read.
Finite enumeration tests bounded fixtures; it cannot establish a universal cover.
"""
from __future__ import annotations
import argparse, copy, hashlib, itertools, json, pathlib, time
from fractions import Fraction

HERE = pathlib.Path(__file__).resolve().parent

class Graph:
    def __init__(self, tree):
        self.tree = tree
        self.adj, self.children, self.parent, self.address, self.leaf = {}, {}, {}, {}, {}
        self.labels = []
        def visit(t, p=None, a=""):
            v = len(self.adj)
            self.adj[v], self.children[v], self.address[v] = [], [], a
            if p is not None:
                self.adj[v].append(p); self.adj[p].append(v)
                self.parent[v] = p; self.children[p].append(v)
            if type(t) is int:
                if t < 0: raise ValueError("negative label")
                self.labels.append(t)
                self.leaf.setdefault(t, []).append(v)
            elif isinstance(t, (tuple, list)) and len(t) == 2:
                visit(t[0], v, a+"0"); visit(t[1], v, a+"1")
            else: raise ValueError("not binary Tree")
            return v
        self.root = visit(tree)
        self.by_address = {a:v for v,a in self.address.items()}
        self.proper = len(self.labels) == len(set(self.labels))
    def vertex(self, x):
        if x not in self.leaf or len(self.leaf[x]) != 1: raise ValueError("absent/duplicate label")
        return self.leaf[x][0]
    def path(self, x, y):
        start, end = self.vertex(x), self.vertex(y)
        queue, prev = [start], {start:None}
        for v in queue:
            if v == end: break
            for w in self.adj[v]:
                if w not in prev: prev[w] = v; queue.append(w)
        result, v = [], end
        while v is not None: result.append(v); v = prev[v]
        return list(reversed(result))
    def hull(self, block):
        if not block: raise ValueError("empty block")
        first = block[0]
        return set().union(*(set(self.path(first,x)) for x in block))
    def descendants(self, v):
        seen, stack = set(), [v]
        while stack:
            w=stack.pop(); seen.add(w); stack.extend(self.children[w])
        return sorted(x for x in self.labels if self.vertex(x) in seen)
    def cherries(self):
        return sorted(tuple(sorted(self.descendants(v))) for v,ch in self.children.items()
                      if len(ch)==2 and all(not self.children[w] for w in ch))
    def pendant(self, a, b, reverse=False):
        path=self.path(a,b); inside=set(path)
        heads=[w for v in path for w in self.children[v] if w not in inside]
        return list(reversed(heads)) if reverse else heads
    def restricted(self, block):
        block=set(block)
        if not block <= set(self.labels) or not block: raise ValueError("restriction labels")
        def go(v):
            if not self.children[v]:
                x=next(x for x,vs in self.leaf.items() if v in vs)
                return ("L",x) if x in block else None
            cs=[a for w in self.children[v] if (a:=go(w)) is not None]
            if not cs: return None
            if len(cs)==1: return cs[0]
            return ("N",)+tuple(sorted(cs,key=repr))
        return go(self.root)
    def cut_partition(self, heads):
        if len(heads)!=len(set(heads)): raise ValueError("duplicate cut")
        if any(v not in self.adj or v==self.root for v in heads): raise ValueError("invalid original cut")
        # Literal selected branches have incomparable cut heads.
        for v,w in itertools.combinations(heads,2):
            av,aw=self.address[v],self.address[w]
            if av.startswith(aw) or aw.startswith(av): raise ValueError("comparable cut")
        cuts={frozenset((v,self.parent[v])) for v in heads}
        regions=[]; pending=set(self.adj)
        while pending:
            seed=min(pending); comp={seed}; queue=[seed]; pending.remove(seed)
            for v in queue:
                for w in self.adj[v]:
                    if w in pending and frozenset((v,w)) not in cuts:
                        pending.remove(w); comp.add(w); queue.append(w)
            labels=sorted(x for x in self.labels if self.vertex(x) in comp)
            if not labels: raise ValueError("leafless component")
            regions.append((comp,labels))
        return regions

def partition_ok(labels,F):
    flat=[x for b in F for x in b]
    return bool(F) and all(b for b in F) and sorted(flat)==sorted(labels) and len(flat)==len(set(flat))

def separated(g,F):
    hs=[g.hull(b) for b in F]
    return all(hs[i].isdisjoint(hs[j]) for i in range(len(hs)) for j in range(i))

def agreement(t,s,F):
    return (t.proper and s.proper and partition_ok(t.labels,F) and partition_ok(s.labels,F)
            and all(t.restricted(b)==s.restricted(b) for b in F)
            and separated(t,F) and separated(s,F))

def partitions(labels):
    # Restricted-growth insertion: each unordered partition exactly once.
    blocks=[]
    def go(i):
        if i==len(labels): yield [b[:] for b in blocks]; return
        x=labels[i]
        for b in blocks:
            b.append(x); yield from go(i+1); b.pop()
        blocks.append([x]); yield from go(i+1); blocks.pop()
    yield from go(0)

def refines(F,P): return all(any(set(b)<=set(c) for c in P) for b in F)

def t1(t,s):
    return [(a,b) for a,b in t.cherries() if len(s.pendant(a,b))==1]

def choices(t,s,reverse=False):
    if not t.proper or not s.proper or sorted(t.labels)!=sorted(s.labels): return []
    if set(t.cherries())&set(s.cherries()) or t1(t,s) or t1(s,t): return []
    out=[]
    for cherry in t.cherries():
        for a,b in (cherry,tuple(reversed(cherry))):
            heads=s.pendant(a,b,reverse)
            if len(heads)!=2: continue
            for h in heads:
                xs=s.descendants(h)
                if len(xs)!=1: continue
                c=xs[0]
                if tuple(sorted((a,c))) not in s.cherries(): continue
                other=next(v for v in heads if v!=h)
                swapped=t.pendant(a,c)
                if len(swapped)<2: raise AssertionError("no-t1 failed to derive m>=2")
                out.append({"a":a,"b":b,"c":c,"c_head":s.address[h],
                            "x2_head":s.address[other],"x2":s.descendants(other),
                            "swapped_heads":[t.address[v] for v in swapped]})
    return out

def literal_branches(t,s,ch):
    a=ch["a"]
    configs=[(t,s,[s.by_address[ch["c_head"]],s.by_address[ch["x2_head"]]]),
             (t,s,[s.vertex(a)]),
             (s,t,[t.by_address[v] for v in ch["swapped_heads"]])]
    result=[]
    for target,source,heads in configs:
        regions=source.cut_partition(heads); P=[b for _,b in regions]
        assert len(P)==len(heads)+1 and partition_ok(source.labels,P) and separated(source,P)
        forest=[source.restricted(b) for b in P]
        result.append({"target":target,"source":source,"heads":heads,"P":P,
                       "forest":forest,"cost":len(heads),"regions":regions})
    return result

def forest_agrees(branch,F):
    t,s,P=branch["target"],branch["source"],branch["P"]
    if not partition_ok(t.labels,P) or len(P)!=len(branch["forest"]): return False
    if not separated(s,P): return False
    if any(actual!=s.restricted(p) for p,actual in zip(P,branch["forest"])): return False
    if not partition_ok(t.labels,F) or not refines(F,P) or not separated(t,F): return False
    # Independent source restriction checks: do not require target embeddings of P.
    for p,restricted in zip(P,branch["forest"]):
        family=[b for b in F if set(b)<=set(p)]
        if not partition_ok(p,family): return False
        sg=Graph(topology_to_tree(restricted))
        if not separated(sg,family): return False
        if any(t.restricted(b)!=sg.restricted(b) for b in family): return False
    return True

def topology_to_tree(top):
    return top[1] if top[0]=="L" else [topology_to_tree(top[1]),topology_to_tree(top[2])]

def canon(F): return tuple(sorted(tuple(sorted(b)) for b in F))
def same_partition(F,G): return canon(F)==canon(G)
def expect_refusal(fn):
    try: fn()
    except (ValueError,AssertionError,IndexError): return True
    return False

def exact_tables(branches,allF):
    return [[F for F in allF if forest_agrees(b,F)] for b in branches]

def solve(branches,q,tables,mutation=None):
    returned=[]; calls=[]
    for i,b in enumerate(branches):
        if b["cost"]>q: continue
        r=q-b["cost"]; calls.append((i,r))
        feasible=[F for F in tables[i] if len(F)-len(b["P"])<=r]
        answer=min(feasible,key=lambda F:len(F),default=None)
        if mutation is not None: answer=mutation(i,r,answer,b)
        if answer is not None:
            if not forest_agrees(b,answer): raise ValueError("returned child query mismatch")
            if not agreement(b["target"],b["source"],answer): raise ValueError("returned original mismatch")
            if b["cost"]+(len(answer)-len(b["P"]))!=len(answer)-1: raise ValueError("paid identity")
            if len(answer)-1>q: raise ValueError("returned budget")
            returned.append((i,answer))
    return min(returned,key=lambda x:len(x[1]),default=None),calls

def check_controls(expect):
    checks=[]
    def check(name,value):
        checks.append({"control":name,"passed":bool(value)})
        if not value: raise AssertionError(name)
    t,s=Graph(expect["T"]),Graph(expect["S"])
    check("T cherries",[list(x) for x in t.cherries()]==expect["T_cherries"])
    check("S cherries",[list(x) for x in s.cherries()]==expect["S_cherries"])
    check("original S path",[s.address[v] for v in s.path(0,1)]==expect["S_path_a_b"])
    check("original T path",[t.address[v] for v in t.path(0,2)]==expect["T_path_a_c"])
    check("original unsuppressed hull",sorted(t.address[v] for v in t.hull([0,3]))==expect["original_hull_T_0_3"])
    check("suppressed topology",t.restricted([0,3])==("N",("L",0),("L",3)))
    check("caught false suppressed separation",not separated(t,expect["overlap_false_partition_T"]))
    check("no priorities",not t1(t,s) and not t1(s,t) and not(set(t.cherries())&set(s.cherries())))
    cs=choices(t,s)
    check("admitted original geometry",any(c["a"]==0 and c["b"]==1 and c["c"]==2 for c in cs))
    ch=next(c for c in cs if c["a"]==0)
    bs=literal_branches(t,s,ch)
    check("literal source partitions",all(same_partition(b["P"],p) for b,p in zip(bs,expect["branch_source_partitions"])))
    check("literal branch costs",[b["cost"] for b in bs]==expect["branch_costs"])
    F,G=expect["strict_refinement_false_F"],expect["same_size_replacement_G"]
    check("strict-F false control original",agreement(t,s,F) and not any(refines(F,b["P"]) for b in bs))
    check("exchange replacement",agreement(t,s,G) and len(G)==len(F) and refines(G,bs[0]["P"]))
    check("whole partition false",not agreement(t,s,[t.labels]))
    check("singletons true",agreement(t,s,[[x] for x in t.labels]))
    crossT=Graph(expect["four_label_crossed_T"]); crossS=Graph(expect["four_label_crossed_S"])
    crossF=[F for F in partitions(sorted(crossT.labels)) if agreement(crossT,crossS,F)]
    check("planted crossed quartet min",min(map(len,crossF))==expect["four_label_crossed_minimum_components"])
    # This source-valid P has overlapping target hulls. The singleton answer is valid.
    P=[[0,2],[1,3]]
    example={"target":crossT,"source":crossS,"P":P,"forest":[crossS.restricted(p) for p in P]}
    check("target-Q separation not a premise",not separated(crossT,P) and forest_agrees(example,[[i] for i in range(4)]))
    bad=copy.copy(example); bad["forest"]=example["forest"][:-1]
    check("caught dropped nonempty block",not forest_agrees(bad,[[i] for i in range(4)]))
    for name,heads in [("root cut",[s.root]),("duplicate cut",[s.vertex(0),s.vertex(0)]),
                       ("absent cut",[999]),("comparable cut",[s.by_address["1"],s.by_address["11"]])]:
        check(name,expect_refusal(lambda heads=heads:s.cut_partition(heads)))
    check("absent endpoint",expect_refusal(lambda:s.path(99,1)))
    check("common cherry guard",not choices(t,t))
    check("duplicate labels guard",not choices(t,Graph([[0,2],[1,[3,3]]])))
    check("unequal labels guard",not choices(t,Graph([[0,2],[1,[3,9]]])))
    check("bad pendant geometry",not choices(Graph([[0,1],[2,3]]),Graph([[0,2],[1,3]])))
    # Swapping input roles and leaf names must not be hidden by a fixed orientation.
    check("role-swap admitted",bool(choices(s,t)))
    def relabel(tree,f): return f(tree) if type(tree)is int else [relabel(x,f) for x in tree]
    flipped=choices(Graph(relabel(expect["T"],lambda x:1-x if x in(0,1) else x)),Graph(relabel(expect["S"],lambda x:1-x if x in(0,1) else x)))
    check("opposite endpoint admitted",any(c["a"]==1 and c["b"]==0 and c["c"]==2 for c in flipped))
    check("both pendant traversal orders",canon_choices(cs)==canon_choices(choices(t,s,True)))
    # Dedicated t1 fixtures have no common cherry, and t1 only one direction.
    t1T=Graph([[0,1],[2,3]]); t1S=Graph([[[0,2],1],3])
    check("t1 forward catches",bool(t1(t1T,t1S)) and not choices(t1T,t1S))
    check("t1 swapped catches",bool(t1(t1S,t1T)) and not choices(t1S,t1T))
    return checks

def canon_choices(cs): return sorted((x["a"],x["b"],x["c"],tuple(x["x2"])) for x in cs)

def run_fixture(T,S,name,cap):
    start=time.perf_counter(); t,s=Graph(T),Graph(S)
    allF=list(partitions(sorted(t.labels)))
    if len(allF)>cap: raise ValueError("partition cap")
    agrees=[F for F in allF if agreement(t,s,F)]
    results=[]
    for reverse in (False,True):
        for ch in choices(t,s,reverse):
            bs=literal_branches(t,s,ch); tables=exact_tables(bs,allF)
            witnesses=[]
            for F in agrees:
                candidates=[(i,G) for i,tab in enumerate(tables) for G in tab if len(G)<=len(F)]
                if not candidates: raise AssertionError({"COVER_FIRE":F,"choice":ch})
                witnesses.append({"F":F,"branch":candidates[0][0],"G":candidates[0][1]})
            budgets=[]
            for q in range(5):
                answer,calls=solve(bs,q,tables)
                feasible=[F for F in agrees if len(F)-1<=q]
                if (answer is None)!=(not feasible): raise AssertionError("None iff")
                if answer and len(answer[1])!=min(map(len,feasible)): raise AssertionError("minimum")
                masses={str(c):str(sum((c**(-bs[i]["cost"]) for i,_ in calls),Fraction(0))) for c in (Fraction(2),Fraction(233,100),Fraction(3))}
                for c in (Fraction(2),Fraction(233,100),Fraction(3)):
                    assert sum((c**(-bs[i]["cost"]) for i,_ in calls),Fraction(0))<=1/c+2/c**2
                budgets.append({"q":q,"calls":calls,"answer":answer,"masses":masses})
            results.append({"reverse_pendant_order":reverse,"choice":ch,"source_partitions":[b["P"] for b in bs],
                "source_forests":[b["forest"] for b in bs],"child_tables":tables,
                "costs":[b["cost"] for b in bs],"coverage":witnesses,"budgets":budgets})
    return {"name":name,"T":T,"S":S,"partition_count":len(allF),"agreements":agrees,
            "minimum_components":min(map(len,agrees)),"choices":results,"elapsed_seconds":time.perf_counter()-start}

def main():
    parser=argparse.ArgumentParser(); parser.add_argument("--mode",choices=["controls","pilot","fixtures"],required=True)
    args=parser.parse_args(); start=time.time()
    E=json.loads((HERE/"EXPECTATIONS-v1.json").read_text())
    output={"mode":args.mode,"start_unix":start,"candidate_contact":False}
    output["controls"]=check_controls(E)
    if args.mode in ("pilot","fixtures"):
        output["fixtures"]=[run_fixture(E["T"],E["S"],"five-label-root",203)]
    if args.mode=="fixtures":
        output["fixtures"].append(run_fixture([E["T"],5],[E["S"],5],"external-root-sibling",203))
        output["fixtures"].append(run_fixture(E["S"],E["T"],"reversed-roles",203))
    output["end_unix"]=time.time(); output["elapsed_seconds"]=time.time()-start
    dest=HERE/(args.mode+"-output-v1.json"); dest.write_text(json.dumps(output,indent=2)+"\n")
    print(json.dumps({"mode":args.mode,"controls":len(output["controls"]),"fixtures":len(output.get("fixtures",[])),"elapsed_seconds":output["elapsed_seconds"],"output":str(dest)}))
if __name__=="__main__": main()
