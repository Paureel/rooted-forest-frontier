"""Postrelease actual Python readouts against frozen independent graph fixtures.
The explicit cut-first query adapter is postcontact, not blind-query-order credit.
"""
import argparse,dataclasses,hashlib,importlib.util,json,pathlib,sys,time,traceback
H=pathlib.Path(__file__).resolve().parent;PRE=H.parent
ROOT=next(p for p in H.parents if(p/"bootloops-python").exists())
sys.path.insert(0,str(PRE));import original_graph as og
SOURCE=ROOT/"research/rmaf/algorithm/universal233/rule4/rule4.py"
def strs(t):return str(t)if type(t)is int else tuple(strs(x)for x in t)
def ints(t):return int(t)if isinstance(t,str)else [ints(x)for x in t]
def Fint(F):return [[int(x)for x in b]for b in F]
def Fstr(F):return tuple(tuple(str(x)for x in b)for b in F)
def top(t):
    g=og.Graph(ints(t));return g.restricted(g.labels)
def any_residual(g,heads):
    if len(heads)!=len(set(heads))or any(h not in g.adj or h==g.root for h in heads):raise ValueError("bad original final cut")
    cuts={frozenset((h,g.parent[h]))for h in heads};seen=set();out=[]
    for seed in g.adj:
        if seed in seen:continue
        queue=[seed];comp={seed};seen.add(seed)
        for v in queue:
            for w in g.adj[v]:
                if w not in seen and frozenset((v,w))not in cuts:queue.append(w);comp.add(w);seen.add(w)
        B=sorted(x for x in g.labels if g.vertex(x)in comp)
        if not B:raise ValueError("leafless final region")
        out.append({"vertices":sorted(g.address[v]for v in comp),"labels":B})
    return out
def main():
    p=argparse.ArgumentParser();p.add_argument("--limit",type=int,required=True);p.add_argument("--output",required=True);a=p.parse_args()
    pins=json.loads((ROOT/"research/rmaf/algorithm/universal233/rule4/RULE4-MANIFEST-v1.json").read_text())
    pin=next(r for r in pins["immutable_files"]if r["path"]==str(SOURCE.relative_to(ROOT)))
    assert hashlib.sha256(SOURCE.read_bytes()).hexdigest()==pin["sha256"]
    spec=importlib.util.spec_from_file_location("released_rule4_actual",SOURCE);mod=importlib.util.module_from_spec(spec);sys.modules[spec.name]=mod;spec.loader.exec_module(mod)
    fixtures=json.loads((PRE/"fixtures-output-v2.json").read_text())["fixtures"][:a.limit]
    results=[];checks=[];start=time.perf_counter()
    def check(name,ok):
        checks.append({"name":name,"passed":bool(ok)})
        if not ok:raise AssertionError(name)
    for f in fixtures:
        t,s=og.Graph(f["T"]),og.Graph(f["S"]);T,S=strs(f["T"]),strs(f["S"])
        candidates=mod.candidates(T,S);records=[]
        check(f["name"]+" candidates admitted",bool(candidates))
        for sel in candidates:
            independent=next(x for x in og.choices(t,s)if(x["a"],x["b"],x["c"])==(int(sel.a),int(sel.b),int(sel.c)))
            ib=og.literal_branches(t,s,independent);branchrows=[]
            for i,b in enumerate(sel.branches):
                g=ib[i]["source"];tt=ib[i]["target"];heads=[g.by_address[h]for h in b.cuts]
                expected_cuts=[g.address[v]for v in ib[i]["heads"]]
                if i==2:expected_cuts.sort()
                check(f"{f['name']} branch{i} exact outgoing cuts",list(b.cuts)==expected_cuts)
                actual_regions=mod.Graph(b.source).cut_regions(b.cuts)
                regions=any_residual(g,heads)
                expected_order=[next(r for r in regions if h in r["vertices"])for h in(*b.cuts,"")]
                P=[r["labels"]for r in expected_order]
                check(f"{f['name']} branch{i} literal partition",Fint(b.partition)==P)
                check(f"{f['name']} branch{i} original vertices",all(sorted(ar["vertices"])==er["vertices"]for ar,er in zip(actual_regions,expected_order)))
                check(f"{f['name']} branch{i} target role",top(b.target)==tt.restricted(tt.labels))
                check(f"{f['name']} branch{i} source restrictions",[top(x)for x in b.source_forest]==[g.restricted(p)for p in P])
                check(f"{f['name']} branch{i} paid",b.cost+1==len(P)and b.cost==len(heads))
                branchrows.append({"index":i,"target":b.target,"source":b.source,"cuts":b.cuts,"partition":b.partition,"source_forest":b.source_forest,"cost":b.cost,"swapped":b.swapped,"original_regions":expected_order})
            exchanges=[]
            for F in f["agreements"]:
                index,G,why=mod.covering_exchange(sel,Fstr(F));Gi=Fint(G)
                check(f"{f['name']} original exchange {og.canon(F)}",og.agreement(t,s,Gi)and len(Gi)<=len(F)and og.refines(Gi,ib[index]["P"]))
                exchanges.append({"F":F,"G":Gi,"branch":index,"why":why})
            budgets=[]
            for q in range(5):
                calls=[]
                def child(b,r):
                    i=next(j for j,bb in enumerate(sel.branches)if b is bb)
                    if r!=q-b.cost or b.cost>q:raise ValueError("wrong budget request")
                    calls.append({"branch_index":i,"residual":r,"target":b.target,"source_forest":b.source_forest})
                    tab=[F for F in f["agreements"]if og.refines(F,ib[i]["P"])and len(F)-len(ib[i]["P"])<=r]
                    return Fstr(min(tab,key=lambda F:(len(F),og.canon(F))))if tab else None
                answer,actual_calls=mod.solve_selected(sel,q,child)
                feasible=[F for F in f["agreements"]if len(F)-1<=q]
                check(f"{f['name']} parent minimum q{q}",(answer is None)==(not feasible)and(answer is None or answer["k"]==min(map(len,feasible))))
                if answer:
                    Gi=Fint(answer["forest"]);headsv=[s.by_address[h]for h in answer["original_source_cuts"]]
                    rr=any_residual(s,headsv)
                    check(f"{f['name']} final original certificate q{q}",og.agreement(t,s,Gi)and len(headsv)==len(Gi)-1 and og.same_partition([r["labels"]for r in rr],Gi))
                expected_indices=[i for i,b in enumerate(sel.branches)if b.cost<=q]
                check(f"{f['name']} actual affordable callbacks q{q}",[x["branch_index"]for x in calls]==expected_indices)
                budgets.append({"q":q,"literal_requests":calls,"actual_call_report":actual_calls,"answer":answer})
            records.append({"a":sel.a,"b":sel.b,"c":sel.c,"branches":branchrows,"exchanges":exchanges,"budgets":budgets})
        results.append({"fixture":f["name"],"records":records})
        if time.perf_counter()-start>5:raise TimeoutError("fixed Python fixture slice5s cap")
    guards=[]
    guardtrees=[("common",[[[0,1],3],[2,4]],[[[0,1],3],[2,4]]),
        ("t1-forward",[[0,1],[2,3]],[[[0,2],1],3]),("t1-source",[[[0,2],1],3],[[0,1],[2,3]]),
        ("unequal",[[[0,1],3],[2,4]],[[0,2],[1,[3,9]]]),
        ("bad-geometry",[[[0,1],3],[2,[4,5]]],[[[[[0,2],3],4],1],5])]
    for name,T,S in guardtrees:
        got=mod.select(strs(T),strs(S));check("actual selector guard "+name,got is None);guards.append({"name":name,"selected":got is not None})
    try:mod.select(strs([[[0,1],3],[2,4]]),strs([[0,2],[1,[3,3]]]))
    except ValueError:duplicate=True
    else:duplicate=False
    check("actual selector duplicate",duplicate)
    source=strs(fixtures[0]["S"]);graph=mod.Graph(source)
    for name,cuts in[("root",("",)),("duplicate",("01","01")),("absent",("111111",))]:
        check("actual original cut refusal "+name,og.expect_refusal(lambda cuts=cuts:graph.partition_after(cuts)))
    # Comparable heads can be valid general original cuts; only literal Rule4
    # source partitions require an antichain. Do not conflate the two domains.
    nested=("1","11")
    rr=any_residual(og.Graph(fixtures[0]["S"]),[og.Graph(fixtures[0]["S"]).by_address[h]for h in nested])
    check("general comparable original cuts may be valid",og.same_partition(Fint(graph.partition_after(nested)),[r["labels"]for r in rr]))
    out={"source_sha256":pin["sha256"],"postcontact_query_adapter":"cut heads in literal order then retained original root component; frozen BFS-first tables preserved unchanged",
        "checks":checks,"passed":len(checks),"fixtures":results,"guards":guards,"seconds":time.perf_counter()-start,
        "qualifications":"actual Python finite readouts only; exact/minimum/complete callback is supplied from frozen independent original agreements; no universal Lean/Python equivalence"}
    (H/a.output).write_text(json.dumps(out,indent=2)+"\n");print(json.dumps({"checks":len(checks),"fixtures":len(results),"seconds":out["seconds"]}))
if __name__=="__main__":
    try:main()
    except Exception:
        with(H/"runtime-python-failures.log").open("a")as f:f.write(traceback.format_exc()+"\n")
        raise
