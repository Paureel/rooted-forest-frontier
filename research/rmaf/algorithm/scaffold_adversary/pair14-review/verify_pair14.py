"""Targeted released-literal reconstruction using the pre-existing checker.

No author Python evaluator imports. Production outputs are read from the owned
Lean source replay. Exact simultaneous original cuts precede any suppression.
"""
from controls import *


ROOT=HERE.parents[4]
RESULTS=ROOT/"research/rmaf/results"


def address_clades(raw,expansion=None):
    result={}
    def rec(x,p):
        if isinstance(x,int):
            lab=frozenset([x]) if expansion is None else frozenset(expansion[x])
        else:
            lab=rec(x[0],p+"0")|rec(x[1],p+"1")
        result[p]=lab
        return lab
    rec(raw,"")
    return result


def label_node_map(g):
    return {g.labs(v):v for v in g.ch}


def map_raw_edges(g,raw,edges):
    bylabel=label_node_map(g)
    addresses=address_clades(raw)
    pa=g.parent()
    ans=[]
    for a,b in edges:
        if b[:-1]!=a or len(b)!=len(a)+1 or a not in addresses or b not in addresses:
            raise ValueError("not an original raw source edge")
        v=bylabel[addresses[b]]
        p=pa[v]
        if g.labs(p)!=addresses[a]:
            raise AssertionError("original parent mapping")
        ans.append((p,v))
    return ans


def raw_edge_for_graph(g,raw,edge):
    addresses=address_clades(raw)
    inverse={lab:p for p,lab in addresses.items()}
    return (inverse[g.labs(edge[0])],inverse[g.labs(edge[1])])


def simultaneous_original_cuts(original,edges):
    if len(edges)!=len(set(edges)):
        raise ValueError("duplicate edge cannot earn cut charge")
    g=original.clone()
    for e in edges:
        if e not in original.original_edges:
            raise ValueError("not an original graph edge")
        a,b=e
        g.ch[a].remove(b)
        g.lift.pop(e)
        g.roots.add(b)
        g.cut_history.append(e)
    empty=[r for r in g.roots if not g.labs(r)]
    if empty:
        raise ValueError(("leafless component",empty))
    part=g.partition()
    if len(part)!=len(edges)+1:
        raise AssertionError("source cuts are redundant")
    g.tidy()
    if g.partition()!=part:
        raise AssertionError("unary suppression changed labels")
    return g


def region_colors_original(t,v,labels_):
    adjacency={w:set() for w in t.ch}
    for a,b in t.lift:
        adjacency[a].add(b);adjacency[b].add(a)
    todo=set(adjacency)-{v}
    colors={};regions=[]
    while todo:
        seed=min(todo);found={seed};stack=[seed]
        while stack:
            w=stack.pop()
            for z in adjacency[w]-{v}-found:
                found.add(z);stack.append(z)
        todo-=found
        labs=frozenset().union(*(t.group.get(w,frozenset()) for w in found))&frozenset(labels_)
        if labs:
            for a in labs:colors[a]=len(regions)
            regions.append(labs)
    if set(colors)!=set(labels_):
        raise AssertionError("vertex-region label coverage")
    return colors,regions


def expand_tree(raw,expansion):
    if isinstance(raw,int):
        return frozenset(expansion[raw])
    return canon(tuple(expand_tree(q,expansion) for q in raw))


def main():
    start=time.perf_counter()
    author=json.loads((RESULTS/"algorithm-universal233-pair-charging-fire-v1.json").read_text())
    w=author["witness"]
    cuts_receipt=json.loads((RESULTS/"algorithm-universal233-pair-fire-original-cuts-v3.json").read_text())
    prod=json.loads((HERE/"production-readout.json").read_text())
    t,s=Graph(tree(w["original_T"])),Graph(tree(w["original_Tprime"]))
    admission=evaluate(w["original_T"],w["original_Tprime"],w["cherry"],False)
    if not admission["eligible"] or len(admission["original"]["labels"])!=14:
        raise AssertionError("literal fails original source guards")
    ps=pendants(s,*map(leaf,w["cherry"]))
    hardcuts=[p["edge"] for p in ps]
    child=simultaneous_original_cuts(s,hardcuts)
    if child.partition()!=pkey(cuts_receipt["source_parents"]):
        raise AssertionError("actual original pendant parents")
    cl=classification(t,child)
    if cl["homeomorphic"]!=[False,True,True] or cl["overlap_pairs"]!=[(0,1)] or cl["isolated"]!=[2]:
        raise AssertionError("original parent homeomorphism/overlap/isolated guard")
    selectors=actual_selectors(t,child)
    expansion={int(k):v for k,v in w["reduced"]["expansion"].items()}
    target_addresses=address_clades(w["reduced"]["T"],expansion)
    target_nodes=label_node_map(t)
    author_to_own={p:target_nodes[lab] for p,lab in target_addresses.items()}
    own_to_author={v:p for p,v in author_to_own.items()}
    shared_vertices=sorted(own_to_author[v] for v in selectors["vertices"])
    shared_edges=sorted((own_to_author[a],own_to_author[b]) for a,b in selectors["edges"])
    if not exact_selector_claim(shared_vertices,[r["vertex"] for r in w["vertex_rows"]]):
        raise AssertionError("author omitted/duplicated an actual shared vertex selector")
    if len(shared_vertices)!=3 or len(shared_edges)!=2:
        raise AssertionError("shared-selector denominator")
    # Fresh core and source-rule reconstruction uses the old checker, not author code.
    core_rows=[];mutation_rows=[];cut_record_differences=[]
    for vr in w["vertex_rows"]:
        vertex=author_to_own[vr["vertex"]]
        tasks=[];emissions=[]
        for source_index in [0,1]:
            labels_=cl["blocks"][source_index]
            colors,regions=region_colors_original(t,vertex,labels_)
            if len(regions)!=2:
                raise AssertionError("not actual pure-two-region source case")
            own_core=colored_core(component_graph(child,cl["roots"][source_index]),colors)
            pname=("A" if colors[0]==0 else "ASwap") if source_index==0 else ("B" if colors[4]==0 else "BSwap")
            production=prod[pname]
            if production["refusals"] or production["pruned"]:
                raise AssertionError("production core refused or pruned required output")
            if pkey(e["partition"] for e in []):
                raise AssertionError("unreachable")
            expected_parts={pkey(e["partition"]) for e in own_core}
            if expected_parts!={pkey(e["partition"]) for e in production["outputs"]}:
                raise AssertionError("fresh core/production partition correspondence")
            raw_source=w["reduced"]["forest_trees"][source_index]
            core_addresses=address_clades(raw_source,expansion)
            original_addresses=address_clades(w["original_Tprime"])
            for output in production["outputs"]:
                part=pkey(output["partition"])
                originals=[]
                for address in output["sourceCuts"]:
                    p="".join(map(str,address))
                    group=core_addresses[p]
                    candidates=[(a[:-1],a) for a,lab in original_addresses.items() if a and lab==group]
                    if len(candidates)!=1:
                        raise AssertionError("production original source edge lift not unique")
                    originals.append(candidates[0])
                lifted=map_raw_edges(s,w["original_Tprime"],originals)
                allcuts=hardcuts+lifted
                actual=simultaneous_original_cuts(s,allcuts)
                expected=[p for i,p in enumerate(cl["blocks"]) if i!=source_index]+[frozenset(p) for p in part]
                if actual.partition()!=pkey(expected) or len(lifted)!=len(part)-1:
                    raise AssertionError("production original source partition/payment")
                own_match=[e for e in own_core if e["partition"]==part]
                if len(own_match)!=1 or own_match[0]["charge"]!=len(lifted):
                    raise AssertionError("fresh core true charge correspondence")
                if not partition_af(s,s,actual.partition()):
                    raise AssertionError("original-source cut partition not source valid")
                tidied_t,tidied_s,history=tidy_pair(t,actual)
                author_em=[e for e in vr["emissions"] if e["source"]==source_index and pkey(e["partition"])==part]
                if len(author_em)!=1:
                    raise AssertionError("author emission multiplicity")
                ae=author_em[0]
                ae_expand={int(a):frozenset(x for b in bs for x in expansion[b]) for a,bs in ae["reduced"]["expansion"].items()}
                if tidied_t.forest()!=(expand_tree(ae["reduced"]["T"],ae_expand),):
                    raise AssertionError("actual target tidying mismatch")
                af=tuple(sorted((expand_tree(raw,ae_expand) for raw in ae["reduced"]["forest_trees"]),key=key))
                if tidied_s.forest()!=af:
                    raise AssertionError("actual source tidying mismatch")
                fcl=classification(t,actual)
                if fcl["overlap_pairs"] or sum(not z for z in fcl["homeomorphic"])!=1:
                    raise AssertionError("paid child not disjoint p1")
                full_pretest=pretest(t,actual)
                if full_pretest["solved"]:
                    raise AssertionError("paid child terminal within zero/one")
                engine=Continuation(t,k=12,max_states=20)
                out=engine.run(actual)
                if out["status"]!="COMPLETE" or len(out["tasks"])!=1:
                    raise AssertionError("specified actual disjoint-query continuation")
                task=out["tasks"][0]
                if task["other_parent_loss"]!=0 or task["full_task_charge"]!=len(allcuts) or task["query_budget"]!=12-len(allcuts):
                    raise AssertionError("false own-parent/extra-cut budget credit")
                if any("further_split" in st for st in engine.states):
                    raise AssertionError("unexpected remaining further-SPLIT consumer")
                receipt_rows=[r for r in cuts_receipt["rows"] if r["vertex"]==vr["vertex"] and r["source"]==source_index and pkey(r["expanded_partition"])==actual.partition()]
                if len(receipt_rows)!=1:
                    raise AssertionError("original-cut receipt partition correspondence")
                reported=set(tuple(e) for e in receipt_rows[0]["original_cut_edges"])
                actual_raw=set(raw_edge_for_graph(s,w["original_Tprime"],e) for e in allcuts)
                same_cuts=reported==actual_raw
                if not same_cuts:
                    cut_record_differences.append({"vertex":vr["vertex"],"source":source_index,"partition":actual.partition(),"reported_original_edges":sorted(reported),"actual_production_original_edges":sorted(actual_raw),"same_partition_and_charge":True})
                # Verify the released original-cut receipt too, even if a valid alternate lift.
                reported_graph=map_raw_edges(s,w["original_Tprime"],sorted(reported))
                if simultaneous_original_cuts(s,reported_graph).partition()!=actual.partition():
                    raise AssertionError("released original cut receipt invalid")
                for n in range(len(allcuts)):
                    try:
                        dropped=simultaneous_original_cuts(s,allcuts[:n]+allcuts[n+1:])
                        caught=dropped.partition()!=actual.partition()
                    except ValueError:
                        caught=True
                    if not caught:
                        raise AssertionError("omitted-original-cut plant escaped")
                    mutation_rows.append({"vertex":vr["vertex"],"source":source_index,"type":"omitted_original_cut","cut":allcuts[n],"caught":True})
                try:
                    simultaneous_original_cuts(s,allcuts+[allcuts[-1]])
                    caught=False
                except ValueError:
                    caught=True
                if not caught:
                    raise AssertionError("duplicate original-cut payment plant escaped")
                mutation_rows.append({"vertex":vr["vertex"],"source":source_index,"type":"duplicate_original_cut_charge","caught":True})
                tasks.extend(out["tasks"])
                emissions.append({"source":source_index,"production_call":pname,"production_output":output,"own_core":own_match[0],"regions":regions,"actual_original_source_edges":sorted(actual_raw),"actual_original_graph_cuts":allcuts,"expanded_source_partition":actual.partition(),"source_charge":len(allcuts),"no_leafless_components":True,"tidying":history,"full_original_pretest":full_pretest,"continuation_states":engine.states,"task":task,"reported_exact_cut_records_match":same_cuts})
        vector=[1,1]+[x["full_task_charge"] for x in tasks]
        if sorted(vector)!=[1,1,3,4,4]:
            raise AssertionError("full task vector mismatch")
        D=max(vector);num=sum(100**d*233**(D-d) for d in vector);den=233**D
        if num<=den or str(Fraction(num,den))!=vr["after_one_paid_continuation_full_mass"]:
            raise AssertionError("integer exact mass mismatch")
        core_rows.append({"vertex":vr["vertex"],"actual_graph_vertex":vertex,"emissions":emissions,"full_task_vector":vector,"mass":str(Fraction(num,den)),"integer_numerator":num,"integer_denominator":den,"excess":num-den})
    edge_rows=initial_selectors(w["original_T"],w["original_Tprime"],w["cherry"],12)
    if len(edge_rows)!=2 or any(sorted(x["task_vector"])!=[1,1,3,4,4] for x in edge_rows):
        raise AssertionError("actual shared-edge selectors not all reconstructed")
    result={"verdict":"CONFIRMED specified finite pair-certificate mass failure; exact production-cut lifts retained separately from valid alternate prototype receipt lifts","scope":"same pre-existing independent checker lineage; no new independent replication or global algorithm lower-bound claim","original":admission["original"],"admission":admission,"actual_source_parents":child.partition(),"initial_original_cuts":hardcuts,"actual_shared_vertices":shared_vertices,"actual_shared_edges":shared_edges,"shared_vertex_denominator":3,"shared_edge_denominator":2,"vertex_rows":core_rows,"edge_rows":edge_rows,"production_original_cut_receipt_differences":cut_record_differences,"corruption_checks":mutation_rows,"elapsed_seconds":time.perf_counter()-start,"milestones":{"Algorithm":"OPEN","Correctness":"OPEN","Smaller base":"OPEN"}}
    path=RESULTS/"algorithm-scaffold-adversary-pair14-graph-review-v1.json"
    path.write_text(json.dumps(jsonable(result),separators=(",",":"))+"\n")
    print(json.dumps({"path":str(path),"seconds":result["elapsed_seconds"],"vertices":3,"edges":2,"emissions":sum(len(r["emissions"]) for r in core_rows),"all_vectors":[r["full_task_vector"] for r in core_rows],"mass":core_rows[0]["mass"],"valid_alternate_prototype_cut_records":len(cut_record_differences),"corruption_checks":len(mutation_rows)}))


if __name__=="__main__":
    main()
