"""Coupled finite continuation using the previously frozen independent lineage.

Fitch completion is polynomial dynamic programming. Any bounded exact search is
in controls.py only. Source cut costs always refer to original uncontracted trees.
"""
import sys
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parent.parent))
from scaffold import *


def connected_groups(cl):
    unseen=set(range(len(cl["blocks"])))
    ans=[]
    while unseen:
        seed=min(unseen)
        found={seed}
        pending=[seed]
        while pending:
            i=pending.pop()
            for a,b in cl["overlap_pairs"]:
                if a==i and b not in found:
                    found.add(b);pending.append(b)
                if b==i and a not in found:
                    found.add(a);pending.append(a)
        unseen-=found
        ans.append(sorted(found))
    return ans


def fitch(g,colors):
    """Minimum unit color-change assignment; polynomial O(n*r^2)."""
    if len(g.roots)!=1:
        raise ValueError("one connected tree required")
    states=sorted(set(colors.values()))
    dp={}
    INF=len(g.ch)+1
    def bottom(v):
        if v in g.group:
            fixed={colors[a] for a in g.group[v]}
            if len(fixed)!=1:
                raise ValueError("a contracted group crosses fixed colors")
            only=next(iter(fixed))
            dp[v]={c:(0 if c==only else INF) for c in states}
            return
        for w in g.ch[v]:
            bottom(w)
        dp[v]={c:sum(min(dp[w][d]+int(c!=d) for d in states) for w in g.ch[v]) for c in states}
    root=next(iter(g.roots))
    bottom(root)
    assignment={root:min(states,key=lambda c:(dp[root][c],c))}
    def top(v):
        for w in g.ch[v]:
            p=assignment[v]
            assignment[w]=min(states,key=lambda c:(dp[w][c]+int(c!=p),int(c!=p),c))
            top(w)
    top(root)
    cuts=[e for e in sorted(g.lift) if assignment[e[0]]!=assignment[e[1]]]
    score=dp[root][assignment[root]]
    if score!=len(cuts):
        raise AssertionError("Fitch edge score")
    work=g.clone()
    actual=[]
    for e in cuts:
        actual.append(work.cut_original(min(g.lift[e])))
    if len(work.partition())!=score+1:
        raise AssertionError("Fitch has an empty unlabeled piece")
    return {"score":score,"assignment":assignment,"original_cuts":actual,"partition":work.partition()}


def good_completion(t,s,indices,cl):
    if not all(cl["homeomorphic"][i] for i in indices):
        raise ValueError("Fitch group has a bad parent")
    blocks=[cl["blocks"][i] for i in indices]
    labset=frozenset().union(*blocks)
    target=Graph(restriction(t,labset))
    color={a:i for i,p in enumerate(blocks) for a in p}
    tf=fitch(target,color)
    piece_colors={a:i for i,p in enumerate(tf["partition"]) for a in p}
    actual=[]
    source_witnesses=[]
    for idx in indices:
        local=component_graph(s,cl["roots"][idx])
        sf=fitch(local,{a:piece_colors[a] for a in cl["blocks"][idx]})
        actual.extend(sf["original_cuts"])
        source_witnesses.append(sf)
    expected=tf["score"]+1-len(indices)
    if expected<0 or len(set(actual))!=expected:
        raise AssertionError(("Fitch additional source charge",expected,actual))
    rebuilt=s.clone()
    for e in actual:
        rebuilt.cut_original(e)
    parts=[rebuilt.labs(r) for r in rebuilt.roots if rebuilt.labs(r)<=labset]
    if pkey(parts)!=tf["partition"]:
        raise AssertionError("Fitch source realization partition")
    group_source=rebuilt.clone()
    for r in list(group_source.roots):
        if not group_source.labs(r)<=labset:
            group_source.remove_component(r)
    if not partition_af(Graph(restriction(t,labset)),group_source,parts):
        raise AssertionError("Fitch group is not a whole agreement forest")
    return {"indices":indices,"labels":labset,"source_component_count":len(indices),"target_fitch":tf,"source_piece_coloring":source_witnesses,"additional_source_cuts":actual,"cost":expected,"whole_group_terminal":True,"partition":pkey(parts)}


def typed_queries(q,solved_cost,unresolved):
    if type(q) is not int or q<0 or type(solved_cost) is not int or solved_cost<0:
        raise ValueError("nonnegative integer q and source solved-cut cost required")
    if any(type(z) is not int or z!=2 for z in unresolved):
        raise ValueError("only genuinely zero/one-refused ell=2 enters recursive queries")
    return [{"index":i,"other_loss":sum(unresolved)-ell,"solved_cost":solved_cost,"query_budget":q-solved_cost-(sum(unresolved)-ell),"task_additional_charge":solved_cost+sum(unresolved)-ell} for i,ell in enumerate(unresolved)]


def check_task_claim(q,solved_cost,ells,charges,multiplicity):
    tasks=typed_queries(q,solved_cost,ells)
    return len(tasks)==multiplicity and [r["task_additional_charge"] for r in tasks]==charges


def local_test(t,s,root):
    labs=s.labs(root)
    target=Graph(restriction(t,labs))
    source=component_graph(s,root)
    pp=pretest(target,source)
    ell=pp["q"] if pp["solved"] else 2
    if type(ell) is not int or ell not in (0,1,2):
        raise AssertionError("ill-typed local lower bound")
    signature=json.dumps(jsonable((target.forest(),source.forest())),sort_keys=True)
    return {"root":root,"labels":labs,"ell":ell,"pretest":pp,"target":target.forest(),"source":source.forest(),"signature":hashlib.sha256(signature.encode()).hexdigest()}


class Continuation:
    def __init__(self,t,k=12,max_states=200):
        if type(k) is not int or k<0:
            raise ValueError("typed initial cut budget required")
        self.t=t
        self.k=k
        self.max_states=max_states
        self.states=[]

    def run(self,s,selector_path=()):
        if len(self.states)>=self.max_states:
            return {"status":"OPEN","consumer":"bounded pilot state cap","path":selector_path,"tasks":[]}
        s=s.clone()
        cl=classification(self.t,s)
        groups=connected_groups(cl)
        record={"id":len(self.states),"path":selector_path,"source_cuts_before":list(s.cut_history),"source_partition_before":s.partition(),"classification":cl,"overlap_groups":groups,"solved_good_groups":[]}
        self.states.append(record)
        for inds in groups:
            if all(cl["homeomorphic"][i] for i in inds):
                comp=good_completion(self.t,s,inds,cl)
                record["solved_good_groups"].append(comp)
                for e in comp["additional_source_cuts"]:
                    s.cut_original(e)
        cl=classification(self.t,s)
        groups=connected_groups(cl)
        bad_overlap=[inds for inds in groups if len(inds)>1 and any(not cl["homeomorphic"][i] for i in inds)]
        record["post_good_source_cuts"]=list(s.cut_history)
        record["post_good_partition"]=s.partition()
        if bad_overlap:
            # Actual continuation: least original target edge, then component pair.
            choices=[]
            for inds in bad_overlap:
                for i,j in combinations(inds,2):
                    if (i,j) not in cl["overlap_pairs"]:
                        continue
                    for e in edges_span(self.t,cl["blocks"][i])&edges_span(self.t,cl["blocks"][j]):
                        choices.append((e,i,j))
            if not choices:
                record["status"]="OPEN"
                return {"status":"OPEN","consumer":"bad overlap without a shared edge","state":record["id"],"tasks":[]}
            e,i,j=min(choices)
            record["further_split"]={"all_actual_choices":choices,"selected_target_edge":e,"pair":(i,j),"branches":[]}
            descendants=[]
            for idx in (i,j):
                root=cl["roots"][idx]
                side=self.t.labs(e[1])
                source=component_graph(s,root)
                core=colored_core(source,{a:int(a in side) for a in cl["blocks"][idx]})
                for n,em in enumerate(core):
                    child=s.clone()
                    before=len(set(child.cut_history))
                    for cut in em["cuts"]:
                        child.cut_original(cut)
                    if len(set(child.cut_history))-before!=em["charge"]:
                        raise AssertionError("further SPLIT actual charge")
                    branch={"source_index":idx,"core":em,"source_cuts_after":list(child.cut_history)}
                    record["further_split"]["branches"].append(branch)
                    if len(set(child.cut_history))>self.k:
                        branch["budget_pruned"]=True
                        continue
                    result=self.run(child,selector_path+((record["id"],idx,n),))
                    descendants.append(result)
            record["status"]="SPLIT"
            if any(z["status"]=="OPEN" for z in descendants):
                return {"status":"OPEN","consumer":"descendant remains unsupported","tasks":[t for z in descendants for t in z.get("tasks",[])]}
            return {"status":"COMPLETE","tasks":[t for z in descendants for t in z["tasks"]]}
        if cl["overlap_pairs"]:
            raise AssertionError("an unresolved overlap was silently treated as disjoint")
        # Exact disjoint-query step; known local solutions become actual source cuts.
        locals_=[local_test(self.t,s,r) for r in cl["roots"]]
        record["local_depth01"]=locals_
        unresolved=[r for r in locals_ if r["ell"]==2]
        for local in locals_:
            if local["ell"]==1:
                for cut in local["pretest"]["witness"]:
                    s.cut_original(tuple(cut))
        actual_charge=len(set(s.cut_history))
        tasks=[]
        queries=typed_queries(self.k-actual_charge,0,[r["ell"] for r in unresolved])
        for query,local in zip(queries,unresolved):
            charge=actual_charge+query["other_loss"]
            tasks.append({"state":record["id"],"labels":local["labels"],"target":local["target"],"source":local["source"],"signature":local["signature"],"actual_source_cuts":list(s.cut_history),"actual_source_cut_charge":actual_charge,"all_unresolved_ells":[r["ell"] for r in unresolved],"other_parent_loss":query["other_loss"],"full_task_charge":charge,"original_budget":self.k,"query_budget":query["query_budget"],"budget_pruned":query["query_budget"]<0})
        record["source_cuts_after_local_solutions"]=list(s.cut_history)
        record["tasks"]=tasks
        record["status"]="DISJOINT_QUERY" if tasks else "POLYNOMIAL_TERMINAL"
        return {"status":"COMPLETE","tasks":[z for z in tasks if not z["budget_pruned"]]}


def initial_selectors(t_nested,s_nested,selected,k=12):
    t=Graph(tree(t_nested))
    s=Graph(tree(s_nested))
    a,b=map(leaf,selected)
    ps=pendants(s,a,b)
    if len(ps)!=2:
        raise AssertionError("selected child must have exactly two actual pendants")
    child=s.clone()
    for p in ps:
        child.cut_original(min(s.lift[p["edge"]]))
    cl=classification(t,child)
    choices=sorted(set(e for i,j in cl["overlap_pairs"] for e in edges_span(t,cl["blocks"][i])&edges_span(t,cl["blocks"][j])))
    results=[]
    for edge in choices:
        engine=Continuation(t,k=k)
        side=t.labs(edge[1])
        pairs=[(i,j) for i,j in cl["overlap_pairs"] if edge in edges_span(t,cl["blocks"][i])&edges_span(t,cl["blocks"][j])]
        i,j=min(pairs)
        emissions=[]
        tasks=[]
        for idx in (i,j):
            root=cl["roots"][idx]
            source=component_graph(child,root)
            core=colored_core(source,{a:int(a in side) for a in cl["blocks"][idx]})
            for n,em in enumerate(core):
                current=child.clone()
                for cut in em["cuts"]:
                    current.cut_original(cut)
                out=engine.run(current,(("initial",idx,n),))
                emissions.append({"source_index":idx,"core":em,"uncontracted_pretest":pretest(t,current),"continuation_status":out["status"],"recursive_tasks":out["tasks"]})
                tasks.extend(out["tasks"])
        if any(e["continuation_status"]!="COMPLETE" for e in emissions):
            status="OPEN"
            full_mass=None
            vector=None
        else:
            status="COMPLETE"
            vector=[1,1]+[t["full_task_charge"] for t in tasks]
            full_mass=mass(vector)
        raw=[1,1]+[2+e["core"]["charge"] for e in emissions]
        preonly=[1,1]+[2+e["core"]["charge"] for e in emissions if not e["uncontracted_pretest"]["solved"]]
        results.append({"target_edge":edge,"target_side":side,"pair":(i,j),"status":status,"initial_actual_pendant_cuts":child.cut_history,"original_budget":k,"raw_vector":raw,"raw_mass":mass(raw),"pretest_only_vector":preonly,"pretest_only_mass":mass(preonly),"task_vector":vector,"task_mass":full_mass,"passes":None if full_mass is None else full_mass<=1,"emissions":emissions,"states":engine.states})
    return results
