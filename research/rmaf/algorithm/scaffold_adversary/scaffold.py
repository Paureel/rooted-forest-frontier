"""Post-freeze source guard adapter from original Figure 16 definitions only.

No production evaluator imports. Graph/core arithmetic is the precontact engine.
"""
from fresh_graph import *
from pathlib import Path


def cherries(g):
    return sorted((tuple(sorted((g.group[w] for w in cs),key=lambda s:tuple(sorted(s)))) for v,cs in g.ch.items() if len(cs)==2 and all(w in g.group for w in cs)),key=lambda z:tuple(tuple(sorted(x)) for x in z))


def path(g,a,b):
    pa=g.parent()
    va=next(v for v,s in g.group.items() if s==a)
    vb=next(v for v,s in g.group.items() if s==b)
    aa=[va]
    bb=[vb]
    while aa[-1] in pa:
        aa.append(pa[aa[-1]])
    while bb[-1] in pa:
        bb.append(pa[bb[-1]])
    common=set(aa)&set(bb)
    if not common:
        return []
    lca=next(v for v in aa if v in common)
    return aa[:aa.index(lca)+1]+list(reversed(bb[:bb.index(lca)]))


def pendants(g,a,b):
    pp=path(g,a,b)
    on=set(pp)
    return [{"edge":(v,w),"labels":g.labs(w)} for v in pp for w in g.ch[v] if w not in on]


def edges_span(g,p):
    sp=span(g,p)
    return frozenset(e for e in g.lift if e[0] in sp and e[1] in sp)


def classification(t,s):
    roots=sorted(s.roots,key=lambda v:tuple(sorted(s.labs(v))))
    blocks=[s.labs(r) for r in roots]
    spans=[span(t,p) for p in blocks]
    overlaps=[(i,j) for i,j in combinations(range(len(blocks)),2) if spans[i]&spans[j]]
    return {"blocks":blocks,"homeomorphic":[restriction(t,p)==s.nested(r) for p,r in zip(blocks,roots)],"overlap_pairs":overlaps,"isolated":[i for i in range(len(blocks)) if all(i not in e for e in overlaps)],"roots":roots}


def source_admission(t,s):
    shared=set(cherries(t))&set(cherries(s))
    rows=[]
    for a,b in cherries(t):
        ps=pendants(s,a,b)
        n=len(ps)
        rule4=any(len(p["labels"])==1 and any({p["labels"],endpoint}==set(cherry) for cherry in cherries(s) for endpoint in (a,b)) for p in ps)
        st=s.clone()
        for p in ps:
            st.cut_original(min(s.lift[p["edge"]]))
        cl=classification(t,st)
        rule5=(n==2 and not cl["overlap_pairs"] and sum(cl["homeomorphic"])>=2)
        rows.append({"cherry":[sorted(a),sorted(b)],"pendants":ps,"t":n,"step2a":n==1,"step2b":n>=3,"step2c":n==2 and rule4,"step2d":rule5,"two_cut_classification":cl})
    return {"common_cherries":shared,"rows":rows,"excluded_2a_to_2d":not shared and not any(any(r[k] for k in ("step2a","step2b","step2c","step2d")) for r in rows)}


def drop_group(g,group):
    v=next(v for v,s in g.group.items() if s==group)
    pa=g.parent()
    if v in pa:
        p=pa[v]
        g.ch[p].remove(v)
        g.lift.pop((p,v))
    else:
        g.roots.remove(v)
    g.ch.pop(v)
    g.group.pop(v)
    g.tidy()


def tidy_pair(t,s):
    t=t.clone()
    s=s.clone()
    actions=[]
    closed=[]
    while True:
        singles=[r for r in s.roots if r in s.group]
        if singles:
            r=min(singles,key=lambda r:tuple(sorted(s.group[r])))
            group=s.group[r]
            drop_group(t,group)
            drop_group(s,group)
            closed.append(group)
            actions.append({"op":"delete_singleton_component","labels":sorted(group)})
            continue
        common=set(cherries(t))&set(cherries(s))
        if common:
            a,b=min(common,key=lambda z:tuple(tuple(sorted(q)) for q in z))
            for g in (t,s):
                v=next(v for v,cs in g.ch.items() if len(cs)==2 and all(w in g.group for w in cs) and {g.group[w] for w in cs}=={a,b})
                g.contract(v)
            actions.append({"op":"contract_common_cherry","groups":[sorted(a),sorted(b)],"expanded_labels":sorted(a|b)})
            continue
        break
    return t,s,{"actions":actions,"closed_components":closed,"target":t.forest(),"source":s.forest(),"source_cut_history":s.cut_history,"target_tidy_history":t.tidy_history,"source_tidy_history":s.tidy_history}


def rules67(t,s,cl):
    blocks=cl["blocks"]
    overlap=cl["overlap_pairs"]
    homes=cl["homeomorphic"]
    rule6=[]
    if len(blocks)==3 and sum(homes)==2 and len(overlap)==1:
        i,j=overlap[0]
        k=next(k for k in range(3) if k not in (i,j))
        es=edges_span(t,blocks[i])&edges_span(t,blocks[j])
        if homes[k] and homes[i]!=homes[j] and len(es)==1:
            rule6.append({"overlap":(i,j),"edge":next(iter(es))})
    rule7=[]
    for n in range(2,len(blocks)+1):
        for inds in combinations(range(len(blocks)),n):
            inds=set(inds)
            if all(homes[i] for i in inds) and not any((i in inds)!=(j in inds) for i,j in overlap):
                rule7.append({"subset":sorted(inds),"requires_cut":any(i in inds and j in inds for i,j in overlap)})
    return {"rule6":rule6,"rule7":rule7,"excluded":not rule6 and not any(r["requires_cut"] for r in rule7)}


def component_graph(s,root):
    z=s.clone()
    for r in list(z.roots):
        if r!=root:
            z.remove_component(r)
    return z


def evaluate(t_nested,s_nested,selected=(8,9),include_boundaries=True):
    t=Graph(tree(t_nested))
    s=Graph(tree(s_nested))
    labs_t=frozenset().union(*t.group.values())
    labs_s=frozenset().union(*s.group.values())
    original={"T":t_nested,"Tprime":s_nested,"labels":sorted(labs_t),"n":len(labs_t),"target_graph":{"children":t.ch,"groups":t.group,"original_edges":t.original_edges},"source_graph":{"children":s.ch,"groups":s.group,"original_edges":s.original_edges},"binary":True,"distinct_common_labels":labs_t==labs_s and sum(map(len,t.group.values()))==len(labs_t) and sum(map(len,s.group.values()))==len(labs_s),"no_rho":all(isinstance(a,int) for a in labs_t|labs_s)}
    if labs_t!=labs_s or sum(map(len,t.group.values()))!=len(labs_t) or sum(map(len,s.group.values()))!=len(labs_s):
        return {"original":original,"eligible":False,"failure":"distinct_common_labels"}
    admissions=[source_admission(t,s),source_admission(s,t)]
    a,b=map(leaf,selected)
    ps=pendants(s,a,b)
    failures=[]
    if not all(z["excluded_2a_to_2d"] for z in admissions):
        failures.append("earlier_Figure16_rule")
    if not original["no_rho"]:
        failures.append("noninteger_or_rho_label")
    if (a,b) not in cherries(t) and (b,a) not in cherries(t):
        failures.append("selected_not_target_cherry")
    if len(ps)!=2:
        failures.append("selected_not_exactly_two_pendants")
    result={"original":original,"admission_both_orientations":admissions,"selected_cherry":selected,"actual_pendants":ps,"eligible":False,"failures":failures}
    if failures:
        return result
    source=s.clone()
    for p in ps:
        source.cut_original(min(s.lift[p["edge"]]))
    expected_parts=pkey([p["labels"] for p in ps]+[labs_s-frozenset().union(*(p["labels"] for p in ps))])
    if source.partition()!=expected_parts:
        raise AssertionError("actual pendant source cuts differ from actual pendant groups")
    tt,ss,tidy=tidy_pair(t,source)
    cl=classification(tt,ss)
    r67=rules67(tt,ss,cl)
    if len(cl["blocks"])!=3 or len(cl["overlap_pairs"])!=1:
        failures.append("not_three_parent_single_overlap")
    if not any(cl["homeomorphic"][i] for i in cl["isolated"]):
        failures.append("no_isolated_homeomorphic_third")
    if not r67["excluded"]:
        failures.append("source_rule6_or_7")
    result.update({"tidying":tidy,"classification":cl,"rules67":r67,"eligible":not failures,"failures":failures})
    if failures or not include_boundaries:
        return result
    i,j=cl["overlap_pairs"][0]
    boundary_edges=sorted(edges_span(tt,cl["blocks"][i])&edges_span(tt,cl["blocks"][j]))
    result["boundaries"]=[]
    c=Fraction(233,100)
    for e in boundary_edges:
        side=tt.labs(e[1])
        branches=[]
        for idx in (i,j):
            root=cl["roots"][idx]
            sg=component_graph(ss,root)
            colors={a:int(a in side) for a in sg.labs(root)}
            emissions=colored_core(sg,colors)
            for em in emissions:
                actual=ss.clone()
                before=len(actual.cut_history)
                for cut in em["cuts"]:
                    actual.cut_original(cut)
                if len(actual.cut_history)-before!=em["charge"]:
                    raise AssertionError("whole forest charge")
                t2,s2,history=tidy_pair(tt,actual)
                depth=pretest(t2,s2)
                em["actual_whole_source_cuts"]=actual.cut_history
                em["post_tidy"]=history
                em["pretest"]=depth
                em["remaining_source_forest"]=s2.forest()
                em["remaining_target"]=t2.forest()
            branches.append({"source_index":idx,"colors":colors,"emissions":emissions,"raw_core_mass":mass([em["charge"] for em in emissions]),"remaining_core_mass":mass([em["charge"] for em in emissions if not em["pretest"]["solved"]])})
        raw=2/c+sum((z["raw_core_mass"] for z in branches),Fraction())/c**2
        remaining=2/c+sum((z["remaining_core_mass"] for z in branches),Fraction())/c**2
        result["boundaries"].append({"target_edge":e,"target_side":side,"branches":branches,"raw_full_mass":raw,"remaining_full_mass":remaining,"pass":remaining<=1})
    result["H1_fire"]=any(not b["pass"] for b in result["boundaries"])
    result["H2_fire"]=bool(result["boundaries"]) and all(not b["pass"] for b in result["boundaries"])
    return result


def graft(t,at,replacement):
    if isinstance(t,int):
        return replacement if t==at else t
    return [graft(z,at,replacement) for z in t]


def relabel(t,offset=10):
    if isinstance(t,int):
        return t+offset
    return [relabel(z,offset) for z in t]


def save(path,obj):
    Path(path).write_text(json.dumps(jsonable(obj),indent=2)+"\n")
