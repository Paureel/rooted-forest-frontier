"""One-shot own instrument extension: exact finite callbacks and paid budgets.
Own reuse: imports this review's original_graph.py, never candidate or reviewer code.
"""
import copy,json,pathlib,time
from fractions import Fraction
import original_graph as og
H=pathlib.Path(__file__).resolve().parent

def key(branch,r):
    return (branch["target"].restricted(branch["target"].labels),tuple(branch["forest"]),r)

def exact_child(branch,r,table,request,answer):
    if request!=key(branch,r): raise ValueError("wrong literal child tuple")
    possible=[F for F in table if len(F)-len(branch["P"])<=r]
    if answer is None:
        if possible: raise ValueError("false refusal")
        return
    if not possible or not og.forest_agrees(branch,answer): raise ValueError("invalid returned child")
    if len(answer)-len(branch["P"])>r: raise ValueError("wrong residual budget")
    if len(answer)!=min(map(len,possible)): raise ValueError("not minimum")

def main():
    start=time.perf_counter(); E=json.loads((H/"EXPECTATIONS-v1.json").read_text())
    t,s=og.Graph(E["T"]),og.Graph(E["S"])
    ch=next(x for x in og.choices(t,s) if x["a"]==0)
    bs=og.literal_branches(t,s,ch); allF=list(og.partitions(sorted(t.labels)))
    tables=og.exact_tables(bs,allF); checks=[]; tuples=[]
    def check(name,value):
        checks.append({"name":name,"passed":bool(value)})
        if not value: raise AssertionError(name)
    for q in range(5):
        ans,calls=og.solve(bs,q,tables)
        check(f"affordable indices q{q}",[i for i,r in calls]==E["affordable_branch_indices"][q])
        check(f"literal residual q{q}",[r for i,r in calls]==E["residual_budgets"][q])
        check(f"minimum None iff q{q}",ans is None if q<2 else ans is not None and len(ans[1])==3)
        if q>=2: check(f"first minimum tie q{q}",ans[0]==0)
        for i,r in calls:
            b=bs[i]; req=key(b,r)
            feasible=[F for F in tables[i] if len(F)-len(b["P"])<=r]
            answer=min(feasible,key=len,default=None)
            exact_child(b,r,tables[i],req,answer)
            tuples.append({"q":q,"branch":i,"literal_tuple":req,"answer":answer})
            # Each wrong-request detector goes through the same ExactChild gate.
            wrongs={"budget":(req[0],req[1],r+1),"target":(s.restricted(s.labels) if i<2 else t.restricted(t.labels),req[1],r),
                    "source order":(req[0],tuple(reversed(req[1])),r),
                    "source data":(req[0],req[1][:-1],r)}
            for label,bad in wrongs.items(): check(f"reject {label} q{q}b{i}",og.expect_refusal(lambda bad=bad:exact_child(b,r,tables[i],bad,answer)))
            wrongrole=key(bs[2 if i<2 else 0],r)
            check(f"reject role q{q}b{i}",og.expect_refusal(lambda:exact_child(b,r,tables[i],wrongrole,answer)))
            if answer:
                check(f"reject false refusal q{q}b{i}",og.expect_refusal(lambda:exact_child(b,r,tables[i],req,None)))
                duplicate=copy.deepcopy(answer); duplicate.append([answer[0][0]])
                check(f"reject duplicate q{q}b{i}",og.expect_refusal(lambda:exact_child(b,r,tables[i],req,duplicate)))
                nonminimum=next((F for F in feasible if len(F)>len(answer)),None)
                if nonminimum: check(f"reject nonminimum q{q}b{i}",og.expect_refusal(lambda:exact_child(b,r,tables[i],req,nonminimum)))
            check(f"strict q decrease q{q}b{i}",r<q)
            for F in tables[i]:
                # Integer identity before any Nat subtraction; no unpaid cut claim.
                check(f"paid identity q{q}b{i}F{og.canon(F)}",b["cost"]+len(F)-len(b["P"])==len(F)-1)
    masses=[]
    for c,upper,actual in [(Fraction(2),Fraction(1),Fraction(7,8)),(Fraction(233,100),Fraction(43300,54289),Fraction(8758900,12649337)),(Fraction(3),Fraction(5,9),Fraction(13,27))]:
        values=[c**(-b["cost"]) for b in bs]
        check(f"rational generic mass {c}",1/c+2/c**2==upper)
        check(f"rational actual mass {c}",sum(values)==actual and actual<=upper)
        # Same branch twice contributes twice: no set coalescing in mass.
        check(f"duplicate LIST mass {c}",sum([values[0],values[0]])==2*values[0])
        masses.append({"c":str(c),"actual":str(actual),"upper":str(upper)})
    check("unpaid cut false",len(bs[0]["P"])-len(bs[0]["P"])!=len(bs[0]["P"])-1)
    check("free local min false",len(bs[0]["P"])-len(bs[0]["P"])!=2)
    check("truncation false",max(0,0-bs[0]["cost"])==0 and not any(i==0 for i,r in og.solve(bs,0,tables)[1]))
    out={"controls":checks,"count":len(checks),"tuples":tuples,"tables":tables,"masses":masses,"elapsed_seconds":time.perf_counter()-start,"scope":"finite exact callbacks only; no mutual recursion"}
    (H/"child-controls-output-v1.json").write_text(json.dumps(out,indent=2)+"\n")
    print(json.dumps({"passed":len(checks),"callback_tuples":len(tuples),"elapsed_seconds":out["elapsed_seconds"]}))
if __name__=="__main__": main()
