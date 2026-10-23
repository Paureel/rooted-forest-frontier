"""Postcontact actual readout comparison to frozen independent graph fixtures.
Literal query-list reordering is explicitly postcontact; original expectations stay.
"""
import argparse,collections,copy,json,pathlib,sys,time
from fractions import Fraction
H=pathlib.Path(__file__).resolve().parent;PRE=H.parent
sys.path.insert(0,str(PRE));import original_graph as og
sys.path.insert(0,str(H));from runtime_python import any_residual
def canonF(F):return og.canon(F)
def top(t):
    g=og.Graph(t);return g.restricted(g.labels)
def validate(rows,calls,fixtures):
    checks=[]
    def check(name,value):
        checks.append({"name":name,"passed":bool(value)})
        if not value:raise ValueError(name)
    records={x["fixture"]:x for x in rows if"fixture"in x}
    check("fixture denominator",len(records)==len(fixtures))
    for f in fixtures:
        name=f["name"];row=records[name];check(name+" admitted",row["selected"])
        t,s=og.Graph(f["T"]),og.Graph(f["S"])
        ch=next(c for c in og.choices(t,s)if(c["a"],c["b"],c["c"])==(row["a"],row["b"],row["c"]))
        ib=og.literal_branches(t,s,ch);expectedTables=[]
        check(name+" literal branch denominator",len(row["states"])==3)
        for i,(bstate,b)in enumerate(zip(row["states"],ib)):
            rb=bstate["branch"];g=b["source"];tt=b["target"]
            expectedCuts=[g.address[v]for v in b["heads"]]
            # Actual executable pendantOriginal enumerates original DFS vertices.
            if i==2:expectedCuts=sorted(expectedCuts)
            check(f"{name} b{i} exact original cuts",rb["cuts"]==expectedCuts)
            check(f"{name} b{i} literal roles",rb["target"]==tt.tree and rb["source"]==g.tree and rb["swapped"]==(i==2))
            rr=any_residual(g,[g.by_address[h]for h in expectedCuts])
            ordered=[next(r for r in rr if h in r["vertices"])for h in(*expectedCuts,"")]
            expectedP=[r["labels"]for r in ordered]
            check(f"{name} b{i} actual partition membership/order",[sorted(x)for x in rb["partition"]]==expectedP)
            check(f"{name} b{i} actual source list/order",[top(x)for x in rb["source_forest"]]==[g.restricted(p)for p in expectedP])
            check(f"{name} b{i} paid/proper",rb["cost"]==len(expectedCuts)and len(expectedP)==rb["cost"]+1 and rb["proper"])
            expected=[F for F in f["agreements"]if og.refines(F,b["P"])]
            expectedTables.append(expected)
            check(f"{name} b{i} whole52/203 ForestState table",{canonF(F)for F in bstate["table"]}=={canonF(F)for F in expected})
        check(name+" budget denominator",len(row["budgets"])==5)
        for budget in row["budgets"]:
            q=budget["q"];expectedRequests=[];expectedAnswers=[]
            for i,b in enumerate(ib):
                if b["cost"]>q:continue
                req={"branch":row["states"][i]["branch"],"residual":q-b["cost"]}
                expectedRequests.append(req)
                feasible=[F for F in expectedTables[i]if len(F)-len(b["P"])<=q-b["cost"]]
                if feasible:expectedAnswers.append(min(feasible,key=len))
            check(f"{name} q{q} literal requests",budget["affordable"]==expectedRequests)
            expected=min(expectedAnswers,key=len,default=None)
            check(f"{name} q{q} exact first minimum or None",budget["solveForest"]==expected)
            actualCalls=[c for c in calls if c["fixture"]==name and c["parent_q"]==q]
            normal=[{"branch":c["branch"],"residual":c["residual"]}for c in actualCalls]
            fingerprint=lambda x:json.dumps(x,sort_keys=True)
            check(f"{name} q{q} actual CALL count/tuples",collections.Counter(map(fingerprint,normal))==collections.Counter({fingerprint(r):2 for r in expectedRequests}))
            if expected is None:check(f"{name} q{q} no final recovery output",budget["solveCuts"]is None)
            else:
                rec=budget["solveCuts"];F=rec["partition"]
                rr=any_residual(s,[s.by_address[h]for h in rec["cuts"]])
                check(f"{name} q{q} full originalS output",og.agreement(t,s,F)and len(rec["cuts"])==len(expected)-1 and og.same_partition([r["labels"]for r in rr],F)and len(F)==len(expected))
            for c,actual in zip([Fraction(2),Fraction(233,100),Fraction(3)],budget["masses"]):
                expectedMass=sum((c**(-b["cost"])for b in ib if b["cost"]<=q),Fraction(0))
                check(f"{name} q{q} rational mass{c}",Fraction(actual)==expectedMass and expectedMass<=1/c+2/c**2)
    guards=[r for r in rows if"guard"in r]
    check("actual guard denominator",len(guards)==6)
    for r in guards:check("actual runtime guard "+r["guard"],not r["selected"])
    return checks
def main():
    p=argparse.ArgumentParser();p.add_argument("tag");p.add_argument("--limit",type=int,required=True);a=p.parse_args();start=time.perf_counter()
    rows=[json.loads(l[7:])for l in(H/(a.tag+".stdout")).read_text().splitlines()if l.startswith("RESULT ")]
    calls=[json.loads(l[5:])for l in(H/(a.tag+".stderr")).read_text().splitlines()if l.startswith("CALL ")]
    fixtures=json.loads((PRE/"fixtures-output-v2.json").read_text())["fixtures"][:a.limit]
    checks=validate(rows,calls,fixtures);mutations=[]
    for name in["source-order","target","role","budget","duplicate-call","false-refusal","nonminimum"]:
        bad=copy.deepcopy(rows);bc=copy.deepcopy(calls)
        first=next(r for r in bad if"fixture"in r)
        if name=="source-order":bc[0]["branch"]["source_forest"].reverse()
        if name=="target":bc[0]["branch"]["target"]=bc[0]["branch"]["source"]
        if name=="role":bc[0]["branch"]["swapped"]=not bc[0]["branch"]["swapped"]
        if name=="budget":bc[0]["residual"]+=1
        if name=="duplicate-call":bc.append(copy.deepcopy(bc[0]))
        if name=="false-refusal":first["budgets"][2]["solveForest"]=None
        if name=="nonminimum":first["budgets"][2]["solveForest"]=[[x]for x in sorted(og.Graph(fixtures[0]["T"]).labels)]
        try:validate(bad,bc,fixtures)
        except ValueError as e:mutations.append({"name":name,"caught":str(e)})
        else:raise AssertionError("uncaught runtime comparator mutation "+name)
    out={"passed":len(checks),"checks":checks,"actual_callback_traces":len(calls),"mutations":mutations,"seconds":time.perf_counter()-start,"postcontact_adapter":True}
    (H/(a.tag+"-validation.json")).write_text(json.dumps(out,indent=2)+"\n")
    print(json.dumps({"passed":len(checks),"actual_calls":len(calls),"mutations_caught":len(mutations),"seconds":out["seconds"]}))
if __name__=="__main__":main()
