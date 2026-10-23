"""Bounded graft pilot. Literal data are declared development contacts."""
from scaffold import *
import argparse

ROOT=Path(__file__).resolve().parents[2]
HERE=Path(__file__).resolve().parent


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument("--mode",choices=["pilot","extend"],default="pilot")
    args=ap.parse_args()
    fixtures=json.loads((HERE/"literal-inputs.json").read_text())
    T=fixtures["base"]["T"]
    S=fixtures["base"]["Tprime"]
    hard=fixtures["hard"]
    cases=[("base",T,S)]
    locations=[0] if args.mode=="pilot" else [1,2,3,4,5,6]
    for location in locations:
        for flip in [False,True]:
            ht,hs=(hard["Tprime"],hard["T"]) if flip else (hard["T"],hard["Tprime"])
            cases.append((f"graft-{location}-flip-{int(flip)}",graft(T,location,relabel(ht)),graft(S,location,relabel(hs))))
    result={"mode":args.mode,"cases":[],"started_utc":time.strftime("%Y-%m-%dT%H:%M:%SZ",time.gmtime()),"scope":"finite independent falsification of frozen colored-core tie-break; no algorithm lower bound"}
    for name,t,s in cases:
        start=time.perf_counter()
        row=evaluate(t,s)
        row["case"]=name
        row["elapsed_seconds"]=time.perf_counter()-start
        result["cases"].append(row)
        save(HERE/f"{args.mode}-progress.json",result)
        print(json.dumps({"case":name,"seconds":row["elapsed_seconds"],"eligible":row["eligible"],"failures":row.get("failures"),"boundaries":[{"edge":b["target_edge"],"raw":str(b["raw_full_mass"]),"remaining":str(b["remaining_full_mass"])} for b in row.get("boundaries",[])],"H1_fire":row.get("H1_fire"),"H2_fire":row.get("H2_fire")} ),flush=True)
    result["completed"]=len(result["cases"])
    save(ROOT/"results"/f"algorithm-scaffold-adversary-{args.mode}-v1.json",result)


if __name__=="__main__":
    main()
