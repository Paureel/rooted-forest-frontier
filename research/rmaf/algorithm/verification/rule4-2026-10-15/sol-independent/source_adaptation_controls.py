"""One-shot actual copied-source pin controls; own checker reuse only.

Expected: exact copied CleanA passes; changed comment/import/type/body bytes fail
SOURCE_PIN_MISMATCH before any module may be accepted as an exact-source replay.
Written pre-candidate. No scientific module is opened or copied.
"""
import hashlib,json,pathlib,time
import producer_controls as pc
H=pathlib.Path(__file__).resolve().parent
def main():
    start=time.perf_counter(); src=(pc.C/"SolCleanA.lean").read_text()
    expected=hashlib.sha256(src.encode()).hexdigest(); record=json.loads((H/"battery-clean-AB.json").read_text())
    out=[]; dest=H/"adaptation-controls";dest.mkdir(exist_ok=True)
    for tag,contents in [("clean",src),("source",src+"\n-- changed exact source\n"),
                         ("import",src.replace("import Std","import Lean")),
                         ("type",src.replace("token : True","token : True ∧ True")),
                         ("body",src.replace("True.intro","by trivial"))]:
        p=dest/(tag+".lean");p.write_text(contents); error=None
        try:pc.validate(record,{str(p):expected})
        except ValueError as e:error=str(e)
        good=(error is None) if tag=="clean" else error=="SOURCE_PIN_MISMATCH"
        out.append({"tag":tag,"path":str(p),"expected":expected,"actual":pc.digest(p),"detector":error,"passed":good})
        if not good:raise AssertionError(tag)
    result={"checks":out,"count":len(out),"elapsed_seconds":time.perf_counter()-start,"candidate_contact":False}
    (H/"source-adaptation-results-v1.json").write_text(json.dumps(result,indent=2)+"\n")
    print(json.dumps({"passed":len(out),"elapsed_seconds":result["elapsed_seconds"]}))
if __name__=="__main__":main()
