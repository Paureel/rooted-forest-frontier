"""Reconstruct the original uncontracted forest and package a compact witness."""
from scaffold import *


def main():
    here=Path(__file__).parent
    results=here.parents[1]/"results"
    pilot=json.loads((results/"algorithm-scaffold-adversary-pilot-v1.json").read_text())
    row=next(r for r in pilot["cases"] if r["case"]=="graft-0-flip-0")
    t=Graph(tree(row["original"]["T"]))
    original_s=Graph(tree(row["original"]["Tprime"]))
    hardset=frozenset(range(10,16))
    repeated=[]
    boundaries=[]
    # Integer arithmetic independent of Fraction mass() implementation.
    for b in row["boundaries"]:
        charges=[]
        branches=[]
        for branch in b["branches"]:
            emissions=[]
            for em in branch["emissions"]:
                s=original_s.clone()
                for e in em["actual_whole_source_cuts"]:
                    s.cut_original(tuple(e))
                if len(set(s.cut_history))!=2+em["charge"]:
                    raise AssertionError("distinct original-cut charge")
                pre=pretest(t,s)
                if pre["solved"]:
                    raise AssertionError("uncontracted original forest solved within one cut")
                # Every attempt must have used a different live original source edge.
                if len(pre["attempts"])!=1+len(s.lift):
                    raise AssertionError("incomplete one-cut enumeration")
                target_hard=restriction(t,hardset)
                source_hard=restriction(s,hardset)
                signature=json.dumps(jsonable((target_hard,source_hard)),sort_keys=True)
                repeated.append(signature)
                charges.append(2+em["charge"])
                emissions.append({"partition":em["partition"],"core_cuts":em["cuts"],"core_charge":em["charge"],"all_original_source_cuts":s.cut_history,"full_source_partition":s.partition(),"core_history":em["history"],"tidying":em["post_tidy"],"tidied_pretest":em["pretest"],"uncontracted_pretest":pre,"hard_restriction_signature":hashlib.sha256(signature.encode()).hexdigest()})
            branches.append({"source_index":branch["source_index"],"colors":branch["colors"],"emissions":emissions})
        # Full charges include original endpoint branches, hence [1,1].
        exponents=[1,1]+charges
        D=max(exponents)
        den=233**D
        num=sum(100**d*233**(D-d) for d in exponents)
        remainder=num-den
        if remainder<=0:
            raise AssertionError("integer excess did not fire")
        reduced=Fraction(num,den)
        if str(reduced)!=b["remaining_full_mass"]:
            raise AssertionError("mass recomposition")
        boundaries.append({"target_edge":b["target_edge"],"target_side":b["target_side"],"branches":branches,"full_charges":exponents,"full_mass":str(reduced),"integer_comparison":{"common_exponent":D,"numerator":num,"denominator":den,"excess":remainder},"passes":False})
    endpoint_rows=[]
    for a in [8,9]:
        s=original_s.clone()
        v=next(v for v,q in s.group.items() if q==leaf(a))
        cut=s.cut((s.parent()[v],v))
        pp=pretest(t,s)
        if pp["solved"]:
            raise AssertionError("endpoint q<=1 unexpectedly succeeds")
        endpoint_rows.append({"endpoint":a,"actual_cut":cut,"pretest":pp})
    result={"scope":"Executed finite H1/H2 counterexample to frozen normal colored-core sufficient mass certificate at c=233/100, with both original unit endpoint branches unchanged. Algorithm/Correctness/Smaller base OPEN.","source_receipt":"algorithm-scaffold-adversary-pilot-v1.json","frozen_rule":"PRECONTACT-FREEZE.sha256 and WORKFILE.md deterministic tie-break","original":row["original"],"selected_cherry":row["selected_cherry"],"actual_pendants":row["actual_pendants"],"admission_both_orientations":row["admission_both_orientations"],"initial_tidying":row["tidying"],"classification":row["classification"],"rules67":row["rules67"],"all_overlap_boundaries":boundaries,"H1":"FIRE","H2":"FIRE","boundary_denominator":len(boundaries),"emission_denominator":len(repeated),"repeated_hard_residuals":{"occurrences":len(repeated),"distinct_signatures":len(set(repeated)),"target_source_restrictions":json.loads(repeated[0]),"interpretation":"identical induced hard tree pair survives every emitted forest; no cache or speed claim"},"endpoint_pretests":endpoint_rows,"controls":{"precontact":"controls-run-20261015T064808Z.json","postcontact_source":"source-controls-v1.json"},"limitations":["Exact computation independently falsifies the frozen source-core rule/certificate only; no lower bound on other covers or rMAF algorithms.","Different homogeneous contraction/mixed-cherry/unique-group tie-breaks were not universally quantified.","The graft's one-cut endpoint pretests also refuse, but deeper endpoint algorithms or different decompositions could change the overall recurrence.","No full formal proof or second nonauthor reconstruction has been performed by this adversarial arm."]}
    dest=results/"algorithm-scaffold-adversary-H2-witness-v1.json"
    dest.write_text(json.dumps(jsonable(result),separators=(",",":"))+"\n")
    print(json.dumps({"path":str(dest),"bytes":dest.stat().st_size,"boundaries":len(boundaries),"emissions":len(repeated),"hard_residual_distinct":len(set(repeated)),"masses":[b["full_mass"] for b in boundaries],"H1":"FIRE","H2":"FIRE"}))


if __name__=="__main__":
    main()
