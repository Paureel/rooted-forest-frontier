import Rule5CommonDecreaseV3

namespace SourceHard2NonAdmittedV3
open RMAF Universal233 WholeSourceWork SourceForestV3
open OrdinaryDispatch.Hard2SourceWork OrdinaryDispatch.CompleteSource
open SourceCouplingV2 (enabled)

inductive RouteExec (OrdExec : Tree→Tree→Nat→Option F→Prop)
    (T S : Tree) (c : CherryBranching.Candidate) (q : Nat) : Hard2Route→Charged (Option F)→Prop
  | refused : RouteExec OrdExec T S c q .refused ⟨none,0⟩
  | direct (a : Option F) : RouteExec OrdExec T S c q (.direct a) ⟨a,0⟩
  | disjoint (execution : SourceDisjointRunV3.DisjointExec OrdExec (.cutoff q) T S c.a c.b q r calls slots) :
      RouteExec OrdExec T S c q .disjointPaid r
  | paid (execution : SourcePaidUnitsV3.PaidUnitsExec OrdExec (.cutoff q) T S c q out r rec chrono) :
      RouteExec OrdExec T S c q (.paid out) r

variable {OrdExec : Tree→Tree→Nat→Option F→Prop} {T S : Tree}

theorem route_source_fields
    (sound : ∀ T S b a,OrdExec T S b a→a=OrdinaryDispatch.FastOrdinary.solve b T S)
    (h : RouteExec OrdExec T S c q route r) :
    r=completeRouteSource (fun _ _ _=>0) T S c q route := by
  cases h with
  | refused => rfl
  | direct a => rfl
  | disjoint execution =>
    have hv:=SourceDisjointRunV3.disjoint_source_fields
      (base:=fun T S b=>OrdinaryDispatch.FastOrdinary.solve b T S) sound execution
    rw [cutoff_spec] at hv
    exact hv
  | paid execution => exact SourcePaidUnitsV3.paid_units_complete_fields sound execution

theorem route_exists
    (total : ∀ T S b,enabled (.cutoff q) b=true→∃ a,OrdExec T S b a)
    (T S : Tree) (c : CherryBranching.Candidate) (route : Hard2Route) (notAdmitted : route≠.admittedRule5) :
    ∃ r,RouteExec OrdExec T S c q route r := by
  cases route with
  | refused => exact ⟨_,RouteExec.refused⟩
  | direct a => exact ⟨_,RouteExec.direct a⟩
  | admittedRule5 => exact False.elim (notAdmitted rfl)
  | disjointPaid =>
    obtain ⟨r,calls,slots,execution⟩:=SourceDisjointRunV3.disjoint_exists total T S c.a c.b q
    exact ⟨_,RouteExec.disjoint execution⟩
  | paid out =>
    obtain ⟨r,rec,chrono,execution⟩:=SourcePaidUnitsV3.paid_units_exists total T S c q out
    exact ⟨_,RouteExec.paid execution⟩

def finish (T S : Tree) (c : CherryBranching.Candidate) (q : Nat) (r : Charged (Option F)) : Charged (Option F) :=
  ⟨r.value,(hard2FrontMeter T S c q).work+r.work⟩
inductive Hard2Exec (OrdExec : Tree→Tree→Nat→Option F→Prop)
    (T S : Tree) (c : CherryBranching.Candidate) (q : Nat) : Charged (Option F)→Prop
  | run (execution : RouteExec OrdExec T S c q (hard2FrontMeter T S c q).value r) :
      Hard2Exec OrdExec T S c q (finish T S c q r)

theorem hard2_source_fields
    (sound : ∀ T S b a,OrdExec T S b a→a=OrdinaryDispatch.FastOrdinary.solve b T S)
    (h : Hard2Exec OrdExec T S c q r) :
    r=hard2CompleteSource (fun _ _ _=>0) T S c q := by
  cases h with
  | run execution =>
    have hv:=route_source_fields sound execution
    simp only [finish,hard2CompleteSource,hv]
end SourceHard2NonAdmittedV3
