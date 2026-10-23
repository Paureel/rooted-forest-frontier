import Rule5DispatchExecutionV3

namespace SourceHard2WholeV3
open RMAF Universal233 WholeSourceWork SourceForestV3
open OrdinaryDispatch.Hard2SourceWork OrdinaryDispatch.CompleteSource OrdinaryDispatch.EarlyLocalWork
open SourceCouplingV2 (enabled)

inductive RouteExec (OrdExec : Tree→Tree→Nat→Option F→Prop)
    (T S : Tree) (c : CherryBranching.Candidate) (q : Nat) : Hard2Route→Charged (Option F)→Prop
  | other (execution : SourceHard2NonAdmittedV3.RouteExec OrdExec T S c q route r) :
      RouteExec OrdExec T S c q route r
  | admitted (execution : SourceRule5DispatchV3.DispatchExec OrdExec (.cutoff q) T S c.a c.b q 0 r slots) :
      RouteExec OrdExec T S c q .admittedRule5 (SourceRule5DispatchV3.answerView r)

variable {OrdExec : Tree→Tree→Nat→Option F→Prop} {T S : Tree}

theorem route_source_fields
    (sound : ∀ T S b a,OrdExec T S b a→a=OrdinaryDispatch.FastOrdinary.solve b T S)
    (h : RouteExec OrdExec T S c q route r) :
    r=completeRouteSource (fun _ _ _=>0) T S c q route := by
  cases h with
  | other execution => exact SourceHard2NonAdmittedV3.route_source_fields sound execution
  | admitted execution => exact SourceRule5DispatchV3.admitted_source_fields sound execution

theorem route_exists
    (total : ∀ T S b,enabled (.cutoff q) b=true→∃ a,OrdExec T S b a)
    (T S : Tree) (c : CherryBranching.Candidate) (route : Hard2Route) :
    ∃ r,RouteExec OrdExec T S c q route r := by
  by_cases admitted:route=.admittedRule5
  · subst route
    obtain ⟨r,slots,execution⟩:=SourceRule5DispatchV3.dispatch_exists total T S c.a c.b q 0
    exact ⟨_,RouteExec.admitted execution⟩
  · obtain ⟨r,execution⟩:=SourceHard2NonAdmittedV3.route_exists total T S c route admitted
    exact ⟨_,RouteExec.other execution⟩

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

theorem hard2_exists
    (total : ∀ T S b,enabled (.cutoff q) b=true→∃ a,OrdExec T S b a)
    (T S : Tree) (c : CherryBranching.Candidate) : ∃ r,Hard2Exec OrdExec T S c q r := by
  obtain ⟨r,execution⟩:=route_exists total T S c (hard2FrontMeter T S c q).value
  exact ⟨_,Hard2Exec.run execution⟩

theorem hard2_complete_branch_fields
    (sound : ∀ T S b a,OrdExec T S b a→a=OrdinaryDispatch.FastOrdinary.solve b T S)
    (h : Hard2Exec OrdExec T S c q r) (d : CherryBranching.Candidate) :
    r=completeBranchSource (fun _ _ _=>0) q T S (.hard2 c d) :=
  hard2_source_fields sound h

theorem hard2_local_credit
    (sound : ∀ T S b a,OrdExec T S b a→a=OrdinaryDispatch.FastOrdinary.solve b T S)
    (h : Hard2Exec OrdExec T S c q r)
    (selected : (meterFront q T S).value=.selected (.hard2 c d)) :
    r.work≤completeLocalDebit T S q := by
  have hv:=hard2_complete_branch_fields sound h d
  simp only [completeLocalDebit,ordinaryCompleteStepSource,selected]
  rw [←hv]
  exact Nat.le_add_left _ _
end SourceHard2WholeV3
