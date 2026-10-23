import PendantCutMetadataV3
import Rule4BijectionV3

namespace SourceRule4ValuesV3
open RMAF Universal233 OrdinaryDispatch.FullSourceWork
open SourcePendantValuesV3

theorem branches_value {T S : Tree} (s : Rule4.Choice T S) :
    (rule4BranchesMeter s).value=Rule4.branches s := by
  simp only [rule4BranchesMeter,Rule4.branches,Rule4.aHead,leafAddress_value,cuts_value]

end SourceRule4ValuesV3

namespace SourceRule4V3
open RMAF Universal233 WholeSourceWork CoreWork
open GenericForest GenericForest.FrontierWork GenericForest.CheckCorrespondence
open OrdinaryDispatch.FullSourceWork OrdinaryDispatch.WorkRecursion
open OrdinaryDispatch.WorkIntegration Universal233.Rule5SelectedLocalWork
open SourceForestV3 SourceCouplingV2 SourceRule4ValuesV3 SourceLocalValuesV3
open SourceDisjointV2 (ordinarySpec)

variable {OrdExec : Tree→Tree→Nat→Option F→Prop} {mode : Mode}
  {base : Tree→Tree→Nat→Option F}

theorem answers_raw_value
    (sound : ∀ T S b a,OrdExec T S b a→a=base T S b)
    (h : AnswersExec OrdExec mode q i bs r cells) :
    r.value=bs.flatMap (fun b=>Rule4.childOutputs b q (OrdinaryDispatch.rule4Child (ordinarySpec mode base))) := by
  induction h with
  | nil => rfl
  | refused tail over ih =>
    simpa only [List.flatMap_cons,Rule4.childOutputs,over,↓reduceIte,List.nil_append] using ih
  | returned tail paid execution ih =>
    have hv:=(forest_correspondence sound _ _ _ _ _ execution).1
    rw [state_value] at hv
    simp only [Rule4.childOutputs,OrdinaryDispatch.rule4Child] at ih
    simp only [List.flatMap_cons,Rule4.childOutputs,paid,↓reduceIte,OrdinaryDispatch.rule4Child,←hv,←ih]

theorem meteredQueries_raw (actual : GenericForest.FrontierWork.Ordinary) (q : Nat)
    (bs : List Rule4.Branch) :
    meteredQueries actual q bs=forestQueries actual
      (affordableCalls bs Rule4.Branch.target Rule4.Branch.sourceForest Rule4.Branch.cost q) := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    simp only [meteredQueries,affordableCalls,forestQueries,state_value] at ih ⊢
    simp only [List.flatMap_cons,List.filterMap_cons,state_value]
    by_cases paid:b.cost≤q
    · simp only [paid,↓reduceIte,List.flatMap_cons]
      rw [ih]
    · simp only [paid,↓reduceIte,List.nil_append]
      exact ih

def finish {T S : Tree} (s : Rule4.Choice T S) (r : Charged (List F)) : Charged (Option F) :=
  let bs:=rule4BranchesMeter s
  let b:=bestLengthMeter (fun _=>⟨true,1⟩) r.value
  ⟨b.value,bs.work+r.work+b.work+2⟩

inductive Rule4Exec (OrdExec : Tree→Tree→Nat→Option F→Prop) (mode : Mode)
    {T S : Tree} (s : Rule4.Choice T S) (q : Nat) : Charged (Option F)→List Cell→Prop
  | run (execution : AnswersExec OrdExec mode q 0 (rule4BranchesMeter s).value r cells) :
      Rule4Exec OrdExec mode s q (finish s r) cells

theorem rule4_source_fields
    (sound : ∀ T S b a,OrdExec T S b a→a=base T S b)
    (h : Rule4Exec OrdExec mode s q out cells) :
    out=rule4Source (ordinarySpec mode base) (fun _ _ _=>0) s q := by
  cases h with
  | run execution =>
    have hr:=answers_source_fields sound execution
    simp only [finish,rule4Source,hr]

theorem rule4_actual_trace
    (sound : ∀ T S b a,OrdExec T S b a→a=base T S b)
    (h : Rule4Exec OrdExec mode s q out cells) :
    out.value=(rule4Trace (ordinarySpec mode base) s q).value ∧
    (recorded cells).map (fun ls=>ls.2.query)=(rule4Trace (ordinarySpec mode base) s q).queries := by
  cases h with
  | run execution =>
    have hv:=answers_raw_value sound execution
    have hq:=recorded_query_projection sound execution
    rw [branches_value] at hv hq
    constructor
    · simp only [finish,SourceLocalValuesV3.bestLength_value,rule4Trace,
        OrdinaryDispatch.runRule4,Rule4.solveForest,Rule4.outputs,hv]
    · rw [meteredQueries_raw] at hq
      exact hq

theorem rule4_exists
    (total : ∀ T S b,enabled mode b=true→∃ a,OrdExec T S b a)
    {T S : Tree} (s : Rule4.Choice T S) (q : Nat) :
    ∃ out cells,Rule4Exec OrdExec mode s q out cells := by
  obtain ⟨r,cells,execution⟩:=answers_exists total q 0 (rule4BranchesMeter s).value
  exact ⟨_,_,Rule4Exec.run execution⟩

theorem rule4_bijection_fields
    (sound : ∀ T S b a,OrdExec T S b a→a=base T S b)
    (h : Rule4Exec OrdExec mode s q out cells) :
    (recorded cells).Pairwise (fun a b=>a.1≠b.1) ∧
    (chronological cells).Pairwise (fun a b=>a.1≠b.1) ∧
    ∀ ls∈chronological cells,SlotRealizes OrdExec mode ls.2 := by
  cases h with
  | run execution => exact ⟨recorded_distinct_ids sound execution,
      chronological_distinct_ids sound execution,chronological_slots_realize execution⟩

end SourceRule4V3
