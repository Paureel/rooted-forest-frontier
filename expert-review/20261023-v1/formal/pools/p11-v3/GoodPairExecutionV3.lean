import LiveRankV3

namespace SourceGoodPairV3
open RMAF Universal233 WholeSourceWork CoreWork
open GenericForest GenericForest.FrontierWork GenericForest.CheckCorrespondence
open OrdinaryDispatch.Hard2SourceWork OrdinaryDispatch.WorkIntegration
open Universal233.Rule5SelectedLocalWork SourceForestV3 SourceCouplingV2
open SourceDisjointV2 (ordinarySpec)

structure Prep where
  sources : Rule5PrefixLocalWork.Measured (List Tree)
  dp : Charged (Option F)
  work : Nat

def prepare (T S : Tree) (A B C : List Nat) : Prep :=
  let ss:=sourceForestMeter S [A,B,C]
  let u1:=appendLabelsMeter A B
  let t:=localTargetMeter (some T) u1.value
  let u2:=appendLabelsMeter A B
  let ds:=ownedMeter ss.value u2.value
  let dp:=AllGoodDP.LocalWork.meterRun t.value ds.value
  ⟨ss,dp,ss.work+u1.work+t.work+u2.work+ds.work+dp.work+12⟩

def score (p : Prep) (A B : List Nat) (H : F) : Charged Nat :=
  let u3:=appendLabelsMeter A B
  let sources:=ownedMeter p.sources.value u3.value
  let s:=additionalCostMeter sources.value H
  ⟨s.value,p.work+u3.work+sources.work+s.work+8⟩

def finish (T S : Tree) (C : List Nat) (q : Nat) (p : Prep) (s : Charged Nat)
    (H : F) (out : SourceForestV3.Result) : SourceExecution :=
  let target:=localTargetMeter (some T) C
  let sources:=ownedMeter p.sources.value C
  let residual:=q-2-s.value
  let checked:=checkedMeter T S q (out.value.map (fun K=>H++K))
  ⟨⟨checked.value,[⟨target.value,sources.value,residual⟩]⟩,
    (s.work+target.work+sources.work+2*H.length+checked.work+16)+(out.debit+0)⟩

inductive GoodExec (OrdExec : Tree→Tree→Nat→Option F→Prop) (mode : Mode)
    (T S : Tree) (A B C : List Nat) (q : Nat) : SourceExecution→List SourceForestV3.S→Prop
  | small (low : ¬2≤q) : GoodExec OrdExec mode T S A B C q ⟨⟨none,[]⟩,6⟩ []
  | dpRefused (enough : 2≤q) (empty : (prepare T S A B C).dp.value=none) :
      GoodExec OrdExec mode T S A B C q ⟨⟨none,[]⟩,(prepare T S A B C).work+4⟩ []
  | scoreRefused (enough : 2≤q) (found : (prepare T S A B C).dp.value=some H)
      (over : ¬(score (prepare T S A B C) A B H).value≤q-2) :
      GoodExec OrdExec mode T S A B C q
        ⟨⟨none,[]⟩,(score (prepare T S A B C) A B H).work+4⟩ []
  | returned (enough : 2≤q) (found : (prepare T S A B C).dp.value=some H)
      (paid : (score (prepare T S A B C) A B H).value≤q-2)
      (execution : ForestExec OrdExec mode 0 (localTargetMeter (some T) C).value
        (ownedMeter (prepare T S A B C).sources.value C).value
        (q-2-(score (prepare T S A B C) A B H).value) out) :
      GoodExec OrdExec mode T S A B C q
        (finish T S C q (prepare T S A B C) (score (prepare T S A B C) A B H) H out) out.slots

variable {OrdExec : Tree→Tree→Nat→Option F→Prop} {mode : Mode}
  {base : Tree→Tree→Nat→Option F} {T S : Tree} {A B C : List Nat}

theorem good_source_fields
    (sound : ∀ T S b a,OrdExec T S b a→a=base T S b)
    (h : GoodExec OrdExec mode T S A B C q r slots) :
    r=goodPairSource (ordinarySpec mode base) (fun _ _ _=>0) T S A B C q := by
  cases h with
  | small low => simp only [goodPairSource,goodPairLocalSource,low,↓reduceIte,callsForestDebit,List.map_nil,List.sum_nil,Nat.add_zero]
  | dpRefused enough none =>
    simp only [prepare] at none
    simp only [goodPairSource,goodPairLocalSource,enough,↓reduceIte,none,callsForestDebit,List.map_nil,List.sum_nil,Nat.add_zero,prepare]
  | scoreRefused enough found over =>
    simp only [prepare] at found
    simp only [score,prepare] at over
    simp only [goodPairSource,goodPairLocalSource,enough,↓reduceIte,found,over,
      callsForestDebit,List.map_nil,List.sum_nil,Nat.add_zero,score,prepare]
  | returned enough found paid execution =>
    have hc:=forest_correspondence sound _ _ _ _ _ execution
    simp only [prepare] at found
    simp only [score,prepare] at paid
    simp only [goodPairSource,goodPairLocalSource,enough,↓reduceIte,found,paid,callsForestDebit,
      List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,finish,score,prepare]
    simp only [prepare,score] at hc
    rw [←hc.1,←hc.2.1]

theorem good_exists
    (total : ∀ T S b,enabled mode b=true→∃ a,OrdExec T S b a)
    (T S : Tree) (A B C : List Nat) (q : Nat) :
    ∃ r slots,GoodExec OrdExec mode T S A B C q r slots := by
  by_cases enough:2≤q
  · cases hd:(prepare T S A B C).dp.value with
    | none => exact ⟨_,_,GoodExec.dpRefused enough hd⟩
    | some H =>
      by_cases paid:(score (prepare T S A B C) A B H).value≤q-2
      · obtain ⟨out,execution⟩:=forest_exists total (q-2-(score (prepare T S A B C) A B H).value) 0
          (localTargetMeter (some T) C).value (ownedMeter (prepare T S A B C).sources.value C).value
        exact ⟨_,_,GoodExec.returned enough hd paid execution⟩
      · exact ⟨_,_,GoodExec.scoreRefused enough hd paid⟩
  · exact ⟨_,_,GoodExec.small enough⟩

theorem good_index
    (sound : ∀ T S b a,OrdExec T S b a→a=base T S b)
    (h : GoodExec OrdExec mode T S A B C q r slots) :
    slots.map (fun s=>(s.index,s.query))=CallbackPairingAuthor.indexFrom 0
      (forestQueries (ordinarySpec mode base) r.value.calls) := by
  cases h with
  | small low => rfl
  | dpRefused enough none => rfl
  | scoreRefused enough found over => rfl
  | returned enough found paid execution =>
    have hi:=(forest_correspondence sound _ _ _ _ _ execution).2.2
    simpa only [finish,forestQueries,List.flatMap_cons,List.flatMap_nil,List.append_nil] using hi

theorem good_slots_realize (h : GoodExec OrdExec mode T S A B C q r slots) :
    ∀ s∈slots,SlotRealizes OrdExec mode s := by
  cases h with
  | small low => simp
  | dpRefused enough none => simp
  | scoreRefused enough found over => simp
  | returned enough found paid execution => exact forest_slots_realize _ _ _ _ _ execution

end SourceGoodPairV3
