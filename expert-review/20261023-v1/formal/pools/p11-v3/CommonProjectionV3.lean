import LocalValueProjectionsV3
import OrdinaryStepTrace

namespace SourceCommonValuesV3
open RMAF ForestState Universal233 WholeSourceWork CoreWork
open GenericForest.CheckCorrespondence
open OrdinaryDispatch.FullSourceWork OrdinaryDispatch.EarlyLocalWork
open OrdinaryDispatch.FastOrdinary SourceLocalValuesV3

theorem labelMax_value (xs : List Nat) :
    (labelMaxMeter xs).value=OrdinaryCommonSplit.Source.labelMax xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [OrdinaryCommonSplit.Source.labelMax] at ih
    simp only [labelMaxMeter,OrdinaryCommonSplit.Source.labelMax,List.foldr_cons,ih]

theorem commonFresh_value (T : Tree) :
    (commonFreshMeter T).value=OrdinaryDispatch.commonFresh T := by
  simp only [commonFreshMeter,OrdinaryDispatch.commonFresh,SourceLocalValuesV3.meterLeaves_value,labelMax_value]

theorem leafEqual_value (T : Tree) (a : Nat) : (leafEqualMeter T a).value=(T==.leaf a) := by
  cases T with
  | leaf x =>
    apply Bool.eq_iff_iff.mpr
    simp only [leafEqualMeter,beq_iff_eq,Tree.leaf.injEq]
  | node l r => rfl

theorem contract_value (a b z : Nat) (T : Tree) :
    (contractMeter a b z T).value=ForestState.contract a b z T := by
  induction T with
  | leaf x => rfl
  | node l r il ir =>
    simp only [contractMeter,ForestState.contract,leafEqual_value,il,ir]
    split <;> rfl

theorem commonPair_value (T S : Tree) (reverse : Bool) (c : CherryBranching.Candidate) :
    (commonPairMeter T S reverse c).value=commonPair T S reverse c := by
  simp only [commonPairMeter,commonPair,commonFresh_value,contract_value]

theorem expandBlock_value (a b z : Nat) (xs : List Nat) :
    (expandBlockMeter a b z xs).value=ForestState.expandBlock a b z xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [ForestState.expandBlock] at ih
    simp only [expandBlockMeter,ForestState.expandBlock,List.flatMap_cons,ih]

theorem expandCommon_value (T S : Tree) (reverse : Bool) (c : CherryBranching.Candidate)
    (fs : SourceForestV3.F) :
    (expandCommonMeter T S reverse c fs).value=expandCommon T S reverse c fs := by
  simp only [expandCommonMeter,expandCommon,SourceLocalValuesV3.meterMap_value,expandBlock_value,commonFresh_value]

end SourceCommonValuesV3

namespace SourceCommonV3
open RMAF ForestState Universal233 WholeSourceWork CoreWork
open GenericForest.CheckCorrespondence OrdinaryDispatch.FastOrdinary OrdinaryDispatch.WorkRecursion
open SourceForestV3 SourceCouplingV2 SourceLocalValuesV3 SourceCommonValuesV3
open CallbackPairingAuthor (indexFrom)

variable {OrdExec : Tree→Tree→Nat→Option SourceForestV3.F→Prop}
  {base : Tree→Tree→Nat→Option SourceForestV3.F} {T S : Tree}

theorem smaller_raw (T S : Tree) (reverse : Bool) (c : CherryBranching.Candidate) :
    smaller T S reverse c ↔
      (leaves (commonPair T S reverse c).1).length<(leaves T).length := by
  simp only [smaller,pair,SourceLocalValuesV3.meterLeaves_value,commonPair_value]

theorem common_raw_value
    (sound : ∀ T S b a,OrdExec T S b a→a=base T S b)
    (h : CommonExec OrdExec q T S reverse c k out slots) :
    out.value = if (leaves (commonPair T S reverse c).1).length<(leaves T).length then
      (base (commonPair T S reverse c).1 (commonPair T S reverse c).2 q).map
        (expandCommon T S reverse c) else none := by
  cases h with
  | refused large =>
    have hl : ¬(leaves (commonPair T S reverse c).1).length<(leaves T).length :=
      fun h=>large ((smaller_raw _ _ _ _).mpr h)
    simp only [refused,hl,↓reduceIte]
  | returned small execution =>
    rename_i answer
    have hs:=(smaller_raw _ _ _ _).mp small
    have hv:=sound _ _ _ _ execution
    simp only [pair,commonPair_value] at hv
    simp only [hs,↓reduceIte,←hv]
    cases answer <;> simp only [returned,Option.map_none,Option.map_some,expandCommon_value]

theorem common_raw_queries (q : Nat) (T S : Tree) (reverse : Bool) (c : CherryBranching.Candidate) :
    queries q T S reverse c =
      if (leaves (commonPair T S reverse c).1).length<(leaves T).length then
        [(commonPair T S reverse c,q)] else [] := by
  simp only [queries,pair,commonPair_value,smaller_raw]

theorem actual_common_trace
    (sound : ∀ T S b a,OrdExec T S b a→a=base T S b)
    (h : CommonExec OrdExec q T S reverse c k out slots)
    (proper : DepthOne.proper T S=true)
    (pretest : DepthOne.pretest01 T S=.rejected)
    (selected : early T S=.common reverse c) :
    out.value=(ordinaryStepTrace (fun b T S=>base T S b) q T S).value ∧
    slots.map (fun s=>(s.index,s.query))=
      indexFrom k (ordinaryStepTrace (fun b T S=>base T S b) q T S).queries := by
  have hv:=common_raw_value sound h
  have hq:=common_index h
  rw [common_raw_queries] at hq
  simp only [ordinaryStepTrace,proper,Bool.true_eq,↓reduceIte,pretest,selected]
  split <;> rename_i hs
  · simp only [hs,↓reduceIte] at hv hq
    exact ⟨hv,hq⟩
  · simp only [hs,↓reduceIte] at hv hq
    exact ⟨hv,hq⟩

end SourceCommonV3
