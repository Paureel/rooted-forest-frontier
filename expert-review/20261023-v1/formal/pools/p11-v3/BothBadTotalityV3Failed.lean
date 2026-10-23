import UnitCombineExecutionV3

namespace SourceBothBadDispatchV3
open RMAF Universal233 WholeSourceWork
open Universal233.BothBad SourceForestV3
open SourceCouplingV2 (enabled)
variable {OrdExec : Tree→Tree→Nat→Option F→Prop} {mode : SourceCouplingV2.Mode}

theorem dispatch_exists
    (total : ∀ T S b,enabled mode b=true→∃ a,OrdExec T S b a)
    (T S : Tree) (e : Entry) (k : Nat) :
    ∃ r debits slots,DispatchExec OrdExec mode T S e k r debits slots := by
  cases hm:e.mode with
  | ordinary =>
    obtain ⟨r,debits,slots,execution⟩:=SourceOrdinaryLocalV3.local_exists total T S e.output.partition e.budget k
    exact ⟨_,_,_,DispatchExec.ordinary hm execution⟩
  | full =>
    obtain ⟨out,execution⟩:=forest_exists total e.budget k (some T) (Rule5SelectedLocalWork.sourceForestMeter S e.output.partition).value
    exact ⟨_,_,_,DispatchExec.full hm execution⟩
  | retained parent residual completed known =>
    obtain ⟨out,execution⟩:=forest_exists total e.budget k
      (Rule5SelectedLocalWork.localTargetMeter (some T) residual).value
      (Rule5SelectedLocalWork.ownedMeter (Rule5SelectedLocalWork.sourceForestMeter S e.output.partition).value residual).value
    exact ⟨_,_,_,DispatchExec.retained hm execution⟩
end SourceBothBadDispatchV3

namespace SourceBothBadFoldV3
open RMAF Universal233 WholeSourceWork SourceForestV3
open SourceCouplingV2 (enabled)
variable {OrdExec : Tree→Tree→Nat→Option F→Prop} {mode : SourceCouplingV2.Mode}

theorem entries_exists
    (total : ∀ T S b,enabled mode b=true→∃ a,OrdExec T S b a)
    (T S : Tree) (q : Nat) (es : List BothBad.Entry) :
    ∀ k,∃ r debits slots,EntriesExec OrdExec mode T S q k es r debits slots := by
  induction es with
  | nil => intro k;exact ⟨_,_,_,EntriesExec.nil⟩
  | cons e es ih =>
    intro k
    obtain ⟨r,debits,slots,head⟩:=SourceBothBadDispatchV3.dispatch_exists total T S e k
    obtain ⟨rr,dd,ss,tail⟩:=ih (k+slots.length)
    exact ⟨_,_,_,EntriesExec.cons head tail⟩
end SourceBothBadFoldV3
