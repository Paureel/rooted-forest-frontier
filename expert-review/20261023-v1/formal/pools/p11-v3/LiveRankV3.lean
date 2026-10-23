import CompleteSelectedChildrenV3

namespace SourceLiveRankV3
open RMAF SourceForestV3 SourceCouplingV2

def Decreases (q : Nat) (T : Tree) (s : SourceForestV3.S) : Prop :=
  s.query.2<q ∨ (s.query.2=q ∧ (leaves s.query.1.1).length<(leaves T).length)

variable {OrdExec : Tree→Tree→Nat→Option SourceForestV3.F→Prop}

theorem cutoff_live_budget
    (h : SlotRealizes OrdExec (.cutoff q) s) (live : s.live=true) : s.query.2<q := by
  rcases h with ⟨off,rest⟩|⟨on,en,execution⟩
  · rw [live] at off
    cases off
  · simpa only [enabled,decide_eq_true_eq] using en

theorem children_live_decreases
    (h : ChildrenExec OrdExec (.cutoff q) T q k cs r debits slots)
    (s : SourceForestV3.S) (hs : s∈liveSlots slots) : Decreases q T s := by
  have hm:=List.mem_filter.mp hs
  exact Or.inl (cutoff_live_budget (children_slots_realize h s hm.1) hm.2)

theorem forest_live_decreases
    (h : ForestExec OrdExec (.cutoff parent) k target ss b out)
    (T : Tree) (s : SourceForestV3.S) (hs : s∈liveSlots out.slots) : Decreases parent T s := by
  have hm:=List.mem_filter.mp hs
  exact Or.inl (cutoff_live_budget (forest_slots_realize _ _ _ _ _ h s hm.1) hm.2)

theorem common_live_decreases {T S : Tree}
    (h : SourceCommonV3.CommonExec OrdExec q T S reverse c k out slots)
    (s : SourceForestV3.S) (hs : s∈slots) : Decreases q T s := by
  cases h with
  | refused large => simp only [List.mem_nil_iff] at hs
  | returned small execution =>
    simp only [List.mem_singleton] at hs
    subst s
    refine Or.inr ⟨rfl,?_⟩
    have ht:=(SourceCommonV3.smaller_raw _ _ _ _).mp small
    simpa only [SourceCommonV3.pair,SourceCommonValuesV3.commonPair_value] using ht

theorem rule4_chronological_live_decreases {T S : Tree}
    (h : SourceRule4V3.Rule4Exec OrdExec (.cutoff q) choice q out cells)
    (ls : (Nat×Nat)×SourceForestV3.S) (hs : ls∈SourceRule4V3.chronological cells)
    (live : ls.2.live=true) : Decreases q T ls.2 := by
  cases h with
  | run execution =>
    exact Or.inl (cutoff_live_budget (SourceRule4V3.chronological_slots_realize execution ls hs) live)

theorem outputs_chronological_live_decreases {T S : Tree}
    (h : SourceFullOutputsV3.OutputsExec OrdExec (.cutoff q) T S q i os r cells)
    (ls : (Nat×Nat)×SourceForestV3.S) (hs : ls∈SourceFullOutputsV3.chronological cells)
    (live : ls.2.live=true) : Decreases q T ls.2 :=
  Or.inl (cutoff_live_budget (SourceFullOutputsV3.chronological_slots_realize h ls hs) live)

end SourceLiveRankV3
