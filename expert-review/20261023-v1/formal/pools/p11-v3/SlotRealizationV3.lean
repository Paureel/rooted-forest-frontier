import OccurrenceInjectionV3

namespace SourceForestV3
open RMAF ForestState GenericForest GenericForest.FrontierWork Universal233.PaidQueries
open SourceCouplingV2 SourceDisjointV2 SourceForestSingletonV2

def SlotRealizes (OrdExec : Tree→Tree→Nat→Option F→Prop) (mode : Mode) (s : S) : Prop :=
  (s.live=false ∧ enabled mode s.query.2=false ∧ s.returned=none) ∨
  (s.live=true ∧ enabled mode s.query.2=true ∧
    ∃ a,OrdExec s.query.1.1 s.query.1.2 s.query.2 a ∧
      s.returned=a.map (fun fs=>(fs.length-1,fs)))

variable {OrdExec : Tree→Tree→Nat→Option F→Prop} {mode : Mode}

theorem pair_child_witness (h : PairChild OrdExec p b a) :
    ∃ raw,OrdExec p.1 p.2 b raw ∧ a=raw.map (fun fs=>(fs.length-1,fs)) := by
  cases h with
  | returned execution => exact ⟨_,execution,rfl⟩

theorem run_slots_realize
    (h : Run (PairChild OrdExec) mode b k js r slots ticks) :
    ∀ s∈slots,SlotRealizes OrdExec mode s := by
  induction h with
  | nil => simp
  | resolved tail ih => exact ih
  | refused off =>
    intro s hs
    simp only [List.mem_singleton] at hs
    subst s
    exact Or.inl ⟨rfl,off,rfl⟩
  | failed on returned =>
    intro s hs
    simp only [List.mem_singleton] at hs
    subst s
    exact Or.inr ⟨rfl,on,pair_child_witness returned⟩
  | success on returned tail ih =>
    intro s hs
    simp only [List.mem_cons] at hs
    rcases hs with rfl|hs
    · exact Or.inr ⟨rfl,on,pair_child_witness returned⟩
    · exact ih s hs

theorem scheduleAt_slots_realize
    (h : ScheduleAt (PairChild OrdExec) mode q js k r slots) :
    ∀ s∈slots,SlotRealizes OrdExec mode s := by
  cases h with
  | refused small => simp
  | run enough execution => exact run_slots_realize execution

theorem invoke_slot_realizes (h : Invoke OrdExec mode k p b a slot) :
    SlotRealizes OrdExec mode slot := by
  cases h with
  | refused off => exact Or.inl ⟨rfl,off,rfl⟩
  | returned on execution => exact Or.inr ⟨rfl,on,_,execution,rfl⟩

theorem branches_slots_realize
    (lower : ∀ b,b<q→∀ k T ss out,
      ForestExec OrdExec mode k T ss b out→∀ s∈out.slots,SlotRealizes OrdExec mode s)
    (h : BranchesExec OrdExec mode k T ss q bs answers debit slots) :
    ∀ s∈slots,SlotRealizes OrdExec mode s := by
  induction bs generalizing k answers debit slots with
  | nil => cases h; simp
  | cons io bs ih =>
    cases h with
    | skip bad tail => exact ih tail
    | take good child tail =>
      intro s hs
      simp only [List.mem_append] at hs
      rcases hs with hs|hs
      · exact lower _ (by have g:=good; dsimp [eligible] at g; omega) _ _ _ _ child s hs
      · exact ih tail s hs

theorem forest_slots_realize (q : Nat) : ∀ k T ss out,
    ForestExec OrdExec mode k T ss q out→∀ s∈out.slots,SlotRealizes OrdExec mode s := by
  refine Nat.strongRecOn q ?_
  intro q lower k T ss out execution
  cases execution with
  | improper hp => simp
  | agreed hp ha => simp
  | absent hp ha => simp
  | singleton hp ha execution =>
    intro s hs
    simp only [List.mem_singleton] at hs
    subst s
    exact invoke_slot_realizes execution
  | noJobs hp ha hn ho hj => simp
  | disjoint hp ha hn ho hj execution => exact scheduleAt_slots_realize execution
  | overlap hp ha hn ho execution => exact branches_slots_realize lower execution

theorem children_slots_realize
    (h : ChildrenExec OrdExec mode T q k cs r debits slots) :
    ∀ s∈slots,SlotRealizes OrdExec mode s := by
  induction h with
  | nil => simp
  | refused over tail ih => exact ih
  | returned paid execution tail ih =>
    intro s hs
    simp only [List.mem_append] at hs
    rcases hs with hs|hs
    · exact forest_slots_realize _ _ _ _ _ execution s hs
    · exact ih s hs

theorem live_slot_execution {slots : List S}
    (h : ∀ s∈slots,SlotRealizes OrdExec mode s) (s : S) (hs : s∈liveSlots slots) :
    enabled mode s.query.2=true ∧
    ∃ a,OrdExec s.query.1.1 s.query.1.2 s.query.2 a ∧
      s.returned=a.map (fun fs=>(fs.length-1,fs)) := by
  have hm := List.mem_filter.mp hs
  rcases h s hm.1 with ⟨off,rest⟩|⟨on,enabled,execution⟩
  · simp [off] at hm
  · exact ⟨enabled,execution⟩

end SourceForestV3
