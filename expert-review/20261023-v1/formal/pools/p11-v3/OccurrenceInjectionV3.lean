import ChildrenExecutionV3

namespace SourceForestV3
open RMAF GenericForest GenericForest.FrontierWork
open SourceCouplingV2 SourceDisjointV2 SourceChildrenV2
open CallbackPairingAuthor (indexFrom indexFrom_bounds indexFrom_nth)

theorem indexFrom_strict {α : Type} (k : Nat) (xs : List α) :
    (indexFrom k xs).Pairwise (fun a b=>a.1<b.1) := by
  induction xs generalizing k with
  | nil => simp [indexFrom]
  | cons x xs ih =>
    simp only [indexFrom,List.pairwise_cons]
    exact ⟨fun p hp=>by have z:=indexFrom_bounds (k+1) xs p hp; omega,ih (k+1)⟩

theorem ledger_strict {slots : List S} {qs : List Q} {k : Nat}
    (h : slots.map (fun s=>(s.index,s.query))=indexFrom k qs) :
    slots.Pairwise (fun s t=>s.index<t.index) := by
  have hp : (slots.map (fun s=>(s.index,s.query))).Pairwise (fun a b=>a.1<b.1) := by
    rw [h]
    exact indexFrom_strict k qs
  simpa only [List.pairwise_map] using hp

theorem ledger_live_strict {slots : List S} {qs : List Q} {k : Nat}
    (h : slots.map (fun s=>(s.index,s.query))=indexFrom k qs) :
    (liveSlots slots).Pairwise (fun s t=>s.index<t.index) :=
  (ledger_strict h).sublist (live_order slots)

theorem ledger_nth {slots : List S} {qs : List Q} {k : Nat}
    (h : slots.map (fun s=>(s.index,s.query))=indexFrom k qs) (j : Nat) :
    (slots.map (fun s=>(s.index,s.query)))[j]?=(qs[j]?).map (fun p=>(k+j,p)) := by
  rw [h]
  exact indexFrom_nth k qs j

theorem ledger_member {slots : List S} {qs : List Q} {k : Nat}
    (h : slots.map (fun s=>(s.index,s.query))=indexFrom k qs)
    (slot : S) (hs : slot∈slots) :
    k≤slot.index ∧ slot.index<k+qs.length ∧ qs[slot.index-k]?=some slot.query := by
  have hm : (slot.index,slot.query)∈indexFrom k qs := by
    rw [←h]
    exact List.mem_map.mpr ⟨slot,hs,rfl⟩
  have hb := indexFrom_bounds k qs _ hm
  obtain ⟨j,hj⟩ := List.mem_iff_getElem?.mp hm
  rw [indexFrom_nth] at hj
  cases he : qs[j]? with
  | none => simp [he] at hj
  | some p =>
    simp only [he,Option.map_some,Option.some.injEq,Prod.mk.injEq] at hj
    rcases hj with ⟨hi,hp⟩
    refine ⟨hb.1,hb.2,?_⟩
    have hk : slot.index-k=j := by omega
    simpa only [hk,hp] using he

variable {OrdExec : Tree→Tree→Nat→Option F→Prop} {mode : Mode}
  {base : Tree→Tree→Nat→Option F}

theorem forest_live_injection
    (sound : ∀ T S b a,OrdExec T S b a→a=base T S b)
    (h : ForestExec OrdExec mode k T ss q out) :
    (liveSlots out.slots).Pairwise (fun s t=>s.index<t.index) ∧
    ∀ slot∈liveSlots out.slots,
      k≤slot.index ∧ slot.index<k+(frontier (ordinarySpec mode base) T ss q).length ∧
      (frontier (ordinarySpec mode base) T ss q)[slot.index-k]?=some slot.query := by
  have hi := (forest_correspondence sound _ _ _ _ _ h).2.2
  refine ⟨ledger_live_strict hi,?_⟩
  intro slot hs
  exact ledger_member hi slot ((live_order out.slots).subset hs)

theorem children_live_injection
    (sound : ∀ T S b a,OrdExec T S b a→a=base T S b)
    (h : ChildrenExec OrdExec mode T q k cs r debits slots) :
    (liveSlots slots).Pairwise (fun s t=>s.index<t.index) ∧
    ∀ slot∈liveSlots slots,
      k≤slot.index ∧ slot.index<k+(childrenQueries (ordinarySpec mode base) T q cs).length ∧
      (childrenQueries (ordinarySpec mode base) T q cs)[slot.index-k]?=some slot.query := by
  have hi := children_index sound h
  refine ⟨ledger_live_strict hi,?_⟩
  intro slot hs
  exact ledger_member hi slot ((live_order slots).subset hs)

end SourceForestV3
