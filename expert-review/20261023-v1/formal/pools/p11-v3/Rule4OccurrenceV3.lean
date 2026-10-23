import Rule4ExecutionV3

namespace SourceRule4V3
open RMAF Universal233 GenericForest GenericForest.FrontierWork
open SourceForestV3 SourceCouplingV2
open SourceDisjointV2 (ordinarySpec)
open OrdinaryDispatch.FullSourceWork
open CallbackPairingAuthor (indexFrom_project)

variable {OrdExec : Tree→Tree→Nat→Option F→Prop} {mode : Mode}
  {base : Tree→Tree→Nat→Option F}

def meteredQueries (actual : GenericForest.FrontierWork.Ordinary)
    (q : Nat) (bs : List Rule4.Branch) : List Q :=
  bs.flatMap fun b=>if b.cost≤q then
    frontier actual (some b.target) (rule4StateMeter b).value (q-b.cost) else []

theorem forest_slot_queries
    (sound : ∀ T S b a,OrdExec T S b a→a=base T S b)
    (h : ForestExec OrdExec mode k T ss q out) :
    out.slots.map Slot.query=frontier (ordinarySpec mode base) T ss q := by
  have hi:=(forest_correspondence sound _ _ _ _ _ h).2.2
  have z:=congrArg (List.map Prod.snd) hi
  simpa only [List.map_map,indexFrom_project,Function.comp_def] using z

theorem recorded_query_projection
    (sound : ∀ T S b a,OrdExec T S b a→a=base T S b)
    (h : AnswersExec OrdExec mode q i bs r cells) :
    (recorded cells).map (fun ls=>ls.2.query)=meteredQueries (ordinarySpec mode base) q bs := by
  induction h with
  | nil => rfl
  | refused tail over ih =>
    simpa only [recorded,List.flatMap_cons,labelCell,cellSlots,List.map_nil,List.nil_append,
      meteredQueries,over,↓reduceIte] using ih
  | returned tail paid execution ih =>
    have hq:=forest_slot_queries sound execution
    simp only [recorded,meteredQueries] at ih
    simp only [recorded,List.flatMap_cons,labelCell,cellSlots,List.map_append,List.map_map,
      Function.comp_def,meteredQueries,paid,↓reduceIte]
    rw [hq,ih]

theorem recorded_lower (h : AnswersExec OrdExec mode q i bs r cells)
    (ls : (Nat×Nat)×SourceForestV3.S) (hs : ls∈recorded cells) : i≤ls.1.1 := by
  induction h with
  | nil => simp only [recorded,List.flatMap_nil,List.mem_nil_iff] at hs
  | refused tail over ih =>
    simp only [recorded,List.flatMap_cons,labelCell,cellSlots,List.map_nil,List.nil_append] at hs
    have ht:=ih hs
    omega
  | returned tail paid execution ih =>
    change ls∈labelCell _++recorded _ at hs
    rcases List.mem_append.mp hs with hs|hs
    · obtain ⟨s,hs,rfl⟩:=List.mem_map.mp hs
      exact Nat.le_refl _
    · have ht:=ih hs; omega

theorem recorded_distinct_ids
    (sound : ∀ T S b a,OrdExec T S b a→a=base T S b)
    (h : AnswersExec OrdExec mode q i bs r cells) :
    (recorded cells).Pairwise (fun a b=>a.1≠b.1) := by
  induction h with
  | nil => simp [recorded]
  | refused tail over ih =>
    simpa only [recorded,List.flatMap_cons,labelCell,cellSlots,List.map_nil,List.nil_append] using ih
  | returned tail paid execution ih =>
    change (labelCell _++recorded _).Pairwise _
    rw [List.pairwise_append]
    refine ⟨?_,ih,?_⟩
    · have hi:=(forest_correspondence sound _ _ _ _ _ execution).2.2
      have strict:=ledger_strict hi
      simp only [labelCell,cellSlots,List.pairwise_map]
      exact strict.imp (fun h he=>by have hz:=congrArg Prod.snd he; omega)
    · intro a ha b hb
      obtain ⟨s,hs,rfl⟩:=List.mem_map.mp ha
      have hl:=recorded_lower tail b hb
      intro he
      have hz:=congrArg Prod.fst he
      dsimp at hz
      omega

theorem chronological_distinct_ids
    (sound : ∀ T S b a,OrdExec T S b a→a=base T S b)
    (h : AnswersExec OrdExec mode q i bs r cells) :
    (chronological cells).Pairwise (fun a b=>a.1≠b.1) := by
  have hp:=recorded_distinct_ids sound h
  exact (two_ledger_perm cells).pairwise_iff (fun h=>Ne.symm h) |>.mpr hp

end SourceRule4V3
