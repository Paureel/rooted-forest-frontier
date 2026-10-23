import ForestViewEquationsV3

namespace SourceForestV3
open RMAF ForestState GenericForest GenericForest.FrontierWork
open SourceCouplingV2 SourceDisjointV2 SourceForestSingletonV2
open CallbackPairingAuthor (indexFrom)

variable {OrdExec : Tree → Tree → Nat → Option F → Prop} {mode : Mode}
  {actual : GenericForest.FrontierWork.Ordinary} {q k : Nat}
  {T : Option Tree} {ss : List Tree} {bs : List B}
  {answers : List F} {debit : Nat} {slots : List S}

theorem branches_correspondence
    (lower : ∀ b, b<q → ∀ k T ss out,
      ForestExec OrdExec mode k T ss b out → Corresponds actual k T ss b out)
    (h : BranchesExec OrdExec mode k T ss q bs answers debit slots) :
    answers=branchAnswers actual T ss q bs ∧
    debit=branchDebit actual T ss q bs ∧
    slots.map (fun s=>(s.index,s.query))=indexFrom k (branchQueries actual T ss q bs) := by
  induction bs generalizing k answers debit slots with
  | nil => cases h; simp [branchAnswers,branchDebit,branchQueries,indexFrom]
  | cons io bs ih =>
    cases h with
    | skip bad tail =>
      have ih := ih tail
      simpa [branchAnswers,branchDebit,branchQueries,bad] using ih
    | take good child tail =>
      have ih := ih tail
      have hc := lower _ (by have g:=good; dsimp [eligible] at g; omega) _ _ _ _ child
      rcases hc with ⟨hv,hd,hq⟩
      rcases ih with ⟨iv,id,iq⟩
      refine ⟨?_,?_,?_⟩
      · simp only [branchAnswers,List.filterMap_cons,good,↓reduceIte]
        rw [←hv,iv]
        simp only [branchAnswers]
        split <;> rename_i hcase <;> simp only [hcase]
        all_goals rfl
      · simp only [branchDebit,List.map_cons,List.sum_cons,good,↓reduceIte]
        rw [hd,id]
        rfl
      · simp only [branchQueries,List.flatMap_cons,good,↓reduceIte]
        rw [List.map_append,hq,iq]
        have hl := index_length hq
        rw [hl]
        exact (indexFrom_append _ _ _).symm

theorem forest_correspondence
    (sound : ∀ T S b a, OrdExec T S b a → a=base T S b)
    (q : Nat) : ∀ k T ss out,
    ForestExec OrdExec mode k T ss q out →
      Corresponds (ordinarySpec mode base) k T ss q out := by
  refine Nat.strongRecOn q ?_
  intro q lower k T ss out execution
  cases execution with
  | improper hp =>
    cases T <;> rcases ss with _ | ⟨s,(_ | ⟨u,rest⟩)⟩ <;>
      (try simp only [List.map_nil,List.map_cons] at *) <;>
      simp [Corresponds,GenericForest.solve,OrdinaryDispatch.WorkRecursion.forestWork,
      nonrecursiveBill,frontier,hp,indexFrom]
  | agreed hp ha =>
    cases T <;> rcases ss with _ | ⟨s,(_ | ⟨u,rest⟩)⟩ <;>
      (try simp only [List.map_nil,List.map_cons] at *) <;>
      simp [Corresponds,GenericForest.solve,OrdinaryDispatch.WorkRecursion.forestWork,
      nonrecursiveBill,frontier,hp,ha,indexFrom]
  | absent hp ha =>
    simp [Corresponds,GenericForest.solve,OrdinaryDispatch.WorkRecursion.forestWork,
      nonrecursiveBill,frontier,hp,ha,indexFrom]
  | singleton hp ha execution =>
    exact ⟨singleton_value execution sound hp ha,
      singleton_debit mode base hp ha,singleton_index execution hp ha⟩
  | noJobs hp ha hn ho hj => exact noJobs_corresponds hp ha hn ho hj
  | disjoint hp ha hn ho hj execution =>
    exact disjointAt_corresponds execution sound hp ha hn ho hj
  | overlap hp ha hn ho execution =>
    have hb := branches_correspondence lower execution
    rcases hb with ⟨hv,hd,hq⟩
    refine ⟨?_,?_,?_⟩
    · rw [overlap_value_equation hp ha hn ho,←hv]
    · rw [overlap_debit_equation hp ha hn ho,←hd]
    · rw [overlap_frontier_equation hp ha hn ho]
      exact hq

end SourceForestV3
