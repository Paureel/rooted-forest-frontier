import FamilyAssembly

namespace TripleDP.Transitions
open TripleDP.CostRoute

variable {α I : Type}

def selectedElems (xs : List I) (P : I → Prop) [DecidablePred P] :
    List {i // P i} :=
  (xs.filter (fun i => decide (P i))).attachWith P
    (by intro i hi; exact of_decide_eq_true (List.mem_filter.mp hi).2)

theorem selectedElems_values (xs : List I) (P : I → Prop) [DecidablePred P] :
    (selectedElems xs P).map Subtype.val = xs.filter (fun i => decide (P i)) := by
  exact List.attachWith_map_subtype_val _

/-- Select exactly the indices satisfying P, retaining their original identity. -/
def selectIndex (f : FiniteIndex I) (P : I → Prop) [DecidablePred P] :
    FiniteIndex {i // P i} where
  elems := selectedElems f.elems P
  nodup := by
    have h : ((selectedElems f.elems P).map Subtype.val).Nodup := by
      rw [selectedElems_values]
      exact List.Pairwise.filter _ f.nodup
    exact List.Pairwise.of_map Subtype.val
      (fun _ _ hn he => hn (congrArg Subtype.val he)) h
  complete := by
    intro i
    simp only [selectedElems, List.mem_attachWith, List.mem_filter]
    exact ⟨f.complete i.val, decide_eq_true i.property⟩

theorem selectIndex_length (f : FiniteIndex I) (P : I → Prop) [DecidablePred P] :
    (selectIndex f P).elems.length =
      (f.elems.filter (fun i => decide (P i))).length := by
  simp [selectIndex, selectedElems]

theorem selectIndex_nonboundary_length {t : BTree α} [DecidableEq I]
    (f : Family t I) (o : I) (ho : f.boundary = some o) :
    (selectIndex f.finite (fun i => i ≠ o)).elems.length = f.cost := by
  rw [selectIndex_length, cost_counts_closed_indices]
  simp [Family.closedIndices, ho]

#print axioms selectedElems_values
#print axioms selectIndex
#print axioms selectIndex_length
#print axioms selectIndex_nonboundary_length
end TripleDP.Transitions
