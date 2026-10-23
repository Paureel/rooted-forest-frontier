import DisjointQuery20
open RMAF Universal233 CherryBranching OrdinaryDispatch
namespace FreshLiteralDisjoint
theorem original_early_hard2_fields {T S : Tree} {c d : Candidate}
 (selected : FastOrdinary.early T S=.hard2 c d) :
 select T S=some (.hard2,c) ∧ select S T=some (.hard2,d) ∧
 Rule4.select T S=none ∧ Rule4.select S T=none := by
 unfold FastOrdinary.early at selected
 split at selected <;> try cases selected
 next ht hs =>
  split at selected <;> try cases selected
  next hf =>
   split at selected <;> try cases selected
   next hr =>
    exact ⟨ht,hs,hf,hr⟩
end FreshLiteralDisjoint

-- Author integration type/axiom reports; proof text above is unchanged apart from recorded import edits.
set_option pp.universes true
#check @FreshLiteralDisjoint.original_early_hard2_fields
#print axioms FreshLiteralDisjoint.original_early_hard2_fields
