import DisjointDirect30
open RMAF Universal233 CherryBranching OrdinaryDispatch
namespace FreshLiteralDisjoint
theorem literal_parent_shape (S : Tree) (a b : Nat) (p r : Vertex)
 (hcuts : cuts S a b=[p,r]) : pendantPartition S a b=
 [PaidAssembly.leftParent S p,PaidAssembly.rightParent S r,PaidAssembly.rootParent S p r] := by
 simp [pendantPartition,coreLabels,hcuts,PaidAssembly.leftParent,PaidAssembly.rightParent,
   PaidAssembly.rootParent,List.contains_append,Bool.not_or]

theorem literal_parent_count (S : Tree) (a b : Nat) (p r : Vertex)
 (hcuts : cuts S a b=[p,r]) : (pendantPartition S a b).length=3 ∧
 (pendantPartition S a b).length-1=2 := by
 rw [literal_parent_shape S a b p r hcuts]
 exact ⟨rfl,rfl⟩
end FreshLiteralDisjoint

-- Author integration type/axiom reports; proof text above is unchanged apart from recorded import edits.
set_option pp.universes true
#check @FreshLiteralDisjoint.literal_parent_shape
#print axioms FreshLiteralDisjoint.literal_parent_shape
#check @FreshLiteralDisjoint.literal_parent_count
#print axioms FreshLiteralDisjoint.literal_parent_count
