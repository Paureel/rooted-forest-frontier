import LiteralPair
open RMAF ForestState ForestGroups ContactedGoodPair
namespace ContactedPairControls
def source : Tree := .node (.node (.leaf 0) (.leaf 1)) (.node (.node (.leaf 2) (.leaf 3)) (.node (.leaf 4) (.leaf 5)))
def crossed : Tree := .node (.node (.leaf 0) (.leaf 4)) (.node (.node (.leaf 1) (.leaf 5)) (.node (.leaf 2) (.leaf 3)))
def A : List Nat := [0,1]
def B : List Nat := [2,3]
def C : List Nat := [4,5]
def noOrdinary : Ordinary := fun _ _ _=>none

theorem local_guards_do_not_imply_global :
 Universal233.DepthOne.proper crossed source=true ∧
 partitionCheck (leaves source) [A,B,C]=true ∧ pairwiseEmbeddings source [A,B,C]=true ∧
 restrictionAgrees source crossed A=true ∧ restrictionAgrees source crossed B=true ∧
 restrictionAgrees source crossed C=true ∧ agreement crossed source [A,B,C]=false := by decide

theorem crossed_checked_refusal : checked crossed source 2 (some [A,B,C])=none := by decide

theorem separated_positive : checked source source 2 (some [A,B,C])=some [A,B,C] := by decide
end ContactedPairControls

-- Author integration type/axiom reports; proof text above is unchanged apart from recorded import edits.
set_option pp.universes true
#check @ContactedPairControls.local_guards_do_not_imply_global
#print axioms ContactedPairControls.local_guards_do_not_imply_global
#check @ContactedPairControls.crossed_checked_refusal
#print axioms ContactedPairControls.crossed_checked_refusal
#check @ContactedPairControls.separated_positive
#print axioms ContactedPairControls.separated_positive
