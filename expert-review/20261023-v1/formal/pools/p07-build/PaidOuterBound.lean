import PaidOuterSource
namespace OrdinaryDispatch.OuterSource
open RMAF ForestState Universal233 WholeSourceWork CoreWork
open OrdinaryDispatch.Hard2SourceWork OrdinaryDispatch.FullSourceWork
open Universal233.Hard2Overlap Universal233.PaidAssembly GenericForest.CheckCorrespondence
open Universal233.Rule5SelectedLocalWork Universal233.Rule5PendantLocalWork

def paidOuterPolynomial (N : Nat) :=62*(N+1)^3+512*(N+1)^2+64

theorem parent_lengths (S : Tree) (p r : RMAF.Vertex) (N : Nat) (sn : treeNodes S≤N) :
 (leftParent S p).length≤N ∧ (rightParent S r).length≤N ∧ (rootParent S p r).length≤N := by
 have sl:=Nat.le_trans (leaves_nodes S) sn
 exact ⟨by simpa only [subtree_labels_value,leftParent] using Nat.le_trans (subtree_labels_payload S p).1 sl,
  by simpa only [subtree_labels_value,rightParent] using Nat.le_trans (subtree_labels_payload S r).1 sl,
  Nat.le_trans (List.length_filter_le _ _) sl⟩

/-- Includes both literal predicate sites after a failed AND, even when the
second site selects hardPaid. No named body fee occurs in this theorem. -/
theorem paidOuterMeter_bound (T S : Tree) (c : CherryBranching.Candidate) (out : Result)
 (N : Nat) (tn : treeNodes T≤N) (sn : treeNodes S≤N) :
 (paidOuterMeter T S c out).work≤paidOuterPolynomial N := by
 unfold paidOuterMeter
 split
 · rename_i p r h
   have parents:=hard2ParentsMeter_bound S p r N sn
   have lengths:=parent_lengths S p r N sn
   simp only [hard2ParentsMeter_value]
   cases out with
   | pair o choice=>cases choice with
    | edge edge=>
     dsimp only
     have xl:(first o (leftParent S p) (rightParent S r) (rootParent S p r)).length≤N:=by
      cases o <;> first | exact lengths.1 | exact lengths.2.1 | exact lengths.2.2
     have yl:(second o (leftParent S p) (rightParent S r) (rootParent S p r)).length≤N:=by
      cases o <;> first | exact lengths.1 | exact lengths.2.1 | exact lengths.2.2
     have x:=meterRestrictionAgrees_bound S T (first o (leftParent S p) (rightParent S r) (rootParent S p r)) N (by omega) (by omega) xl
     have y:=meterRestrictionAgrees_bound S T (second o (leftParent S p) (rightParent S r) (rootParent S p r)) N (by omega) (by omega) yl
     split <;> dsimp only <;> simp only [paidOuterPolynomial] <;> omega
    | vertex v=>simp only [paidOuterPolynomial];omega
   | disjoint=>simp only [paidOuterPolynomial];omega
   | clique v=>simp only [paidOuterPolynomial];omega
   | diagonal o v w=>simp only [paidOuterPolynomial];omega
   | four o v w=>simp only [paidOuterPolynomial];omega
 · simp only [paidOuterPolynomial];omega
end OrdinaryDispatch.OuterSource
