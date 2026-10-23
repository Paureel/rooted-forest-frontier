import DerivedMinimum
namespace OrdinaryCommonSplit.GraphControls
open RMAF
open Universal233

def X : List Nat := [0,1,2]
def Y : List Nat := [3,4,5]
def tx : Tree := .node (.node (.leaf 0) (.leaf 1)) (.leaf 2)
def ty : Tree := .node (.node (.leaf 3) (.leaf 4)) (.leaf 5)
def rootT : Tree := .node (.node ty (.node (.leaf 0) (.leaf 1))) (.leaf 2)
def rootS : Tree := .node (.node tx (.node (.leaf 3) (.leaf 4))) (.leaf 5)
def markedXTree : Tree := .node (.node (.leaf 6) (.node (.leaf 0) (.leaf 1))) (.leaf 2)
def markedXOther : Tree := .node tx (.leaf 6)
def markedYTree : Tree := .node (.leaf 7) ty
def markedYOther : Tree := .node (.node (.leaf 7) (.node (.leaf 3) (.leaf 4))) (.leaf 5)

theorem mixed_original_inputs : DepthOne.proper rootT rootS=true ∧
    partitionCheck (leaves rootT) [X,Y]=true ∧ partitionCheck (leaves rootS) [X,Y]=true ∧
    agreement rootT rootS [X,Y]=true := by decide
theorem mixed_literal_cuts : Universal233.CoreGraph.subtree rootT [false,false]=some ty ∧
    Universal233.CoreGraph.subtree rootS [false,false]=some tx := by decide
theorem mixed_explicit_markers : marked rootT X 3 6=some markedXTree ∧
    marked rootS X 3 6=some markedXOther ∧ marked rootT Y 0 7=some markedYTree ∧
    marked rootS Y 0 7=some markedYOther := by decide
theorem mixed_local_zero : restrict X rootT=some tx ∧ restrict X rootS=some tx ∧
    restrict Y rootT=some ty ∧ restrict Y rootS=some ty := by decide
theorem mixed_flags_unstable : Controls.foundOne markedXTree markedXOther=true ∧
    Controls.foundOne markedYTree markedYOther=true ∧ Controls.foundOne rootT rootS=true := by decide
theorem actual_guarded_values : commonSplitValue 1 1 1 1=2 ∧ commonSplitValue 0 0 1 1=1 ∧
    commonSplitValue 1 1 1 2=3 ∧ commonSplitValue 1 1 2 1=3 := by decide
theorem mixed_projection_witness : restrictionAgrees rootT rootS [0,1,3,4]=true ∧
    restrictionAgrees rootT rootS [0,1,3]=true ∧ restrictionAgrees rootT rootS [3,4,0]=true := by decide
end OrdinaryCommonSplit.GraphControls
