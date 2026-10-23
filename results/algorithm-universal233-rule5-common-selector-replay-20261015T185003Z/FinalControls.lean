import FinalInterface
import ClassificationControls
namespace Universal233.Rule5FinalClassification.Controls
open RMAF CoreGraph Integration HardParent CherryBranching Rule5Local Rule5Local.Pre Rule5Classification
open Rule5Classification.Controls
set_option maxRecDepth 10000

def rootT : Tree := .node (.node (.node (.node (.leaf 6)
 (.node (.node (.leaf 3) (.node (.node (.leaf 0) (.leaf 1)) (.leaf 2))) (.leaf 4))) (.leaf 7)) (.leaf 5)) (.leaf 8)
theorem six_actual : CherryAt sixT [false,false,false,true] 0 1 := rfl
theorem first_actual : CherryAt firstT [false,false] 0 1 := rfl
theorem third_actual : CherryAt thirdT [true,true,true,true,true] 0 1 := rfl
theorem common_actual : CherryAt commonT [true,false] 0 1 := rfl
theorem root_actual : CherryAt rootT [false,false,false,true,false,true,false] 0 1 := rfl
theorem root_admitted : admitted rootT commonS 0 1=true := by decide
theorem six_final : selectFinal sixT sixS 0 1=some (.remaining ⟨[false,false,true],[false,true],2⟩
 (.second [false,true] [false,false,false,true])) := by decide
theorem first_final : selectFinal firstT firstS 0 1=some (.remaining ⟨[false,false,false,true],[false,false,true],2⟩
 (.first [false,true,true,true,true,true] [false,true])) := by decide
theorem third_final : selectFinal thirdT thirdS 0 1=some (.remaining ⟨[false,false,true],[false,true],2⟩
 (.third [true] [true,true,true,true,true])) := by decide
theorem common_final : selectFinal commonT commonS 0 1=some (.remaining ⟨[false,false,true],[false,true],2⟩ (.one [false])) := by decide
theorem root_final : selectFinal rootT commonS 0 1=some (.remaining ⟨[false,false,true],[false,true],2⟩
 (.one [false,false,false,true,false,true])) := by decide
theorem root_mirror_admitted : admitted (mirror rootT) (mirror commonS) 1 0=true := by decide
theorem root_mirror_final_present : (selectFinal (mirror rootT) (mirror commonS) 1 0).isSome=true := by decide
theorem six_mirror_final_present : (selectFinal (mirror sixT) (mirror sixS) 1 0).isSome=true := by decide
theorem first_mirror_final_present : (selectFinal (mirror firstT) (mirror firstS) 1 0).isSome=true := by decide
theorem third_mirror_final_present : (selectFinal (mirror thirdT) (mirror thirdS) 1 0).isSome=true := by decide

theorem six_universal_source : SourceGeometry sixS 0 1 ⟨[false,false,true],[false,true],2⟩ :=
 (final_selected_sound six_actual six_admitted six_final).2.2.1
theorem first_universal_source : SourceGeometry firstS 0 1 ⟨[false,false,false,true],[false,false,true],2⟩ :=
 (final_selected_sound first_actual first_admitted first_final).2.2.1
theorem root_actual_common_witness :
 ∃w,commonSplit? rootT commonS 0 1 (subtreeLabels commonS [false,false,true])=some w ∧
 w.targetArc=[false,false,false,true,false,true] ∧
 Valid rootT w.targetArc ∧ w.targetArc≠[] ∧ Valid commonS w.sourceArc ∧ w.sourceArc≠[] ∧
 (∀x,x∈subtreeLabels commonS w.sourceArc ↔ x∈subtreeLabels commonS [false,false,true]) ∧
 ((∀x,x∈leaves rootT → (x∈subtreeLabels commonS [false,false,true] ↔ x∈subtreeLabels rootT w.targetArc)) ∨
  (∀x,x∈leaves rootT → (x∈subtreeLabels commonS [false,false,true] ↔ x∉subtreeLabels rootT w.targetArc))) :=
 final_one_emits root_actual root_admitted root_final
theorem third_universal_root : ∃s U, [true]=[s] ∧ thirdT=fork s U (.leaf 2) :=
 final_third_root third_actual third_admitted third_final

def V : Tree := .node (.node (.node (.node (.leaf 6) (.node (.leaf 3) (.leaf 4))) (.leaf 7)) (.leaf 5)) (.leaf 8)
def W : Tree := .node (.node (.node (.leaf 3) (.node (.leaf 6) (.node (.leaf 7) (.leaf 8)))) (.leaf 5)) (.leaf 4)
def noRule4T : Tree := .node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 2) V)
def noRule4S : Tree := .node (.node (.leaf 0) (.leaf 2)) (.node (.leaf 1) W)
theorem missing_noRule4_priority : earlierClear noRule4T noRule4S && earlierClear noRule4S noRule4T=true := by decide
theorem missing_noRule4_hits : rule4 noRule4T noRule4S=true := by decide
theorem missing_noRule4_scope : properPair noRule4T noRule4S &&
 pairwiseEmbeddings noRule4T (pendantPartition noRule4S 0 1) &&
 pairwiseEmbeddings noRule4S (pendantPartition noRule4S 0 1)=true := by decide
theorem missing_noRule4_not_admitted : admitted noRule4T noRule4S 0 1=false := by decide
def overlapT : Tree := .node (.node (.leaf 14) (.node (.leaf 0) (.leaf 1)))
 (.node (.leaf 15) (.node (.leaf 12) (.node (.leaf 16) (.leaf 2))))
def overlapS : Tree := .node (.node (.node (.node (.leaf 0) (.node (.node (.leaf 14) (.leaf 15)) (.leaf 16))) (.leaf 2)) (.leaf 1)) (.leaf 12)
theorem missing_clearance_three : (incident overlapT [14,15,16]).length=3 := by decide
theorem missing_clearance_rejected : pairwiseEmbeddings overlapT (pendantPartition overlapS 0 1)=false := by decide
end Universal233.Rule5FinalClassification.Controls
