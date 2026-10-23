import StoredClassifierInterface
set_option maxRecDepth 8192
namespace OrdinaryDispatch.StoredNumeric.ClassifierReach.Controls
open GenericForest.ScalarBits GenericForest.BinaryProvider GenericForest.BinaryProducer
open OrdinaryDispatch.StoredNumeric.ProducerBinding Universal233.WholeSourceWork
abbrev a : Bits:=[true,false,false]
abbrev b : Bits:=[false,true,false]
abbrev c3 : Bits:=[true,true]
abbrev c4 : Bits:=[false,false,true]
abbrev c5 : Bits:=[true,false,true]
abbrev c6 : Bits:=[false,true,true,false,false]
def sourceBad : GenericForest.BinaryProvider.Tree:=.node (.node (.leaf a) (.node (.node (.leaf c3) (.leaf c4)) (.leaf c5))) (.node (.leaf b) (.leaf c6))
def targetBad : GenericForest.BinaryProvider.Tree:=.node (.node (.leaf a) (.leaf b)) (.node (.node (.leaf c3) (.leaf c5)) (.node (.leaf c4) (.leaf c6)))

theorem padded_cherry_order :
 (cherriesBits targetBad).value.map (fun c=>(c.parent,c.a,c.b))=[([false],a,b),([true,false],c3,c5),([true,true],c4,c6)] := by cbv

theorem actual_bad_selection :
 (selectBadBits targetBad sourceBad a b).value.map (fun d=>(d.badArc,d.singletonArc,d.c))=some ([false,true],[true,true],c6) := by cbv

theorem bad_equal_refuses : (badAtBits targetBad sourceBad [false,true] [false,true]).value=none := by cbv
theorem bad_missing_singleton_refuses : (badAtBits targetBad sourceBad [false,true] [true,true,true]).value=none := by cbv
theorem bad_nonleaf_singleton_refuses : (badAtBits targetBad sourceBad [false,true] []).value=none := by cbv
theorem agreeing_source_refuses : (selectBadBits sourceBad sourceBad a b).value=none := by cbv

def duplicateList : Addresses:=[[true,true],[true,true]]
theorem duplicate_bad_candidates_retained : (badFor targetBad sourceBad [false,true] duplicateList).value.length=2 := by cbv

def commonT : GenericForest.BinaryProvider.Tree:=.node (.node (.leaf c5) (.leaf c6)) (.node (.node (.leaf a) (.leaf b)) (.node (.leaf c3) (.leaf c4)))
def commonS : GenericForest.BinaryProvider.Tree:=.node (.node (.leaf c5) (.leaf c6)) (.node (.node (.leaf a) (.leaf c3)) (.node (.leaf b) (.leaf c4)))
def commonCandidate : CandidateBits:=⟨[false],c5,c6,[]⟩
def paddedBudget : Bits:=[true,false,false,false]

theorem common_priority_actual : (selectPriorityBits commonT commonS).value=some (.common,commonCandidate) := by cbv

theorem actual_common_pretest : Universal233.DepthOne.pretest01 (treeValue commonT) (treeValue commonS)=.rejected := by cbv

theorem actual_common_event (rec : Nat→RMAF.Tree→RMAF.Tree→Option OrdinaryDispatch.CommonForest) :
 let p:=(contractPairBits c5 c6 commonT commonS).value
 BoundEvent rec commonT commonS paddedBudget p.1 p.2 [true] := by
 apply common_bound_event rec commonT commonS paddedBudget false commonCandidate
 · decide +kernel
 · exact actual_common_pretest
 · cbv
 · exact common_priority_actual

theorem actual_matched_depth (rec : Nat→RMAF.Tree→RMAF.Tree→Option OrdinaryDispatch.CommonForest) :
 let p:=(contractPairBits c5 c6 commonT commonS).value
 OrientedPath commonT commonS 1 p.1 p.2 ∧
 OrdinaryDispatch.GlobalNumeric.Reach rec 1 (treeValue commonT) (treeValue commonS) 1 (treeValue p.1) (treeValue p.2) 1 := by
 exact bound_path_bridge rec paddedBudget commonT commonS (BoundPath.next BoundPath.root (actual_common_event rec))

theorem initial_padding_separate : paddedBudget.length=4 ∧ decode paddedBudget=1 ∧ (trimBudget paddedBudget).value.length=1 := by decide
end OrdinaryDispatch.StoredNumeric.ClassifierReach.Controls
