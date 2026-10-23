import ProducerBindingInterface
import ProducerBindingControls
set_option maxRecDepth 8192
namespace OrdinaryDispatch.StoredNumeric.ProducerBinding.Controls
open GenericForest.ScalarBits GenericForest.BinaryProvider GenericForest.BinaryProducer Universal233.WholeSourceWork
abbrev one : Bits := [true]
abbrev two : Bits := [false,true]
abbrev three : Bits := [true,true]
abbrev four : Bits := [false,false,true]
def source : GenericForest.BinaryProvider.Tree := .node (.node (.leaf one) (.leaf four)) (.node (.leaf two) (.leaf three))
def target : GenericForest.BinaryProvider.Tree := .node (.node (.leaf one) (.leaf two)) (.node (.leaf three) (.leaf four))
def bad : Universal233.Rule5FinalClassification.BadSelection:=⟨[false,true],[true,true],3⟩

theorem common_selector_order :
 (commonSelectorsBits source one two three bad.badArc).value.X=[four] ∧
 (commonSelectorsBits source one two three bad.badArc).value.Y=[one,two,three] ∧
 (commonSelectorsBits source one two three bad.badArc).value.x=four ∧
 (commonSelectorsBits source one two three bad.badArc).value.y=one := by cbv

theorem actual_builder_heads :
 ((OrdinaryCommonSplit.Source.buildSetup (treeValue target) (treeValue source) [4] [1,2,3] bad.badArc).map (fun d=>(d.x,d.y,d.rho,d.gamma))).getD (0,0,0,0)=(4,1,5,6) := by cbv

theorem empty_head_zero : (headRepresentative []).value=[] ∧ decode (headRepresentative []).value=0 := by decide

def identityBudget (_ : Unit) (q : Bits) : Charged (Option (Bits×Unit)) :=⟨some (q,()),7⟩
def refusalBudget (_ : Unit) (_ : Bits) : Charged (Option (Bits×Unit)) :=⟨none,7⟩

theorem scheduler_callback_canonical :
 (scheduleCanonical identityBudget [false,false,false,true,false,false] [.hard ()]).value.answers=some [([false,false,false,true],())] := by cbv

theorem scheduler_early_refusal :
 (scheduleCanonical refusalBudget [false,false,false,true,false,false] [.hard (),.hard ()]).value.calls.length=1 ∧
 (scheduleCanonical refusalBudget [false,false,false,true,false,false] [.hard (),.hard ()]).value.answers=none := by cbv

def rawIdentity (_ : Option GenericForest.BinaryProvider.Tree) (_ : List GenericForest.BinaryProvider.Tree) (q : Bits) : Charged (Option GenericForest.BinaryProvider.Forest):=⟨some [[q]],7⟩
def occurrence : Bits×Output := ([],⟨[],[[false]]⟩)
def rejectedOccurrence : Bits×Output := ([],⟨[],[]⟩)

theorem raw_duplicate_and_rejected :
 (rawCandidates (rawCallbackCanonical rawIdentity) none [] [false,true,false,false] [occurrence,rejectedOccurrence,occurrence]).value=[[[[true]]],[[[true]]]] ∧
 rawCanonicalTrimWork [false,true,false,false] [occurrence,rejectedOccurrence,occurrence]=74 ∧
 rawCanonicalSolveWork rawIdentity none [] [false,true,false,false] [occurrence,rejectedOccurrence,occurrence]=14 := by cbv

theorem input_padding_paid :
 (canonicalCall (fun q=>⟨q,7⟩) (List.replicate 1024 false)).work=8204 := by decide

theorem common_payload_width_control :
 (commonSelectedPayload target source one two three bad.badArc).value.rho=[true,false,true] ∧
 (commonSelectedPayload target source one two three bad.badArc).value.gamma=[false,true,true] := by cbv
end OrdinaryDispatch.StoredNumeric.ProducerBinding.Controls
