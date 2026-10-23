import ForestCallerSetup
namespace GenericForest.BinaryProducer.BoundControls
open BinaryProvider GenericForest.ScalarBits CostControls Universal233.WholeSourceWork

def alternate : BinaryProvider.Tree := .node (.node (.leaf z) (.leaf b)) (.node (.leaf a) (.leaf c))
def crossSources : List BinaryProvider.Tree := [.node (.leaf z) (.leaf b),.node (.leaf a) (.leaf c)]
def refusal (_ _ : BinaryProvider.Tree) (_ : Bits) : Charged (Option BinaryProvider.Forest):=⟨none,777⟩

theorem concrete_receipt_truth : Generator.receiptCells (Generator.generateBits crossed parity b).value=60 ∧
 Generator.generateRetention crossed parity b=7830 := by decide +kernel

theorem actual_prefix_truth : (Generator.generateBits crossed parity []).work>0 ∧
 (Generator.generateBits crossed parity []).value.pruned.length=2 ∧
 (Generator.generateBits crossed parity b).value.visited.length=3 := by decide +kernel

theorem generated_storage_truth : (Generator.generateBits crossed parity b).value.outputs.length=2 ∧
 ((Generator.generateBits crossed parity b).value.outputs.headD ⟨[],[]⟩).partition.flatten.length=4 ∧
 ((Generator.generateBits crossed parity b).value.outputs.headD ⟨[],[]⟩).sourceCuts.length=2 := by decide +kernel

theorem forest_fixed_point_truth : forestOptionValue (forestFromInput refusal (some crossed) crossSources b).value=
 some [[0],[2],[1,3]] ∧ (forestFromInput refusal (some crossed) crossSources b).work=83028 := by decide +kernel

theorem singleton_callback_truth : (forestFromInput refusal (some crossed) [alternate] b).value=none ∧
 (forestFromInput refusal (some crossed) [alternate] b).work≥777 := by decide +kernel

theorem paid_setup_truth : (leafFuel [z,a,b,c]).value.length=4 ∧ (leafFuel [z,a,b,c]).work=17 := by decide +kernel

theorem duplicate_rejection_truth : (forestFromInput refusal (some CostControls.pair) [.leaf z,.leaf z] a).value=none := by decide +kernel

theorem crossed_width : TreeWidth 2 crossed := by
 intro x hx;simp only [crossed,TreeWidth,leavesBits,List.mem_append,List.mem_singleton] at hx
 rcases hx with (rfl|rfl)|(rfl|rfl) <;> change _ ≤ 2 <;> decide

theorem full_generation_truth : (Generator.generateBits crossed parity b).work≤Generator.generationCost 2 7 2 4*2^(decode b) := by
 apply Generator.generateBits_cost 2 7 2 4 crossed parity b crossed_width (by decide) (by decide) (by decide)
 intro x hx;exact Nat.le_refl _

theorem full_retention_truth : Generator.generateRetention crossed parity b≤Generator.retentionCost 2 7 2 4*2^(decode b) := by
 apply Generator.generateRetention_bound 2 7 2 4 crossed parity b crossed_width (by decide) (by decide) (by decide)
 intro x hx;exact Nat.le_refl _

theorem generated_caps_truth : ∀io∈(branchesProducer crossed [crossed] repeated q8).value,
 BranchCaps (Generator.inputResource 7) 2 1 (Generator.inputResource 7) (Generator.inputResource 7+1) io := by
 apply branchesProducer_caps 2 7 1 crossed [crossed] repeated q8
 · intro s hs;have e:=List.mem_singleton.mp hs;subst s;exact crossed_width
 · intro s hs;have e:=List.mem_singleton.mp hs;subst s;decide
 · decide
 · decide

theorem leaf_width (x : Bits) (h : x.length≤2) : TreeWidth 2 (.leaf x) := by
 intro y hy
 have e : y=x:=by simpa only [leavesBits,List.mem_singleton] using hy
 subst y
 exact h

theorem overlap_paid_truth : (overlapProducer crossed [.leaf z,.leaf z,.leaf a]).work≤overlapCost 7 2 3 ∧
 (overlapProducer crossed [.leaf z,.leaf z,.leaf a]).work>0 := by
 constructor
 · apply overlapProducer_cost 7 2 3 crossed [.leaf z,.leaf z,.leaf a] crossed_width (by decide)
   · intro s hs;rcases List.mem_cons.mp hs with rfl|hs
     · exact leaf_width z (by decide)
     · rcases List.mem_cons.mp hs with rfl|hs
       · exact leaf_width z (by decide)
       · have e:=List.mem_singleton.mp hs;subst s
         exact leaf_width a (by decide)
   · intro s hs;rcases List.mem_cons.mp hs with rfl|hs
     · decide
     · rcases List.mem_cons.mp hs with rfl|hs
       · decide
       · have e:=List.mem_singleton.mp hs;subst s;decide
   · decide
 · decide +kernel
end GenericForest.BinaryProducer.BoundControls
