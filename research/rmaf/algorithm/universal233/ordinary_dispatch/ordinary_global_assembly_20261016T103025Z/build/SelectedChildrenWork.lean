import SiblingChildrenWork
import SelectedInterfaces
namespace Universal233.Rule5SelectedLocalWork
open RMAF CoreGraph HardParent Rule5PrefixLocalWork Rule5PendantLocalWork
open CherryBranching CoreWork Rule5Classification Rule5FinalClassification Rule5SourceOrientation
open Rule5OrdinaryDispatch

def selectedChildrenMeter (S : Tree) (a b : Nat) : FinalSelection→Measured (List Child)
 | .prefix s=>localChildrenMeter S a b s
 | .remaining d (.first _ _)=>firstChildrenMeter S a b d
 | .remaining d (.third _ _)=>thirdChildrenMeter S a b d
 | _=>⟨[],1⟩

theorem selected_children_value (S : Tree) (a b : Nat) (z : FinalSelection) :
 (selectedChildrenMeter S a b z).value=selectedForestChildren S a b z := by
 cases z with
 | «prefix» s=>exact local_children_value S a b s
 | remaining d z=>cases z <;> simp only [selectedChildrenMeter,selectedForestChildren,first_children_value,third_children_value]

def selectedChildrenBudget (n : Nat) :=fiveChildrenBudget n+siblingChildrenBudget n n+3

theorem selected_children_work (fee : CheckRequest→Nat) (T S : Tree) (a b : Nat) {z : FinalSelection}
 (sel : (finalMeter fee T S a b).value=some z) :
 (selectedChildrenMeter S a b z).work≤selectedChildrenBudget (leaves S).length := by
 have payload:=final_payload fee T S a b sel
 cases z with
 | «prefix» s=>
  have w:=local_children_work S a b s
  simp only [selectedChildrenMeter]
  unfold selectedChildrenBudget
  omega
 | remaining d z=>
  have cap : d.badArc.length≤(leaves S).length := by have:=payload.1;omega
  have monotone : siblingChildrenBudget (leaves S).length d.badArc.length≤
   siblingChildrenBudget (leaves S).length (leaves S).length := by unfold siblingChildrenBudget;omega
  cases z with
  | one q=>simp only [selectedChildrenMeter];unfold selectedChildrenBudget;omega
  | second q r=>simp only [selectedChildrenMeter];unfold selectedChildrenBudget;omega
  | first q r=>
   have w:=first_children_work S a b d
   simp only [selectedChildrenMeter]
   unfold selectedChildrenBudget
   omega
  | third q r=>
   have w:=third_children_work S a b d
   simp only [selectedChildrenMeter]
   unfold selectedChildrenBudget
   omega

/-- The sum counts actual materialized tree cells, including every source
component. A tree contributes fewer nodes than twice its leaf count. -/
theorem forest_nodes_le_leaves (ss : List Tree) :
 (ss.map treeNodes).sum≤2*(ss.map leaves).flatten.length := by
 induction ss with
 | nil=>simp
 | cons s ss ih=>
  have n:=treeNodes_le_twice_leaves s
  simp only [List.map_cons,List.sum_cons,List.flatten_cons,List.length_append]
  omega

/-- These are payload conclusions of actual selected source checks; no bounded
forest is supplied as a desired local-work premise. -/
theorem selected_child_payload (fee : CheckRequest→Nat) {T S : Tree} {i : RMAF.Vertex} {a b : Nat} {z : FinalSelection}
 (ch : CherryAt T i a b) (ad : Rule5Local.admitted T S a b=true)
 (sel : (finalMeter fee T S a b).value=some z) {c : Child}
 (mem : c∈(selectedChildrenMeter S a b z).value) :
 c.partition.flatten.length=(leaves S).length ∧ c.partition.length≤(leaves S).length ∧
 c.sourceForest.length=c.partition.length ∧
 (c.sourceForest.map treeNodes).sum≤2*(leaves S).length ∧
 (∀x,x∈c.partition.flatten →x∈leaves S) ∧
 (∀U,U∈c.sourceForest →treeNodes U≤treeNodes S ∧ leaves U⊆leaves S) := by
 rw [selected_children_value] at mem
 rw [final_value] at sel
 have facts:=(selected_forest_facts ch ad sel mem).1
 have proper:=properPair_parts (admitted_parts ad).1
 have perm:=FinalCutRecovery.checked_flatten_perm S c.partition proper.2.1 facts.1
 have blocks:=FinalCutRecovery.blocks_le_flatten c.partition
  (fun B hB=>RestrictionBridge.checked_nonempty _ _ facts.1 B hB)
 have mat:=OutputState.checked_materialization S c.partition proper.2.1 facts.1
 rw [←facts.2.2.2.1] at mat
 have leavesLen : (c.sourceForest.map leaves).flatten.length=(leaves S).length :=
  mat.2.1.length_eq.trans perm.length_eq
 have nodes:=forest_nodes_le_leaves c.sourceForest
 have plen:=perm.length_eq
 refine ⟨plen,by omega,mat.1,by omega,?_,?_⟩
 · intro x hx
   exact SourceCoverage.partitionCheck_subset _ _ facts.1 hx
 · intro U hU
   obtain ⟨B,hB,hres,hl,hnd,hne⟩:=mat.2.2 U hU
   have labs:=RestrictionBridge.restrict_labels S U B hres
   exact ⟨GenericForest.CheckCorrespondence.restricted_nodes B S U hres,
    by rw [labs];exact fun x hx=>(List.mem_filter.1 hx).1⟩

theorem selected_child_label_bits (fee : CheckRequest→Nat) {T S : Tree} {i : RMAF.Vertex} {a b L : Nat} {z : FinalSelection}
 (ch : CherryAt T i a b) (ad : Rule5Local.admitted T S a b=true)
 (sel : (finalMeter fee T S a b).value=some z) (slabs : ∀x,x∈leaves S →x<2^L)
 {c : Child} (mem : c∈(selectedChildrenMeter S a b z).value) :
 (∀x,x∈c.partition.flatten →x<2^L) ∧
 (∀U,U∈c.sourceForest →∀x,x∈leaves U →x<2^L) := by
 have p:=selected_child_payload fee ch ad sel mem
 exact ⟨fun x hx=>slabs x (p.2.2.2.2.1 x hx),
  fun U hU x hx=>slabs x ((p.2.2.2.2.2 U hU).2 hx)⟩
end Universal233.Rule5SelectedLocalWork
