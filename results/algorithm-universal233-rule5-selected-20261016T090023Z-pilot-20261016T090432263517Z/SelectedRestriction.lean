import ClassifierPayload
import TreeCheckMeters
import SelectedConsumers
import GroupRestriction
namespace Universal233.Rule5SelectedLocalWork
open RMAF CoreGraph HardParent Rule5PrefixLocalWork Rule5PendantLocalWork
open CherryBranching CoreWork GenericForest.CheckCorrespondence

/-- Reuse the frozen exact RMAF.restrict meter. No second restriction recursion
is defined here. Both successful and failed block occurrences are evaluated. -/
def sourceForestMeter (S : Tree) : List (List Nat)→Measured (List Tree)
 | []=>⟨[],1⟩
 | B::P=>let t:=meterRestrict B S;let r:=sourceForestMeter S P
           ⟨match t.value with | none=>r.value | some U=>U::r.value,t.work+r.work+3⟩

theorem source_forest_value (S : Tree) (P : List (List Nat)) :
 (sourceForestMeter S P).value=P.filterMap (fun B=>restrict B S) := by
 induction P with
 | nil=>rfl
 | cons B P ih=>simp only [sourceForestMeter,List.filterMap_cons,meterRestrict_value,ih];split <;> simp_all

theorem source_forest_work (S : Tree) (P : List (List Nat)) (N : Nat)
 (blocks : ∀B,B∈P →B.length≤N) :
 (sourceForestMeter S P).work≤(4*(N+2)*treeNodes S+3)*P.length+1 := by
 induction P with
 | nil=>simp [sourceForestMeter]
 | cons B P ih=>
  have c:=meterRestrict_bound B S
  have scaled:=Nat.mul_le_mul_right (treeNodes S) (Nat.mul_le_mul_left 4 (Nat.add_le_add_right (blocks B (by simp)) 2))
  have tail:=ih (fun C hc=>blocks C (by simp [hc]))
  simp only [sourceForestMeter,List.length_cons,Nat.mul_succ]
  omega

theorem source_forest_count (S : Tree) (P : List (List Nat)) :
 (sourceForestMeter S P).value.length≤P.length := by
 rw [source_forest_value]
 exact List.length_filterMap_le _ _

theorem source_forest_payload (S : Tree) (P : List (List Nat)) {U : Tree}
 (mem : U∈(sourceForestMeter S P).value) :
 treeNodes U≤treeNodes S ∧ (leaves U).length≤(leaves S).length ∧ leaves U⊆leaves S := by
 rw [source_forest_value] at mem
 obtain ⟨B,hB,hU⟩:=List.mem_filterMap.1 mem
 have labs:=RestrictionBridge.restrict_labels S U B hU
 exact ⟨restricted_nodes B S U hU,by rw [labs];exact List.length_filter_le _ _,
  by rw [labs];exact List.filter_subset _ _⟩

def makeChildMeter (S : Tree) (P : List (List Nat)) (paid : Nat) : Measured Child :=
 let fs:=sourceForestMeter S P;⟨⟨P,fs.value,paid⟩,fs.work+4⟩

theorem make_child_value (S : Tree) (P : List (List Nat)) (paid : Nat) :
 (makeChildMeter S P paid).value=makeChild S P paid := by
 simp only [makeChildMeter,source_forest_value,makeChild]

theorem make_child_work (S : Tree) (P : List (List Nat)) (paid N : Nat)
 (blocks : ∀B,B∈P →B.length≤N) :
 (makeChildMeter S P paid).work≤(4*(N+2)*treeNodes S+3)*P.length+5 := by
 have:=source_forest_work S P N blocks
 simp only [makeChildMeter]
 omega

/-- PendantChild evaluates its partition and then its separate paid-cut count
before materializing restrictions. Reused equal lists are not free inputs. -/
def pendantChildMeter (S : Tree) (a b : Nat) : Measured Child :=
 let p:=partitionMeter S a b;let c:=cutsMeter S a b
 let child:=makeChildMeter S p.value c.value.length
 ⟨child.value,p.work+c.work+c.value.length+child.work+2⟩

theorem pendant_child_value (S : Tree) (a b : Nat) :
 (pendantChildMeter S a b).value=pendantChild S a b := by
 simp only [pendantChildMeter,make_child_value,partition_value,cuts_value,pendantChild]

def pendantChildBudget (n : Nat) :=partitionBudget n+cutsBudget n+2*n+
 (4*(n+2)*(2*n)+3)*(2*n+1)+7

theorem pendant_child_work (S : Tree) (a b : Nat) :
 (pendantChildMeter S a b).work≤pendantChildBudget (leaves S).length := by
 have p:=partition_work S a b
 have c:=cuts_work S a b
 have cn:=cuts_count S a b
 have pd:=partition_domain S a b
 have child:=make_child_work S (partitionMeter S a b).value (cutsMeter S a b).value.length (leaves S).length
  (fun B hB=>(partition_block_domain S a b hB).1)
 have nodes:=treeNodes_le_twice_leaves S
 have factor:=Nat.mul_le_mul_left (4*((leaves S).length+2)) (show treeNodes S≤2*(leaves S).length by omega)
 have slots:=Nat.mul_le_mul (Nat.add_le_add_right factor 3) pd.1
 simp only [pendantChildMeter,pendantChildBudget]
 omega
end Universal233.Rule5SelectedLocalWork
