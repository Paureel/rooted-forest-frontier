import RILifetime
namespace OrdinaryDispatch.RecoveryControlBits
open Universal233 WholeSourceWork CoreProgram CoreWork
open OrdinaryDispatch.RecoveryBits OrdinaryDispatch.RecoveryInitialBits

def GroupCap (W N : Nat) (g : BitGroup) : Prop :=
 (∀x∈g.labels,x.length≤W) ∧ g.color.length≤W ∧ footprint (viewTree (.leaf g))≤N

def GroupCaps (W N : Nat) (gs : List BitGroup) : Prop := ∀g∈gs,GroupCap W N g

def rawGroups : BitTree→List BitGroup
 | .leaf g=>[g]
 | .node _ l r=>rawGroups l++rawGroups r
@[simp] theorem rawGroups_view (t : BitTree) : (rawGroups t).map viewGroup=groups (viewTree t) := by
 induction t <;> simp_all [rawGroups,viewTree,groups,List.map_append]
theorem rawGroups_length (t : BitTree) : (rawGroups t).length≤footprint (viewTree t) := by
 have h:=CoreWork.groups_length (viewTree t)
 rw [←rawGroups_view,List.length_map] at h
 exact h

theorem rawGroups_caps (W N : Nat) (t : BitTree) (words : TreeWords W t) (size : footprint (viewTree t)≤N) : GroupCaps W N (rawGroups t) := by
 induction t with
 | leaf g=>intro a ha;have eq:a=g:=by simpa [rawGroups] using ha
            subst a;exact ⟨words.1,words.2,size⟩
 | node p l r il ir=>
  have ls:footprint (viewTree l)≤N:=by simp only [viewTree,footprint] at size;omega
  have rs:footprint (viewTree r)≤N:=by simp only [viewTree,footprint] at size;omega
  intro g hg;rcases List.mem_append.mp hg with hg|hg
  · exact il words.1 ls g hg
  · exact ir words.2 rs g hg

/-- Derived generic copied-group/list-step envelope, never a runtime fee. -/
def groupFee (W N : Nat) : Nat :=64*(W+4)*(N+1)
theorem groupFee_positive (W N : Nat) : 64≤groupFee W N := by
 have p:1≤(W+4)*(N+1):=by simpa only [Nat.one_mul] using Nat.mul_le_mul (show 1≤W+4 by omega) (show 1≤N+1 by omega)
 have s:=Nat.mul_le_mul_left 64 p
 simpa only [groupFee,Nat.mul_assoc,Nat.mul_one] using s

theorem group_cells_cap (W N : Nat) (g : BitGroup) (h : GroupCap W N g) : groupCells g≤(W+4)*N := by
 have a:=treeCells_source_bound W (.leaf g) ⟨h.1,h.2.1⟩
 have b:=Nat.mul_le_mul_left (W+4) h.2.2
 simp only [treeCells] at a
 omega

theorem copied_group_fee (W N : Nat) (g : BitGroup) (h : GroupCap W N g) : (copyGroup g).work+4≤groupFee W N := by
 have a:=copyGroup_work g;have b:=group_cells_cap W N g h
 have c:=Nat.mul_le_mul_left 32 b
 have pos:1≤W+4:=by omega
 simp only [groupFee,Nat.mul_add,Nat.mul_one,Nat.mul_assoc] at c ⊢
 omega

theorem closed_group_fee (W N : Nat) (g : BitGroup) (h : GroupCap W N g) : (closeGroup g).work+4≤groupFee W N := by
 have a:=closeGroup_work g;have b:=group_cells_cap W N g h
 have c:=Nat.mul_le_mul_left 32 b
 simp only [groupFee,Nat.mul_add,Nat.mul_one,Nat.mul_assoc] at c ⊢
 omega

def closeGroups : List BitGroup→Charged Unit
 | []=>⟨(),2⟩
 | g::gs=>let a:=closeGroup g;let b:=closeGroups gs;⟨(),a.work+b.work+4⟩
theorem closeGroups_work (W N : Nat) (gs : List BitGroup) (caps : GroupCaps W N gs) :
 (closeGroups gs).work≤groupFee W N*(gs.length+1) := by
 have pos:=groupFee_positive W N
 induction gs with
 | nil=>simp only [closeGroups,List.length_nil,Nat.zero_add,Nat.mul_one];omega
 | cons g gs ih=>
  have a:=closed_group_fee W N g (caps g (by simp))
  have b:=ih (by intro x hx;exact caps x (by simp [hx]))
  simp only [closeGroups,List.length_cons,Nat.mul_add,Nat.mul_one] at b ⊢
  omega

def groupsBits : BitTree→Charged (List BitGroup)
 | .leaf g=>let c:=copyGroup g;⟨[c.value],c.work+4⟩
 | .node _ l r=>let a:=groupsBits l;let b:=groupsBits r;let j:=appendRefs a.value b.value;let c:=closeSpine a.value
   ⟨j.value,a.work+b.work+j.work+c.work+8⟩
@[simp] theorem groupsBits_value (t : BitTree) : (groupsBits t).value=rawGroups t := by
 induction t <;> simp_all [groupsBits,rawGroups]

theorem groupsBits_work_nodes (W N : Nat) (t : BitTree) (words : TreeWords W t) (size : footprint (viewTree t)≤N) :
 (groupsBits t).work≤groupFee W N*bitNodes t := by
 have shape:64*(N+1)≤groupFee W N:=by
  exact Nat.mul_le_mul_right (N+1) (by simp only [groupFee];omega)
 induction t with
 | leaf g=>simpa only [groupsBits,bitNodes,Nat.mul_one] using copied_group_fee W N g ⟨words.1,words.2,size⟩
 | node p l r il ir=>
  have ls:footprint (viewTree l)≤N:=by simp only [viewTree,footprint] at size;omega
  have rs:footprint (viewTree r)≤N:=by simp only [viewTree,footprint] at size;omega
  have a:=il words.1 ls;have b:=ir words.2 rs
  have len:=Nat.le_trans (rawGroups_length l) ls
  have expand (A l r : Nat) : A*(1+l+r)=A*l+A*r+A:=by simp only [Nat.mul_add,Nat.mul_one];omega
  simp only [groupsBits,groupsBits_value,appendRefs_work,closeSpine_work,bitNodes,expand]
  omega

theorem groupsBits_work (W N : Nat) (t : BitTree) (words : TreeWords W t) (size : footprint (viewTree t)≤N) :
 (groupsBits t).work≤groupFee W N*N :=
 Nat.le_trans (groupsBits_work_nodes W N t words size)
  (Nat.mul_le_mul_left (groupFee W N) (Nat.le_trans (bitNodes_footprint t) size))
end OrdinaryDispatch.RecoveryControlBits
