import PersistentLists
namespace GenericForest.BinaryProvider
open Universal233.WholeSourceWork GenericForest.ScalarBits GenericForest.CheckCorrespondence

theorem beta_positive (W : Nat) : 1≤ScalarBits.beta W := by unfold ScalarBits.beta;omega

def containsLabel (x : Label) : Block→Charged Bool
 | []=>⟨false,1⟩
 | y::ys=>let e:=copiedEqual x y
           if e.value then ⟨true,e.work+4⟩ else
            let r:=containsLabel x ys;⟨r.value,e.work+r.work+4⟩

theorem containsLabel_projects (W : Nat) (x : Label) (L : Block)
 (xw : LabelWidth W x) (cap : BlockWidth W L) :
 Projects W id (containsLabel x L) (meterContains (labelValue x) (blockValue L)) := by
 induction L with
 | nil=>simp [Projects,containsLabel,blockValue,meterContains,ScalarBits.beta];omega
 | cons y ys ih=>
  have yw : y.length≤W:=cap y (by simp)
  have tail:=ih (fun z hz=>cap z (by simp [hz]))
  have e:=copiedEqual_work W x y xw yw
  have ev : (copiedEqual x y).value=(labelValue x==labelValue y):=copiedEqual_value x y
  simp only [Projects,id_eq,blockValue] at tail ⊢
  simp only [containsLabel,blockValue,List.map_cons,meterContains,ev]
  cases h : labelValue x==labelValue y <;> simp only [h,Bool.false_eq_true,ite_false,ite_true]
  · refine ⟨tail.1,?_⟩
    simp only [Nat.mul_add,Nat.mul_comm (ScalarBits.beta W) 4]
    unfold ScalarBits.beta at tail ⊢;omega
  · refine ⟨by trivial,?_⟩
    unfold ScalarBits.beta;omega

def allChecks {α : Type} (f : α→Charged Bool) : List α→Charged Bool
 | []=>⟨true,1⟩
 | x::xs=>let a:=f x;let r:=allChecks f xs;⟨a.value&&r.value,a.work+r.work+4⟩
def anyChecks {α : Type} (f : α→Charged Bool) : List α→Charged Bool
 | []=>⟨false,1⟩
 | x::xs=>let a:=f x;let r:=anyChecks f xs;⟨a.value||r.value,a.work+r.work+4⟩

theorem allChecks_projects {α β : Type} (W : Nat) (π : α→β) (f : α→Charged Bool) (g : β→Charged Bool)
 (L : List α) (point : ∀x∈L,Projects W id (f x) (g (π x))) :
 Projects W id (allChecks f L) (meterAll g (L.map π)) := by
 induction L with
 | nil=>simp [Projects,allChecks,meterAll,ScalarBits.beta];omega
 | cons x xs ih=>
  have a:=point x (by simp);have r:=ih (fun y hy=>point y (by simp [hy]));have p:=beta_positive W
  simp only [Projects,id_eq] at a r ⊢
  simp only [allChecks,List.map_cons,meterAll,a.1,r.1]
  refine ⟨by trivial,?_⟩
  simp only [Nat.mul_add];omega

theorem anyChecks_projects {α β : Type} (W : Nat) (π : α→β) (f : α→Charged Bool) (g : β→Charged Bool)
 (L : List α) (point : ∀x∈L,Projects W id (f x) (g (π x))) :
 Projects W id (anyChecks f L) (meterAny g (L.map π)) := by
 induction L with
 | nil=>simp [Projects,anyChecks,meterAny,ScalarBits.beta];omega
 | cons x xs ih=>
  have a:=point x (by simp);have r:=ih (fun y hy=>point y (by simp [hy]));have p:=beta_positive W
  simp only [Projects,id_eq] at a r ⊢
  simp only [anyChecks,List.map_cons,meterAny,a.1,r.1]
  refine ⟨by trivial,?_⟩
  simp only [Nat.mul_add];omega
end GenericForest.BinaryProvider
