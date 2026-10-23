import RSCopyBounds
namespace OrdinaryDispatch.RecoveryInitialBits
open Universal233 WholeSourceWork
open OrdinaryDispatch.RecoveryBits

/-- Abstract bit/cell scope-close traversal. It is paid even when immutable
sharing could avoid it; no native deallocator or heap mutation is asserted. -/
def closeBits : List Bool→Charged Unit
 | []=>⟨(),1⟩
 | _::bs=>let r:=closeBits bs;⟨(),r.work+4⟩
@[simp] theorem closeBits_work (bs : List Bool) : (closeBits bs).work=4*bs.length+1 := by
 induction bs <;> simp only [closeBits,List.length_nil,List.length_cons] at * <;> omega

def closeArrays : List (List Bool)→Charged Unit
 | []=>⟨(),2⟩
 | b::bs=>let a:=closeBits b;let r:=closeArrays bs;⟨(),a.work+r.work+4⟩
theorem closeArrays_work (bs : List (List Bool)) : (closeArrays bs).work≤8*(arrayCells bs+1) := by
 induction bs with
 | nil=>simp [closeArrays,arrayCells]
 | cons b bs ih=>simp only [closeArrays,closeBits_work,arrayCells,Nat.mul_add,Nat.mul_one];omega

def closeForest : List (List (List Bool))→Charged Unit
 | []=>⟨(),2⟩
 | b::bs=>let a:=closeArrays b;let r:=closeForest bs;⟨(),a.work+r.work+4⟩
theorem closeForest_work (P : List (List (List Bool))) : (closeForest P).work≤16*(forestCells P+1) := by
 induction P with
 | nil=>simp [closeForest,forestCells]
 | cons b P ih=>have a:=closeArrays_work b;simp only [closeForest,forestCells,Nat.mul_add,Nat.mul_one] at *;omega

def ownedEqual (xs ys : List Bool) : Charged Bool :=
 let a:=copyBits xs;let b:=copyBits ys;let e:=equalBits a.value b.value
 let ca:=closeBits a.value;let cb:=closeBits b.value
 ⟨e.value,a.work+b.work+e.work+ca.work+cb.work+8⟩
@[simp] theorem ownedEqual_value (xs ys : List Bool) : (ownedEqual xs ys).value=(decode xs==decode ys) := by simp [ownedEqual]
theorem ownedEqual_work (W : Nat) (xs ys : List Bool) (xw : xs.length≤W) (yw : ys.length≤W) :
 (ownedEqual xs ys).work≤96*(W+1) := by
 have a:=(scalar_width_bounds W xs ys xw yw).1
 simp only [ownedEqual,copyBits_value,copyBits_work,closeBits_work];omega

def ownedContains (x : List Bool) : List (List Bool)→Charged Bool
 | []=>⟨false,2⟩
 | y::ys=>let e:=ownedEqual x y
   if e.value then ⟨true,e.work+4⟩ else
    let r:=ownedContains x ys;⟨r.value,e.work+r.work+4⟩
@[simp] theorem ownedContains_value (x : List Bool) (ys : List (List Bool)) :
 (ownedContains x ys).value=(ys.map decode).contains (decode x) := by
 induction ys with
 | nil=>rfl
 | cons y ys ih=>simp [ownedContains,ih];split <;> simp_all

theorem ownedContains_work (W : Nat) (x : List Bool) (ys : List (List Bool))
 (xw : x.length≤W) (yw : ∀y∈ys,y.length≤W) :
 (ownedContains x ys).work≤112*(W+1)*(ys.length+1) := by
 induction ys with
 | nil=>simp only [ownedContains,List.length_nil];omega
 | cons y ys ih=>
  have e:=ownedEqual_work W x y xw (yw y (by simp))
  have tail:=ih (by intro z hz;exact yw z (by simp [hz]))
  simp only [ownedContains,List.length_cons,Nat.mul_add,Nat.mul_one] at tail ⊢
  split <;> simp only [Charged.work] <;> omega

def ownedNodup : List (List Bool)→Charged Bool
 | []=>⟨true,2⟩
 | x::xs=>let c:=ownedContains x xs;let r:=ownedNodup xs
   ⟨!c.value && r.value,c.work+r.work+4⟩
@[simp] theorem ownedNodup_value (xs : List (List Bool)) :
 (ownedNodup xs).value=decide (xs.map decode).Nodup := by
 induction xs with
 | nil=>rfl
 | cons x xs ih=>
  simp only [ownedNodup,ownedContains_value,ih,List.map_cons]
  by_cases mem:decode x∈xs.map decode <;> simp [List.contains_iff_mem,mem,List.nodup_cons]

theorem ownedNodup_work (W : Nat) (xs : List (List Bool)) (h : ∀x∈xs,x.length≤W) :
 (ownedNodup xs).work≤128*(W+1)*(xs.length+1)^2 := by
 induction xs with
 | nil=>simp only [ownedNodup,List.length_nil];omega
 | cons x xs ih=>
  have tail:=ih (by intro y hy;exact h y (by simp [hy]))
  have c:=ownedContains_work W x xs (h x (by simp)) (by intro y hy;exact h y (by simp [hy]))
  have cc:=Nat.le_trans c (Nat.mul_le_mul_right (xs.length+1) (show 112*(W+1)≤128*(W+1) by omega))
  have eq:(xs.length+1+1)^2=(xs.length+1)^2+2*(xs.length+1)+1:=by
   simp only [Nat.pow_two,Nat.mul_add,Nat.add_mul,Nat.mul_one,Nat.one_mul];omega
  have growth:128*(W+1)*(xs.length+1+1)^2=
   128*(W+1)*(xs.length+1)^2+2*(128*(W+1)*(xs.length+1))+128*(W+1):=by
   have algebra (A k : Nat) : A*(k+1)^2=A*k^2+2*(A*k)+A:=by
    simp only [Nat.pow_two,Nat.mul_add,Nat.add_mul,Nat.mul_one,Nat.one_mul,Nat.mul_assoc]
    omega
   exact algebra (128*(W+1)) (xs.length+1)
  simp only [ownedNodup,List.length_cons,growth]
  omega

def ownedColor : List (List (List Bool))→List Bool→Charged (List Bool)
 | [],_=>⟨[],2⟩
 | b::P,x=>let c:=ownedContains x b
   if c.value then let a:=copyBits (b.headD []);⟨a.value,c.work+a.work+8⟩
   else let r:=ownedColor P x;⟨r.value,c.work+r.work+8⟩
@[simp] theorem ownedColor_value (P : List (List (List Bool))) (x : List Bool) :
 decode (ownedColor P x).value=FinalCutRecovery.blockColor (P.map (List.map decode)) (decode x) := by
 induction P with
 | nil=>rfl
 | cons b P ih=>
  have head:decode (b.headD [])=(b.map decode).headD 0:=by cases b <;> rfl
  simp only [ownedColor,ownedContains_value,List.map_cons,FinalCutRecovery.blockColor]
  split <;> simp_all

theorem ownedColor_length (W : Nat) (P : List (List (List Bool))) (x : List Bool)
 (h : ForestWords W P) : (ownedColor P x).value.length≤W := by
 induction P with
 | nil=>simp [ownedColor]
 | cons b P ih=>
  have head:(b.headD []).length≤W:=by
   cases b with
   | nil=>simp
   | cons y ys=>exact h (y::ys) (by simp) y (by simp)
  have tail:=ih (by intro c hc y hy;exact h c (by simp [hc]) y hy)
  simp only [ownedColor,copyBits_value]
  split <;> assumption

theorem ownedColor_work (W : Nat) (P : List (List (List Bool))) (x : List Bool)
 (xw : x.length≤W) (h : ForestWords W P) :
 (ownedColor P x).work≤160*(W+1)*(P.flatten.length+P.length+1) := by
 induction P with
 | nil=>simp only [ownedColor,List.flatten_nil,List.length_nil];omega
 | cons b P ih=>
  have a:=ownedContains_work W x b xw (h b (by simp))
  have head:(b.headD []).length≤W:=by
   cases b with
   | nil=>simp
   | cons y ys=>exact h (y::ys) (by simp) y (by simp)
  have tail:=ih (by intro c hc y hy;exact h c (by simp [hc]) y hy)
  have scale:=Nat.mul_le_mul_right b.length (show 112*(W+1)≤160*(W+1) by omega)
  simp only [ownedColor,copyBits_work,List.flatten_cons,List.length_append,List.length_cons,Nat.mul_add,Nat.mul_one] at a tail scale ⊢
  split <;> simp only [Charged.work] <;> omega
end OrdinaryDispatch.RecoveryInitialBits
