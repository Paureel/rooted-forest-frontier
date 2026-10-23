import RSBounds
namespace OrdinaryDispatch.RecoveryBits
open Universal233 WholeSourceWork

def minBits (xs ys : List Bool) : Charged (List Bool) :=
 let r:=compareBits xs ys
 let c:=copyBits (if r.value=.greater then ys else xs)
 ⟨c.value,r.work+c.work+4⟩
@[simp] theorem minBits_value (xs ys : List Bool) :
 decode (minBits xs ys).value=min (decode xs) (decode ys) := by
 have h:=compareBits_spec xs ys
 cases hr:(compareBits xs ys).value <;> simp only [hr,OrderSpec] at h <;>
  simp [minBits,hr] <;> omega

theorem minBits_length (W : Nat) (xs ys : List Bool) (xl : xs.length≤W) (yl : ys.length≤W) :
 (minBits xs ys).value.length≤W := by
 simp only [minBits,copyBits_value]
 split <;> assumption

theorem minBits_work (W : Nat) (xs ys : List Bool) (xl : xs.length≤W) (yl : ys.length≤W) :
 (minBits xs ys).work≤32*(W+1) := by
 have h:=compareBits_work xs ys
 have out:(if (compareBits xs ys).value=Order.greater then ys else xs).length≤W:=by split <;> assumption
 simp only [minBits,copyBits_work];omega

/-- Supplied finite-bit budget; actual list-length, saturated subtract and min.
There is no Nat-to-bits conversion inside this producer. -/
def clipBudget {α : Type} (W : Nat) (budget : List Bool) (leaves : List α) : Charged (List Bool) :=
 let n:=lengthBits W leaves
 let s:=subtractBits n.value [true]
 let m:=minBits budget s.value
 ⟨m.value,n.work+s.work+m.work+12⟩
@[simp] theorem clipBudget_value {α : Type} (W : Nat) (budget : List Bool) (leaves : List α)
 (fits : leaves.length<2^W) :
 decode (clipBudget W budget leaves).value=min (decode budget) (leaves.length-1) := by
 simp [clipBudget,lengthBits_value W leaves fits,decode,bit]

theorem clipBudget_work {α : Type} (W : Nat) (budget : List Bool) (leaves : List α)
 (positive : 1≤W) (bw : budget.length≤W) :
 (clipBudget W budget leaves).work≤160*(W+1)*(leaves.length+1) := by
 have nw:=lengthBits_length W leaves
 have sw:=subtractBits_length (lengthBits W leaves).value [true]
 have subWidth:(subtractBits (lengthBits W leaves).value [true]).value.length≤W:=by simp only [List.length_cons,List.length_nil] at sw;omega
 have a:=lengthBits_work W leaves positive
 have b:=(scalar_width_bounds W (lengthBits W leaves).value [true] nw (by simpa)).2.2.2
 have c:=minBits_work W budget (subtractBits (lengthBits W leaves).value [true]).value bw subWidth
 have p:W+1≤(W+1)*(leaves.length+1):=by simpa only [Nat.mul_one] using Nat.mul_le_mul_left (W+1) (show 1≤leaves.length+1 by omega)
 simp only [clipBudget,Nat.mul_assoc] at a ⊢
 omega

/-- Copy-paid equality on the supplied persistent finite arrays. -/
def containsBits (x : List Bool) : List (List Bool)→Charged Bool
 | []=>⟨false,2⟩
 | y::ys=>let e:=copiedEqual x y
   if e.value then ⟨true,e.work+4⟩ else
    let r:=containsBits x ys;⟨r.value,e.work+r.work+4⟩
@[simp] theorem containsBits_value (x : List Bool) (ys : List (List Bool)) :
 (containsBits x ys).value=(ys.map decode).contains (decode x) := by
 induction ys with
 | nil=>rfl
 | cons y ys ih=>simp [containsBits,ih];split <;> simp_all

theorem containsBits_work (W : Nat) (x : List Bool) (ys : List (List Bool))
 (xw : x.length≤W) (yw : ∀ y∈ys,y.length≤W) :
 (containsBits x ys).work≤64*(W+1)*(ys.length+1) := by
 induction ys with
 | nil=>simp only [containsBits,List.length_nil];omega
 | cons y ys ih=>
  have a:=copiedEqual_work W x y xw (yw y (by simp))
  have b:=ih (by intro z hz;exact yw z (by simp [hz]))
  simp only [containsBits,List.length_cons,Nat.mul_add,Nat.mul_one] at b ⊢
  split <;> simp only [Charged.work] <;> omega

/-- Literal final recovery block-color scan. All equality inputs and the returned
head color are copied with a bit-by-bit loop; absent color is the empty array. -/
def colorBits : List (List (List Bool))→List Bool→Charged (List Bool)
 | [],_=>⟨[],2⟩
 | b::P,x=>let e:=containsBits x b
   if e.value then
    let c:=copyBits (b.headD []);⟨c.value,e.work+c.work+8⟩
   else let r:=colorBits P x;⟨r.value,e.work+r.work+8⟩
@[simp] theorem colorBits_value (P : List (List (List Bool))) (x : List Bool) :
 decode (colorBits P x).value=FinalCutRecovery.blockColor (P.map (List.map decode)) (decode x) := by
 induction P with
 | nil=>rfl
 | cons b P ih=>
  have head:decode (b.headD [])=(b.map decode).headD 0:=by cases b <;> rfl
  simp only [colorBits,containsBits_value,List.map_cons,FinalCutRecovery.blockColor]
  split <;> simp_all

theorem colorBits_length (W : Nat) (P : List (List (List Bool))) (x : List Bool)
 (pw : ∀ b∈P,∀ y∈b,y.length≤W) : (colorBits P x).value.length≤W := by
 induction P with
 | nil=>simp [colorBits]
 | cons b P ih=>
  have head:(b.headD []).length≤W:=by
   cases b with
   | nil=>simp
   | cons y ys=>exact pw (y::ys) (by simp) y (by simp)
  have tail:=ih (by intro c hc y hy;exact pw c (by simp [hc]) y hy)
  simp only [colorBits]
  split <;> simp only [copyBits_value] <;> assumption

theorem colorBits_work (W : Nat) (P : List (List (List Bool))) (x : List Bool)
 (xw : x.length≤W) (pw : ∀ b∈P,∀ y∈b,y.length≤W) :
 (colorBits P x).work≤96*(W+1)*(P.flatten.length+P.length+1) := by
 induction P with
 | nil=>simp only [colorBits,List.flatten_nil,List.length_nil];omega
 | cons b P ih=>
  have h:∀y∈b,y.length≤W:=pw b (by simp)
  have a:=containsBits_work W x b xw h
  have bnd:(b.headD []).length≤W:=by cases b with
   | nil=>simp
   | cons y ys=>exact h _ (by simp)
  have tail:=ih (by intro c hc y hy;exact pw c (by simp [hc]) y hy)
  have scale:=Nat.mul_le_mul_right b.length (show 64*(W+1)≤96*(W+1) by omega)
  simp only [colorBits,copyBits_work,List.flatten_cons,List.length_append,List.length_cons,Nat.mul_add,Nat.mul_one] at a tail scale ⊢
  split <;> simp only [Charged.work] <;> omega
end OrdinaryDispatch.RecoveryBits
