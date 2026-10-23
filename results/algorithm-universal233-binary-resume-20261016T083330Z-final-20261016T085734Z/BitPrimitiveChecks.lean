import BinaryCopy
namespace GenericForest.ScalarBits
open RMAF Universal233 Universal233.WholeSourceWork GenericForest.CheckCorrespondence

/-- Coarse per-slot bound for the explicitly metered binary reference providers. -/
def beta (W : Nat) := 256*(W+1)
def LabelCap (W : Nat) (L : List Nat) := ∀x∈L,x<2^W

def Refines {α : Type} (W : Nat) (a b : Charged α) : Prop :=
 a.value=b.value ∧ a.work≤beta W*b.work

/-- Representation-boundary evaluation: the scalar provider is equalBits on
finite supplied bit arrays. Encode is the mathematical representation map;
8*(W+1) bills copying the two represented operands, not native Nat conversion. -/
def referenceEq (W x y : Nat) : Charged Bool :=
 copiedEqual (encode W x) (encode W y)
theorem referenceEq_value (W x y : Nat) (hx : x<2^W) (hy : y<2^W) :
 (referenceEq W x y).value=(x==y) := by simp [referenceEq,encode_value W x hx,encode_value W y hy]
theorem referenceEq_work (W x y : Nat) : (referenceEq W x y).work≤56*(W+1) := by
 exact copiedEqual_work W (encode W x) (encode W y) (by simp) (by simp)

def bitContains (W x : Nat) : List Nat → Charged Bool
 | []=>⟨false,beta W⟩
 | y::ys=>let e:=referenceEq W x y
           if e.value then ⟨true,e.work+4*(W+1)⟩ else
            let r:=bitContains W x ys;⟨r.value,e.work+r.work+4*(W+1)⟩

theorem bitContains_refines (W x : Nat) (L : List Nat) (hx : x<2^W) (cap : LabelCap W L) :
 Refines W (bitContains W x L) (meterContains x L) := by
 induction L with
 | nil=>simp [Refines,bitContains,meterContains]
 | cons y ys ih=>
  have hy:=cap y (by simp)
  have tailCap : LabelCap W ys:=fun z hz=>cap z (by simp [hz])
  have r:=ih tailCap
  have eq:=referenceEq_value W x y hx hy
  have cost:=referenceEq_work W x y
  unfold Refines at r ⊢
  cases h : x==y <;>
   simp only [bitContains,meterContains,eq,h,Bool.false_eq_true,ite_false,ite_true]
  · constructor
    · exact r.1
    · dsimp only [beta] at r ⊢
      simp only [Nat.mul_add,Nat.mul_assoc] at r ⊢
      omega
  · constructor
    · trivial
    · dsimp only [beta];omega

def bitAll {α : Type} (W : Nat) (f : α→Charged Bool) : List α→Charged Bool
 | []=>⟨true,beta W⟩
 | x::xs=>let a:=f x;let r:=bitAll W f xs;⟨a.value&&r.value,a.work+r.work+4*beta W⟩
def bitAny {α : Type} (W : Nat) (f : α→Charged Bool) : List α→Charged Bool
 | []=>⟨false,beta W⟩
 | x::xs=>let a:=f x;let r:=bitAny W f xs;⟨a.value||r.value,a.work+r.work+4*beta W⟩

theorem bitAll_refines {α : Type} (W : Nat) (f g : α→Charged Bool) (L : List α)
 (point : ∀x∈L,Refines W (f x) (g x)) : Refines W (bitAll W f L) (meterAll g L) := by
 induction L with
 | nil=>simp [Refines,bitAll,meterAll]
 | cons x xs ih=>
  have a:=point x (by simp)
  have r:=ih (fun y hy=>point y (by simp [hy]))
  simp only [Refines,bitAll,meterAll] at a r ⊢
  constructor
  · simp [a.1,r.1]
  · simp only [Nat.mul_add,Nat.mul_comm (beta W) 4];omega

theorem bitAny_refines {α : Type} (W : Nat) (f g : α→Charged Bool) (L : List α)
 (point : ∀x∈L,Refines W (f x) (g x)) : Refines W (bitAny W f L) (meterAny g L) := by
 induction L with
 | nil=>simp [Refines,bitAny,meterAny]
 | cons x xs ih=>
  have a:=point x (by simp)
  have r:=ih (fun y hy=>point y (by simp [hy]))
  simp only [Refines,bitAny,meterAny] at a r ⊢
  constructor
  · simp [a.1,r.1]
  · simp only [Nat.mul_add,Nat.mul_comm (beta W) 4];omega

/-- Binary equality plus fixed-width binary increment, even for duplicate labels. -/
def bitCount (W x : Nat) : List Nat → Charged Nat
 | []=>⟨0,beta W⟩
 | y::ys=>
  let r:=bitCount W x ys;let e:=referenceEq W x y
  let a:=addAtWidth W (encode W r.value) (encode W (if e.value then 1 else 0))
  ⟨decode a.value,r.work+e.work+a.work+8*(W+1)⟩

theorem bitCount_refines (W x : Nat) (L : List Nat) (hx : x<2^W) (cap : LabelCap W L)
 (length : L.length<2^W) : Refines W (bitCount W x L) (meterCount x L) := by
 induction L with
 | nil=>simp [Refines,bitCount,meterCount]
 | cons y ys ih=>
  have hy:=cap y (by simp)
  have tailCap : LabelCap W ys:=fun z hz=>cap z (by simp [hz])
  have tailLength : ys.length<2^W:=by simp only [List.length_cons] at length;omega
  have r:=ih tailCap tailLength
  have rv : (bitCount W x ys).value=ys.count x:=r.1.trans (meterCount_value x ys)
  have eq:=referenceEq_value W x y hx hy
  have countLength : ys.count x≤ys.length:=List.count_le_length
  have countFits : (bitCount W x ys).value<2^W:=by omega
  have small : (if (referenceEq W x y).value then 1 else 0)<2^W:=by
   split <;> simp only [List.length_cons] at length <;> omega
  have sumFits : (bitCount W x ys).value+(if (referenceEq W x y).value then 1 else 0)<2^W:=by
   split <;> simp only [List.length_cons] at length <;> omega
  have av:=addAtWidth_value W (encode W (bitCount W x ys).value)
   (encode W (if (referenceEq W x y).value then 1 else 0))
   (by simpa only [encode_value W _ countFits,encode_value W _ small] using sumFits)
  simp only [encode_value W _ countFits,encode_value W _ small] at av
  have eCost:=referenceEq_work W x y
  have aCost:=addAtWidth_work W (encode W (bitCount W x ys).value)
   (encode W (if (referenceEq W x y).value then 1 else 0)) (by simp) (by simp)
  unfold Refines at r ⊢
  simp only [bitCount,meterCount]
  constructor
  · rw [av,eq,r.1];omega
  · simp only [Nat.mul_add,Nat.mul_comm (beta W) 4]
    dsimp only [beta] at r ⊢
    omega
end GenericForest.ScalarBits
