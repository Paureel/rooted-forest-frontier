import BitPrimitiveChecks
namespace GenericForest.ScalarBits
open RMAF Universal233 Universal233.WholeSourceWork GenericForest.CheckCorrespondence

/-- Scalar-free pointer/Bool/copy counterpart with conservative slot expansion.
The argument is a named structural source meter; no scalar provider is hidden
in this constructor. Label equality/count/arithmetic calls are replaced below. -/
def pointerLift {α : Type} (W : Nat) (a : Charged α) : Charged α := ⟨a.value,beta W*a.work⟩
theorem pointerLift_refines {α : Type} (W : Nat) (a : Charged α) : Refines W (pointerLift W a) a := ⟨rfl,Nat.le_refl _⟩
theorem referenceEq_refines (W x y : Nat) (hx : x<2^W) (hy : y<2^W) :
 Refines W (referenceEq W x y) ⟨x==y,4⟩ := by
 have h:=referenceEq_work W x y
 exact ⟨referenceEq_value W x y hx hy,by dsimp [beta];omega⟩

def bitPartition (W : Nat) (L : List Nat) (F : List (List Nat)) : Charged Bool :=
 let nonempty:=bitAll W (fun B : List Nat=>pointerLift W ⟨!B.isEmpty,1⟩) F
 let counts:=bitAll W (fun x=>let cells:=pointerLift W (meterFlatten F)
   let cnt:=bitCount W x cells.value;let e:=referenceEq W cnt.value 1
   ⟨e.value,cells.work+cnt.work+e.work⟩) L
 let cells:=pointerLift W (meterFlatten F)
 let labels:=bitAll W (fun x=>bitContains W x L) cells.value
 ⟨nonempty.value&&counts.value&&labels.value,nonempty.work+counts.work+cells.work+labels.work+4*beta W⟩

theorem bitPartition_refines (W : Nat) (L : List Nat) (F : List (List Nat))
 (positive : 1≤W) (lcap : LabelCap W L) (fcap : LabelCap W F.flatten)
 (cellsFit : F.flatten.length<2^W) : Refines W (bitPartition W L F) (meterPartition L F) := by
 have oneFits : 1<2^W:=by
  have h:=Nat.pow_le_pow_right (n:=2) (by decide) positive
  simp only [Nat.pow_one] at h;omega
 have ne:=bitAll_refines W (fun B : List Nat=>pointerLift W ⟨!B.isEmpty,1⟩)
  (fun B : List Nat=>⟨!B.isEmpty,1⟩) F (fun _ _=>pointerLift_refines _ _)
 have cnt:=bitAll_refines W
  (fun x=>let cells:=pointerLift W (meterFlatten F);let c:=bitCount W x cells.value;let e:=referenceEq W c.value 1
   ⟨e.value,cells.work+c.work+e.work⟩)
  (fun x=>let cells:=meterFlatten F;let c:=meterCount x cells.value;⟨c.value==1,cells.work+c.work+4⟩) L (by
   intro x hx
   have c:=bitCount_refines W x F.flatten (lcap x hx) fcap cellsFit
   have value:=c.1.trans (meterCount_value x F.flatten)
   have countLen : F.flatten.count x≤F.flatten.length:=List.count_le_length
   have cFits : (bitCount W x F.flatten).value<2^W:=by omega
   have eq:=referenceEq_refines W (bitCount W x F.flatten).value 1 cFits oneFits
   simp only [Refines,pointerLift,meterFlatten_value] at c eq ⊢
   constructor
   · rw [eq.1,c.1]
   · simp only [Nat.mul_add];omega)
 have lab:=bitAll_refines W (fun x=>bitContains W x L) (fun x=>meterContains x L) F.flatten
  (fun x hx=>bitContains_refines W x L (fcap x hx) lcap)
 simp only [Refines,pointerLift,meterFlatten_value,Nat.mul_one] at ne cnt lab ⊢
 simp only [bitPartition,meterPartition,pointerLift,meterFlatten_value,Nat.mul_one]
 constructor
 · rw [ne.1,cnt.1,lab.1]
 · simp only [Nat.mul_add,Nat.mul_comm (beta W) 4];omega
end GenericForest.ScalarBits
