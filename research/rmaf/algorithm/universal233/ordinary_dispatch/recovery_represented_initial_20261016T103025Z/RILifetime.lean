import RINormBound
namespace OrdinaryDispatch.RecoveryInitialBits
open Universal233 WholeSourceWork CoreProgram CoreWork
open OrdinaryDispatch.RecoveryBits

theorem initializeBits_work_decomposition (W : Nat) (t : InputTree) (P : List (List (List Bool))) (budget : List Bool) :
 (initializeBits W t P budget).work=
 (copyInput t).work+(copyForest P).work+(copyBits budget).work+(initialCore W t P budget).work+
 (closeInput t).work+(closeForest P).work+(closeBits budget).work+16 := by
 simp only [initializeBits,copyInput_value,copyForest_value,copyBits_value]

theorem initializeBits_input_lifetime_paid (W : Nat) (t : InputTree) (P : List (List (List Bool))) (budget : List Bool) :
 (copyInput t).work+(copyForest P).work+(copyBits budget).work+
 (closeInput t).work+(closeForest P).work+(closeBits budget).work≤(initializeBits W t P budget).work := by
 rw [initializeBits_work_decomposition];omega

theorem initialCore_first_leaves_lifetime_paid (W : Nat) (t : InputTree) (P : List (List (List Bool))) (budget : List Bool) :
 (closeArrays (leafArrays t).value).work≤(initialCore W t P budget).work := by
 simp only [initialCore]
 split <;> simp only [Charged.work] <;> omega

theorem stepLength_temporary_lifetime_paid (W : Nat) (xs : List Bool) :
 (closeBits (addCarry true xs []).value).work+(closeBits xs).work≤(stepLength W xs).work := by
 simp only [stepLength];omega

theorem ownedSubtract_temporary_lifetime_paid (xs ys : List Bool) :
 (closeBits (alignBits xs ys).value.1).work+(closeBits (alignBits xs ys).value.2).work+
 (closeBits (subtractBorrow false (alignBits xs ys).value.1 (alignBits xs ys).value.2).value.2).work≤
 (ownedSubtract xs ys).work := by simp only [ownedSubtract];omega

theorem merged_children_lifetime_paid (p : List Bool) (a b : BitGroup) (same : decode a.color=decode b.color) :
 (closeTree (.leaf a)).work+(closeTree (.leaf b)).work≤(assemble p (.leaf a) (.leaf b)).work := by
 simp only [assemble,ownedEqual_value,same,beq_self_eq_true,ite_true]
 omega
end OrdinaryDispatch.RecoveryInitialBits
