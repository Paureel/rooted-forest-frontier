import ActualInspection
namespace GenericForest.ScalarBits.Controls

def decode : List Bool → Nat | []=>0 | b::bs=>(if b then 1 else 0)+2*decode bs

theorem binary_truth : decode [true,false,true]=5 ∧ decode [true,false,true,false,false]=5 ∧
 decode [false,false,false,false,false,true]=32 ∧ decode []=0 := by decide
theorem scalar_truth : (31:Nat)+1=32 ∧ (32:Nat)-1=31 ∧ (1:Nat)-32=0 ∧
 (max 7 19:Nat)=19 ∧ (0:Nat)<1 ∧ ¬(decode [false,true]≤decode [true]) := by decide
theorem counter_truth : ([false,false,true] : List Bool).length=3 ∧
 (([[0],[0],[0]] : List (List Nat)).flatten).count 0=3 := by decide
end GenericForest.ScalarBits.Controls
