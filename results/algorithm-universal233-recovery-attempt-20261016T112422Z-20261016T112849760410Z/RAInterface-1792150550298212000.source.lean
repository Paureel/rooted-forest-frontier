import RAAttempt
namespace OrdinaryDispatch.RecoveryAttemptBits
open Universal233 WholeSourceWork CoreProgram CoreWork
open OrdinaryDispatch.RecoveryBits OrdinaryDispatch.RecoveryInitialBits OrdinaryDispatch.RecoveryControlBits

/-- Complete local attempt interface; K is the actual continuation bound.
C is counter width, W is label/color width, addresses remain structural paths.
Neither C nor the callback cost/fits premise has been derived for a whole run. -/
theorem represented_attempt (W C N K : Nat)
 (f : BitTree→List BitGroup→List (List Bool)→Charged BitReceipt)
 (F : GTree→List Group→List (List Bool)→Receipt)
 (refines : ∀t d c,viewReceipt (f t d c).value=F (viewTree t) (d.map viewGroup) c)
 (positive : 1≤C) (t : BitTree) (d : List BitGroup) (cuts : List (List Bool)) (g : BitGroup)
 (words : TreeWords W t) (size : footprint (viewTree t)≤N)
 (dcaps : GroupCaps W N d) (gc : GroupCap W N g)
 (dn : d.length≤N) (cn : cuts.length≤N) (paths : ∀p∈cuts,p.length≤N)
 (callback : ∀next,(eraseBits g.origin t).value=some next→
  (f next (g::d) (g.origin::cuts)).work≤K ∧ ReceiptWords C (f next (g::d) (g.origin::cuts)).value ∧
  decode (f next (g::d) (g.origin::cuts)).value.childAttempts+1<2^C) :
 viewReceipt (attemptBits C f t d cuts g).value=CoreProgram.attempt F (viewTree t) (d.map viewGroup) cuts (viewGroup g) ∧
 (attemptBits C f t d cuts g).work≤K+2048*(W+4)*(N+1)^2+72*(C+1) ∧
 ReceiptWords C (attemptBits C f t d cuts g).value := by
 refine ⟨attemptBits_value C f F refines t d cuts g (by intro next h;exact (callback next h).2.2),?_,?_⟩
 · exact attemptBits_source_work W C N K f t d cuts g words size dcaps gc dn cn paths
    (by intro next h;exact ⟨(callback next h).1,(callback next h).2.1.2.1⟩)
 · exact attemptBits_words C f positive t d cuts g (by intro next h;exact (callback next h).2.1)

def prunedAttempt (C : Nat) (t : BitTree) (d : List BitGroup) (cuts : List (List Bool)) (g : BitGroup) : Charged BitReceipt :=
 attemptBits C (fun _ _ _=>prunedReceipt) t d cuts g

theorem actual_zero_fuel_child (C : Nat) (positive : 1≤C)
 (t next : BitTree) (d : List BitGroup) (cuts : List (List Bool)) (g : BitGroup)
 (root : g.origin≠[]) (dup : cuts.contains g.origin=false) (h : (eraseBits g.origin t).value=some next) :
 viewReceipt (prunedAttempt C t d cuts g).value=⟨[],[],0,1,1⟩ := by
 have p:2≤2^C:=by simpa only [Nat.pow_one] using Nat.pow_le_pow_right (n:=2) (by decide : 0<2) positive
 have v:=attemptBits_value C (fun _ _ _=>prunedReceipt) (fun _ _ _=>⟨[],[],0,0,1⟩)
  (by intros;rfl) t d cuts g (by intros;simp only [prunedReceipt,decode];omega)
 have src:=eraseBits_value g.origin t;rw [h,Option.map_some] at src
 simpa only [prunedAttempt,CoreProgram.attempt,viewGroup,root,ite_false,dup,Bool.false_eq_true,←src] using v
end OrdinaryDispatch.RecoveryAttemptBits
