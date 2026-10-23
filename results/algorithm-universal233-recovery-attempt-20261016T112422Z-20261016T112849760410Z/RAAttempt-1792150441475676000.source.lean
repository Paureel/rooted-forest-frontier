import RAState
set_option maxRecDepth 2000
namespace OrdinaryDispatch.RecoveryAttemptBits
open Universal233 WholeSourceWork CoreProgram CoreWork
open OrdinaryDispatch.RecoveryBits OrdinaryDispatch.RecoveryInitialBits OrdinaryDispatch.RecoveryControlBits

def rootAddress : List Bool→Charged Bool
 | []=>⟨true,2⟩ | _::_=>⟨false,2⟩
@[simp] theorem rootAddress_value (p : List Bool) : (rootAddress p).value=decide (p=[]) := by cases p <;> rfl
@[simp] theorem rootAddress_work (p : List Bool) : (rootAddress p).work=2 := by cases p <;> rfl

def attemptBits (C : Nat)
 (f : BitTree→List BitGroup→List (List Bool)→Charged BitReceipt)
 (t : BitTree) (d : List BitGroup) (cuts : List (List Bool)) (g : BitGroup) : Charged BitReceipt :=
 let root:=rootAddress g.origin
 if root.value then let r:=refusalReceipt .rootCut;⟨r.value,root.work+r.work+4⟩ else
 let duplicate:=addressContains g.origin cuts
 if duplicate.value then let r:=refusalReceipt .duplicateCut;⟨r.value,root.work+duplicate.work+r.work+8⟩ else
 let e:=eraseBits g.origin t
 match e.value with
 | none=>let r:=refusalReceipt .entireRemoval;⟨r.value,root.work+duplicate.work+e.work+r.work+12⟩
 | some next=>let r:=callOwned C f next d cuts g;⟨r.value,root.work+duplicate.work+e.work+r.work+12⟩

theorem attemptBits_value (C : Nat)
 (f : BitTree→List BitGroup→List (List Bool)→Charged BitReceipt)
 (F : GTree→List Group→List (List Bool)→Receipt)
 (refines : ∀t d c,viewReceipt (f t d c).value=F (viewTree t) (d.map viewGroup) c)
 (t : BitTree) (d : List BitGroup) (cuts : List (List Bool)) (g : BitGroup)
 (fits : ∀next,(eraseBits g.origin t).value=some next→decode (f next (g::d) (g.origin::cuts)).value.childAttempts+1<2^C) :
 viewReceipt (attemptBits C f t d cuts g).value=CoreProgram.attempt F (viewTree t) (d.map viewGroup) cuts (viewGroup g) := by
 by_cases root:g.origin=[]
 · simp only [attemptBits,CoreProgram.attempt,viewGroup,rootAddress_value,root,decide_true,ite_true,refusalReceipt_value,viewRefusal]
 · simp only [attemptBits,CoreProgram.attempt,viewGroup,rootAddress_value,root,decide_false,Bool.false_eq_true,ite_false,addressContains_value]
   by_cases dup:cuts.contains g.origin=true
   · simp only [dup,ite_true,refusalReceipt_value,viewRefusal]
   · simp only [dup,ite_false]
     cases h:(eraseBits g.origin t).value with
     | none=>
      have src:=eraseBits_value g.origin t;rw [h] at src
      simp only [h,←src,Option.map_none,refusalReceipt_value,viewRefusal]
     | some next=>
      have src:=eraseBits_value g.origin t;rw [h] at src
      have v:=callOwned_value C f F refines next d cuts g (fits next h)
      simpa only [h,←src,Option.map_some,viewGroup] using v

theorem attemptBits_words (C : Nat)
 (f : BitTree→List BitGroup→List (List Bool)→Charged BitReceipt)
 (positive : 1≤C) (t : BitTree) (d : List BitGroup) (cuts : List (List Bool)) (g : BitGroup)
 (words : ∀next,(eraseBits g.origin t).value=some next→ReceiptWords C (f next (g::d) (g.origin::cuts)).value) :
 ReceiptWords C (attemptBits C f t d cuts g).value := by
 simp only [attemptBits]
 split
 · exact refusalReceipt_words C positive _
 · split
   · exact refusalReceipt_words C positive _
   · cases h:(eraseBits g.origin t).value with
     | none=>simp only [h];exact refusalReceipt_words C positive _
     | some next=>simp only [h,callOwned,copyGroup_value,copyGroups_value,copyBits_value,copyArrays_value]
                  exact bumpAttempt_words C _ (words next h)

theorem attemptBits_source_work (W C N K : Nat)
 (f : BitTree→List BitGroup→List (List Bool)→Charged BitReceipt)
 (t : BitTree) (d : List BitGroup) (cuts : List (List Bool)) (g : BitGroup)
 (words : TreeWords W t) (size : footprint (viewTree t)≤N)
 (dcaps : GroupCaps W N d) (gc : GroupCap W N g)
 (dn : d.length≤N) (cn : cuts.length≤N) (paths : ∀p∈cuts,p.length≤N)
 (callback : ∀next,(eraseBits g.origin t).value=some next→
  (f next (g::d) (g.origin::cuts)).work≤K ∧ (f next (g::d) (g.origin::cuts)).value.childAttempts.length≤C) :
 (attemptBits C f t d cuts g).work≤K+2048*(W+4)*(N+1)^2+72*(C+1) := by
 have gn:g.origin.length≤N:=by have h:=gc.2.2;simp only [viewTree,viewGroup,footprint] at h;omega
 have dup:=addressContains_work N g.origin cuts gn paths
 have dd:(addressContains g.origin cuts).work≤64*(N+1)*(N+1):=
  Nat.le_trans dup (Nat.mul_le_mul_left (64*(N+1)) (by omega))
 let L:=(W+4)*(N+1)^2
 have pos:1≤L:=by simpa only [Nat.one_mul] using Nat.mul_le_mul (show 1≤W+4 by omega) (Nat.one_le_pow 2 (N+1) (by omega))
 have dbl:(addressContains g.origin cuts).work≤64*L:=by
  have h:(N+1)^2≤L:=by simpa only [L,Nat.one_mul] using Nat.mul_le_mul_right ((N+1)^2) (show 1≤W+4 by omega)
  exact Nat.le_trans dd (by simpa only [Nat.pow_two,Nat.mul_assoc] using Nat.mul_le_mul_left 64 h)
 have er:=eraseBits_source_bound W N g.origin t words size gn
 have eb:(eraseBits g.origin t).work≤256*L:=by
  have h:(N+1)*N≤(N+1)^2:=by rw [Nat.pow_two];exact Nat.mul_le_mul_left (N+1) (by omega)
  exact Nat.le_trans er.2.1 (by simpa only [L,Nat.mul_assoc] using Nat.mul_le_mul_left (256*(W+4)) h)
 have call (next : BitTree) (h : (eraseBits g.origin t).value=some next) :
  (callOwned C f next d cuts g).work≤K+1024*L+72*(C+1):=by
  have nw:TreeWords W next:=eraseBits_words W g.origin t next words h
  have src:=er.1;rw [h,Option.map_some] at src
  have ns:footprint (viewTree next)≤N:=Nat.le_trans (erase_footprint _ _ _ src.symm) size
  simpa only [L,Nat.mul_assoc] using callOwned_work W C N K f next d cuts g nw ns dcaps gc dn cn paths (callback next h).2 (callback next h).1
 simp only [attemptBits,rootAddress_work]
 split
 · simp only [refusalReceipt_work];change _≤K+2048*L+72*(C+1);omega
 · split
   · simp only [refusalReceipt_work];change _≤K+2048*L+72*(C+1);omega
   · cases h:(eraseBits g.origin t).value with
     | none=>simp only [h,refusalReceipt_work];change _≤K+2048*L+72*(C+1);omega
     | some next=>have a:=call next h;simp only [h];change _≤K+2048*L+72*(C+1);omega

theorem root_refusal_priority (C : Nat) (f : BitTree→List BitGroup→List (List Bool)→Charged BitReceipt)
 (t : BitTree) (d : List BitGroup) (cuts : List (List Bool)) (g : BitGroup) (root : g.origin=[]) :
 (attemptBits C f t d cuts g).value=(refusalReceipt .rootCut).value ∧ (attemptBits C f t d cuts g).work=30 := by
 simp [attemptBits,root]

theorem successful_attempt_lifetime (C : Nat) (f : BitTree→List BitGroup→List (List Bool)→Charged BitReceipt)
 (t next : BitTree) (d : List BitGroup) (cuts : List (List Bool)) (g : BitGroup)
 (root : g.origin≠[]) (dup : cuts.contains g.origin=false) (h : (eraseBits g.origin t).value=some next) :
 (closeTree next).work+(closeGroups (g::d)).work+(closeArrays (g.origin::cuts)).work≤(attemptBits C f t d cuts g).work := by
 have a:=callOwned_lifetime C f next d cuts g
 simp only [attemptBits,rootAddress_value,root,decide_false,Bool.false_eq_true,ite_false,addressContains_value,dup,h]
 omega
end OrdinaryDispatch.RecoveryAttemptBits
