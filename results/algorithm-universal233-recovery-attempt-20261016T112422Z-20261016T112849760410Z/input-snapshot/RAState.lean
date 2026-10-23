import RAReceipt
set_option maxRecDepth 2000
namespace OrdinaryDispatch.RecoveryAttemptBits
open Universal233 WholeSourceWork CoreProgram CoreWork
open OrdinaryDispatch.RecoveryBits OrdinaryDispatch.RecoveryInitialBits OrdinaryDispatch.RecoveryControlBits

/-- Actual deep copies; original detached state stays borrowed by the attempt. -/
def copyGroups : List BitGroup→Charged (List BitGroup)
 | []=>⟨[],2⟩
 | g::gs=>let a:=copyGroup g;let b:=copyGroups gs;⟨a.value::b.value,a.work+b.work+4⟩
@[simp] theorem copyGroups_value (gs : List BitGroup) : (copyGroups gs).value=gs := by
 induction gs <;> simp_all [copyGroups]
theorem copyGroups_work (W N : Nat) (gs : List BitGroup) (caps : GroupCaps W N gs) :
 (copyGroups gs).work≤groupFee W N*(gs.length+1) := by
 have pos:=groupFee_positive W N
 induction gs with
 | nil=>simp only [copyGroups,List.length_nil,Nat.zero_add,Nat.mul_one];omega
 | cons g gs ih=>
  have a:=copied_group_fee W N g (caps g (by simp))
  have b:=ih (by intro x hx;exact caps x (by simp [hx]))
  simp only [copyGroups,List.length_cons,Nat.mul_add,Nat.mul_one] at b ⊢;omega

/-- Owns a fresh survivor, independent copies of selected/detached groups, and
independent cut paths. The continuation borrows these values. The caller closes
them after the continuation returns its independent receipt. -/
def callOwned (C : Nat)
 (f : BitTree→List BitGroup→List (List Bool)→Charged BitReceipt)
 (next : BitTree) (d : List BitGroup) (cuts : List (List Bool)) (g : BitGroup) : Charged BitReceipt :=
 let a:=copyGroup g;let b:=copyGroups d;let p:=copyBits g.origin;let cs:=copyArrays cuts
 let ds:=a.value::b.value;let vs:=p.value::cs.value
 let r:=f next ds vs
 let bumped:=bumpAttempt C r.value
 let cn:=closeTree next;let cd:=closeGroups ds;let cc:=closeArrays vs
 ⟨bumped.value,a.work+b.work+p.work+cs.work+8+r.work+bumped.work+cn.work+cd.work+cc.work+12⟩

theorem callOwned_value (C : Nat)
 (f : BitTree→List BitGroup→List (List Bool)→Charged BitReceipt)
 (F : GTree→List Group→List (List Bool)→Receipt)
 (refines : ∀t d c,viewReceipt (f t d c).value=F (viewTree t) (d.map viewGroup) c)
 (next : BitTree) (d : List BitGroup) (cuts : List (List Bool)) (g : BitGroup)
 (fits : decode (f next (g::d) (g.origin::cuts)).value.childAttempts+1<2^C) :
 viewReceipt (callOwned C f next d cuts g).value=
 {F (viewTree next) (viewGroup g::d.map viewGroup) (g.origin::cuts) with
 childAttempts:=(F (viewTree next) (viewGroup g::d.map viewGroup) (g.origin::cuts)).childAttempts+1} := by
 simp only [callOwned,copyGroup_value,copyGroups_value,copyBits_value,copyArrays_value]
 rw [bumpAttempt_value C _ fits,refines]
 rfl

theorem callOwned_lifetime (C : Nat) (f : BitTree→List BitGroup→List (List Bool)→Charged BitReceipt)
 (next : BitTree) (d : List BitGroup) (cuts : List (List Bool)) (g : BitGroup) :
 (closeTree next).work+(closeGroups (g::d)).work+(closeArrays (g.origin::cuts)).work≤
 (callOwned C f next d cuts g).work := by
 simp only [callOwned,copyGroup_value,copyGroups_value,copyBits_value,copyArrays_value];omega

theorem callOwned_work (W C N K : Nat)
 (f : BitTree→List BitGroup→List (List Bool)→Charged BitReceipt)
 (next : BitTree) (d : List BitGroup) (cuts : List (List Bool)) (g : BitGroup)
 (words : TreeWords W next) (size : footprint (viewTree next)≤N)
 (dcaps : GroupCaps W N d) (gc : GroupCap W N g)
 (dn : d.length≤N) (cn : cuts.length≤N) (paths : ∀p∈cuts,p.length≤N)
 (counter : (f next (g::d) (g.origin::cuts)).value.childAttempts.length≤C)
 (callback : (f next (g::d) (g.origin::cuts)).work≤K) :
 (callOwned C f next d cuts g).work≤K+1024*(W+4)*(N+1)^2+72*(C+1) := by
 have gn:g.origin.length≤N:=by have h:=gc.2.2;simp only [viewTree,viewGroup,footprint] at h;omega
 have a:=copied_group_fee W N g gc
 have b:=copyGroups_work W N d dcaps
 have c:=copyArrays_work cuts
 have ca:=arrayCells_bound N cuts paths
 have cp:arrayCells cuts≤(N+1)*N:=Nat.le_trans ca (Nat.mul_le_mul_left (N+1) cn)
 have tr:=closeTree_work next
 have tc:=Nat.le_trans (treeCells_source_bound W next words) (Nat.mul_le_mul_left (W+4) size)
 have ds:=closeGroups_work W N (g::d) (by intro x hx;rcases List.mem_cons.mp hx with hx|hx;subst x;exact gc;exact dcaps x hx)
 have cl:=closeArrays_work (g.origin::cuts)
 have bump:=bumpAttempt_work C (f next (g::d) (g.origin::cuts)).value counter
 have bd:groupFee W N*(d.length+1)≤groupFee W N*(N+1):=Nat.mul_le_mul_left _ (by omega)
 have bds:groupFee W N*((g::d).length+1)≤groupFee W N*(N+2):=Nat.mul_le_mul_left _ (by simp only [List.length_cons];omega)
 let L:=(W+4)*(N+1)^2
 have wn:1≤W+4:=by omega
 have square:N+1≤(N+1)^2:=by
  simpa only [Nat.one_mul,Nat.pow_two] using Nat.mul_le_mul_right (N+1) (show 1≤N+1 by omega)
 have pl:N+1≤L:=Nat.le_trans square (by simpa only [L,Nat.one_mul] using Nat.mul_le_mul_right ((N+1)^2) wn)
 have lp:1≤L:=by omega
 have n2:(N+1)*N≤L:=by
  have h:(N+1)*N≤(N+1)^2:=by rw [Nat.pow_two];exact Nat.mul_le_mul_left (N+1) (by omega)
  exact Nat.le_trans h (by simpa only [L,Nat.one_mul] using Nat.mul_le_mul_right ((N+1)^2) wn)
 have small:(W+4)*N≤L:=by
  exact Nat.mul_le_mul_left (W+4) (Nat.le_trans (Nat.le_succ N) square)
 have scales (x : Nat) (le : x≤N+2) : groupFee W N*x≤128*L:=by
  calc groupFee W N*x≤groupFee W N*(2*(N+1)):=Nat.mul_le_mul_left _ (by omega)
       _= (64*2)*((W+4)*((N+1)*(N+1))):=by simp only [groupFee];ac_rfl
       _=128*L:=by simp only [L,Nat.pow_two]
 have aa:groupFee W N≤128*L:=by simpa only [Nat.mul_one] using scales 1 (by omega)
 have bb:=scales (d.length+1) (by omega)
 have dd:=scales ((g::d).length+1) (by simp only [List.length_cons];omega)
 have trb:(closeTree next).work≤64*L:=Nat.le_trans tr (Nat.mul_le_mul_left 64 (Nat.le_trans tc small))
 have p:(copyBits g.origin).work≤8*L:=by rw [copyBits_work];omega
 have cla:(closeArrays (g.origin::cuts)).work≤24*L:=by simp only [arrayCells] at cl;omega
 have cpa:(copyArrays cuts).work≤16*L:=by omega
 simp only [callOwned,copyGroup_value,copyGroups_value,copyBits_value,copyArrays_value]
 have bbb:=Nat.le_trans b bb
 have ddd:=Nat.le_trans ds dd
 have aaa: (copyGroup g).work≤128*L:=by simpa only [Nat.mul_one] using Nat.le_trans (show (copyGroup g).work≤groupFee W N by omega) aa
 calc _≤K+1024*L+72*(C+1):=by omega
      _=K+1024*(W+4)*(N+1)^2+72*(C+1):=by simp only [L,Nat.mul_assoc]
end OrdinaryDispatch.RecoveryAttemptBits
