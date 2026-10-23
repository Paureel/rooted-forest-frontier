import RCErase
namespace OrdinaryDispatch.RecoveryControlBits
open Universal233 WholeSourceWork CoreProgram CoreWork
open OrdinaryDispatch.RecoveryBits OrdinaryDispatch.RecoveryInitialBits

/-- Actual step-front execution retains the normalized owned tree for subsequent
attempts. chooseBits returns independent copied selected groups. -/
def prepare (W : Nat) (t : BitTree) : Charged (BitTree×BitChoice) :=
 let n:=normalizeBits t;let c:=chooseBits W n.value
 ⟨(n.value,c.value),n.work+c.work+8⟩

theorem represented_prepare (W N : Nat) (t : BitTree) (positive : 1≤W)
 (words : TreeWords W t) (shape : footprint (viewTree t)≤N) (countFit : N<2^W) :
 viewTree (prepare W t).value.1=normalize (viewTree t) ∧
 viewChoice (prepare W t).value.2=CoreProgram.choose (normalize (viewTree t)) ∧
 (prepare W t).work≤8192*(W+4)*(N+1)^3 ∧
 treeCells (prepare W t).value.1+choiceCells (prepare W t).value.2≤3*((W+4)*N)+1 := by
 have norm:=normalizeBits_source_bound W N t words shape
 have nw:=normalizeBits_words W t words
 have ns:footprint (viewTree (normalizeBits t).value)≤N:=by rw [normalizeBits_value];exact Nat.le_trans (normalize_footprint _) shape
 have ch:=represented_choose W N (normalizeBits t).value positive nw ns countFit
 let K:=(W+4)*(N+1)^3
 have power:N*(N+1)≤(N+1)^3:=by
  have a: N*(N+1)≤(N+1)^2:=by rw [Nat.pow_two];exact Nat.mul_le_mul_right (N+1) (Nat.le_succ N)
  have b:=Nat.pow_le_pow_right (n:=N+1) (by omega : 0<N+1) (by decide : 2≤3)
  exact Nat.le_trans a b
 have nk:(normalizeBits t).work≤1024*K:=by
  have b:=Nat.mul_le_mul_left (1024*(W+4)) power
  have eq:1024*(W+4)*(N+1)*N=1024*(W+4)*(N*(N+1)):=by ac_rfl
  rw [←eq] at b
  exact Nat.le_trans norm.2.1 (by simpa only [K,Nat.mul_assoc] using b)
 have ck:(chooseBits W (normalizeBits t).value).work≤4096*K:=by simpa only [K,Nat.mul_assoc] using ch.2.1
 have kp:1≤K:=by simpa only [Nat.one_mul] using Nat.mul_le_mul (show 1≤W+4 by omega) (Nat.one_le_pow 3 (N+1) (by omega))
 refine ⟨normalizeBits_value t,?_,?_,?_⟩
 · simpa only [prepare,normalizeBits_value] using ch.1
 · simp only [prepare]
   calc _≤8192*K:=by omega
        _=8192*(W+4)*(N+1)^3:=by simp only [K,Nat.mul_assoc]
 · simp only [prepare]
   have a:=norm.2.2;have b:=ch.2.2;omega

theorem chosen_one_address (W N : Nat) (t : BitTree) (g : BitGroup)
 (words : TreeWords W t) (shape : footprint (viewTree t)≤N) (h : (chooseBits W t).value=.one g) : g.origin.length≤N := by
 have c:=chooseBits_caps W N t words shape
 rw [h] at c
 have s:=c.2.2
 simp only [viewTree,viewGroup,footprint] at s
 omega

theorem chosen_two_addresses (W N : Nat) (t : BitTree) (a b : BitGroup)
 (words : TreeWords W t) (shape : footprint (viewTree t)≤N) (h : (chooseBits W t).value=.two a b) :
 a.origin.length≤N ∧ b.origin.length≤N := by
 have c:=chooseBits_caps W N t words shape
 rw [h] at c
 have sa:=c.1.2.2;have sb:=c.2.2.2
 simp only [viewTree,viewGroup,footprint] at sa sb
 constructor <;> omega

theorem chosen_one_erase_work (W N : Nat) (t : BitTree) (g : BitGroup)
 (words : TreeWords W t) (shape : footprint (viewTree t)≤N) (h : (chooseBits W t).value=.one g) :
 (eraseBits g.origin t).work≤256*(W+4)*(N+1)*N :=
 (eraseBits_source_bound W N g.origin t words shape (chosen_one_address W N t g words shape h)).2.1

theorem chooseBits_work_decomposition (W : Nat) (t : BitTree) :
 (chooseBits W t).work=(groupsBits t).work+(chooseCore W (groupsBits t).value t).work+(closeGroups (groupsBits t).value).work+12 := rfl

theorem chooseBits_collector_lifetime_paid (W : Nat) (t : BitTree) :
 (closeGroups (groupsBits t).value).work≤(chooseBits W t).work := by rw [chooseBits_work_decomposition];omega

theorem uniqueTest_lifetime_paid (W : Nat) (gs : List BitGroup) (g : BitGroup) :
 (closeGroups (filterColor g.color gs).value).work+(closeBits (lengthOwned W (filterColor g.color gs).value).value).work≤
 (uniqueTest W gs g).work := by simp only [uniqueTest];omega

theorem pickPair_discarded_lifetime_paid (a : GroupPair) (b : Option GroupPair) :
 (pickPair (some a) b).work=(closeMaybePair b).work+8 := rfl

theorem homogeneous_refusal_lifetime_paid (W : Nat) (first : BitGroup) (rest : List BitGroup) (t : BitTree) (a b : BitGroup)
 (uniform : (allColor first.color (first::rest)).value=false)
 (unique : (findUnique W (first::rest) (first::rest)).value=none)
 (mixed : (mixedBits t).value=some (a,b)) (same : decode a.color=decode b.color) :
 (closePair (a,b)).work≤(chooseCore W (first::rest) t).work := by
 simp only [chooseCore,uniform,Bool.false_eq_true,ite_false,unique,mixed,ownedEqual_value,same,beq_self_eq_true,ite_true]
 omega

theorem address_operands_lifetime_paid (a b : List Bool) :
 (closeBits (copyBits a).value).work+(closeBits (copyBits b).value).work≤(ownedAddressEqual a b).work := by
 simp only [ownedAddressEqual];omega
end OrdinaryDispatch.RecoveryControlBits
