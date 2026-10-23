import CherryGuardWork
namespace Universal233.Rule5PrefixLocalWork
open RMAF

def guardPrefixMeter (T S : Tree) (a b : Nat) : Measured Bool :=
 let p:=properPairMeter T S
 if p.value then let c:=hasCherryMeter T a b;⟨c.value,p.work+c.work+1⟩
 else ⟨false,p.work+1⟩

theorem guard_prefix_value (T S : Tree) (a b : Nat) :
 (guardPrefixMeter T S a b).value=(Rule5Local.properPair T S && Rule5Local.hasCherry T a b) := by
 simp only [guardPrefixMeter,proper_pair_value,has_cherry_value]
 split <;> simp_all

theorem admitted_has_prefix (T S : Tree) (a b : Nat) (ad : Rule5Local.admitted T S a b=true) :
 (guardPrefixMeter T S a b).value=true := by
 rw [guard_prefix_value]
 unfold Rule5Local.admitted at ad
 simp only [Bool.and_eq_true] at ad ⊢
 grind

theorem prefix_false_refuses (T S : Tree) (a b : Nat)
 (failed : (guardPrefixMeter T S a b).value=false) : Rule5Local.admitted T S a b=false := by
 apply Bool.eq_false_iff.2
 intro h
 have:=admitted_has_prefix T S a b h
 rw [failed] at this
 contradiction

def prefixPolynomial (N : Nat) : Nat := properPolynomial N+16*N*N+8*N+3

theorem guard_prefix_work (T S : Tree) (a b N : Nat)
 (ht : (leaves T).length≤N) (hs : (leaves S).length≤N) :
 (guardPrefixMeter T S a b).work≤prefixPolynomial N := by
 have p:=proper_pair_work T S N ht hs
 have c:=has_cherry_work T a b
 have square:=Nat.mul_le_mul ht ht
 have uniform:=Nat.mul_le_mul_left 16 square
 simp only [Nat.mul_assoc] at uniform c
 unfold guardPrefixMeter prefixPolynomial
 split <;> (try dsimp only) <;> simp only [Nat.mul_assoc] <;> omega

/-- Raw input leaf payload, including repetitions; no bijective-labelling
premise is needed for a refused-input source-work envelope. -/
theorem leaf_payload_domain (T : Tree) (L : Nat) (labels : ∀x,x∈leaves T →x<2^L) :
 (leavesMeter T).value.length=(leaves T).length ∧
 ∀x,x∈(leavesMeter T).value →x<2^L := by
 rw [leaves_value]
 exact ⟨rfl,labels⟩

/-- Every enumerated original source address and endpoint is bounded as data;
contains/nodup use only these original labels. Scalar fee still stays explicit. -/
theorem cherry_payload_domain (T : Tree) (L : Nat) (labels : ∀x,x∈leaves T →x<2^L)
 {p : RMAF.Vertex} {a b : Nat} (mem : (p,a,b)∈(cherriesMeter T).value) :
 p.length+1≤(leaves T).length ∧ a<2^L ∧ b<2^L := by
 have cap:=cherry_row_payload T p a b mem
 exact ⟨cap.1,labels a cap.2.1,labels b cap.2.2⟩

def scalarWork (fee : Nat) {α : Type} (r : Measured α) := fee*r.work

theorem guard_prefix_scaled (T S : Tree) (a b N fee : Nat)
 (ht : (leaves T).length≤N) (hs : (leaves S).length≤N) :
 scalarWork fee (guardPrefixMeter T S a b)≤fee*prefixPolynomial N :=
 Nat.mul_le_mul_left fee (guard_prefix_work T S a b N ht hs)
end Universal233.Rule5PrefixLocalWork
