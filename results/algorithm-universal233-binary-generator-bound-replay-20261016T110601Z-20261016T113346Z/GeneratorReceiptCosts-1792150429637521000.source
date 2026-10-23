import GeneratorTreeCosts
namespace GenericForest.BinaryProducer.Generator
open BinaryProvider GenericForest.ScalarBits Universal233.WholeSourceWork

def CounterCap (K : Nat) (r : Receipt) : Prop := r.visited.length≤K ∧ r.childAttempts.length≤K ∧ r.pruned.length≤K

theorem prefixBits_cap (K : Nat) (r : Receipt) (h : CounterCap K r) : CounterCap (K+1) (prefixBits r).value := by
 have z:=addCarry_length r.visited [] true
 simp only [prefixBits,CounterCap,incrementBits,List.length_nil,Nat.max_zero] at *;omega

theorem childBits_cap (K : Nat) (r : Receipt) (h : CounterCap K r) : CounterCap (K+1) (childBits r).value := by
 have z:=addCarry_length r.childAttempts [] true
 simp only [childBits,CounterCap,incrementBits,List.length_nil,Nat.max_zero] at *;omega

theorem combineBits_cap (K : Nat) (a b : Receipt) (ha : CounterCap K a) (hb : CounterCap K b) :
 CounterCap (K+1) (combineBits a b).value := by
 have v:=addCarry_length a.visited b.visited false
 have c:=addCarry_length a.childAttempts b.childAttempts false
 have p:=addCarry_length a.pruned b.pruned false
 simp only [combineBits,CounterCap,addBits] at *
 exact ⟨by omega,by omega,by omega⟩

theorem attemptBits_cap (K : Nat) (kp : 1≤K) (f : GTree→List Group→Addresses→Charged Receipt)
 (hf : ∀t d c,CounterCap K (f t d c).value) (T d c g) : CounterCap (K+1) (attemptBits f T d c g).value := by
 dsimp only [attemptBits];split
 · simp [CounterCap]
 · split
   · simp [CounterCap]
   · cases he : (eraseBits g.origin T).value with
     | none=>simp [CounterCap]
     | some U=>exact childBits_cap K _ (hf _ _ _)

theorem stepBits_cap (K : Nat) (kp : 1≤K) (f : GTree→List Group→Addresses→Charged Receipt)
 (hf : ∀t d c,CounterCap K (f t d c).value) (T d c) : CounterCap (K+3) (stepBits f T d c).value := by
 dsimp only [stepBits]
 cases h : (chooseBits (normalizeBits T).value).value with
 | finish=>simp [finishBits,CounterCap]
 | refuse why=>simp [CounterCap]
 | one g=>
  have a:=attemptBits_cap K kp f hf (normalizeBits T).value d c g
  have p:=prefixBits_cap (K+1) _ a
  simp only [CounterCap] at p ⊢;omega
 | two a b=>
  have x:=attemptBits_cap K kp f hf (normalizeBits T).value d c a
  have y:=attemptBits_cap K kp f hf (normalizeBits T).value d c b
  exact prefixBits_cap (K+2) _ (combineBits_cap (K+1) _ _ x y)

theorem runBits_cap (fuel : Capacity) (T d c) : CounterCap (3*fuel.length+4) (runBits fuel T d c).value := by
 induction fuel generalizing T d c with
 | nil=>exact stepBits_cap 1 (by decide) _ (by intros;simp [CounterCap]) T d c
 | cons u fuel ih=>
  have h:=stepBits_cap (3*fuel.length+4) (by omega) (runBits fuel) ih T d c
  simpa only [runBits,List.length_cons,Nat.mul_add,Nat.mul_one,Nat.add_assoc] using h

theorem prefixBits_cost (K : Nat) (r : Receipt) (h : CounterCap K r) : (prefixBits r).work≤12*(K+1)+4 := by
 have a:=addCarry_work r.visited [] true
 simp only [prefixBits,incrementBits,List.length_nil,Nat.add_zero] at *
 have m:=Nat.mul_le_mul_left 12 (Nat.add_le_add_right h.1 1);omega

theorem childBits_cost (K : Nat) (r : Receipt) (h : CounterCap K r) : (childBits r).work≤12*(K+1)+4 := by
 have a:=addCarry_work r.childAttempts [] true
 simp only [childBits,incrementBits,List.length_nil,Nat.add_zero] at *
 have m:=Nat.mul_le_mul_left 12 (Nat.add_le_add_right h.2.1 1);omega

def recordCount (r : Receipt) := r.outputs.length+r.refusals.length

theorem combineBits_cost (K : Nat) (a b : Receipt) (ha : CounterCap K a) (hb : CounterCap K b) :
 (combineBits a b).work≤4*recordCount a+36*(2*K+1)+18 := by
 have v:=addCarry_work a.visited b.visited false
 have c:=addCarry_work a.childAttempts b.childAttempts false
 have p:=addCarry_work a.pruned b.pruned false
 have vb:=Nat.mul_le_mul_left 12 (show a.visited.length+b.visited.length+1≤2*K+1 by rcases ha with ⟨_,_,_⟩;rcases hb with ⟨_,_,_⟩;omega)
 have cb:=Nat.mul_le_mul_left 12 (show a.childAttempts.length+b.childAttempts.length+1≤2*K+1 by rcases ha with ⟨_,_,_⟩;rcases hb with ⟨_,_,_⟩;omega)
 have pb:=Nat.mul_le_mul_left 12 (show a.pruned.length+b.pruned.length+1≤2*K+1 by rcases ha with ⟨_,_,_⟩;rcases hb with ⟨_,_,_⟩;omega)
 simp only [combineBits,appendSpine_work,addBits,recordCount];omega

theorem runBits_records (fuel : Capacity) (T d c) : recordCount (runBits fuel T d c).value≤3*2^(fuel.length+1) := by
 have h:=Universal233.CoreWork.run_records_bound fuel.length (gtreeValue T) (groupsValue d) c
 have e:=runBits_value fuel T d c
 have a:=congrArg (fun r : Universal233.CoreProgram.Receipt=>r.outputs.length+r.refusals.length) e
 simp only [receiptValue,List.length_map,←a,Universal233.CoreWork.records,recordCount] at *;exact h

theorem attemptBits_records (f : GTree→List Group→Addresses→Charged Receipt) (R : Nat) (rp : 1≤R)
 (hf : ∀t d c,recordCount (f t d c).value≤R) (T d c g) : recordCount (attemptBits f T d c g).value≤R := by
 dsimp only [attemptBits];split
 · simpa [recordCount] using rp
 · split
   · simpa [recordCount] using rp
   · cases he : (eraseBits g.origin T).value with
     | none=>simpa [recordCount] using rp
     | some U=>exact hf _ _ _
end GenericForest.BinaryProducer.Generator
