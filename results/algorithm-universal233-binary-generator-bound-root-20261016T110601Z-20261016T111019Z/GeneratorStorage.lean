import GeneratedParentAssembly
namespace GenericForest.BinaryProducer.Generator
open BinaryProvider GenericForest.ScalarBits Universal233.WholeSourceWork Universal233.CoreWork
/-- Logical cell counts expand immutable sharing, hence overcount shared data.
A refusal string is a pointer to a fixed source literal; native heap is separate. -/
def blockCells (B : Block) := (B.map (fun x=>1+x.length)).sum
 def forestCells (F : BinaryProvider.Forest) := (F.map (fun B=>1+blockCells B)).sum
 def addressCells (cs : Addresses) := (cs.map (fun p=>1+p.length)).sum
 def outputCells (o : BinaryProducer.Output) := 4+forestCells o.partition+addressCells o.sourceCuts
 def receiptCells (r : Receipt) := 8+(r.outputs.map (fun o=>1+outputCells o)).sum+r.refusals.length+
 r.visited.length+r.childAttempts.length+r.pruned.length

def outputCellCap (W M : Nat) := 4+(M+1)*(1+M*(W+1))+M*(M+1)

theorem blockCells_cap (W : Nat) (B : Block) (w : BlockWidth W B) : blockCells B≤B.length*(W+1) := by
 exact GenericForest.LocalPolynomial.nat_sum_le_constant B _ (W+1) (fun x hx=>by have h:=w x hx;change x.length≤W at h;omega)

theorem outputCells_cap (W M : Nat) (o : BinaryProducer.Output) (h : OutputCap W M o) :
 outputCells o≤outputCellCap W M := by
 have f:=GenericForest.LocalPolynomial.nat_sum_le_constant o.partition (fun B=>1+blockCells B) (1+M*(W+1))
  (fun B hb=>by have a:=blockCells_cap W B (h.1 B hb);have b:=Nat.mul_le_mul_right (W+1) (h.2.1 B hb);omega)
 have a:=GenericForest.LocalPolynomial.nat_sum_le_constant o.sourceCuts (fun p=>1+p.length) (M+1)
  (fun p hp=>by have z:=h.2.2.2.2 p hp;omega)
 have fm:=Nat.mul_le_mul_right (1+M*(W+1)) h.2.2.2.1
 have am:=Nat.mul_le_mul_right (M+1) h.2.2.1
 unfold outputCells outputCellCap forestCells addressCells;omega

theorem receiptCells_cap (W M K R : Nat) (r : Receipt) (og : OutputGood W M r) (cc : CounterCap K r)
 (rr : recordCount r≤R) : receiptCells r≤(outputCellCap W M+2)*R+3*K+8 := by
 have outputs:=GenericForest.LocalPolynomial.nat_sum_le_constant r.outputs (fun o=>1+outputCells o) (outputCellCap W M+1)
  (fun o ho=>by have h:=outputCells_cap W M o (og o ho);omega)
 have expand : r.outputs.length*(outputCellCap W M+1)+r.refusals.length≤(outputCellCap W M+2)*R:=by
  have sum:=Nat.mul_le_mul_left (outputCellCap W M+2) rr
  have extra : r.refusals.length≤(outputCellCap W M+2)*r.refusals.length:=by
   have z:=Nat.mul_le_mul_right r.refusals.length (show 1≤outputCellCap W M+2 by omega);simpa only [Nat.one_mul] using z
  have out : r.outputs.length*(outputCellCap W M+1)≤(outputCellCap W M+2)*r.outputs.length:=by
   simpa only [Nat.mul_comm] using Nat.mul_le_mul_left r.outputs.length (show outputCellCap W M+1≤outputCellCap W M+2 by omega)
  simp only [recordCount,Nat.mul_add] at sum;omega
 rcases cc with ⟨_,_,_⟩
 unfold receiptCells;omega

theorem runBits_returned_storage (W M : Nat) (fuel : Capacity) (T d c)
 (h : StateGood W M (fuel.length+1) T d c) :
 receiptCells (runBits fuel T d c).value≤
 (outputCellCap W M+2)*(3*2^(fuel.length+1))+3*(3*fuel.length+4)+8 :=
 receiptCells_cap W M _ _ _ (runBits_output W M fuel T d c h) (runBits_cap fuel T d c) (runBits_records fuel T d c)

theorem generateBits_returned_storage (W N : Nat) (S : BinaryProvider.Tree) (color : Bits→Charged Color) (q : Bits)
 (sw : TreeWidth W S) (sn : treeNodes (treeValue S)≤N) :
 receiptCells (generateBits S color q).value≤
 (6*(outputCellCap W (inputResource N)+2)+9*N+20)*2^(decode q) := by
 have fn : (fuelBits q (leavesBits S).tail).value.length≤N:=by
  rw [fuelBits_length];have z:=bitsLeaves_count S
  exact Nat.le_trans (Nat.min_le_right _ _) (by simp only [List.length_tail];omega)
 have fq : (fuelBits q (leavesBits S).tail).value.length≤decode q:=by rw [fuelBits_length];exact Nat.min_le_left _ _
 have pow:=Nat.pow_le_pow_right (n:=2) (by decide) (Nat.add_le_add_right fq 1)
 have pc:=Nat.mul_le_mul_left (outputCellCap W (inputResource N)+2) (Nat.mul_le_mul_left 3 pow)
 simp only [Nat.pow_succ] at pc
 have p : 1≤2^(decode q):=Nat.one_le_pow _ _ (by decide)
 have fixed:=Nat.mul_le_mul_left (9*N+20) p
 simp only [Nat.mul_one] at fixed
 dsimp only [generateBits];simp only [leavesCopy_value]
 split
 · have r:=runBits_returned_storage W (inputResource N) _ _ [] [] (initial_state W N color S _ sw sn fn)
   have re (A p : Nat) : A*(3*(p*2))=6*A*p:=by rw [show (6:Nat)=3*2 by decide];ac_rfl
   simp only [Nat.pow_succ,re] at r pc
   simp only [Nat.add_mul] at fixed ⊢;omega
 · simp only [receiptCells,List.map_nil,List.sum_nil,List.length_cons,List.length_nil]
   simp only [Nat.add_mul];omega
end GenericForest.BinaryProducer.Generator
