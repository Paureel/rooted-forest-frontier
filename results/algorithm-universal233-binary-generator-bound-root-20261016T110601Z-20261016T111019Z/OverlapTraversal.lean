import GeneratorOutputCaps
namespace GenericForest.BinaryProducer
open BinaryProvider GenericForest.ScalarBits GenericForest.CheckCorrespondence Universal233.WholeSourceWork Universal233.CoreWork

theorem zipBits_count (i : Bits) (ss : List BinaryProvider.Tree) : (zipBits i ss).value.length=ss.length := by
 induction ss generalizing i <;> simp_all [zipBits]

theorem zipBits_caps (i : Bits) (ss : List BinaryProvider.Tree) :
 ∀p∈(zipBits i ss).value,p.1∈ss ∧ p.2.length≤i.length+ss.length := by
 induction ss generalizing i with
 | nil=>simp [zipBits]
 | cons s ss ih=>
  have r:=ih (incrementBits i).value
  have il:=addCarry_length i [] true
  simp only [List.length_nil,Nat.max_zero] at il
  change (incrementBits i).value.length≤i.length+1 at il
  simp only [zipBits,List.mem_cons,List.length_cons]
  intro p hp;rcases hp with rfl|hp
  · exact ⟨by simp,by dsimp only;omega⟩
  · have z:=r p hp;exact ⟨Or.inr z.1,by omega⟩

theorem zipBits_cost (K : Nat) (i : Bits) (ss : List BinaryProvider.Tree) (h : i.length+ss.length≤K) :
 (zipBits i ss).work≤(12*(K+1)+8)*(ss.length+1) := by
 induction ss generalizing i with
 | nil=>simp [zipBits] <;> omega
 | cons s ss ih=>
  have il:=addCarry_length i [] true
  have iw:=addCarry_work i [] true
  simp only [List.length_nil,Nat.max_zero,Nat.add_zero] at il iw
  change (incrementBits i).value.length≤i.length+1 at il
  change (incrementBits i).work≤12*(i.length+1) at iw
  have r:=ih (incrementBits i).value (by simp only [List.length_cons] at h;omega)
  simp only [zipBits,List.length_cons,Nat.mul_add,Nat.mul_one] at r ⊢;omega

def minimalCost (N W : Nat) := beta W*((16*(2*N+2)+16)*(N+1)*N)

theorem minimalLabels_cost (N W : Nat) (B : Block) (T : BinaryProvider.Tree)
 (bw : BlockWidth W B) (tw : TreeWidth W T) (bn : B.length≤N) (tn : treeNodes (treeValue T)≤N) :
 (minimalLabels B T).work≤minimalCost N W := by
 have a:=(minimalLabels_projects W B T bw tw).2
 have b:=meterMinimal_bound (blockValue B) (treeValue T) N tn
 have n:=Nat.mul_le_mul_right (N+1) (show 16*((blockValue B).length+N+2)+16≤16*(2*N+2)+16 by simp only [blockValue_length];omega)
 have m:=Nat.mul_le_mul n tn
 exact Nat.le_trans a (Nat.mul_le_mul_left _ (Nat.le_trans b (by simpa only [spanCap] using m)))

theorem minimalLabels_caps (N : Nat) (B : Block) (T : BinaryProvider.Tree) (tn : treeNodes (treeValue T)≤N) :
 (minimalLabels B T).value.length≤N ∧ ∀v∈(minimalLabels B T).value,v.length≤N := by
 rw [minimalLabels_value]
 exact ⟨Nat.le_trans (minimal_length _ _) tn,fun v hv=>by have a:=minimal_address _ _ v hv;have b:=leaves_nodes (treeValue T);omega⟩

def sharedCost (N : Nat) := (8*(N+1)*(N+1)+4)*(N+1)

theorem firstShared_cost (N : Nat) (B A : Addresses) (bn : B.length≤N) (an : A.length≤N)
 (paths : ∀v∈A,v.length≤N) : (firstShared B A).work≤sharedCost N := by
 have aux : (firstShared B A).work≤(8*(N+1)*(N+1)+4)*(A.length+1) := by
  induction A with
  | nil=>simp [firstShared] <;> omega
  | cons v vs ih=>
   have a:=meterVertexContains_bound v B N (paths v (by simp))
   have m:=Nat.mul_le_mul_left (8*(N+1)) (Nat.add_le_add_right bn 1)
   have r:=ih (by simp only [List.length_cons] at an;omega) (fun x hx=>paths x (by simp [hx]))
   dsimp only [firstShared];split <;> dsimp only [Charged.work]
   all_goals simp only [List.length_cons,Nat.mul_add,Nat.mul_one] at a m r ⊢;omega
 exact Nat.le_trans aux (Nat.mul_le_mul_left _ (Nat.add_le_add_right an 1))

theorem indexLt_cost (I : Nat) (a b : Bits) (aw : a.length≤I) (bw : b.length≤I) :
 (indexLt a b).work≤32*(I+2) := by
 have awork:=addCarry_work a [] true
 have al:=addCarry_length a [] true
 have bwork:=(compare_family_work (incrementBits a).value b).2.1
 simp only [indexLt,incrementBits,List.length_nil,Nat.add_zero,Nat.max_zero] at *;omega

def overlapPairCost (N W I : Nat) := 32*(I+2)+2*leafCost N W+2*minimalCost N W+sharedCost N+12

def IndexedCaps (N W I : Nat) (xs : List (BinaryProvider.Tree×Bits)) : Prop :=
 ∀p∈xs,TreeWidth W p.1 ∧ treeNodes (treeValue p.1)≤N ∧ p.2.length≤I

theorem overlapRow_count (t a) (bs : List (BinaryProvider.Tree×Bits)) : (overlapRow t a bs).value.length≤bs.length := by
 induction bs with
 | nil=>simp [overlapRow]
 | cons b bs ih=>
  dsimp only [overlapRow];split
  · cases h : (firstShared _ _).value <;> simp only [List.length_cons] at * <;> omega
  · simp only [List.length_cons];omega

theorem overlapRow_cost (N W I : Nat) (t : BinaryProvider.Tree) (a : BinaryProvider.Tree×Bits) (bs : List (BinaryProvider.Tree×Bits))
 (tw : TreeWidth W t) (tn : treeNodes (treeValue t)≤N)
 (ac : TreeWidth W a.1 ∧ treeNodes (treeValue a.1)≤N ∧ a.2.length≤I) (bc : IndexedCaps N W I bs) :
 (overlapRow t a bs).work≤overlapPairCost N W I*(bs.length+1) := by
 induction bs with
 | nil=>simp [overlapRow];unfold overlapPairCost;omega
 | cons b bs ih=>
  have bcap:=bc b (by simp)
  have tail:=ih (fun p hp=>bc p (by simp [hp]))
  have i:=indexLt_cost I a.2 b.2 ac.2.2 bcap.2.2
  have al:=leavesCopy_cost N W a.1 ac.1 ac.2.1
  have bl:=leavesCopy_cost N W b.1 bcap.1 bcap.2.1
  have am:=minimalLabels_cost N W (leavesBits a.1) t ac.1 tw (Nat.le_trans (bitsLeaves_count _) ac.2.1) tn
  have bm:=minimalLabels_cost N W (leavesBits b.1) t bcap.1 tw (Nat.le_trans (bitsLeaves_count _) bcap.2.1) tn
  have ash:=minimalLabels_caps N (leavesBits a.1) t tn
  have bsh:=minimalLabels_caps N (leavesBits b.1) t tn
  have sh:=firstShared_cost N (minimalLabels (leavesBits b.1) t).value (minimalLabels (leavesBits a.1) t).value bsh.1 ash.1 ash.2
  dsimp only [overlapRow];split <;> dsimp only [Charged.work]
  all_goals simp only [leavesCopy_value,List.length_cons,Nat.mul_add,Nat.mul_one] at tail ⊢
  all_goals unfold overlapPairCost at tail ⊢;omega

def overlapRowsCost (N W I S : Nat) := (overlapPairCost N W I*(S+1)+4*S+9)*(S+1)

theorem overlapRows_cost (N W I S : Nat) (t : BinaryProvider.Tree) (bs xs : List (BinaryProvider.Tree×Bits))
 (tw : TreeWidth W t) (tn : treeNodes (treeValue t)≤N) (bc : IndexedCaps N W I bs) (xc : IndexedCaps N W I xs)
 (bn : bs.length≤S) (xn : xs.length≤S) : (overlapRows t bs xs).work≤overlapRowsCost N W I S := by
 have aux : (overlapRows t bs xs).work≤(overlapPairCost N W I*(S+1)+4*S+9)*(xs.length+1) := by
  induction xs with
  | nil=>simp [overlapRows] <;> omega
  | cons a xs ih=>
   have row:=Nat.le_trans (overlapRow_cost N W I t a bs tw tn (xc a (by simp)) bc)
    (Nat.mul_le_mul_left _ (Nat.add_le_add_right bn 1))
   have count:=Nat.le_trans (overlapRow_count t a bs) bn
   have tail:=ih (fun p hp=>xc p (by simp [hp])) (by simp only [List.length_cons] at xn;omega)
   simp only [overlapRows,appendSpine_work,List.length_cons,Nat.mul_add,Nat.mul_one] at row tail ⊢;omega
 exact Nat.le_trans aux (Nat.mul_le_mul_left _ (Nat.add_le_add_right xn 1))

def overlapCost (N W S : Nat) := (12*(S+1)+8)*(S+1)+overlapRowsCost N W S S+4

theorem overlapProducer_cost (N W S : Nat) (t : BinaryProvider.Tree) (ss : List BinaryProvider.Tree)
 (tw : TreeWidth W t) (tn : treeNodes (treeValue t)≤N) (sw : SourcesWidth W ss)
 (sn : ∀s∈ss,treeNodes (treeValue s)≤N) (sc : ss.length≤S) :
 (overlapProducer t ss).work≤overlapCost N W S := by
 have z:=Nat.le_trans (zipBits_cost S [] ss (by simpa only [List.length_nil,Nat.zero_add] using sc))
  (Nat.mul_le_mul_left _ (Nat.add_le_add_right sc 1))
 have cap : IndexedCaps N W S (zipBits [] ss).value:=by
  intro p hp;have a:=zipBits_caps [] ss p hp
  exact ⟨sw p.1 a.1,sn p.1 a.1,by simp only [List.length_nil,Nat.zero_add] at a;omega⟩
 have len : (zipBits [] ss).value.length≤S:=by rw [zipBits_count];exact sc
 have r:=overlapRows_cost N W S S t _ _ tw tn cap cap len len
 simp only [overlapProducer];unfold overlapCost;omega
end GenericForest.BinaryProducer
