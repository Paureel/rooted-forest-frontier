import GeneratorTraversal
namespace GenericForest.BinaryProducer.Generator
open BinaryProvider GenericForest.ScalarBits Universal233.WholeSourceWork Universal233.CoreWork

theorem leafListBits_count (B : Block) (T : BinaryProvider.Tree) :
 (leafListBits B T).value.length≤treeNodes (treeValue T) := by
 rw [leafListBits_value];exact leafList_length _ _

theorem leafListBits_cost (W N : Nat) (B : Block) (T : BinaryProvider.Tree)
 (bw : BlockWidth W B) (tw : TreeWidth W T) (tn : treeNodes (treeValue T)≤N) :
 (leafListBits B T).work≤(beta W*(4*(B.length+1))+32*(N+1))*treeNodes (treeValue T) := by
 induction T with
 | leaf x=>
  have a:=containsLabel_cost W x B (tw x (by simp [leavesBits])) bw
  simp only [leafListBits,treeValue,treeNodes,Nat.mul_one];omega
 | node l r ihl ihr=>
  have ln : treeNodes (treeValue l)≤N:=by simp only [treeValue,treeNodes] at tn;omega
  have rn : treeNodes (treeValue r)≤N:=by simp only [treeValue,treeNodes] at tn;omega
  have a:=ihl (fun x hx=>tw x (by simp [leavesBits,hx])) ln
  have b:=ihr (fun x hx=>tw x (by simp [leavesBits,hx])) rn
  have al:=Nat.le_trans (leafListBits_count B l) ln
  have bl:=Nat.le_trans (leafListBits_count B r) rn
  have ap:=prependAddresses_work false (leafListBits B l).value
  have bp:=prependAddresses_work true (leafListBits B r).value
  simp only [leafListBits,appendSpine_work,prependAddresses_value,RMAF.prependSide,List.length_map,treeValue,treeNodes,Nat.mul_add,Nat.mul_one] at a b ⊢
  omega

theorem regionBits_cost (v a : RMAF.Vertex) : (regionBits v a).work≤4*(v.length+1) := by
 induction v generalizing a with
 | nil=>cases a with
  | nil=>decide
  | cons b bs=>cases b <;> simp only [regionBits,List.length_nil,Nat.zero_add,Nat.mul_one,Nat.le_refl]
 | cons b v ih=>
  cases a with
  | nil=>simp [regionBits];omega
  | cons c a=>
   have h:=ih a
   dsimp only [regionBits];split <;> dsimp only [Charged.work] <;> simp only [List.length_cons] <;> omega

def colorCost (W N P : Nat) := (beta W*8+32*(N+1))*N+4*(P+1)+8

theorem colorBits_cost (W N P : Nat) (T : BinaryProvider.Tree) (v : RMAF.Vertex)
 (tw : TreeWidth W T) (tn : treeNodes (treeValue T)≤N) (vp : v.length≤P) (x : Bits) (xw : x.length≤W) :
 (colorBits T v x).work≤colorCost W N P := by
 have a:=leafListBits_cost W N [x] T (by intro y hy;simpa using (List.mem_singleton.mp hy ▸ xw)) tw tn
 have b:=regionBits_cost v ((leafListBits [x] T).value.headD [])
 have m:=Nat.mul_le_mul_left (beta W*8+32*(N+1)) tn
 simp only [List.length_singleton,Nat.reduceAdd,Nat.reduceMul] at a
 simp only [colorBits];unfold colorCost;omega

def preparationCost (W N B C : Nat) := leafCost N W+beta W*(8*(N+1)^2)+
 (34*(B+2)+8)*(N+1)+(C+4*W+8*(N+1)+32)*N+16

def generationCost (W N B C : Nat) := preparationCost W N B C+
 64*(runCoefficient W (inputResource N)+6)*(N+1)

/-- Complete executable source work, including initial colors and fuel,
failed/pruned prefixes, stored counters and every receipt append. -/
theorem generateBits_cost (W N B C : Nat) (S : BinaryProvider.Tree) (color : Bits→Charged Color) (q : Bits)
 (sw : TreeWidth W S) (sn : treeNodes (treeValue S)≤N)
 (bp : 1≤B) (qw : q.length≤B) (cc : ∀x,x.length≤W→(color x).work≤C) :
 (generateBits S color q).work≤generationCost W N B C*2^(decode q) := by
 have a:=leavesCopy_cost N W S sw sn
 have lc:=Nat.le_trans (bitsLeaves_count S) sn
 have nd:=(nodupLabels_projects W (leavesBits S) sw).2
 have nb:=GenericForest.CheckCorrespondence.meterNodup_bound (blockValue (leavesBits S))
 have np:=Nat.mul_le_mul_left 8 (Nat.pow_le_pow_left (Nat.add_le_add_right lc 1) 2)
 have nm:=Nat.mul_le_mul_left (beta W) np
 simp only [blockValue_length] at nb
 have ndcap : (nodupLabels (leavesBits S)).work≤beta W*(8*(N+1)^2):=Nat.le_trans nd (Nat.mul_le_mul_left _ (Nat.le_trans nb np))
 have f:=fuelBits_cost B q (leavesBits S).tail bp qw
 have fn : (fuelBits q (leavesBits S).tail).value.length≤N:=by rw [fuelBits_length];have z:=Nat.min_le_right (decode q) (leavesBits S).tail.length;simp only [List.length_tail] at z ⊢;omega
 have fb:=Nat.mul_le_mul_left (34*(B+2)+8) (show (leavesBits S).tail.length+1≤N+1 by simp only [List.length_tail];omega)
 have tr:=Nat.le_trans (fromTreeBits_cost W N C color cc [] S sw (by simpa only [List.length_nil,Nat.zero_add] using sn))
  (Nat.mul_le_mul_left (C+4*W+8*(N+1)+32) sn)
 have run:=runBits_polynomial_exponential W (inputResource N) (fuelBits q (leavesBits S).tail).value _ [] [] (initial_state W N color S _ sw sn fn)
 have fp : (fuelBits q (leavesBits S).tail).value.length≤decode q:=by rw [fuelBits_length];exact Nat.min_le_left _ _
 have pow:=Nat.pow_le_pow_right (n:=2) (by decide) (Nat.add_le_add_right fp 1)
 simp only [Nat.pow_succ] at pow
 have runscale:=Nat.mul_le_mul (Nat.mul_le_mul_left (32*(runCoefficient W (inputResource N)+6)) (Nat.add_le_add_right fn 1)) pow
 have rearrange : 32*(runCoefficient W (inputResource N)+6)*(N+1)*(2^(decode q)*2)=
  (64*(runCoefficient W (inputResource N)+6)*(N+1))*2^(decode q):=by rw [show (64:Nat)=32*2 by decide];ac_rfl
 have runcap : (runBits (fuelBits q (leavesBits S).tail).value (fromTreeBits color [] S).value [] []).work≤
  (64*(runCoefficient W (inputResource N)+6)*(N+1))*2^(decode q):=by rw [←rearrange];exact Nat.le_trans run runscale
 have positive : 1≤2^(decode q):=Nat.one_le_pow _ _ (by decide)
 have paid:=Nat.mul_le_mul_left (preparationCost W N B C) positive
 simp only [Nat.mul_one] at paid
 dsimp only [generateBits];simp only [leavesCopy_value]
 split
 · unfold generationCost;simp only [Nat.add_mul];unfold preparationCost at paid ⊢;omega
 · unfold generationCost;simp only [Nat.add_mul];unfold preparationCost at paid ⊢;omega
end GenericForest.BinaryProducer.Generator
