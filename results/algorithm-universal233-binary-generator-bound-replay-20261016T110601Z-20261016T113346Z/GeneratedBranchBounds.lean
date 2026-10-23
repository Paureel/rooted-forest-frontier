import OverlapTraversal
namespace GenericForest.BinaryProducer
open BinaryProvider GenericForest.ScalarBits Universal233.WholeSourceWork Universal233.CoreWork

theorem sourceAtBits_mem (i : Bits) (ss : List BinaryProvider.Tree) (s : BinaryProvider.Tree)
 (h : (sourceAtBits i ss).value=some s) : s∈ss := by
 induction ss generalizing i with
 | nil=>simp [sourceAtBits] at h
 | cons a ss ih=>
  dsimp only [sourceAtBits] at h;split at h
  · cases h;simp
  · exact List.mem_cons_of_mem _ (ih _ h)

def lookupCost (I S : Nat) := (56*(I+1)+24*(I+2)+8)*(S+1)

theorem sourceAtBits_cost (I : Nat) (i : Bits) (ss : List BinaryProvider.Tree) (ip : 1≤I) (iw : i.length≤I) :
 (sourceAtBits i ss).work≤lookupCost I ss.length := by
 induction ss generalizing i with
 | nil=>simp [sourceAtBits];unfold lookupCost;omega
 | cons s ss ih=>
  have e:=copiedEqual_work I i [] iw (by simp)
  have d:=subtractBits_work i [true]
  have dl:=subtractBits_length i [true]
  have r:=ih (subtractBits i [true]).value (by simp only [List.length_singleton] at dl;omega)
  dsimp only [sourceAtBits];split <;> dsimp only [Charged.work]
  all_goals unfold lookupCost at r ⊢;simp only [List.length_cons,List.length_nil,List.length_singleton,Nat.mul_add,Nat.mul_one] at d r ⊢;omega

def rawCost (W N B I S P : Nat) := lookupCost I S+Generator.generationCost W N B (Generator.colorCost W N P)+8

theorem rawProducer_cost (W N B I S P : Nat) (t : BinaryProvider.Tree) (ss : List BinaryProvider.Tree)
 (i : Bits) (v : RMAF.Vertex) (q : Bits)
 (tw : TreeWidth W t) (tn : treeNodes (treeValue t)≤N) (sw : SourcesWidth W ss)
 (sn : ∀s∈ss,treeNodes (treeValue s)≤N) (ssn : ss.length≤S)
 (bp : 1≤B) (qw : q.length≤B) (ip : 1≤I) (iw : i.length≤I) (vp : v.length≤P) :
 (rawProducer t ss i v q).work≤rawCost W N B I S P*2^(decode q) := by
 have l:=sourceAtBits_cost I i ss ip iw
 have lm:=Nat.mul_le_mul_left (56*(I+1)+24*(I+2)+8) (Nat.add_le_add_right ssn 1)
 have lc : (sourceAtBits i ss).work≤lookupCost I S:=Nat.le_trans l lm
 have pow : 1≤2^(decode q):=Nat.one_le_pow _ _ (by decide)
 have lp:=Nat.mul_le_mul_left (lookupCost I S+8) pow
 simp only [Nat.mul_one] at lp
 dsimp only [rawProducer]
 cases he : (sourceAtBits i ss).value with
 | none=>simp only;unfold rawCost;simp only [Nat.add_mul] at lp ⊢;omega
 | some s=>
  have sm:=sourceAtBits_mem i ss s he
  have g:=Generator.generateBits_cost W N B (Generator.colorCost W N P) s (Generator.colorBits t v) q
   (sw s sm) (sn s sm) bp qw (Generator.colorBits_cost W N P t v tw tn vp)
  simp only;unfold rawCost;simp only [Nat.add_mul] at lp ⊢;omega

theorem rawProducer_caps (W N : Nat) (t : BinaryProvider.Tree) (ss : List BinaryProvider.Tree) (i : Bits) (v : RMAF.Vertex) (q : Bits)
 (sw : SourcesWidth W ss) (sn : ∀s∈ss,treeNodes (treeValue s)≤N) :
 ∀o∈(rawProducer t ss i v q).value,Generator.OutputCap W (Generator.inputResource N) o := by
 dsimp only [rawProducer]
 cases he : (sourceAtBits i ss).value with
 | none=>simp
 | some s=>
  have sm:=sourceAtBits_mem i ss s he
  exact Generator.generateBits_output W N s (Generator.colorBits t v) q (sw s sm) (sn s sm)

theorem indexedOutputs_mem (i : Bits) (os : List Output) :
 ∀io∈(indexedOutputs i os).value,io.1=i ∧ io.2∈os := by
 induction os with
 | nil=>simp [indexedOutputs]
 | cons o os ih=>
  simp only [indexedOutputs,List.mem_cons]
  intro io hi;rcases hi with rfl|hi
  · exact ⟨rfl,Or.inl rfl⟩
  · have a:=ih io hi;exact ⟨a.1,Or.inr a.2⟩

theorem branchesProducer_caps (W N I : Nat) (t : BinaryProvider.Tree) (ss : List BinaryProvider.Tree) (h : OverlapBits) (q : Bits)
 (sw : SourcesWidth W ss) (sn : ∀s∈ss,treeNodes (treeValue s)≤N)
 (left : h.left.length≤I) (right : h.right.length≤I) :
 ∀io∈(branchesProducer t ss h q).value,
 BranchCaps (Generator.inputResource N) W I (Generator.inputResource N) (Generator.inputResource N+1) io := by
 have aux (i : Bits) (iw : i.length≤I) (io : Bits×Output)
  (mem : io∈(indexedOutputs i (rawProducer t ss i h.vertex q).value).value) :
  BranchCaps (Generator.inputResource N) W I (Generator.inputResource N) (Generator.inputResource N+1) io := by
  have m:=indexedOutputs_mem i _ io mem
  have c:=rawProducer_caps W N t ss i h.vertex q sw sn io.2 m.2
  exact ⟨m.1 ▸ iw,c.1,c.2.1,c.2.2.1,c.2.2.2.1⟩
 simp only [branchesProducer,appendSpine_value,List.mem_append]
 intro io hi;rcases hi with hi|hi
 · exact aux h.left left io hi
 · exact aux h.right right io hi

def branchesCost (W N B I S P : Nat) := 2*rawCost W N B I S P+87

theorem branchesProducer_cost (W N B I S P : Nat) (t : BinaryProvider.Tree) (ss : List BinaryProvider.Tree) (h : OverlapBits) (q : Bits)
 (tw : TreeWidth W t) (tn : treeNodes (treeValue t)≤N) (sw : SourcesWidth W ss)
 (sn : ∀s∈ss,treeNodes (treeValue s)≤N) (ssn : ss.length≤S)
 (bp : 1≤B) (qw : q.length≤B) (ip : 1≤I) (left : h.left.length≤I) (right : h.right.length≤I) (vp : h.vertex.length≤P) :
 (branchesProducer t ss h q).work≤branchesCost W N B I S P*2^(decode q) := by
 have a:=rawProducer_cost W N B I S P t ss h.left h.vertex q tw tn sw sn ssn bp qw ip left vp
 have b:=rawProducer_cost W N B I S P t ss h.right h.vertex q tw tn sw sn ssn bp qw ip right vp
 have ac:=rawProducer_exponential_count t ss h.left h.vertex q
 have bc:=rawProducer_exponential_count t ss h.right h.vertex q
 have pow : 1≤2^(decode q):=Nat.one_le_pow _ _ (by decide)
 rw [branchesProducer_multiplicity_paid]
 unfold branchesCost;simp only [Nat.add_mul,Nat.mul_assoc] at a b ⊢;omega
end GenericForest.BinaryProducer
