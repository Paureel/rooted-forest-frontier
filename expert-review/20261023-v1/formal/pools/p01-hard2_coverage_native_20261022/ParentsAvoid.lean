import ActualSelector
open RMAF VertexGeometry ForestState ForestGroups RestrictionBridge Universal233
namespace ContactedHard2Survival

def ParentAvoids (T : Tree) (F : List (List Nat)) (A : List Nat) (v : RMAF.Vertex) : Prop :=
 ∀ K,K∈F→K⊆A→v∉minimalVertices K T

theorem two_parent_avoidance (T : Tree) (F : List (List Nat)) (A B : List Nat) (v : RMAF.Vertex)
 (nonempty : ∀K,K∈F→K≠[]) (emb : pairwiseEmbeddings T F=true)
 (apart : ∀x,x∈A→x∈B→False) : ParentAvoids T F A v ∨ ParentAvoids T F B v := by
 classical
 by_cases ca : ParentAvoids T F A v
 · exact Or.inl ca
 · right
   obtain ⟨K,kF,kA,vK⟩ : ∃K,K∈F ∧ K⊆A ∧ v∈minimalVertices K T := by
    apply Classical.byContradiction
    intro no
    apply ca
    intro K kF kA vK
    exact no ⟨K,kF,kA,vK⟩
   intro L lF lB vL
   have eq:=IndependentOneExchange.shared_hull_block_equal emb kF lF vK vL
   obtain ⟨x,xK⟩:=List.exists_mem_of_ne_nil K (nonempty K kF)
   exact apart x (kA xK) (lB (eq ▸ xK))

theorem three_parent_avoidance (T : Tree) (F : List (List Nat)) (A B C : List Nat) (v : RMAF.Vertex)
 (nonempty : ∀K,K∈F→K≠[]) (emb : pairwiseEmbeddings T F=true)
 (ab : ∀x,x∈A→x∈B→False) (ac : ∀x,x∈A→x∈C→False) (bc : ∀x,x∈B→x∈C→False) :
 (ParentAvoids T F B v ∧ ParentAvoids T F C v) ∨
 (ParentAvoids T F A v ∧ ParentAvoids T F C v) ∨
 (ParentAvoids T F A v ∧ ParentAvoids T F B v) := by
 have x:=two_parent_avoidance T F A B v nonempty emb ab
 have y:=two_parent_avoidance T F A C v nonempty emb ac
 have z:=two_parent_avoidance T F B C v nonempty emb bc
 rcases x with a|b
 · rcases z with b|c
   · exact Or.inr (Or.inr ⟨a,b⟩)
   · exact Or.inr (Or.inl ⟨a,c⟩)
 · rcases y with a|c
   · exact Or.inr (Or.inr ⟨a,b⟩)
   · exact Or.inl ⟨b,c⟩

theorem four_parent_avoidance (T : Tree) (F : List (List Nat)) (A B C : List Nat) (v w : RMAF.Vertex)
 (nonempty : ∀K,K∈F→K≠[]) (emb : pairwiseEmbeddings T F=true)
 (ab : ∀x,x∈A→x∈B→False) (bc : ∀x,x∈B→x∈C→False) :
 (ParentAvoids T F B v ∧ ParentAvoids T F C w) ∨
 (ParentAvoids T F B v ∧ ParentAvoids T F B w) ∨
 (ParentAvoids T F A v ∧ ParentAvoids T F C w) ∨
 (ParentAvoids T F A v ∧ ParentAvoids T F B w) := by
 have x:=two_parent_avoidance T F A B v nonempty emb ab
 have y:=two_parent_avoidance T F B C w nonempty emb bc
 rcases x with a|b
 · rcases y with b|c
   · exact Or.inr (Or.inr (Or.inr ⟨a,b⟩))
   · exact Or.inr (Or.inr (Or.inl ⟨a,c⟩))
 · rcases y with bw|c
   · exact Or.inr (Or.inl ⟨b,bw⟩)
   · exact Or.inl ⟨b,c⟩

theorem agreement_nonempty (T S : Tree) (F : List (List Nat)) (a : agreement T S F=true) :
 ∀K,K∈F→K≠[] := by
 have a:=a
 simp only [agreement,Bool.and_eq_true] at a
 have p:=a.1.1.1.1
 simp only [partitionCheck,Bool.and_eq_true] at p
 intro K kF empty
 have good:=List.all_eq_true.1 p.1.1 K kF
 simp [empty] at good

theorem agreement_target_embedding (T S : Tree) (F : List (List Nat)) (a : agreement T S F=true) :
 pairwiseEmbeddings T F=true := by
 have checks:=a
 simp only [agreement,Bool.and_eq_true] at checks
 exact checks.1.2
end ContactedHard2Survival

-- Author integration type/axiom reports; proof text above is unchanged apart from recorded import edits.
set_option pp.universes true
#check @ContactedHard2Survival.two_parent_avoidance
#print axioms ContactedHard2Survival.two_parent_avoidance
#check @ContactedHard2Survival.three_parent_avoidance
#print axioms ContactedHard2Survival.three_parent_avoidance
#check @ContactedHard2Survival.four_parent_avoidance
#print axioms ContactedHard2Survival.four_parent_avoidance
#check @ContactedHard2Survival.agreement_nonempty
#print axioms ContactedHard2Survival.agreement_nonempty
#check @ContactedHard2Survival.agreement_target_embedding
#print axioms ContactedHard2Survival.agreement_target_embedding
