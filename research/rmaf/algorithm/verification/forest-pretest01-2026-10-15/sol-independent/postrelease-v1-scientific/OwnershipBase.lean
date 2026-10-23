import Requests

namespace Universal233.Assembly
open RMAF CoreProgram SourceCoverage VertexGeometry

def parentTag (A B : List Nat) : Nat → Nat := taggedColor A B (fun _ => 0) (fun _ => 0) (fun _ => 0)

def parentGroups (F : List (List Nat)) (A B : List Nat) (i : Nat) : List (List Nat) :=
  F.filter fun b => b.all fun x => parentTag A B x == i

theorem parentGroups_mem (F : List (List Nat)) (A B b : List Nat) (i : Nat) :
    b ∈ parentGroups F A B i ↔ b ∈ F ∧ ∀ x, x ∈ b → parentTag A B x = i := by
  simp only [parentGroups,List.mem_filter,List.all_eq_true,beq_iff_eq]

theorem parentGroups_belongs (F : List (List Nat)) (A B : List Nat) :
    ∀ i b, b ∈ parentGroups F A B i → b ∈ F := by
  intro i b hb
  exact ((parentGroups_mem F A B b i).1 hb).1

theorem parentGroups_disjoint (F : List (List Nat)) (A B : List Nat) :
    ∀ i j, i ≠ j → ∀ P, P ∈ parentGroups F A B i → ∀ Q, Q ∈ parentGroups F A B j →
      ∀ x, x ∈ P → x ∈ Q → False := by
  intro i j hij P hP Q hQ x hx hy
  have hp := ((parentGroups_mem F A B P i).1 hP).2 x hx
  have hq := ((parentGroups_mem F A B Q j).1 hQ).2 x hy
  exact hij (hp.symm.trans hq)

theorem parentGroups_A (F : List (List Nat)) (A B b : List Nat) (hb : b ∈ F)
    (hs : ∀ x, x ∈ b → x ∈ A) : b ∈ parentGroups F A B 0 := by
  apply (parentGroups_mem F A B b 0).2
  refine ⟨hb,?_⟩
  intro x hx
  simp [parentTag,taggedColor,hs x hx]

theorem parentGroups_B (F : List (List Nat)) (A B b : List Nat) (hb : b ∈ F)
    (hab : ∀ x, x ∈ A → x ∈ B → False)
    (hs : ∀ x, x ∈ b → x ∈ B) : b ∈ parentGroups F A B 1 := by
  apply (parentGroups_mem F A B b 1).2
  refine ⟨hb,?_⟩
  intro x hx
  have hn : x ∉ A := fun h => hab x h (hs x hx)
  simp [parentTag,taggedColor,hn,hs x hx]

theorem parentGroups_C (F : List (List Nat)) (A B C b : List Nat) (hb : b ∈ F)
    (hac : ∀ x, x ∈ A → x ∈ C → False) (hbc : ∀ x, x ∈ B → x ∈ C → False)
    (hs : ∀ x, x ∈ b → x ∈ C) : b ∈ parentGroups F A B 2 := by
  apply (parentGroups_mem F A B b 2).2
  refine ⟨hb,?_⟩
  intro x hx
  have hna : x ∉ A := fun h => hac x h (hs x hx)
  have hnb : x ∉ B := fun h => hbc x h (hs x hx)
  simp [parentTag,taggedColor,hna,hnb]

theorem parentGroups_1_subset_B (F : List (List Nat)) (A B : List Nat)
    (b : List Nat) (hb : b ∈ parentGroups F A B 1) : ∀ x, x ∈ b → x ∈ B := by
  intro x hx
  have h := ((parentGroups_mem F A B b 1).1 hb).2 x hx
  by_cases ha : x ∈ A <;> by_cases hb : x ∈ B <;> simp_all [parentTag,taggedColor]

theorem clears_A (t : Tree) (F : List (List Nat)) (A B : List Nat) (v : RMAF.Vertex)
    (hc : Clears t (parentGroups F A B 0) v) : ParentClears t F A (.at v) := by
  intro b hb hs z hz
  have hzv : z = v := by simpa [targets] using hz
  subst z
  exact hc b (parentGroups_A F A B b hb hs)

theorem clears_B (t : Tree) (F : List (List Nat)) (A B : List Nat) (v : RMAF.Vertex)
    (hab : ∀ x, x ∈ A → x ∈ B → False)
    (hc : Clears t (parentGroups F A B 1) v) : ParentClears t F B (.at v) := by
  intro b hb hs z hz
  have hzv : z = v := by simpa [targets] using hz
  subst z
  exact hc b (parentGroups_B F A B b hb hab hs)

theorem clears_C (t : Tree) (F : List (List Nat)) (A B C : List Nat) (v : RMAF.Vertex)
    (hac : ∀ x, x ∈ A → x ∈ C → False) (hbc : ∀ x, x ∈ B → x ∈ C → False)
    (hc : Clears t (parentGroups F A B 2) v) : ParentClears t F C (.at v) := by
  intro b hb hs z hz
  have hzv : z = v := by simpa [targets] using hz
  subst z
  exact hc b (parentGroups_C F A B C b hb hac hbc hs)

theorem keeps_clear (t : Tree) (F : List (List Nat)) (A : List Nat) : ParentClears t F A .keep := by
  simp [ParentClears,targets]

theorem both_clear (t : Tree) (F : List (List Nat)) (A : List Nat) (v w : RMAF.Vertex)
    (hv : ParentClears t F A (.at v)) (hw : ParentClears t F A (.at w)) :
    ParentClears t F A (.both v w) := by
  intro b hb hs z hz
  simp only [targets,List.mem_cons,List.not_mem_nil,or_false] at hz
  rcases hz with hve | hwe
  · exact hv b hb hs z (by simpa [targets] using hve)
  · exact hw b hb hs z (by simpa [targets] using hwe)

theorem internal_keep (t : Tree) : ∀ v, v ∈ targets .keep → ¬selectedLeaves (leaves t) t v := by
  simp [targets]

theorem internal_at (t : Tree) (v : RMAF.Vertex) (hi : ¬selectedLeaves (leaves t) t v) :
    ∀ z, z ∈ targets (.at v) → ¬selectedLeaves (leaves t) t z := by
  simpa [targets] using hi

theorem internal_both (t : Tree) (v w : RMAF.Vertex)
    (hv : ¬selectedLeaves (leaves t) t v) (hw : ¬selectedLeaves (leaves t) t w) :
    ∀ z, z ∈ targets (.both v w) → ¬selectedLeaves (leaves t) t z := by
  simp [targets,hv,hw]

def BranchSolution (target source : Tree) (A B C : List Nat) (F : List (List Nat))
    (q : Nat) (a b c : Request) : Prop :=
    ∃ o, o ∈ (generate source (requestedColor target A B a b c) q).outputs ∧
      RefinesBlocks F o.partition ∧ RefinesBlocks o.partition [A,B,C] ∧
      partitionCheck (leaves source) o.partition = true ∧
      CutRealization.RealizedOutput source o ∧ o.sourceCuts.length ≤ q ∧
      ParentClears target o.partition A a ∧ ParentClears target o.partition B b ∧
      ParentClears target o.partition C c

/-- Original agreement, not a pre-supplied abstract ownership witness, chooses
one of the three actual whole-source clique generator calls. -/
theorem clique_actual_cover (target source : Tree) (A B C : List Nat)
    (F : List (List Nat)) (v : RMAF.Vertex) (q : Nat)
    (ht : (leaves target).Nodup) (hs : (leaves source).Nodup)
    (hlabels : ∀ x, x ∈ leaves source → x ∈ leaves target)
    (hf : agreement target source F = true)
    (hpp : partitionCheck (leaves source) [A,B,C] = true)
    (hab : ∀ x, x ∈ A → x ∈ B → False)
    (hac : ∀ x, x ∈ A → x ∈ C → False)
    (hbc : ∀ x, x ∈ B → x ∈ C → False)
    (hfp : RefinesBlocks F [A,B,C])
    (hi : ¬selectedLeaves (leaves target) target v) (hq : F.length - 1 ≤ q) :
    BranchSolution target source A B C F q .keep (.at v) (.at v) ∨
    BranchSolution target source A B C F q (.at v) .keep (.at v) ∨
    BranchSolution target source A B C F q (.at v) (.at v) .keep := by
  have hpt : partitionCheck (leaves target) F = true := by
    have h := hf; simp only [agreement,Bool.and_eq_true] at h; exact h.1.1.1.1
  have hps : partitionCheck (leaves source) F = true := by
    have h := hf; simp only [agreement,Bool.and_eq_true] at h; exact h.1.1.1.2
  have hes : pairwiseEmbeddings source F = true := (agreement_graph_factors target source F hf).2.1
  have build : ∀ a b c, (∀ z, z ∈ targets a → ¬selectedLeaves (leaves target) target z) →
      (∀ z, z ∈ targets b → ¬selectedLeaves (leaves target) target z) →
      (∀ z, z ∈ targets c → ¬selectedLeaves (leaves target) target z) →
      ParentClears target F A a → ParentClears target F B b → ParentClears target F C c →
      BranchSolution target source A B C F q a b c := by
    intro a b c hia hib hic ca cb cc
    exact requests_whole_source target source A B C F a b c q ht hs hlabels hpt hps hes hpp
      hab hac hbc hfp hia hib hic ca cb cc hq
  have own := executable_clique_survivor_cover target source F (parentGroups F A B) v hf
    (parentGroups_belongs F A B) (parentGroups_disjoint F A B)
  rcases own with ⟨cb,cc⟩ | ⟨ca,cc⟩ | ⟨ca,cb⟩
  · exact Or.inl (build .keep (.at v) (.at v) (internal_keep target)
      (internal_at target v hi) (internal_at target v hi) (keeps_clear target F A)
      (clears_B target F A B v hab cb) (clears_C target F A B C v hac hbc cc))
  · exact Or.inr (Or.inl (build (.at v) .keep (.at v) (internal_at target v hi)
      (internal_keep target) (internal_at target v hi) (clears_A target F A B v ca)
      (keeps_clear target F B) (clears_C target F A B C v hac hbc cc)))
  · exact Or.inr (Or.inr (build (.at v) (.at v) .keep (internal_at target v hi)
      (internal_at target v hi) (internal_keep target) (clears_A target F A B v ca)
      (clears_B target F A B v hab cb) (keeps_clear target F C)))

end Universal233.Assembly
