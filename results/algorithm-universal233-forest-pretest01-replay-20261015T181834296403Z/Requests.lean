import WholeSource

namespace Universal233.Assembly
open RMAF CoreProgram SourceCoverage VertexGeometry

inductive Request where
  | keep
  | at : RMAF.Vertex → Request
  | both : RMAF.Vertex → RMAF.Vertex → Request

def targets : Request → List RMAF.Vertex
  | .keep => []
  | .at v => [v]
  | .both v w => [v,w]

def localColor (t : Tree) : Request → Nat → Nat
  | .keep => fun _ => 0
  | .at v => colorLabel t v
  | .both v w => fun x => 4 * colorLabel t v x + colorLabel t w x

theorem colorLabel_le_three (t : Tree) (v : RMAF.Vertex) (x : Nat) : colorLabel t v x ≤ 3 :=
  region_le_three v ((leafList [x] t).headD [])

theorem request_mono_iff_clear (t : Tree) (b : List Nat) (r : Request)
    (hn : (leaves t).Nodup) (hl : ∀ x, x ∈ b → x ∈ leaves t)
    (hi : ∀ v, v ∈ targets r → ¬selectedLeaves (leaves t) t v) :
    LabelMonochromatic (localColor t r) b ↔
      ∀ v, v ∈ targets r → v ∉ minimalVertices b t := by
  have hno : ∀ v, v ∈ targets r → ¬selectedLeaves b t v := by
    intro v hv hs
    exact hi v hv (selected_leaves_mono b (leaves t) t hl v hs)
  cases r with
  | keep => simp [targets,localColor,LabelMonochromatic]
  | «at» v =>
    have he := original_label_avoids_iff t b v hn hl (hno v (by simp [targets]))
    simpa [targets,localColor] using he.symm
  | both v w =>
    have hv := original_label_avoids_iff t b v hn hl (hno v (by simp [targets]))
    have hw := original_label_avoids_iff t b w hn hl (hno w (by simp [targets]))
    constructor
    · intro hm z hz
      simp only [targets,List.mem_cons,List.not_mem_nil,or_false] at hz
      have hmv : LabelMonochromatic (colorLabel t v) b := by
        intro x y hx hy
        have h := hm x y hx hy
        change 4 * colorLabel t v x + colorLabel t w x = 4 * colorLabel t v y + colorLabel t w y at h
        have bx := colorLabel_le_three t w x
        have bound_y := colorLabel_le_three t w y
        omega
      have hmw : LabelMonochromatic (colorLabel t w) b := by
        intro x y hx hy
        have h := hm x y hx hy
        change 4 * colorLabel t v x + colorLabel t w x = 4 * colorLabel t v y + colorLabel t w y at h
        have bx := colorLabel_le_three t w x
        have bound_y := colorLabel_le_three t w y
        omega
      rcases hz with rfl | rfl
      · exact hv.2 hmv
      · exact hw.2 hmw
    · intro hc x y hx hy
      have hmv := hv.1 (hc v (by simp [targets]))
      have hmw := hw.1 (hc w (by simp [targets]))
      simp only [localColor,hmv x y hx hy,hmw x y hx hy]

theorem tagged_extract_A (A B b : List Nat) (ca cb cc : Nat → Nat)
    (hs : ∀ x, x ∈ b → x ∈ A)
    (hm : LabelMonochromatic (taggedColor A B ca cb cc) b) : LabelMonochromatic ca b := by
  intro x y hx hy
  have h := hm x y hx hy
  simp only [taggedColor,hs x hx,hs y hy,ite_true] at h
  omega

theorem tagged_extract_B (A B b : List Nat) (ca cb cc : Nat → Nat)
    (hab : ∀ x, x ∈ A → x ∈ B → False) (hs : ∀ x, x ∈ b → x ∈ B)
    (hm : LabelMonochromatic (taggedColor A B ca cb cc) b) : LabelMonochromatic cb b := by
  intro x y hx hy
  have h := hm x y hx hy
  have hnx : x ∉ A := fun ha => hab x ha (hs x hx)
  have hny : y ∉ A := fun ha => hab y ha (hs y hy)
  simp only [taggedColor,hnx,hny,hs x hx,hs y hy,ite_true,ite_false] at h
  omega

theorem tagged_extract_C (A B C b : List Nat) (ca cb cc : Nat → Nat)
    (hac : ∀ x, x ∈ A → x ∈ C → False) (hbc : ∀ x, x ∈ B → x ∈ C → False)
    (hs : ∀ x, x ∈ b → x ∈ C)
    (hm : LabelMonochromatic (taggedColor A B ca cb cc) b) : LabelMonochromatic cc b := by
  intro x y hx hy
  have h := hm x y hx hy
  have hxa : x ∉ A := fun ha => hac x ha (hs x hx)
  have hya : y ∉ A := fun ha => hac y ha (hs y hy)
  have hxb : x ∉ B := fun hb => hbc x hb (hs x hx)
  have hyb : y ∉ B := fun hb => hbc y hb (hs y hy)
  simp only [taggedColor,hxa,hya,hxb,hyb,ite_false] at h
  omega

def requestedColor (t : Tree) (A B : List Nat) (a b c : Request) : Nat → Nat :=
  taggedColor A B (localColor t a) (localColor t b) (localColor t c)

def ParentClears (t : Tree) (F : List (List Nat)) (A : List Nat) (r : Request) : Prop :=
  ∀ b, b ∈ F → (∀ x, x ∈ b → x ∈ A) → ∀ v, v ∈ targets r → v ∉ minimalVertices b t

/-- Complete actual whole-source ownership branch. All region/graph conclusions
are constructed at literal generate outputs; P/history safety is explicit. -/
theorem requests_whole_source (target source : Tree) (A B C : List Nat)
    (F : List (List Nat)) (a b c : Request) (q : Nat)
    (ht : (leaves target).Nodup) (hs : (leaves source).Nodup)
    (hlabels : ∀ x, x ∈ leaves source → x ∈ leaves target)
    (hpt : partitionCheck (leaves target) F = true)
    (hps : partitionCheck (leaves source) F = true)
    (hes : pairwiseEmbeddings source F = true)
    (hpp : partitionCheck (leaves source) [A,B,C] = true)
    (hab : ∀ x, x ∈ A → x ∈ B → False)
    (hac : ∀ x, x ∈ A → x ∈ C → False)
    (hbc : ∀ x, x ∈ B → x ∈ C → False)
    (hfp : RefinesBlocks F [A,B,C])
    (hia : ∀ v, v ∈ targets a → ¬selectedLeaves (leaves target) target v)
    (hib : ∀ v, v ∈ targets b → ¬selectedLeaves (leaves target) target v)
    (hic : ∀ v, v ∈ targets c → ¬selectedLeaves (leaves target) target v)
    (hca : ParentClears target F A a)
    (hcb : ParentClears target F B b)
    (hcc : ParentClears target F C c)
    (hq : F.length - 1 ≤ q) :
    ∃ o, o ∈ (generate source (requestedColor target A B a b c) q).outputs ∧
      RefinesBlocks F o.partition ∧ RefinesBlocks o.partition [A,B,C] ∧
      partitionCheck (leaves source) o.partition = true ∧
      CutRealization.RealizedOutput source o ∧ o.sourceCuts.length ≤ q ∧
      ParentClears target o.partition A a ∧ ParentClears target o.partition B b ∧
      ParentClears target o.partition C c := by
  have hin : ∀ d, d ∈ F → ∀ x, x ∈ d → x ∈ leaves target := by
    intro d hd x hx
    exact partitionCheck_subset _ F hpt (List.mem_flatten.mpr ⟨d,hd,hx⟩)
  have hma : ∀ d, d ∈ F → (∀ x, x ∈ d → x ∈ A) → LabelMonochromatic (localColor target a) d := by
    intro d hd hsub
    exact (request_mono_iff_clear target d a ht (hin d hd) hia).2 (hca d hd hsub)
  have hmb : ∀ d, d ∈ F → (∀ x, x ∈ d → x ∈ B) → LabelMonochromatic (localColor target b) d := by
    intro d hd hsub
    exact (request_mono_iff_clear target d b ht (hin d hd) hib).2 (hcb d hd hsub)
  have hmc : ∀ d, d ∈ F → (∀ x, x ∈ d → x ∈ C) → LabelMonochromatic (localColor target c) d := by
    intro d hd hsub
    exact (request_mono_iff_clear target d c ht (hin d hd) hic).2 (hcc d hd hsub)
  obtain ⟨o,ho,href,hbudget⟩ := tagged_whole_source_coverage source A B C F _ _ _
    hs hps hes hab hac hbc hfp hma hmb hmc q hq
  have hpout := CutRealization.generate_partition_check source _ q o ho
  have hmout := CutRealization.generate_monochromatic source _ q o ho
  have houtlabels : ∀ d, d ∈ o.partition → ∀ x, x ∈ d → x ∈ leaves target := by
    intro d hd x hx
    exact hlabels x (partitionCheck_subset _ o.partition hpout (List.mem_flatten.mpr ⟨d,hd,hx⟩))
  refine ⟨o,ho,href,tagged_output_refines_parents source A B C _ _ _ q o ho hpp hab hac hbc,
    hpout,CutRealization.generate_original_realization source _ q o ho,hbudget,?_,?_,?_⟩
  · intro d hd hsub
    apply (request_mono_iff_clear target d a ht (houtlabels d hd) hia).1
    exact tagged_extract_A A B d _ _ _ hsub (hmout d hd)
  · intro d hd hsub
    apply (request_mono_iff_clear target d b ht (houtlabels d hd) hib).1
    exact tagged_extract_B A B d _ _ _ hab hsub (hmout d hd)
  · intro d hd hsub
    apply (request_mono_iff_clear target d c ht (houtlabels d hd) hic).1
    exact tagged_extract_C A B C d _ _ _ hac hbc hsub (hmout d hd)

end Universal233.Assembly
