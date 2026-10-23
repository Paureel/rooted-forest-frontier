import Selector
import SourceEdge

/- Fresh nonauthor interface proof. Original G/E bodies are unchanged. -/
namespace FreshPairReview
open RMAF VertexGeometry BinaryExchange

theorem original_vertex_treeAt (t : Tree) (v : RMAF.Vertex)
    (hv : v ∈ PairGeometry.vertices t) :
    ∃ u, treeAt t v = some u := by
  induction t generalizing v with
  | leaf x =>
    have he : v = [] := by simpa [PairGeometry.vertices] using hv
    subst v
    exact ⟨.leaf x,rfl⟩
  | node l r il ir =>
    cases v with
    | nil => exact ⟨.node l r,rfl⟩
    | cons s v =>
      cases s with
      | false =>
        have hvl : v ∈ PairGeometry.vertices l := by
          simpa [PairGeometry.vertices,prependSide] using hv
        exact il v hvl
      | true =>
        have hvr : v ∈ PairGeometry.vertices r := by
          simpa [PairGeometry.vertices,prependSide] using hv
        exact ir v hvr

theorem descendants_treeAt (t u : Tree) (v : RMAF.Vertex)
    (hn : (leaves t).Nodup) (hu : treeAt t v = some u) (x : Nat) :
    x ∈ PairGeometry.descendants t v ↔ x ∈ leaves u := by
  constructor
  · intro hd
    obtain ⟨hxt,hpre⟩ := (PairGeometry.descendants_mem t v x).1 hd
    obtain ⟨a,ha⟩ := (singleton_selected_exists t x).2 hxt
    have haddr := PairGeometry.leafAddress_correct t x hn a ha
    exact (selected_descendant_iff t u v a x hn hu ha).1 (by simpa [haddr] using hpre)
  · intro hxu
    have hxt := treeAt_mem t u v hu x hxu
    obtain ⟨a,ha⟩ := (singleton_selected_exists t x).2 hxt
    have haddr := PairGeometry.leafAddress_correct t x hn a ha
    apply (PairGeometry.descendants_mem t v x).2
    exact ⟨hxt,by simpa [haddr] using (selected_descendant_iff t u v a x hn hu ha).2 hxu⟩

theorem side_yes (A : List Nat) (t u : Tree) (v : RMAF.Vertex)
    (hn : (leaves t).Nodup) (hu : treeAt t v = some u) :
    PairGeometry.sideLabels A t v true = yes A ((leaves u).contains ·) := by
  change A.filter (fun x => (PairGeometry.descendants t v).contains x) =
    A.filter (fun x => (leaves u).contains x)
  apply List.filter_congr
  intro x _
  apply Bool.eq_iff_iff.mpr
  simpa only [List.contains_iff_mem] using descendants_treeAt t u v hn hu x

theorem side_no (A : List Nat) (t u : Tree) (v : RMAF.Vertex)
    (hn : (leaves t).Nodup) (hu : treeAt t v = some u) :
    PairGeometry.sideLabels A t v false = no A ((leaves u).contains ·) := by
  change A.filter (fun x => !(PairGeometry.descendants t v).contains x) =
    A.filter (fun x => !(leaves u).contains x)
  apply List.filter_congr
  intro x _
  have he : (PairGeometry.descendants t v).contains x = (leaves u).contains x := by
    apply Bool.eq_iff_iff.mpr
    simpa only [List.contains_iff_mem] using descendants_treeAt t u v hn hu x
  rw [he]

theorem actual_clear_disj (t : Tree) (C E : List Nat)
    (hc : ∀ w, w ∈ minimalVertices C t → w ∉ minimalVertices E t) : Disj t C E := by
  intro w h
  exact hc w ((minimalVertices_correct C t w).2 h.1)
    ((minimalVertices_correct E t w).2 h.2)

theorem selector_edge_exchange (s t : Tree) (P : List (List Nat))
    (A B : List Nat) (e : RMAF.Vertex × RMAF.Vertex)
    (hs : (leaves s).Nodup)
    (sameLabels : ∀ x, x ∈ leaves s ↔ x ∈ leaves t)
    (hP : partitionCheck (leaves s) P = true)
    (hPS : pairwiseEmbeddings s P = true)
    (hAP : A ∈ P) (hBP : B ∈ P) (hAB : A ≠ B)
    (hchoose : PairGeometry.choose t A B = some (.edge e))
    (clearOther : ∀ E, E ∈ P → E ≠ A → E ≠ B → Disj t E A ∧ Disj t E B)
    (hA : restrictionAgrees s t A = true)
    (F : List (List Nat)) (hF : agreement s t F = true) (hf : Refines F P) :
    ∃ u, treeAt t e.2 = some u ∧
      (let F' := exchange A B F u
       agreement s t F' = true ∧ Refines F' P ∧ F'.count A = 1 ∧
       (∀ C, C ∈ F' → Sub C B →
         (∀ x, x ∈ C → x ∈ leaves u) ∨ (∀ x, x ∈ C → x ∉ leaves u)) ∧
       F'.length ≤ F.length ∧ outside A B F' = outside A B F) := by
  obtain ⟨hp,hvalid⟩ := PairGeometry.choose_sound t A B (.edge e) hchoose
  have ht := PairGeometry.proper_nodup t A B hp
  change e ∈ PairGeometry.edges t ∧ e.1 ∈ minimalVertices A t ∧ e.1 ∈ minimalVertices B t ∧
    e.2 ∈ minimalVertices A t ∧ e.2 ∈ minimalVertices B t ∧
    (∀ inside, PairGeometry.sideLabels A t e.2 inside ≠ []) ∧
    (∀ inside, PairGeometry.sideLabels B t e.2 inside ≠ []) ∧
    PairGeometry.ActualClear t A B e.2 at hvalid
  obtain ⟨he,hap,hbp,hav,hbv,has,hbs,hclear⟩ := hvalid
  obtain ⟨u,hu⟩ := original_vertex_treeAt t e.2 (PairGeometry.minimal_vertices A t e.2 hav)
  have hne : e.2 ≠ [] := by
    obtain ⟨p,b,hshape⟩ := PairGeometry.edges_shape t e he
    rw [hshape]
    simp
  have hAy : yes A ((leaves u).contains ·) ≠ [] := by
    rw [← side_yes A t u e.2 ht hu]
    exact has true
  have hAn : no A ((leaves u).contains ·) ≠ [] := by
    rw [← side_no A t u e.2 ht hu]
    exact has false
  have hBy : yes B ((leaves u).contains ·) ≠ [] := by
    rw [← side_yes B t u e.2 ht hu]
    exact hbs true
  have hBn : no B ((leaves u).contains ·) ≠ [] := by
    rw [← side_no B t u e.2 ht hu]
    exact hbs false
  have hAm : mixed A ((leaves u).contains ·) = true := by
    simpa only [mixed,Bool.and_eq_true,Bool.not_eq_true',isEmpty_false] using And.intro hAy hAn
  have hBm : mixed B ((leaves u).contains ·) = true := by
    simpa only [mixed,Bool.and_eq_true,Bool.not_eq_true',isEmpty_false] using And.intro hBy hBn
  have cay : Disj t (yes A ((leaves u).contains ·)) B := by
    rw [← side_yes A t u e.2 ht hu]
    exact actual_clear_disj t _ _ (hclear.1 true)
  have can : Disj t (no A ((leaves u).contains ·)) B := by
    rw [← side_no A t u e.2 ht hu]
    exact actual_clear_disj t _ _ (hclear.1 false)
  have cby : Disj t (yes B ((leaves u).contains ·)) A := by
    rw [← side_yes B t u e.2 ht hu]
    exact actual_clear_disj t _ _ (hclear.2 true)
  have cbn : Disj t (no B ((leaves u).contains ·)) A := by
    rw [← side_no B t u e.2 ht hu]
    exact actual_clear_disj t _ _ (hclear.2 false)
  exact ⟨u,hu,binary_exchange s t u P A B e.2 hs ht sameLabels hP hPS hAP hBP hAB
    hne hu hAm hBm cay can cby cbn clearOther hA F hF hf⟩

#print axioms original_vertex_treeAt
#print axioms descendants_treeAt
#print axioms side_yes
#print axioms side_no
#print axioms actual_clear_disj
#print axioms selector_edge_exchange
#check PairGeometry.actual_selector_exists
#check PairGeometry.choose_complete
#check PairGeometry.choose_binary_when_two
#check PairGeometry.region_count_actual_hull_degree
#check BinaryExchange.binary_exchange
#check BinaryExchange.descendant_final_source_edge
#check selector_edge_exchange
end FreshPairReview
