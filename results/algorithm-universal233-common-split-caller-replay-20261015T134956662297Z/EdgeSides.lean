import OriginalProjection
namespace OrdinaryCommonSplit
open RMAF RestrictionBridge VertexGeometry PairGeometry
open Universal233.CoreGraph Universal233.Integration Universal233.CutRealization

theorem descendants_subtree (T u : Tree) (p : RMAF.Vertex) (nd : (leaves T).Nodup)
    (hp : subtree T p=some u) (x : Nat) : x∈descendants T p ↔ x∈leaves u := by
  constructor
  · intro hx
    obtain ⟨hxl,hpre⟩ := (descendants_mem T p x).1 hx
    obtain ⟨a,ha⟩ := leaf_exists hxl
    have had := leafAddress_correct T x nd a ((leafAt_selected T a x).1 ha)
    rw [had] at hpre
    obtain ⟨v,hv⟩ := hpre
    have hu : LeafAt u v x := by
      change subtree u v=some (.leaf x)
      rw [←subtree_append hp v]
      simpa only [LeafAt,←hv] using ha
    exact leafAt_label u v x hu
  · intro hx
    obtain ⟨v,hv⟩ := leaf_exists hx
    have ha : LeafAt T (p++v) x := by
      change subtree T (p++v)=some (.leaf x)
      rw [subtree_append hp v]
      exact hv
    apply (descendants_mem T p x).2
    refine ⟨leafAt_label T (p++v) x ha,?_⟩
    rw [leafAddress_correct T x nd (p++v) ((leafAt_selected T _ x).1 ha)]
    exact ⟨v,rfl⟩

theorem selected_mono (t : Tree) (K X : List Nat) (sub : K⊆X) :
    ∀a,selectedLeaves K t a→selectedLeaves X t a := by
  intro a ha
  obtain ⟨x,hx,hax⟩ := (selected_decompose_label K t a).1 ha
  exact (selected_decompose_label X t a).2 ⟨x,sub hx,hax⟩

/-- Literal original cut input produces both occupied-side guards, including
the complementary/root orientation. No span/merge clearance is assumed. -/
theorem original_split_side_guards (T : Tree) (X Y : List Nat)
    (nd : (leaves T).Nodup) (hp : partitionCheck (leaves T) [X,Y]=true)
    (edge : OriginalSplit T X Y) :
    ∃ p b inside, (∀a,selectedLeaves X T a→IsSide p b inside a) ∧
      (∀a,selectedLeaves Y T a→IsSide p b (!inside) a) := by
  obtain ⟨v,u,hv,hvu,hside⟩ := edge
  have ev := List.dropLast_concat_getLast hv
  let p := v.dropLast
  let b := v.getLast hv
  have he : p++[b]=v := ev
  have disj := split_disjoint _ X Y hp
  rcases hside with sideY | sideX
  · refine ⟨p,b,false,?_,?_⟩
    · apply selected_side_of_labels T X p b false nd
      intro x hx
      change x∉descendants T (p++[b])
      rw [he,descendants_subtree T u v nd hvu]
      exact fun h => disj x hx (sideY.mem_iff.1 h)
    · apply selected_side_of_labels T Y p b true nd
      intro x hx
      change x∈descendants T (p++[b])
      rw [he,descendants_subtree T u v nd hvu]
      exact sideY.mem_iff.2 hx
  · refine ⟨p,b,true,?_,?_⟩
    · apply selected_side_of_labels T X p b true nd
      intro x hx
      change x∈descendants T (p++[b])
      rw [he,descendants_subtree T u v nd hvu]
      exact sideX.mem_iff.2 hx
    · apply selected_side_of_labels T Y p b false nd
      intro x hx
      change x∉descendants T (p++[b])
      rw [he,descendants_subtree T u v nd hvu]
      exact fun h => disj x (sideX.mem_iff.1 h) hx

/-- Projecting an original mixed block onto X plus an arbitrary Y marker
representative preserves clearance from every original X-only block. -/
theorem original_projection_clear (T : Tree) (X Y B K E : List Nat) (y z : Nat)
    (nd : (leaves T).Nodup) (hp : partitionCheck (leaves T) [X,Y]=true)
    (edge : OriginalSplit T X Y) (subKX : K⊆X) (subKB : K⊆B) (subE : E⊆X)
    (hy : y∈Y) (hz : z∈Y) (hzB : z∈B)
    (hc : Clear (minimalVertices B T) (minimalVertices E T)) :
    Clear (minimalVertices (K++[y]) T) (minimalVertices E T) := by
  obtain ⟨p,b,inside,sideX,sideY⟩ := original_split_side_guards T X Y nd hp edge
  have hzin : z∈leaves T := (split_labels _ X Y hp z).2 (Or.inr hz)
  have cOld : Clear (minimalVertices (K++[z]) T) (minimalVertices E T) := by
    intro v hv hw
    exact hc v (executable_span_monotone T (K++[z]) B
      (by
        intro x hx
        rcases List.mem_append.1 hx with hx | hx
        · exact subKB hx
        · have he : x=z := by simpa using hx
          subst x
          exact hzB) v hv) hw
  apply original_merge_clear T K [y] E z p b inside nd hzin
    (fun a ha => sideX a (selected_mono T K X subKX a ha))
    (fun a ha => sideY a (selected_mono T [y] Y (by
      intro x hx
      have he : x=y := by simpa using hx
      simpa [he] using hy) a ha))
    (fun a ha => sideX a (selected_mono T E X subE a ha))
    (fun a ha => sideY a (selected_mono T [z] Y (by
      intro x hx
      have he : x=z := by simpa using hx
      simpa [he] using hz) a ha)) cOld
end OrdinaryCommonSplit
