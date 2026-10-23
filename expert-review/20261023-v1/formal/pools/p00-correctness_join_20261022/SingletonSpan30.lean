-- Own singleton hull separation from literal leaf addresses.
import Embeddings28
open RMAF Universal233 CherryBranching VertexGeometry SourceBoundary OwnHigh
namespace HighChildren
theorem leaf_descendant_eq (S : Tree) (z p : List Bool) (a x : Nat)
    (hz : CoreGraph.subtree S z=some (.leaf a))
    (hp : CoreGraph.subtree S p=some (.leaf x)) (hpre : z <+: p) : p=z := by
  obtain ⟨tail,rfl⟩:=hpre
  rw [subtree_compose,hz] at hp
  cases tail with
  | nil => exact List.append_nil z
  | cons s tail => simp only [Option.bind_some,CoreGraph.subtree] at hp; cases hp
theorem leaf_minimal_selected (S : Tree) (P : List Nat) (z : List Bool) (a : Nat)
    (hz : CoreGraph.subtree S z=some (.leaf a)) (hm : z∈minimalVertices P S) : a∈P := by
  obtain ⟨p,q,hp,hq,hpath⟩:=(minimalVertices_correct P S z).mp hm
  obtain ⟨x,hx,hxp⟩:=(selected_leaf_iff P S p).mp hp
  obtain ⟨y,hy,hyq⟩:=(selected_leaf_iff P S q).mp hq
  rcases path_prefix_endpoint hpath z (List.prefix_refl z) with hpre | hpre
  · have he:=leaf_descendant_eq S z p a x hz hxp hpre
    subst p
    have he2 : x=a := Tree.leaf.inj (Option.some.inj (hxp.symm.trans hz))
    exact he2 ▸ hx
  · have he:=leaf_descendant_eq S z q a y hz hyq hpre
    subst q
    have he2 : y=a := Tree.leaf.inj (Option.some.inj (hyq.symm.trans hz))
    exact he2 ▸ hy
theorem singleton_minimal_leaf (S : Tree) (a : Nat) (z : List Bool)
    (hn : (leaves S).Nodup) (ha : a∈leaves S) (hz : z∈minimalVertices [a] S) :
    CoreGraph.subtree S z=some (.leaf a) := by
  obtain ⟨p,hp⟩:=label_has_leaf S a ha
  have hpre : p <+: z := by
    apply subtree_minimal_prefix S [a] p z hn ?_ hz
    intro x hx
    have he := List.mem_singleton.mp hx
    subst x
    simpa only [subtree_labels_eq,hp,leaves,List.mem_singleton] using (rfl : a=a)
  obtain ⟨u,v,hu,hv,hpath⟩:=(minimalVertices_correct [a] S z).mp hz
  obtain ⟨x,hx,hxu⟩:=(selected_leaf_iff [a] S u).mp hu
  obtain ⟨y,hy,hyv⟩:=(selected_leaf_iff [a] S v).mp hv
  have ex:=List.mem_singleton.mp hx
  have ey:=List.mem_singleton.mp hy
  subst x; subst y
  have eu:=leaf_address_unique S a u p hn hxu hp
  have ev:=leaf_address_unique S a v p hn hyv hp
  subst u; subst v
  have hzpre : z <+: p := by
    -- Any vertex on a path to itself is a prefix of that endpoint.
    have ht : ∀ {w u v : List Bool}, PathAt w u v → w <+: u ∨ w <+: v := by
      intro w u v h
      exact path_prefix_endpoint h w (List.prefix_refl w)
    exact (ht hpath).elim id id
  have he : p=z := by
    obtain ⟨tail,ht⟩:=hpre
    have hl2 : z.length≤p.length := by
      obtain ⟨other,ho⟩:=hzpre
      have hh:=congrArg List.length ho
      simp only [List.length_append] at hh
      omega
    have hlen : tail.length=0 := by
      have hh:=congrArg List.length ht
      simp only [List.length_append] at hh
      omega
    have hnilt : tail=[] := List.eq_nil_of_length_eq_zero hlen
    simpa only [hnilt,List.append_nil] using ht

  exact he ▸ hp
end HighChildren
