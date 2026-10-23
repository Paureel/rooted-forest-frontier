import CrossingCount
namespace OrdinaryCommonSplit
open RMAF RestrictionBridge

/-- Explicit original representative plus fresh attachment marker. There is no
implicit root taxon; y is an actual leaf in the complementary original side. -/
def marked (t : Tree) (X : List Nat) (y rho : Nat) : Option Tree :=
  (restrict (y::X) t).map (relabel (swap y rho))

theorem swap_fixes (y rho x : Nat) (hy : x≠y) (hr : x≠rho) : swap y rho x=x := by
  simp [swap,hy,hr]

theorem marked_labels (t : Tree) (X : List Nat) (y rho : Nat)
    (ht : (leaves t).Nodup) (ndX : X.Nodup) (hy : y∈leaves t) (hnot : y∉X)
    (sub : X⊆leaves t) (fresh : rho∉leaves t) :
    ∃ u, marked t X y rho=some u ∧ (leaves u).Perm (rho::X) ∧ (leaves u).Nodup := by
  have hrX : rho∉X := fun h => fresh (sub h)
  have hyr : y≠rho := by intro h;subst rho;exact fresh hy
  have ndU : (y::X).Nodup := List.nodup_cons.2 ⟨hnot,ndX⟩
  obtain ⟨v,hv⟩ := restriction_exists t (y::X) ⟨y,hy,by simp⟩
  have permV : (leaves v).Perm (y::X) := by
    apply (List.perm_ext_iff_of_nodup (restricted_nodup t v (y::X) hv ht) ndU).2
    intro x
    rw [restricted_labels_exact t v (y::X) hv]
    constructor
    · exact And.right
    · intro hx
      refine ⟨?_,hx⟩
      rcases List.mem_cons.1 hx with rfl | hx
      · exact hy
      · exact sub hx
  have mapX : X.map (swap y rho)=X := by
    have hmap : X.map (swap y rho)=X.map id := by
      apply List.map_congr_left
      intro x hx
      exact swap_fixes y rho x (fun he => hnot (he ▸ hx)) (fun he => hrX (he ▸ hx))
    simpa only [List.map_id] using hmap
  have mapU : (y::X).map (swap y rho)=rho::X := by simp [List.map_cons,swap,mapX]
  have renamed : (leaves (relabel (swap y rho) v)).Perm (rho::X) := by
    rw [leaves_relabel,←mapU]
    exact permV.map _
  exact ⟨relabel (swap y rho) v,by simp [marked,hv],renamed,
    renamed.nodup_iff.2 (List.nodup_cons.2 ⟨hrX,ndX⟩)⟩

/-- The actual newly constructed marked pair is an ordinary proper rooted
pair on exactly rho::X; original label order is irrelevant. -/
theorem marked_pair_proper (T S : Tree) (X : List Nat) (y rho : Nat)
    (ht : (leaves T).Nodup) (hs : (leaves S).Nodup) (ndX : X.Nodup)
    (hyT : y∈leaves T) (hyS : y∈leaves S) (hnot : y∉X)
    (subT : X⊆leaves T) (subS : X⊆leaves S)
    (frT : rho∉leaves T) (frS : rho∉leaves S) :
    ∃ t s, marked T X y rho=some t ∧ marked S X y rho=some s ∧
      Universal233.DepthOne.proper t s=true ∧
      (leaves t).Perm (rho::X) ∧ (leaves s).Perm (rho::X) := by
  obtain ⟨t,hrt,hlt,ndt⟩ := marked_labels T X y rho ht ndX hyT hnot subT frT
  obtain ⟨s,hrs,hls,nds⟩ := marked_labels S X y rho hs ndX hyS hnot subS frS
  exact ⟨t,s,hrt,hrs,(Universal233.DepthOne.proper_iff t s).2 ⟨ndt,nds,hlt.trans hls.symm⟩,hlt,hls⟩
end OrdinaryCommonSplit
