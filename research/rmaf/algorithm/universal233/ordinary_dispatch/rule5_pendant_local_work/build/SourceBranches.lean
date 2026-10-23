import Priority
namespace Universal233.CherryBranching
open RMAF CoreGraph Integration VertexGeometry CutRealization HardParent

structure SourceBranch where
 child : Child
 originalCuts : List RMAF.Vertex
 deriving Repr, DecidableEq

def endpointBranch (S : Tree) (a : Nat) : Option SourceBranch :=
 (terminalCut S a).map fun q => ⟨singletonChild S a,[q]⟩

def highBranch (S : Tree) (a b : Nat) : SourceBranch :=
 ⟨pendantChild S a b,cuts S a b⟩

theorem endpoint_literal {S : Tree} {a b : Nat}
 (ha : a ∈ leaves S) (hb : b ∈ leaves S) (hab : a ≠ b) :
 ∃ q br, endpointBranch S a = some br ∧ br.originalCuts = [q] ∧
 br.child = singletonChild S a ∧ br.child.paid = br.originalCuts.length ∧
 LeafAt S q a ∧ q ≠ [] := by
 obtain ⟨q,hq,hl⟩ := terminalCut_exists ha
 exact ⟨q,⟨singletonChild S a,[q]⟩,by simp [endpointBranch,hq],rfl,rfl,rfl,
   hl,terminal_nonroot hl hb hab⟩

theorem high_literal (S : Tree) (a b : Nat) :
 (highBranch S a b).originalCuts = cuts S a b ∧
 (highBranch S a b).child.paid = (highBranch S a b).originalCuts.length := ⟨rfl,rfl⟩

theorem leaf_valid_descendant {S : Tree} {q v : RMAF.Vertex} {a : Nat}
 (hq : LeafAt S q a) (hv : Valid S v) (hp : q <+: v) : v = q := by
 obtain ⟨tail,rfl⟩ := hp
 have hh := subtree_append hq tail
 cases tail with
 | nil => simp
 | cons s tail =>
   obtain ⟨U,hU⟩ := hv
   rw [hh] at hU
   simp [subtree] at hU

/-- Literal original graph after the single endpoint's original leaf edge.
The two regions are exactly the isolated leaf and the original root remainder. -/
theorem endpoint_components {S : Tree} {q : RMAF.Vertex} {a b : Nat}
 (hq : LeafAt S q a) (hb : b ∈ leaves S) (hab : a ≠ b) :
 (∀ v, ResidualWalk S [q] q v ↔ v = q) ∧
 (∀ v, ResidualWalk S [q] [] v ↔ Valid S v ∧ v ≠ q) ∧
 (∀ v, Valid S v → ∃ w x, LeafAt S w x ∧ ResidualWalk S [q] v w) := by
 have hnr := terminal_nonroot hq hb hab
 have qreg : ∀ v, Region [q] q v ↔ q <+: v := by simp [Region,Pre]
 have single : ∀ v, ResidualWalk S [q] q v ↔ v = q := by
   intro v
   rw [region_component (Or.inr (by simp)) hq.valid ⟨List.prefix_rfl,fun _ _ h => h⟩,qreg]
   constructor
   · rintro ⟨hv,hp⟩; exact leaf_valid_descendant hq hv hp
   · rintro rfl; exact ⟨hq.valid,List.prefix_rfl⟩
 have root : ∀ v, ResidualWalk S [q] [] v ↔ Valid S v ∧ v ≠ q := by
   intro v
   rw [region_component (Or.inl rfl) (valid_root S) ⟨List.prefix_rfl,fun _ _ h => h⟩,
     region_root _ _ (by simpa using hnr)]
   constructor
   · rintro ⟨hv,hl⟩
     exact ⟨hv,fun he => hl q (by simp) (by simp [he,Pre])⟩
   · rintro ⟨hv,hne⟩
     refine ⟨hv,?_⟩
     intro p hp hpre
     have he : p = q := by simpa using hp
     subst p
     exact hne (leaf_valid_descendant hq hv hpre)
 refine ⟨single,root,?_⟩
 intro v hv
 by_cases e : v = q
 · subst v; exact ⟨q,a,hq,ResidualWalk.refl hq.valid⟩
 · obtain ⟨w,hw⟩ := leaf_exists hb
   have wne : w ≠ q := by
     intro he
     subst w
     unfold LeafAt at hw hq
     rw [hq] at hw
     exact hab (Tree.leaf.inj (Option.some.inj hw))
   exact ⟨w,b,hw,((root v).2 ⟨hv,e⟩).reverse.trans ((root w).2 ⟨hw.valid,wne⟩)⟩
end Universal233.CherryBranching
