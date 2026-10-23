/- A single original source boundary is crossed by at most one forest block. -/
import BoundaryHullV3
open RMAF ForestState Universal233 Universal233.HardParent
namespace IndependentOneExchange

def Crosses (X B : List Nat) : Prop :=
 (∃x,x∈B ∧ x∈X) ∧ (∃y,y∈B ∧ y∉X)

theorem disjoint_forbids {A B : List Vertex} (h : disjointVertices A B=true)
 {v : Vertex} (a : v∈A) (b : v∈B) : False := by
 have no := List.all_eq_true.1 h v a
 simp at no
 exact no b

theorem shared_hull_block_equal {S : Tree} {F : List (List Nat)}
 (emb : pairwiseEmbeddings S F=true) {B D : List Nat} (bF : B∈F) (dF : D∈F)
 {v : Vertex} (bv : v∈minimalVertices B S) (dv : v∈minimalVertices D S) : B=D := by
 induction F with
 | nil => simp at bF
 | cons A rest ih =>
  simp only [pairwiseEmbeddings,Bool.and_eq_true] at emb
  rcases List.mem_cons.1 bF with eb|bt
  · subst B
    rcases List.mem_cons.1 dF with ed|dt
    · exact ed.symm
    · exact False.elim (disjoint_forbids (List.all_eq_true.1 emb.1 D dt) bv dv)
  · rcases List.mem_cons.1 dF with ed|dt
    · subst D
      exact False.elim (disjoint_forbids (List.all_eq_true.1 emb.1 B bt) dv bv)
    · exact ih emb.2 bt dt

theorem one_crossing_block {S U : Tree} {p : Vertex} {F : List (List Nat)}
 (sub : CoreGraph.subtree S p=some U) (emb : pairwiseEmbeddings S F=true)
 (labels : ∀B∈F,∀x∈B,x∈leaves S) {B D : List Nat} (bF : B∈F) (dF : D∈F)
 (crossB : Crosses (leaves U) B) (crossD : Crosses (leaves U) D) : B=D := by
 obtain ⟨⟨x,xB,xU⟩,⟨y,yB,yn⟩⟩ := crossB
 obtain ⟨⟨u,uD,uU⟩,⟨v,vD,vn⟩⟩ := crossD
 have bh := crossing_boundary_in_minimal sub ⟨x,xU,xB⟩ ⟨y,labels B bF y yB,yB,yn⟩
 have dh := crossing_boundary_in_minimal sub ⟨u,uU,uD⟩ ⟨v,labels D dF v vD,vD,vn⟩
 exact shared_hull_block_equal emb bF dF bh dh

def splitBlock (X B : List Nat) : List (List Nat) :=
 [B.filter X.contains,B.filter (fun x=>!X.contains x)].filter (fun B=>!B.isEmpty)

def splitForest (X : List Nat) (F : List (List Nat)) := F.flatMap (splitBlock X)

theorem split_block_two (X B : List Nat) : (splitBlock X B).length≤2 := by
 exact List.length_filter_le _ _

theorem split_block_one (X B : List Nat) (no : ¬Crosses X B) : (splitBlock X B).length≤1 := by
 cases hl : B.filter X.contains with
 | nil => cases hr : B.filter (fun x=>!X.contains x) <;> simp [splitBlock,hl,hr]
 | cons x xs =>
  cases hr : B.filter (fun x=>!X.contains x) with
  | nil => simp [splitBlock,hl,hr]
  | cons y ys =>
   have xm : x∈B.filter X.contains := by simp [hl]
   have ym : y∈B.filter (fun x=>!X.contains x) := by simp [hr]
   have xp := List.mem_filter.1 xm
   have yp := List.mem_filter.1 ym
   have xX : x∈X := by simpa using xp.2
   have yX : y∉X := by simpa using yp.2
   exact False.elim (no ⟨⟨x,xp.1,xX⟩,⟨y,yp.1,yX⟩⟩)

theorem split_none_bound (X : List Nat) (F : List (List Nat))
 (no : ∀B∈F,¬Crosses X B) : (splitForest X F).length≤F.length := by
 induction F with
 | nil => simp [splitForest]
 | cons B rest ih =>
  have hb := split_block_one X B (no B (by simp))
  have ht := ih (fun D hD=>no D (by simp [hD]))
  simp only [splitForest,List.flatMap_cons,List.length_append,List.length_cons] at ht ⊢
  omega

theorem split_one_bound (X : List Nat) (F : List (List Nat)) (nd : F.Nodup)
 (unique : ∀B∈F,∀D∈F,Crosses X B→Crosses X D→B=D) :
 (splitForest X F).length≤F.length+1 := by
 induction F with
 | nil => simp [splitForest]
 | cons B rest ih =>
  have parts := List.nodup_cons.1 nd
  by_cases cross : Crosses X B
  · have tail : ∀D∈rest,¬Crosses X D := by
     intro D hD hcross
     have eq := unique D (by simp [hD]) B (by simp) hcross cross
     exact parts.1 (eq ▸ hD)
    have ht := split_none_bound X rest tail
    have hb := split_block_two X B
    simp only [splitForest,List.flatMap_cons,List.length_append,List.length_cons] at ht ⊢
    omega
  · have ht := ih parts.2 (fun C hC D hD=>unique C (by simp [hC]) D (by simp [hD]))
    have hb := split_block_one X B cross
    simp only [splitForest,List.flatMap_cons,List.length_append,List.length_cons] at ht ⊢
    omega

theorem original_split_count {T S U : Tree} {p : Vertex} {F : List (List Nat)}
 (sub : CoreGraph.subtree S p=some U) (ns : (leaves S).Nodup)
 (hF : agreement T S F=true) : (splitForest (leaves U) F).length≤F.length+1 := by
 have checks := hF
 simp only [agreement,Bool.and_eq_true] at checks
 have source := checks.1.1.1.2
 have flat := (IndependentCommon.flatten_from_partition _ F ns source).symm.nodup ns
 have nonempty : ∀B∈F,B≠[] := by
  have sc := source
  simp only [partitionCheck,Bool.and_eq_true] at sc
  intro B hB empty
  have ok := List.all_eq_true.1 sc.1.1 B hB
  simp [empty] at ok
 have labels : ∀B∈F,∀x∈B,x∈leaves S := by
  have sc := source
  simp only [partitionCheck,Bool.and_eq_true] at sc
  intro B hB x hx
  exact List.contains_iff_mem.1 (List.all_eq_true.1 sc.2 x (List.mem_flatten.2 ⟨B,hB,hx⟩))
 apply split_one_bound _ F (IndependentPaid.blocks_nodup F flat nonempty)
 intro B bF D dF crossB crossD
 exact one_crossing_block sub checks.2 labels bF dF crossB crossD
end IndependentOneExchange
