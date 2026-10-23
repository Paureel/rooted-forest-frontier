import Rule5Graph
namespace Universal233.Rule5Local
open RMAF CoreGraph Integration VertexGeometry CutRealization HardParent CherryBranching

/-- Literal rooted caterpillar above its bottom subtree. List order is the
actual bottom-to-root source order, and may be empty. -/
def spine : List Nat → Tree → Tree
 | [], t => t
 | x::xs, t => spine xs (.node t (.leaf x))

def figure15Source (a b c : Nat) (X : Tree) (S : List Nat) : Tree :=
 spine S (.node (.node (.node (.leaf a) X) (.leaf c)) (.leaf b))

theorem restrict_spine (S D : List Nat) (T : Tree)
 (h : ∀ x, x ∈ S → x ∉ D) : restrict D (spine S T) = restrict D T := by
 induction S generalizing T with
 | nil => rfl
 | cons x xs ih =>
   have hx : x ∉ D := h x (by simp)
   rw [spine,ih (.node T (.leaf x)) (fun y hy => h y (by simp [hy]))]
   simp [restrict,hx]
   cases restrict D T <;> rfl

theorem source_bcx {a b c x : Nat} {X : Tree} {S : List Nat}
 (hnX : (leaves X).Nodup) (hx : x ∈ leaves X)
 (outside : ∀ y, y ∈ leaves X → y ≠ b ∧ y ≠ c)
 (hab : a ≠ b) (hac : a ≠ c) (hax : a ≠ x)
 (hs : ∀ y, y ∈ S → y ∉ [b,c,x]) :
 restrict [b,c,x] (figure15Source a b c X S) =
 some (.node (.node (.leaf x) (.leaf c)) (.leaf b)) := by
 have he : restrict [b,c,x] X = restrict [x] X := by
   apply BinaryExchange.restrict_congr
   intro y hy
   have yo := outside y hy
   simp [yo.1,yo.2]
 rw [ForestState.proper_singleton_restriction X x hnX hx] at he
 unfold figure15Source
 rw [restrict_spine S [b,c,x] _ hs]
 simp [restrict,he,hab,hac,hax]

/-- Actual original rooted Figure15.3 obstruction. The target remainder U
is arbitrary; neither a cover nor an exchange is assumed. -/
theorem figure153_forbidden_triple {a b c x : Nat} {X U : Tree} {S : List Nat}
 (hnX : (leaves X).Nodup) (hx : x ∈ leaves X)
 (outside : ∀ y, y ∈ leaves X → y ≠ b ∧ y ≠ c)
 (hab : a ≠ b) (hac : a ≠ c) (hax : a ≠ x)
 (hbc : b ≠ c) (hbx : b ≠ x) (hcx : c ≠ x)
 (hs : ∀ y, y ∈ S → y ∉ [b,c,x])
 (hbU : b ∈ leaves U) (hxU : x ∈ leaves U) :
 restrictionAgrees (.node (.leaf c) U) (figure15Source a b c X S) [b,c,x] = false := by
 have source := source_bcx hnX hx outside hab hac hax hs
 unfold restrictionAgrees
 rw [source]
 cases hu : restrict [b,c,x] U with
 | none =>
   have no := (BinaryExchange.restrict_none_iff [b,c,x] U).1 hu b hbU
   simp at no
 | some V =>
   have bv : b ∈ leaves V := (BinaryExchange.restrict_mem [b,c,x] U V hu b).2 ⟨hbU,by simp⟩
   have xv : x ∈ leaves V := (BinaryExchange.restrict_mem [b,c,x] U V hu x).2 ⟨hxU,by simp⟩
   cases V with
   | leaf y =>
     have eb : b = y := by simpa [leaves] using bv
     have ex : x = y := by simpa [leaves] using xv
     exact False.elim (hbx (eb.trans ex.symm))
   | node l r => simp [restrict,hu,sameShape,hbc,Ne.symm hbc]

theorem figure153_block_exclusion {a b c x : Nat} {X U : Tree} {S : List Nat}
 {F : List (List Nat)} {B : List Nat}
 (hnX : (leaves X).Nodup) (hx : x ∈ leaves X)
 (outside : ∀ y, y ∈ leaves X → y ≠ b ∧ y ≠ c)
 (hab : a ≠ b) (hac : a ≠ c) (hax : a ≠ x)
 (hbc : b ≠ c) (hbx : b ≠ x) (hcx : c ≠ x)
 (hs : ∀ y, y ∈ S → y ∉ [b,c,x])
 (hbU : b ∈ leaves U) (hxU : x ∈ leaves U)
 (ha : agreement (.node (.leaf c) U) (figure15Source a b c X S) F = true)
 (hB : B ∈ F) (hbB : b ∈ B) (hcB : c ∈ B) (hxB : x ∈ B) : False := by
 have parts := BinaryExchange.agreement_parts _ _ F ha
 have top := parts.2.2.1 B hB
 have tri := BinaryExchange.restrictionAgrees_sub _ _ B [b,c,x] top
   (by intro y hy
       have hh : y = b ∨ y = c ∨ y = x := by simpa using hy
       rcases hh with rfl | rfl | rfl <;> assumption)
   ⟨b,by simp,by simp [leaves,hbU]⟩
 have no := figure153_forbidden_triple hnX hx outside hab hac hax hbc hbx hcx hs hbU hxU
 rw [no] at tri
 contradiction

/-- Two rooted clusters cannot cross in three witnessed leaf colors. This
lemma is constructor-inductive and independent of a branching cover. -/
theorem clusters_no_cross {T : Tree} {f g : Nat → Bool}
 (hf : BinaryExchange.Cluster (fun _ => True) f T)
 (hg : BinaryExchange.Cluster (fun _ => True) g T)
 {u v w : Nat} (hu : u ∈ leaves T) (hv : v ∈ leaves T) (hw : w ∈ leaves T)
 (fu : f u = true) (fv : f v = true) (fw : f w = false)
 (gu : g u = true) (gv : g v = false) (gw : g w = true) : False := by
 induction hf with
 | allTrue h => have e := h w hw trivial; rw [fw] at e; contradiction
 | allFalse h => have e := h u hu trivial; rw [fu] at e; contradiction
 | @left l r h noR ih =>
   have uL : u ∈ leaves l := by
     rcases List.mem_append.1 hu with hm | hm
     · exact hm
     · have e := noR u hm trivial; rw [fu] at e; contradiction
   have vL : v ∈ leaves l := by
     rcases List.mem_append.1 hv with hm | hm
     · exact hm
     · have e := noR v hm trivial; rw [fv] at e; contradiction
   cases hg with
   | allTrue h => have e := h v hv trivial; rw [gv] at e; contradiction
   | allFalse h => have e := h u hu trivial; rw [gu] at e; contradiction
   | left hg noR' =>
     have wL : w ∈ leaves l := by
       rcases List.mem_append.1 hw with hm | hm
       · exact hm
       · have e := noR' w hm trivial; rw [gw] at e; contradiction
     exact ih hg uL vL wL
   | right noL hg => have e := noL u uL trivial; rw [gu] at e; contradiction
 | @right l r noL h ih =>
   have uR : u ∈ leaves r := by
     rcases List.mem_append.1 hu with hm | hm
     · have e := noL u hm trivial; rw [fu] at e; contradiction
     · exact hm
   have vR : v ∈ leaves r := by
     rcases List.mem_append.1 hv with hm | hm
     · have e := noL v hm trivial; rw [fv] at e; contradiction
     · exact hm
   cases hg with
   | allTrue h => have e := h v hv trivial; rw [gv] at e; contradiction
   | allFalse h => have e := h u hu trivial; rw [gu] at e; contradiction
   | left hg noR => have e := noR u uR trivial; rw [gu] at e; contradiction
   | right noL' hg =>
     have wR : w ∈ leaves r := by
       rcases List.mem_append.1 hw with hm | hm
       · have e := noL' w hm trivial; rw [gw] at e; contradiction
       · exact hm
     exact ih hg uR vR wR

/-- Actual incompatible original cut-edge clusters prohibit a common AF
block. This includes both Figure15 obstruction patterns, and allows arbitrary
upward/root contexts and sibling orientation. The cut-edge subtrees and their
leaf incidences are original graph data, not a desired exchange hypothesis. -/
theorem original_crossing_clusters_exclude_block
 {T S U V : Tree} {q r : RMAF.Vertex} {F : List (List Nat)} {B : List Nat}
 {u v w : Nat}
 (hnT : (leaves T).Nodup) (hnS : (leaves S).Nodup)
 (hU : subtree T q = some U) (hV : subtree S r = some V)
 (uU : u ∈ leaves U) (vU : v ∈ leaves U) (wU : w ∉ leaves U)
 (uV : u ∈ leaves V) (vV : v ∉ leaves V) (wV : w ∈ leaves V)
 (ha : agreement T S F = true) (hB : B ∈ F)
 (uB : u ∈ B) (vB : v ∈ B) (wB : w ∈ B) : False := by
 have parts := BinaryExchange.agreement_parts T S F ha
 have top := parts.2.2.1 B hB
 have pT := parts.1
 have pS := parts.2.1
 cases et : restrict B T with
 | none => simp [restrictionAgrees,et] at top
 | some TT =>
   cases es : restrict B S with
   | none => simp [restrictionAgrees,et,es] at top
   | some SS =>
     have iso : RootedIso TT SS := (sameShape_correct TT SS).1 (by simpa [restrictionAgrees,et,es] using top)
     have atU : BinaryExchange.treeAt T q = some U := by rw [source_treeAt]; exact hU
     have atV : BinaryExchange.treeAt S r = some V := by rw [source_treeAt]; exact hV
     have ct := BinaryExchange.subtree_cluster T U q hnT atU
     have cs := BinaryExchange.subtree_cluster S V r hnS atV
     have ct' := BinaryExchange.cluster_restrict ct B (fun _ _ => trivial) et
     have cs' := BinaryExchange.cluster_restrict cs B (fun _ _ => trivial) es
     have ctSS := BinaryExchange.cluster_iso iso ct'
     have uu : u ∈ leaves SS := (BinaryExchange.restrict_mem B S SS es u).2 ⟨block_labels pS hB uB,uB⟩
     have vv : v ∈ leaves SS := (BinaryExchange.restrict_mem B S SS es v).2 ⟨block_labels pS hB vB,vB⟩
     have ww : w ∈ leaves SS := (BinaryExchange.restrict_mem B S SS es w).2 ⟨block_labels pS hB wB,wB⟩
     exact clusters_no_cross ctSS cs' uu vv ww
       (by simpa using uU) (by simpa using vU) (by simpa using wU)
       (by simpa using uV) (by simpa using vV) (by simpa using wV)

end Universal233.Rule5Local
