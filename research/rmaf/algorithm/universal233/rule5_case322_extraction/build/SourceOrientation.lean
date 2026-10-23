import BsideExtraction
namespace Universal233.Case322Extraction
open RMAF CoreGraph Integration VertexGeometry CutRealization HardParent CherryBranching
open Universal233.Rule5Local Universal233.Rule5Case322
set_option maxRecDepth 15000

def orient (s : Bool) (A B : Tree) : Tree := if s then .node B A else .node A B

theorem orient_mem (s : Bool) (A B : Tree) (x : Nat) :
 x ∈ leaves (orient s A B) ↔ x ∈ leaves A ∨ x ∈ leaves B := by
 cases s <;> simp [orient,leaves,or_comm]

theorem orient_proper {s : Bool} {A B : Tree} (hn : (leaves (orient s A B)).Nodup) :
 (leaves A).Nodup ∧ (leaves B).Nodup ∧ ∀ x, x ∈ leaves A → x ∉ leaves B := by
 cases s
 · obtain ⟨ha,hb,hcross⟩ := List.nodup_append.1 hn
   exact ⟨ha,hb,fun x hx hy => hcross x hx x hy rfl⟩
 · obtain ⟨hb,ha,hcross⟩ := List.nodup_append.1 hn
   exact ⟨ha,hb,fun x hx hy => hcross x hy x hx rfl⟩

def AX (sa : Bool) (a : Nat) (X : Tree) := orient sa (.leaf a) X
def VC (sa sc : Bool) (a c : Nat) (X : Tree) := orient sc (AX sa a X) (.leaf c)
def bottom (sa sc sb : Bool) (a b c : Nat) (X : Tree) := orient sb (VC sa sc a c X) (.leaf b)
def aArc (w : RMAF.Vertex) (sa sc sb : Bool) := w ++ [sb,sc,sa]
def xArc (w : RMAF.Vertex) (sa sc sb : Bool) := w ++ [sb,sc,!sa]
def cArc (w : RMAF.Vertex) (sc sb : Bool) := w ++ [sb,!sc]
def bArc (w : RMAF.Vertex) (sb : Bool) := w ++ [!sb]
def vRoot (w : RMAF.Vertex) (sb : Bool) := w ++ [sb]

theorem bottom_x_lookup {S X : Tree} {w : RMAF.Vertex} {sa sc sb : Bool} {a b c : Nat}
 (he : subtree S w = some (bottom sa sc sb a b c X)) : subtree S (xArc w sa sc sb) = some X := by
 rw [xArc,subtree_append he]
 cases sa <;> cases sc <;> cases sb <;> rfl

theorem bottom_c_lookup {S X : Tree} {w : RMAF.Vertex} {sa sc sb : Bool} {a b c : Nat}
 (he : subtree S w = some (bottom sa sc sb a b c X)) : LeafAt S (cArc w sc sb) c := by
 unfold LeafAt
 rw [cArc,subtree_append he]
 cases sa <;> cases sc <;> cases sb <;> rfl

theorem bottom_a_lookup {S X : Tree} {w : RMAF.Vertex} {sa sc sb : Bool} {a b c : Nat}
 (he : subtree S w = some (bottom sa sc sb a b c X)) : LeafAt S (aArc w sa sc sb) a := by
 unfold LeafAt
 rw [aArc,subtree_append he]
 cases sa <;> cases sc <;> cases sb <;> rfl

theorem bottom_b_lookup {S X : Tree} {w : RMAF.Vertex} {sa sc sb : Bool} {a b c : Nat}
 (he : subtree S w = some (bottom sa sc sb a b c X)) : LeafAt S (bArc w sb) b := by
 unfold LeafAt
 rw [bArc,subtree_append he]
 cases sa <;> cases sc <;> cases sb <;> rfl

theorem bottom_v_lookup {S X : Tree} {w : RMAF.Vertex} {sa sc sb : Bool} {a b c : Nat}
 (he : subtree S w = some (bottom sa sc sb a b c X)) : subtree S (vRoot w sb) = some (VC sa sc a c X) := by
 rw [vRoot,subtree_append he]
 cases sb <;> rfl

theorem bottom_proper {S X : Tree} {w : RMAF.Vertex} {sa sc sb : Bool} {a b c : Nat}
 (hn : (leaves S).Nodup) (he : subtree S w = some (bottom sa sc sb a b c X)) :
 a ∉ leaves X ∧ c ∉ leaves X ∧ a ≠ c ∧ b ∉ leaves (VC sa sc a c X) := by
 have nd := (subtreeLabels_sublist S w).nodup hn
 rw [source_subtree_labels he] at nd
 have pw := orient_proper nd
 have pv := orient_proper pw.1
 have pa := orient_proper pv.1
 have noCV : c ∉ leaves (AX sa a X) := by exact fun h => pv.2.2 c h (by simp [leaves])
 refine ⟨fun h => pa.2.2 a (by simp [leaves]) h,?_,?_,?_⟩
 · exact fun h => noCV ((orient_mem sa (.leaf a) X c).2 (Or.inr h))
 · intro e; subst c; exact noCV ((orient_mem sa (.leaf a) X a).2 (Or.inl (by simp [leaves])))
 · exact fun h => pw.2.2 b h (by simp [leaves])

theorem path_common_prefix (w v p q : RMAF.Vertex) :
 PathAt (w++v) (w++p) (w++q) ↔ PathAt v p q := by
 induction w with
 | nil => rfl
 | cons s w ih => simpa using (path_same_side s (w++v) (w++p) (w++q)).trans ih

/-- The original x and c arcs are actual path pendants in all eight source
sibling patterns, with arbitrary original context above w. -/
theorem bottom_actual_pendants {S X : Tree} {w : RMAF.Vertex} {sa sc sb : Bool} {a b c : Nat}
 (hn : (leaves S).Nodup) (he : subtree S w = some (bottom sa sc sb a b c X)) :
 xArc w sa sc sb ∈ cuts S a b ∧ cArc w sc sb ∈ cuts S a b := by
 have la := bottom_a_lookup he
 have lb := bottom_b_lookup he
 have hx := bottom_x_lookup he
 have hc := bottom_c_lookup he
 have noX : ¬PathAt [sb,sc,!sa] [sb,sc,sa] [!sb] := by
   cases sa <;> cases sc <;> cases sb
   all_goals exact (sameRegion_iff_path_avoids _ _ _ (by decide) (by decide)).1 (by rfl)
 have noC : ¬PathAt [sb,!sc] [sb,sc,sa] [!sb] := by
   cases sa <;> cases sc <;> cases sb
   all_goals exact (sameRegion_iff_path_avoids _ _ _ (by decide) (by decide)).1 (by rfl)
 have parX : PathAt [sb,sc] [sb,sc,sa] [!sb] := by
   cases sa <;> cases sc <;> cases sb
   all_goals exact region_ne_path _ _ _ (by decide)
 have parC : PathAt [sb] [sb,sc,sa] [!sb] := by
   cases sa <;> cases sc <;> cases sb
   all_goals exact region_ne_path _ _ _ (by decide)
 constructor
 · apply (cuts_spec S a b _).2
   refine ⟨⟨X,hx⟩,?_,?_,?_⟩
   · intro h; have n := congrArg List.length h; simp [xArc] at n
   · apply (pair_minimal_path hn la lb _).2
     simpa [xArc,aArc,bArc] using (path_common_prefix w [sb,sc] [sb,sc,sa] [!sb]).2 parX
   · intro h
     have p := (pair_minimal_path hn la lb _).1 h
     exact noX ((path_common_prefix w _ _ _).1 p)
 · apply (cuts_spec S a b _).2
   refine ⟨hc.valid,?_,?_,?_⟩
   · intro h; have n := congrArg List.length h; simp [cArc] at n
   · apply (pair_minimal_path hn la lb _).2
     simpa [cArc,aArc,bArc] using (path_common_prefix w [sb] [sb,sc,sa] [!sb]).2 parC
   · intro h
     have p := (pair_minimal_path hn la lb _).1 h
     exact noC ((path_common_prefix w _ _ _).1 p)

/-- Exact two-pendant admission determines the literal source list up to its
actual traversal order; neither sibling order nor an arc payment is guessed. -/
theorem bottom_two_cut_orders {S X : Tree} {w : RMAF.Vertex} {sa sc sb : Bool} {a b c : Nat}
 (hn : (leaves S).Nodup) (he : subtree S w = some (bottom sa sc sb a b c X))
 (two : (cuts S a b).length = 2) :
 cuts S a b = [xArc w sa sc sb,cArc w sc sb] ∨ cuts S a b = [cArc w sc sb,xArc w sa sc sb] := by
 obtain ⟨hx,hc⟩ := bottom_actual_pendants hn he
 have ne : xArc w sa sc sb ≠ cArc w sc sb := by
   intro e; have n := congrArg List.length e; simp [xArc,cArc] at n
 have shape : ∃ u v, cuts S a b = [u,v] := by
   cases e : cuts S a b with
   | nil => simp [e] at two
   | cons u us =>
     cases us with
     | nil => simp [e] at two
     | cons v vs =>
       have len0 : vs.length = 0 := by simpa [e] using two
       have ev : vs = [] := by cases vs with | nil => rfl | cons x xs => simp at len0
       subst vs
       exact ⟨u,v,rfl⟩
 obtain ⟨u,v,eq⟩ := shape
 rw [eq] at hx hc
 have xx : xArc w sa sc sb = u ∨ xArc w sa sc sb = v := by simpa using hx
 have cc : cArc w sc sb = u ∨ cArc w sc sb = v := by simpa using hc
 rcases xx with xx | xx <;> rcases cc with cc | cc
 · exact False.elim (ne (xx.trans cc.symm))
 · left; simpa [xx,cc] using eq
 · right; simpa [xx,cc] using eq
 · exact False.elim (ne (xx.trans cc.symm))
end Universal233.Case322Extraction
