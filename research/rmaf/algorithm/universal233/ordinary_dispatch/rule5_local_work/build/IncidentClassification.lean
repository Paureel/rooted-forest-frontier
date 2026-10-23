import RemainingStatus
namespace Universal233.Rule5FinalClassification
open RMAF CoreGraph Integration VertexGeometry CutRealization HardParent CherryBranching Rule5Local Rule5Classification

theorem prefix_root_path {p v : RMAF.Vertex} (h : p <+: v) : PathAt p v [] := by
 obtain ⟨tail,rfl⟩ := h
 induction p with
 | nil => exact .endpointR _ _
 | cons s p ih => exact .leftLeg s ih

theorem crossing_child_path {q u v : RMAF.Vertex} (qn : q ≠ [])
 (hu : q <+: u) (hv : ¬q <+: v) : PathAt q u v := by
 induction q generalizing u v with
 | nil => contradiction
 | cons s q ih =>
   cases u with
   | nil => simp at hu
   | cons t u =>
     have st : s = t := List.cons_prefix_cons.1 hu |>.1
     subst t
     have qu : q <+: u := (List.cons_prefix_cons.1 hu).2
     cases v with
     | nil => exact .leftLeg s (prefix_root_path qu)
     | cons t v =>
       by_cases st : s = t
       · subst t
         have qv : ¬q <+: v := by simpa using hv
         have qn : q ≠ [] := by intro e; simp [e] at qv
         exact .down s (ih qn qu qv)
       · have ts : t = !s := by cases s <;> cases t <;> simp_all
         subst t
         exact .crossLeft s (prefix_root_path qu)

def Incoming (T : Tree) (X : List Nat) (q : RMAF.Vertex) : Prop :=
 q ∈ minimalVertices X T ∧ q.dropLast ∉ minimalVertices X T
def Outgoing (T : Tree) (X : List Nat) (q : RMAF.Vertex) : Prop :=
 q ∉ minimalVertices X T ∧ q.dropLast ∈ minimalVertices X T
def OutsideAt (T : Tree) (X : List Nat) (q v : RMAF.Vertex) : Prop :=
 (q <+: v) ↔ q ∉ minimalVertices X T
def OutsideLabel (T : Tree) (X : List Nat) (q : RMAF.Vertex) (x : Nat) : Prop :=
 (x ∈ subtreeLabels T q) ↔ q ∉ minimalVertices X T

theorem boundary_directions {T : Tree} {X : List Nat} {q : RMAF.Vertex}
 (hq : q ∈ incident T X) : Incoming T X q ∨ Outgoing T X q := by
 have hs := (incident_spec T X q).1 hq
 simp only [paint] at hs
 by_cases h : q ∈ minimalVertices X T
 · left
   exact ⟨h,by intro hp; exact hs.2.2 (by simp [h,hp])⟩
 · right
   exact ⟨h,by apply Classical.byContradiction; intro hn; exact hs.2.2 (by simp [h,hn])⟩

theorem incoming_all_hull {T : Tree} {X : List Nat} {q v : RMAF.Vertex}
 (hq : q ∈ incident T X) (hin : Incoming T X q) (hv : v ∈ minimalVertices X T) : q <+: v := by
 apply Classical.byContradiction
 intro hn
 have qn := ((incident_spec T X q).1 hq).2.1
 exact hin.2 (minimal_convex X T q.dropLast q v hin.1 hv
   (cut_crossing_path qn List.prefix_rfl hn))

theorem outgoing_no_hull {T : Tree} {X : List Nat} {q v : RMAF.Vertex}
 (hq : q ∈ incident T X) (hout : Outgoing T X q) (hv : v ∈ minimalVertices X T) : ¬q <+: v :=
 offpath_no_descendant ((incident_spec T X q).1 hq).2.1 hout.2 hout.1 hv

theorem incoming_unique {T : Tree} {X : List Nat} {q r : RMAF.Vertex}
 (hq : q ∈ incident T X) (hr : r ∈ incident T X)
 (hi : Incoming T X q) (hj : Incoming T X r) : q = r :=
 (incoming_all_hull hq hi hj.1).eq_of_length (by
   have h1 := (incoming_all_hull hq hi hj.1).length_le
   have h2 := (incoming_all_hull hr hj hi.1).length_le
   omega)

/-- Different actual boundary arcs lead to disjoint outside regions, including
the original root side of an incoming arc. -/
theorem outside_regions_disjoint {T : Tree} {X : List Nat} {q r v : RMAF.Vertex}
 (hq : q ∈ incident T X) (hr : r ∈ incident T X) (neq : q ≠ r) :
 ¬(OutsideAt T X q v ∧ OutsideAt T X r v) := by
 rintro ⟨vq,vr⟩
 rcases boundary_directions hq with qi | qo <;> rcases boundary_directions hr with ri | ro
 · exact neq (incoming_unique hq hr qi ri)
 · have qrv : q <+: v := (incoming_all_hull hq qi ro.2).trans
     ((List.dropLast_prefix r).trans ((vr).2 ro.1))
   exact ((vq).1 qrv) qi.1
 · have rqv : r <+: v := (incoming_all_hull hr ri qo.2).trans
     ((List.dropLast_prefix q).trans ((vq).2 qo.1))
   exact ((vr).1 rqv) ri.1
 · have qv := vq.2 qo.1
   have rv := vr.2 ro.1
   rcases List.prefix_or_prefix_of_prefix qv rv with qr | rq
   · exact outgoing_no_hull hq qo ro.2 (prefix_parent_of_ne qr neq)
   · exact outgoing_no_hull hr ro qo.2 (prefix_parent_of_ne rq neq.symm)

theorem outside_not_hull {T : Tree} {X : List Nat} {q v : RMAF.Vertex}
 (hq : q ∈ incident T X) (hv : OutsideAt T X q v) : v ∉ minimalVertices X T := by
 intro hh
 rcases boundary_directions hq with hi | ho
 · exact (hv.1 (incoming_all_hull hq hi hh)) hi.1
 · exact outgoing_no_hull hq ho hh (hv.2 ho.1)

theorem outside_label_at {T : Tree} {X : List Nat} {q v : RMAF.Vertex} {x : Nat}
 (hn : (leaves T).Nodup) (hx : LeafAt T v x) :
 OutsideLabel T X q x ↔ OutsideAt T X q v := by
 unfold OutsideLabel OutsideAt
 rw [label_prefix hn hx]

/-- An outside block whose embedding avoids X cannot straddle a boundary
edge of X, in either edge direction. -/
theorem outside_block_constant {T : Tree} {X C : List Nat} {q : RMAF.Vertex} {x y : Nat}
 (hn : (leaves T).Nodup) (hq : q ∈ incident T X)
 (dj : BinaryExchange.Disj T X C) (labs : ∀ z, z ∈ C → z ∈ leaves T)
 (hx : x ∈ C) (hy : y ∈ C) : OutsideLabel T X q x ↔ OutsideLabel T X q y := by
 obtain ⟨u,hu⟩ := leaf_exists (labs x hx)
 obtain ⟨v,hv⟩ := leaf_exists (labs y hy)
 have const : (q <+: u) ↔ q <+: v := by
   have noCross {u v : RMAF.Vertex} {x y : Nat} (hu : LeafAt T u x) (hv : LeafAt T v y)
    (hx : x ∈ C) (hy : y ∈ C) (up : q <+: u) (vp : ¬q <+: v) : False := by
     have hs := (incident_spec T X q).1 hq
     have cPath : ∀ w, PathAt w u v → Hull (selectedLeaves C T) w := by
       intro w hp
       exact ⟨u,v,(selected_at_leaf C T u x hu).2 hx,(selected_at_leaf C T v y hv).2 hy,hp⟩
     rcases boundary_directions hq with hi | ho
     · exact dj q ⟨(minimalVertices_correct X T q).1 hi.1,cPath q (crossing_child_path hs.2.1 up vp)⟩
     · exact dj q.dropLast ⟨(minimalVertices_correct X T q.dropLast).1 ho.2,cPath _ (cut_crossing_path hs.2.1 up vp)⟩
   constructor
   · intro up; apply Classical.byContradiction; intro vp; exact noCross hu hv hx hy up vp
   · intro vp; apply Classical.byContradiction; intro up; exact noCross hv hu hy hx vp up
 unfold OutsideLabel
 rw [label_prefix hn hu,label_prefix hn hv,const]

theorem subtree_selected_leaf {T U : Tree} {q : RMAF.Vertex} (h : subtree T q = some U) :
 ∃ v x, LeafAt T v x ∧ q <+: v := by
 obtain ⟨x,hx⟩ := List.exists_mem_of_ne_nil (leaves U) (CutRealization.leaves_nonempty U)
 obtain ⟨u,hu⟩ := leaf_exists hx
 exact ⟨q++u,x,by unfold LeafAt; rw [subtree_append h]; exact hu,List.prefix_append _ _⟩

theorem valid_outside_leaf {T : Tree} {q : RMAF.Vertex} (hq : Valid T q) (qn : q ≠ []) :
 ∃ v x, LeafAt T v x ∧ ¬q <+: v := by
 rcases List.eq_nil_or_concat q with eq | ⟨p,s,eq⟩
 · contradiction
 · have eq : q = p++[s] := by simpa only [List.concat_eq_append] using eq
   subst q
   simp only [List.concat_eq_append] at *
   obtain ⟨U,hu⟩ := valid_ancestor hq (List.prefix_append p [s])
   cases U with
   | leaf x =>
     obtain ⟨V,hv⟩ := hq
     rw [subtree_append hu] at hv
     simp [subtree] at hv
   | node l r =>
     have other : subtree T (p++[!s]) = some (if s then l else r) := by
       rw [subtree_append hu]; cases s <;> rfl
     obtain ⟨v,x,hv,pv⟩ := subtree_selected_leaf other
     refine ⟨v,x,hv,?_⟩
     intro sp
     obtain ⟨u,eu⟩ := sp
     obtain ⟨w,ew⟩ := pv
     have hh : s::u = (!s)::w := by
       apply List.append_cancel_left (as:=p)
       simpa [List.append_assoc] using eu.trans ew.symm
     have falseEq := (List.cons.inj hh).1
     cases s <;> simp at falseEq

theorem boundary_outside_leaf {T : Tree} {X : List Nat} {q : RMAF.Vertex}
 (hq : q ∈ incident T X) : ∃ v x, LeafAt T v x ∧ OutsideAt T X q v := by
 have hs := (incident_spec T X q).1 hq
 rcases boundary_directions hq with hi | ho
 · obtain ⟨v,x,hv,nv⟩ := valid_outside_leaf hs.1 hs.2.1
   exact ⟨v,x,hv,by unfold OutsideAt; simp [nv,hi.1]⟩
 · obtain ⟨U,hu⟩ := hs.1
   obtain ⟨v,x,hv,pv⟩ := subtree_selected_leaf hu
   exact ⟨v,x,hv,by unfold OutsideAt; simp [pv,ho.1]⟩

theorem boundary_meets_one_other {T : Tree} {X C : List Nat} {c d : Nat} {q : RMAF.Vertex}
 (hn : (leaves T).Nodup) (hp : partitionCheck (leaves T) [X,[c],C] = true)
 (he : pairwiseEmbeddings T [X,[c],C] = true) (hd : d ∈ C)
 (hq : q ∈ incident T X) : OutsideLabel T X q c ∨ OutsideLabel T X q d := by
 obtain ⟨v,x,hv,out⟩ := boundary_outside_leaf hq
 have nx : x ∉ X := by
   intro hx
   exact outside_not_hull hq out ((minimalVertices_terminal X T v x hv).2 hx)
 obtain ⟨B,hB,hx⟩ := partitionCheck_covers (leaves T) [X,[c],C] hp x (leafAt_label T v x hv)
 have Bcase : B = X ∨ B = [c] ∨ B = C := by simpa using hB
 rcases Bcase with eq | eq | eq
 · subst B; exact False.elim (nx hx)
 · subst B
   have xc : x = c := by simpa using hx
   subst x
   exact Or.inl ((outside_label_at hn hv).2 out)
 · subst B
   right
   have all := (executable_pairwiseEmbeddings T [X,[c],C]).1 he
   have dj := (List.pairwise_cons.1 all).1 C (by simp)
   exact (outside_block_constant hn hq dj (fun z hz => block_labels hp (by simp) hz) hx hd).1
     ((outside_label_at hn hv).2 out)

/-- A three-block checked embedding gives at most two actual boundary arcs
for its X block. The proof injects original arcs into the two other regions;
no geometry, boundary-cardinality or coverage premise is supplied. -/
theorem incident_at_most_two {T : Tree} {X C : List Nat} {c : Nat}
 (hn : (leaves T).Nodup) (hp : partitionCheck (leaves T) [X,[c],C] = true)
 (he : pairwiseEmbeddings T [X,[c],C] = true) : (incident T X).length ≤ 2 := by
 classical
 obtain ⟨d,hd⟩ := List.exists_mem_of_ne_nil C (RestrictionBridge.checked_nonempty _ _ hp C (by simp))
 let color : RMAF.Vertex → Bool := fun q => decide (OutsideLabel T X q c)
 have inj {q r : RMAF.Vertex} (hq : q ∈ incident T X) (hr : r ∈ incident T X)
  (eq : color q = color r) : q = r := by
   apply Classical.byContradiction
   intro neq
   have clash (x : Nat) (qx : OutsideLabel T X q x) (rx : OutsideLabel T X r x)
    (xl : x ∈ leaves T) : False := by
     obtain ⟨v,hv⟩ := leaf_exists xl
     exact outside_regions_disjoint hq hr neq
       ⟨(outside_label_at hn hv).1 qx,(outside_label_at hn hv).1 rx⟩
   by_cases qc : OutsideLabel T X q c
   · have rc : OutsideLabel T X r c := by
       have tt : color r = true := eq.symm.trans (by simp [color,qc])
       exact of_decide_eq_true tt
     exact clash c qc rc (block_labels hp (B:=[c]) (by simp) (by simp))
   · have rc : ¬OutsideLabel T X r c := by
       intro rc
       have ff : color q = false := by simp [color,qc]
       have tt : color r = true := by simp [color,rc]
       simp [ff,tt] at eq
     have qd := (boundary_meets_one_other hn hp he hd hq).resolve_left qc
     have rd := (boundary_meets_one_other hn hp he hd hr).resolve_left rc
     exact clash d qd rd (block_labels hp (by simp) hd)
 have nd : (incident T X).Nodup := (vertices_nodup T).filter _
 have mapnd : ((incident T X).map color).Nodup := by
   apply List.pairwise_map.2
   apply List.Pairwise.imp_of_mem _ nd
   intro q r hq hr neq eq
   exact neq (inj hq hr eq)
 have le := mapnd.length_le_of_subset (l₂:=[false,true]) (by intro x hx; cases x <;> simp)
 simpa using le

theorem empty_boundary_adj {T : Tree} {X : List Nat} {u v : RMAF.Vertex}
 (hi : incident T X = []) (he : Adj T u v) : paint T X u = paint T X v := by
 have forward {u v : RMAF.Vertex} (he : Adj T u v)
  (child : ∃ s, v = u++[s]) : paint T X u = paint T X v := by
   obtain ⟨s,rfl⟩ := child
   apply Classical.byContradiction
   intro neq
   have mem : u++[s] ∈ incident T X := (incident_spec T X _).2
     ⟨he.2.1,by simp,by simpa using Ne.symm neq⟩
   rw [hi] at mem; contradiction
 rcases he.2.2 with child | child
 · exact forward he child
 · exact (forward he.symm child).symm

theorem empty_boundary_constant {T : Tree} {X : List Nat}
 (hi : incident T X = []) {v : RMAF.Vertex} (hv : Valid T v) : paint T X v = paint T X [] := by
 have seed : Region [] [] [] := ⟨List.nil_prefix,by simp⟩
 have reg : Region [] [] v := ⟨List.nil_prefix,by simp⟩
 have walk := (region_component (T:=T) (Or.inl rfl) (valid_root T) seed).2 ⟨hv,reg⟩
 have colors {u v : RMAF.Vertex} (w : ResidualWalk T [] u v) : paint T X u = paint T X v := by
   induction w with
   | refl => rfl
   | step he tail ih => exact (empty_boundary_adj hi he.1).trans ih
 exact (colors walk).symm

theorem incident_nonempty {T : Tree} {X C : List Nat} {c : Nat}
 (hp : partitionCheck (leaves T) [X,[c],C] = true)
 (he : pairwiseEmbeddings T [X,[c],C] = true) : incident T X ≠ [] := by
 intro hi
 obtain ⟨x,hx⟩ := List.exists_mem_of_ne_nil X (RestrictionBridge.checked_nonempty _ _ hp X (by simp))
 obtain ⟨u,hu⟩ := leaf_exists (block_labels hp (B:=X) (by simp) hx)
 obtain ⟨v,hv⟩ := leaf_exists (block_labels hp (B:=[c]) (x:=c) (by simp) (by simp))
 have hux : paint T X u = true := by simpa [paint] using (minimalVertices_terminal X T u x hu).2 hx
 have nc : c ∉ X := by
   intro cx
   have dj := (List.pairwise_cons.1 ((executable_pairwiseEmbeddings T [X,[c],C]).1 he)).1 [c] (by simp)
   exact dj v ⟨(minimalVertices_correct X T v).1 ((minimalVertices_terminal X T v c hv).2 cx),
     (minimalVertices_correct [c] T v).1 ((minimalVertices_terminal [c] T v c hv).2 (by simp))⟩
 have hvx : paint T X v = false := by
   have nn : v ∉ minimalVertices X T := fun h => nc ((minimalVertices_terminal X T v c hv).1 h)
   simp [paint,nn]
 have eq : paint T X u = paint T X v :=
   (empty_boundary_constant hi hu.valid).trans (empty_boundary_constant hi hv.valid).symm
 simp [hux,hvx] at eq

theorem incident_one_or_two {T : Tree} {X C : List Nat} {c : Nat}
 (hn : (leaves T).Nodup) (hp : partitionCheck (leaves T) [X,[c],C] = true)
 (he : pairwiseEmbeddings T [X,[c],C] = true) :
 (∃ q, incident T X = [q]) ∨ ∃ q r, incident T X = [q,r] := by
 have upper := incident_at_most_two hn hp he
 have nonempty := incident_nonempty hp he
 cases eq : incident T X with
 | nil => contradiction
 | cons q tail =>
   cases tail with
   | nil => exact Or.inl ⟨q,rfl⟩
   | cons r tail =>
     have tt : tail = [] := by
       rw [eq] at upper
       have len : tail.length = 0 := by simp only [List.length_cons] at upper; omega
       exact List.length_eq_zero_iff.1 len
     subst tail
     exact Or.inr ⟨q,r,rfl⟩

theorem outside_label_not_X {T : Tree} {X : List Nat} {q : RMAF.Vertex} {x : Nat}
 (hn : (leaves T).Nodup) (hq : q ∈ incident T X) (hx : x ∈ leaves T)
 (out : OutsideLabel T X q x) : x ∉ X := by
 obtain ⟨v,hv⟩ := leaf_exists hx
 exact fun xX => outside_not_hull hq ((outside_label_at hn hv).1 out)
   ((minimalVertices_terminal X T v x hv).2 xX)

theorem two_boundary_roles {T : Tree} {X C : List Nat} {c : Nat} {q r : RMAF.Vertex}
 (hn : (leaves T).Nodup) (hp : partitionCheck (leaves T) [X,[c],C] = true)
 (he : pairwiseEmbeddings T [X,[c],C] = true) (hi : incident T X = [q,r]) :
 ∃ u v, (u=q ∧ v=r ∨ u=r ∧ v=q) ∧
 (∀ x, x ∈ leaves T → (OutsideLabel T X u x ↔ x=c)) ∧
 (∀ x, x ∈ leaves T → (OutsideLabel T X v x ↔ x∈C)) := by
 have qm : q ∈ incident T X := by simp [hi]
 have rm : r ∈ incident T X := by simp [hi]
 have neq : q ≠ r := by
   have nd : (incident T X).Nodup := (vertices_nodup T).filter _
   simpa [hi] using nd
 obtain ⟨d,hd⟩ := List.exists_mem_of_ne_nil C (RestrictionBridge.checked_nonempty _ _ hp C (by simp))
 have all := (executable_pairwiseEmbeddings T [X,[c],C]).1 he
 have dj := (List.pairwise_cons.1 all).1 C (by simp)
 have cL : c ∈ leaves T := block_labels hp (B:=[c]) (by simp) (by simp)
 have dL : d ∈ leaves T := block_labels hp (by simp) hd
 have disjoint {u v : RMAF.Vertex} (um : u ∈ incident T X) (vm : v ∈ incident T X)
  (ne : u ≠ v) {x : Nat} (xl : x ∈ leaves T) :
  ¬(OutsideLabel T X u x ∧ OutsideLabel T X v x) := by
   obtain ⟨w,hw⟩ := leaf_exists xl
   exact fun hs => outside_regions_disjoint um vm ne
     ⟨(outside_label_at hn hw).1 hs.1,(outside_label_at hn hw).1 hs.2⟩
 have roles {u v : RMAF.Vertex} (um : u ∈ incident T X) (vm : v ∈ incident T X)
  (ne : u ≠ v) (uc : OutsideLabel T X u c) (vd : OutsideLabel T X v d) :
  (∀ x, x ∈ leaves T → (OutsideLabel T X u x ↔ x=c)) ∧
  (∀ x, x ∈ leaves T → (OutsideLabel T X v x ↔ x∈C)) := by
   have noUd : ¬OutsideLabel T X u d := fun ud => disjoint um vm ne dL ⟨ud,vd⟩
   have noVc : ¬OutsideLabel T X v c := fun vc => disjoint um vm ne cL ⟨uc,vc⟩
   constructor
   · intro x xl
     constructor
     · intro ux
       have nx := outside_label_not_X hn um xl ux
       obtain ⟨B,hB,hx⟩ := partitionCheck_covers (leaves T) [X,[c],C] hp x xl
       have hh : B=X ∨ B=[c] ∨ B=C := by simpa using hB
       rcases hh with eq | eq | eq
       · subst B; exact False.elim (nx hx)
       · subst B; simpa using hx
       · subst B
         exact False.elim (noUd ((outside_block_constant hn um dj (fun z hz => block_labels hp (by simp) hz) hx hd).1 ux))
     · intro eq; subst x; exact uc
   · intro x xl
     constructor
     · intro vx
       have nx := outside_label_not_X hn vm xl vx
       obtain ⟨B,hB,hx⟩ := partitionCheck_covers (leaves T) [X,[c],C] hp x xl
       have hh : B=X ∨ B=[c] ∨ B=C := by simpa using hB
       rcases hh with eq | eq | eq
       · subst B; exact False.elim (nx hx)
       · subst B
         have eq : x=c := by simpa using hx
         subst x; exact False.elim (noVc vx)
       · subst B; exact hx
     · intro xC
       exact (outside_block_constant hn vm dj (fun z hz => block_labels hp (by simp) hz) hd xC).1 vd
 by_cases qc : OutsideLabel T X q c
 · have rd := (boundary_meets_one_other hn hp he hd rm).resolve_left
     (fun rc => disjoint qm rm neq cL ⟨qc,rc⟩)
   exact ⟨q,r,Or.inl ⟨rfl,rfl⟩,roles qm rm neq qc rd⟩
 · have qd := (boundary_meets_one_other hn hp he hd qm).resolve_left qc
   have rc := (boundary_meets_one_other hn hp he hd rm).resolve_right
     (fun rd => disjoint qm rm neq dL ⟨qd,rd⟩)
   exact ⟨r,q,Or.inr ⟨rfl,rfl⟩,roles rm qm neq.symm rc qd⟩

def OutRegion (T : Tree) (X : List Nat) (q : RMAF.Vertex) (B : List Nat) : Prop :=
 Outgoing T X q ∧ ∀ x, x ∈ leaves T → (x ∈ subtreeLabels T q ↔ x ∈ B)
def InRegion (T : Tree) (X : List Nat) (q : RMAF.Vertex) (B : List Nat) : Prop :=
 Incoming T X q ∧ ∀ x, x ∈ leaves T → (x ∉ subtreeLabels T q ↔ x ∈ B)

/-- Exact three boundary alternatives. Incoming sides are stated on the
literal original root side, not silently converted to descendant subtrees. -/
theorem actual_two_boundary_trichotomy {T : Tree} {X C : List Nat} {c : Nat} {q r : RMAF.Vertex}
 (hn : (leaves T).Nodup) (hp : partitionCheck (leaves T) [X,[c],C] = true)
 (he : pairwiseEmbeddings T [X,[c],C] = true) (hi : incident T X = [q,r]) :
 ∃ u v, (u=q ∧ v=r ∨ u=r ∧ v=q) ∧
 ((OutRegion T X u [c] ∧ InRegion T X v C) ∨
  (OutRegion T X u [c] ∧ OutRegion T X v C) ∨
  (InRegion T X u [c] ∧ OutRegion T X v C)) := by
 obtain ⟨u,v,uv,uc,vc⟩ := two_boundary_roles hn hp he hi
 have um : u ∈ incident T X := by rcases uv with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> simp [hi]
 have vm : v ∈ incident T X := by rcases uv with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> simp [hi]
 have ne : u ≠ v := by
   have nd : (incident T X).Nodup := (vertices_nodup T).filter _
   have qr : q ≠ r := by simpa [hi] using nd
   rcases uv with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
   · exact qr
   · exact qr.symm
 have outU (h : Outgoing T X u) : OutRegion T X u [c] := by
   refine ⟨h,?_⟩
   intro x hx
   have hh := uc x hx
   simpa [OutsideLabel,h.1] using hh
 have inU (h : Incoming T X u) : InRegion T X u [c] := by
   refine ⟨h,?_⟩
   intro x hx
   have hh := uc x hx
   simpa [OutsideLabel,h.1] using hh
 have outV (h : Outgoing T X v) : OutRegion T X v C := by
   refine ⟨h,?_⟩
   intro x hx
   simpa [OutsideLabel,h.1] using vc x hx
 have inV (h : Incoming T X v) : InRegion T X v C := by
   refine ⟨h,?_⟩
   intro x hx
   simpa [OutsideLabel,h.1] using vc x hx
 refine ⟨u,v,uv,?_⟩
 rcases boundary_directions um with ui | uo <;> rcases boundary_directions vm with vi | vo
 · exact False.elim (ne (incoming_unique um vm ui vi))
 · exact Or.inr (Or.inr ⟨inU ui,outV vo⟩)
 · exact Or.inl ⟨outU uo,inV vi⟩
 · exact Or.inr (Or.inl ⟨outU uo,outV vo⟩)

theorem proper_one_label_tree {Z : Tree} {c : Nat} (hn : (leaves Z).Nodup)
 (hall : ∀ x, x ∈ leaves Z → x=c) : Z = .leaf c := by
 have len := hn.length_le_of_subset (l₂:=[c]) (by intro x hx; simp [hall x hx])
 have pos := leaves_length_positive Z
 obtain ⟨x,hx⟩ := leaves_one_leaf (T:=Z) (by simp only [List.length_singleton] at len; omega)
 subst Z
 have eq := hall x (by simp [leaves])
 subst x; rfl

theorem fork_nodup_parts {s : Bool} {U Z : Tree} (hn : (leaves (fork s U Z)).Nodup) :
 (leaves U).Nodup ∧ (leaves Z).Nodup ∧ ∀ x, x ∈ leaves U → x ∉ leaves Z := by
 cases s
 · obtain ⟨hu,hz,dj⟩ := List.nodup_append.1 hn
   exact ⟨hu,hz,fun x hx hz => dj x hx x hz rfl⟩
 · obtain ⟨hz,hu,dj⟩ := List.nodup_append.1 hn
   exact ⟨hu,hz,fun x hx hz => dj x hz x hx rfl⟩

/-- A singleton original root side forces the actual root fork. Thus the
third boundary alternative includes the literal c child of the root. -/
theorem singleton_root_side {T : Tree} {q : RMAF.Vertex} {c : Nat}
 (hn : (leaves T).Nodup) (hq : Valid T q) (qn : q ≠ [])
 (hc : ∀ x, x ∈ leaves T → (x ∉ subtreeLabels T q ↔ x=c)) :
 ∃ s U, q=[s] ∧ T=fork s U (.leaf c) := by
 cases q with
 | nil => contradiction
 | cons s v =>
   cases T with
   | leaf x => obtain ⟨U,hU⟩ := hq; simp [subtree] at hU
   | node l r =>
     let U := if s then r else l
     let Z := if s then l else r
     have Teq : Tree.node l r = fork s U Z := by cases s <;> rfl
     rw [Teq] at hn hq hc ⊢
     have parts := fork_nodup_parts hn
     have qu : Valid U v := by cases s <;> exact hq
     have sub : subtreeLabels (fork s U Z) (s::v) = subtreeLabels U v := by cases s <;> rfl
     have uL : ∀ x, x ∈ leaves U → x ∈ leaves (fork s U Z) := by
       intro x hx; cases s <;> simp [fork,leaves,hx]
     have zL : ∀ x, x ∈ leaves Z → x ∈ leaves (fork s U Z) := by
       intro x hx; cases s <;> simp [fork,leaves,hx]
     have allZ : ∀ x, x ∈ leaves Z → x=c := by
       intro x hx
       apply (hc x (zL x hx)).1
       rw [sub]
       intro xv
       exact parts.2.2 x ((subtreeLabels_sublist U v).subset xv) hx
     have Zc : Z = .leaf c := proper_one_label_tree parts.2.1 allZ
     have vn : v=[] := by
       apply Classical.byContradiction
       intro nv
       obtain ⟨w,x,hw,nw⟩ := valid_outside_leaf qu nv
       have no : x ∉ subtreeLabels U v := fun h => nw ((label_prefix parts.1 hw).1 h)
       have xc : x=c := (hc x (uL x (leafAt_label U w x hw))).1 (by simpa [sub] using no)
       have cZ : c ∈ leaves Z := by rw [Zc]; simp [leaves]
       exact parts.2.2 x (leafAt_label U w x hw) (xc ▸ cZ)
     subst v
     exact ⟨s,U,rfl,by rw [Zc]⟩

theorem third_attachment_actual_root {T : Tree} {X : List Nat} {u : RMAF.Vertex} {c : Nat}
 (hn : (leaves T).Nodup) (um : u ∈ incident T X) (h : InRegion T X u [c]) :
 ∃ s U, u=[s] ∧ T=fork s U (.leaf c) := by
 have us := (incident_spec T X u).1 um
 apply singleton_root_side hn us.1 us.2.1
 intro x hx
 simpa using h.2 x hx

end Universal233.Rule5FinalClassification
