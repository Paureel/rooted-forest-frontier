import AdmittedCases
namespace Universal233.Rule5Classification
open RMAF CoreGraph Integration VertexGeometry CutRealization HardParent CherryBranching Rule5Local

theorem prefix_parent_of_ne {a b : RMAF.Vertex} (hp : a <+: b) (hn : a ≠ b) :
 a <+: b.dropLast := by
 obtain ⟨tail,he⟩ := hp
 have nt : tail ≠ [] := by intro e; simp [e] at he; exact hn he
 rw [←he,List.dropLast_append_of_ne_nil nt]
 exact List.prefix_append _ _

theorem zero_cuts_hasCherry {S : Tree} {p q : Nat}
 (hn : (leaves S).Nodup) (hp : p ∈ leaves S) (hq : q ∈ leaves S) (npq : p ≠ q)
 (hc : cuts S p q = []) : HasCherry p q S := by
 obtain ⟨U,hU,ch⟩ := core_has_cherry hn hp hq npq
 have coreEq : coreLabels S p q = leaves S := by simp [coreLabels,hc]
 have whole : restrict (leaves S) S = some S := restrict_of_contains S (leaves S) (by simp)
 rw [coreEq,whole] at hU
 have e := Option.some.inj hU
 exact e ▸ ch

/-- A second cherry of the literal original core, disjoint from a,b, is an
actual source cherry. The proof excludes every putative outgoing pq arc by
original path disjointness; no source caterpillar shape is assumed. -/
theorem original_core_second_cherry {S U : Tree} {a b p q : Nat} {j : RMAF.Vertex}
 (hn : (leaves S).Nodup) (aS : a ∈ leaves S) (bS : b ∈ leaves S) (nab : a ≠ b)
 (hU : restrict (coreLabels S a b) S = some U) (cpq : CherryAt U j p q)
 (sep : p ≠ a ∧ p ≠ b ∧ q ≠ a ∧ q ≠ b) : HasCherry p q S := by
 have hpq := hasCherry_labels (actual_hasCherry cpq)
 have pC := (HardParent.restrict_mem hU p).1 hpq.1
 have qC := (HardParent.restrict_mem hU q).1 hpq.2
 have hnU : (leaves U).Nodup := by rw [restrict_leaves hU]; exact hn.filter _
 have npq := cherry_distinct hnU cpq
 obtain ⟨V,hV,cab⟩ := core_has_cherry hn aS bS nab
 have eU : V = U := Option.some.inj (hV.symm.trans hU)
 subst V
 have clearU := distinct_cherries_clear hnU (actual_hasCherry cpq) cab sep
 have aC := endpoint_core (Or.inl rfl) aS (b:=b)
 have bC := endpoint_core (Or.inr rfl) bS (a:=a)
 have clearS := ((RestrictionBridge.literal_clear_transport S U (coreLabels S a b) [p,q] [a,b] hU
   (by intro x hx; have hh : x = p ∨ x = q := by simpa using hx
       rcases hh with rfl | rfl; exact pC.2; exact qC.2)
   (by intro x hx; have hh : x = a ∨ x = b := by simpa using hx
       rcases hh with rfl | rfl; exact aC; exact bC)).2).2 clearU
 have pr := prunedCherry_of_restrict hn hU (actual_hasCherry cpq)
 have excl := prunedCherry_excluded pr
 have noCuts : ∀ r, r ∉ cuts S p q := by
   intro r hr
   have rs := (cuts_spec S p q r).1 hr
   obtain ⟨x,xr⟩ := List.exists_mem_of_ne_nil _ (subtreeLabels_nonempty rs.1)
   have xS := (subtreeLabels_sublist S r).subset xr
   have xnC := excl r rs.2.1 rs.2.2.1 rs.2.2.2 x xr
   have outside : ∃ e, e ∈ cuts S a b ∧ x ∈ subtreeLabels S e := by
     apply Classical.byContradiction
     intro no
     exact xnC ((mem_core S a b x).2 ⟨xS,fun e he hx => no ⟨e,he,hx⟩⟩)
   obtain ⟨e,he,xe⟩ := outside
   have es := (cuts_spec S a b e).1 he
   obtain ⟨u,hu,hru⟩ := (subtreeLabels_prefix S r x).1 xr
   obtain ⟨v,hv,hev⟩ := (subtreeLabels_prefix S e x).1 xe
   have euv := leaf_unique hn hu hv
   rw [euv] at hru
   by_cases re : r = e
   · exact clearS r.dropLast rs.2.2.1 (re.symm ▸ es.2.2.1)
   · rcases List.prefix_or_prefix_of_prefix hru hev with pre | per
     · have parent := prefix_parent_of_ne pre re
       have an : a ∉ subtreeLabels S r := fun ar => excl r rs.2.1 rs.2.2.1 rs.2.2.2 a ar aC
       have bn : b ∉ subtreeLabels S r := fun br => excl r rs.2.1 rs.2.2.1 rs.2.2.2 b br bC
       exact (no_selected_subtree_hull (D:=[a,b])
         (by intro y hy; have hh : y = a ∨ y = b := by simpa using hy
             rcases hh with rfl | rfl <;> assumption) parent) es.2.2.1
     · have parent := prefix_parent_of_ne per (Ne.symm re)
       have pn : p ∉ subtreeLabels S e := ((mem_core S a b p).1 pC.2).2 e he
       have qn : q ∉ subtreeLabels S e := ((mem_core S a b q).1 qC.2).2 e he
       exact (no_selected_subtree_hull (D:=[p,q])
         (by intro y hy; have hh : y = p ∨ y = q := by simpa using hy
             rcases hh with rfl | rfl <;> assumption) parent) rs.2.2.1
 have hc : cuts S p q = [] := List.eq_nil_iff_forall_not_mem.2 noCuts
 exact zero_cuts_hasCherry hn pC.1 qC.1 npq hc

theorem partition_rotate (L X Y Z : List Nat) :
 partitionCheck L [X,Y,Z] = partitionCheck L [Z,X,Y] := by
 simp only [partitionCheck,List.all_cons,List.all_nil,List.flatten_cons,List.flatten_nil,List.append_nil,
   List.count_append,List.all_append]
 simp only [Nat.add_comm,Nat.add_left_comm,Nat.add_assoc,Bool.and_comm,Bool.and_left_comm,Bool.and_assoc]

theorem embeddings_rotate (T : Tree) (X Y Z : List Nat)
 (he : pairwiseEmbeddings T [X,Y,Z] = true) : pairwiseEmbeddings T [Z,X,Y] = true := by
 have hp := (executable_pairwiseEmbeddings T [X,Y,Z]).1 he
 have dxy := (List.pairwise_cons.1 hp).1 Y (by simp)
 have dxz := (List.pairwise_cons.1 hp).1 Z (by simp)
 have dyz := (List.pairwise_cons.1 (List.pairwise_cons.1 hp).2).1 Z (by simp)
 apply (executable_pairwiseEmbeddings T [Z,X,Y]).2
 apply List.pairwise_cons.2
 constructor
 · intro B hB
   have hh : B = X ∨ B = Y := by simpa using hB
   rcases hh with rfl | rfl
   · exact fun v h => dxz v ⟨h.2,h.1⟩
   · exact fun v h => dyz v ⟨h.2,h.1⟩
 · apply List.pairwise_cons.2
   constructor
   · intro B hB
     have e : B = Y := by simpa using hB
     subst B
     exact dxy
   · simp

structure OutsideSelection where
 parent : RMAF.Vertex
 p : Nat
 q : Nat
 deriving Repr, DecidableEq

def outsideAt (T S : Tree) (a b : Nat) (c : RMAF.Vertex × Nat × Nat) : Option OutsideSelection :=
 let (j,p,q) := c
 if restrictionAgrees T S (coreLabels S a b) && (coreLabels S a b).contains p &&
   (coreLabels S a b).contains q && p != a && p != b && q != a && q != b then
   some ⟨j,p,q⟩ else none
def outsideCandidates (T S : Tree) (a b : Nat) := (cherries S).filterMap (outsideAt T S a b)
def selectOutside (T S : Tree) (a b : Nat) : Option OutsideSelection :=
 (outsideCandidates T S a b).head?

theorem outsideCandidate_sound {T S : Tree} {a b : Nat} {c : OutsideSelection}
 (h : c ∈ outsideCandidates T S a b) :
 CherryAt S c.parent c.p c.q ∧ restrictionAgrees T S (coreLabels S a b) = true ∧
 c.p ∈ coreLabels S a b ∧ c.q ∈ coreLabels S a b ∧
 (c.p ≠ a ∧ c.p ≠ b ∧ c.q ≠ a ∧ c.q ≠ b) := by
 obtain ⟨⟨j,p,q⟩,hc,hh⟩ := List.mem_filterMap.1 h
 simp only [outsideAt] at hh
 split at hh
 · rename_i hg
   have eq := Option.some.inj hh
   subst c
   simp only [Bool.and_eq_true,List.contains_iff_mem,bne_iff_ne] at hg
   exact ⟨cherries_sound S j p q hc,hg.1.1.1.1.1.1,hg.1.1.1.1.1.2,hg.1.1.1.1.2,
     hg.1.1.1.2,hg.1.1.2,hg.1.2,hg.2⟩
 · contradiction

theorem selectOutside_sound {T S : Tree} {a b : Nat} {c : OutsideSelection}
 (h : selectOutside T S a b = some c) : c ∈ outsideCandidates T S a b := by
 obtain ⟨tail,ht⟩ := List.head?_eq_some_iff.1 h
 rw [ht]
 simp

/-- Every actual outside second cherry of the source core is found by the
finite original-source scan. This is a completeness bridge from the literal
restriction; no chosen outside cherry is inserted as an input certificate. -/
theorem outside_selector_complete {S T U : Tree} {a b p q : Nat} {j : RMAF.Vertex}
 (hn : (leaves S).Nodup) (aS : a ∈ leaves S) (bS : b ∈ leaves S) (nab : a ≠ b)
 (hU : restrict (coreLabels S a b) S = some U) (cpq : CherryAt U j p q)
 (sep : p ≠ a ∧ p ≠ b ∧ q ≠ a ∧ q ≠ b)
 (good : restrictionAgrees T S (coreLabels S a b) = true) :
 ∃ c, selectOutside T S a b = some c := by
 have lab := hasCherry_labels (actual_hasCherry cpq)
 have pC := ((HardParent.restrict_mem hU p).1 lab.1).2
 have qC := ((HardParent.restrict_mem hU q).1 lab.2).2
 have cs := original_core_second_cherry hn aS bS nab hU cpq sep
 obtain ⟨i,hi | hi⟩ := hasCherry_actual cs
 · have mem : (⟨i,p,q⟩ : OutsideSelection) ∈ outsideCandidates T S a b := by
     apply List.mem_filterMap.2
     exact ⟨(i,p,q),cherries_complete S i p q hi,by simp [outsideAt,good,pC,qC,sep.1,sep.2.1,sep.2.2.1,sep.2.2.2]⟩
   cases hs : outsideCandidates T S a b with
   | nil => rw [hs] at mem; contradiction
   | cons c tail => exact ⟨c,by simp [selectOutside,hs]⟩
 · have mem : (⟨i,q,p⟩ : OutsideSelection) ∈ outsideCandidates T S a b := by
     apply List.mem_filterMap.2
     exact ⟨(i,q,p),cherries_complete S i q p hi,by simp [outsideAt,good,pC,qC,sep.1,sep.2.1,sep.2.2.1,sep.2.2.2]⟩
   cases hs : outsideCandidates T S a b with
   | nil => rw [hs] at mem; contradiction
   | cons c tail => exact ⟨c,by simp [selectOutside,hs]⟩

theorem admitted_outside_context {T S : Tree} {i : RMAF.Vertex} {a b : Nat}
 (ha : admitted T S a b = true) (ch : CherryAt T i a b) :
 ∃ Y Z, partitionCheck (leaves T) [coreLabels S a b,Y,Z] = true ∧
 pairwiseEmbeddings T [coreLabels S a b,Y,Z] = true ∧
 (∀ B, B ∈ [coreLabels S a b,Y,Z] ↔ B ∈ pendantPartition S a b) := by
 have parts := admitted_parts ha
 obtain ⟨u,v,cutEq⟩ := list_two_named (cuts S a b) parts.2.2.2.2
 have P : pendantPartition S a b = [subtreeLabels S u,subtreeLabels S v,coreLabels S a b] := by
   simp only [pendantPartition,cutEq,List.map_cons,List.map_nil,List.cons_append,List.nil_append]
 refine ⟨subtreeLabels S u,subtreeLabels S v,?_,?_,?_⟩
 · rw [←partition_rotate]
   exact P ▸ (admitted_ordered_checks ha ch).1
 · exact embeddings_rotate T _ _ _ (P ▸ parts.2.2.2.1)
 · intro B; simp [P,or_comm,or_left_comm,or_assoc]

theorem admitted_outside_cover {T S : Tree} {i : RMAF.Vertex} {a b : Nat} {c : OutsideSelection}
 {F : List (List Nat)} (ha : admitted T S a b = true) (ch : CherryAt T i a b)
 (sel : selectOutside T S a b = some c) (hF : agreement T S F = true) :
 ∃ d, d ∈ fiveChildren S a b c.p c.q ∧ feasible T S d F := by
 have sc := outsideCandidate_sound (selectOutside_sound sel)
 obtain ⟨Y,Z,hp,he,perm⟩ := admitted_outside_context ha ch
 have parts := admitted_parts ha
 have prop := properPair_parts parts.1
 exact guarded_five_cover prop.1 prop.2.1 hp he perm parts.2.2.1 sc.2.1 ch sc.1 sc.2.2.1 sc.2.2.2.1 hF

theorem admitted_outside_child_solver {T S : Tree} {i : RMAF.Vertex} {a b : Nat} {c : OutsideSelection}
 (ha : admitted T S a b = true) (ch : CherryAt T i a b)
 (sel : selectOutside T S a b = some c)
 (solver : Child → Nat → Option (List (List Nat)))
 (ih : ∀ d, d ∈ fiveChildren S a b c.p c.q → ExactBoundedChild T S solver d) (k : Nat) :
 OriginalWithin T S k ↔ ∃ d, d ∈ fiveChildren S a b c.p c.q ∧ ∃ G, childCall solver k d = some G := by
 have sc := outsideCandidate_sound (selectOutside_sound sel)
 obtain ⟨Y,Z,hp,he,perm⟩ := admitted_outside_context ha ch
 have parts := admitted_parts ha
 have prop := properPair_parts parts.1
 exact guarded_five_child_solver prop.1 prop.2.1 prop.2.2 hp he perm parts.2.2.1 sc.2.1 ch sc.1
   sc.2.2.1 sc.2.2.2.1 sc.2.2.2.2 parts.2.2.2.2 solver ih k

theorem cherry_parent_at_label {S : Tree} {i : RMAF.Vertex} {a b x : Nat}
 (hc : CherryAt S i a b) (hx : x = a ∨ x = b) :
 ∃ v, LeafAt S v x ∧ v.dropLast = i := by
 rcases hx with rfl | rfl
 · exact ⟨i ++ [false],cherry_left hc,by simp⟩
 · exact ⟨i ++ [true],cherry_right hc,by simp⟩

theorem actual_cherries_same_or_separated {S : Tree} {i j : RMAF.Vertex} {a b p q : Nat}
 (hn : (leaves S).Nodup) (cab : CherryAt S i a b) (cpq : CherryAt S j p q) :
 (p = a ∧ q = b) ∨ (p ≠ a ∧ p ≠ b ∧ q ≠ a ∧ q ≠ b) := by
 have parent {x : Nat} (h1 : x = a ∨ x = b) (h2 : x = p ∨ x = q) : i = j := by
   obtain ⟨u,hu,pu⟩ := cherry_parent_at_label cab h1
   obtain ⟨v,hv,pv⟩ := cherry_parent_at_label cpq h2
   have e := leaf_unique hn hu hv
   exact pu.symm.trans ((congrArg List.dropLast e).trans pv)
 by_cases ij : i = j
 · left
   subst j
   have eq := Tree.node.inj (Option.some.inj (cab.symm.trans cpq))
   exact ⟨(Tree.leaf.inj eq.1).symm,(Tree.leaf.inj eq.2).symm⟩
 · right
   exact ⟨fun e => ij (parent (Or.inl e) (Or.inl rfl)),
     fun e => ij (parent (Or.inr e) (Or.inl rfl)),
     fun e => ij (parent (Or.inl e) (Or.inr rfl)),
     fun e => ij (parent (Or.inr e) (Or.inr rfl))⟩

theorem no_outside_core_cherry_only {T S U : Tree} {a b p q : Nat} {j : RMAF.Vertex}
 (hn : (leaves S).Nodup) (aS : a ∈ leaves S) (bS : b ∈ leaves S) (nab : a ≠ b)
 (hU : restrict (coreLabels S a b) S = some U) (cpq : CherryAt U j p q)
 (good : restrictionAgrees T S (coreLabels S a b) = true)
 (none : selectOutside T S a b = none) :
 (p = a ∧ q = b) ∨ (p = b ∧ q = a) := by
 have hnU : (leaves U).Nodup := by rw [restrict_leaves hU]; exact hn.filter _
 obtain ⟨V,hV,cab⟩ := core_has_cherry hn aS bS nab
 have eU : V = U := Option.some.inj (hV.symm.trans hU)
 subst V
 obtain ⟨i,hi | hi⟩ := hasCherry_actual cab
 · rcases actual_cherries_same_or_separated hnU hi cpq with same | sep
   · exact Or.inl same
   · obtain ⟨c,hc⟩ := outside_selector_complete hn aS bS nab hU cpq sep good
     rw [none] at hc
     contradiction
 · rcases actual_cherries_same_or_separated hnU hi cpq with same | sep
   · exact Or.inr same
   · have sep' : p ≠ a ∧ p ≠ b ∧ q ≠ a ∧ q ≠ b := ⟨sep.2.1,sep.1,sep.2.2.2,sep.2.2.1⟩
     obtain ⟨c,hc⟩ := outside_selector_complete hn aS bS nab hU cpq sep' good
     rw [none] at hc
     contradiction

/-- Refusal of the actual outside-cherry selector implies the remaining
good core is a caterpillar with its unique a,b cherry. This establishes the
source's Case3 continuation from the original selector guard. -/
theorem no_outside_core_caterpillar {T S U : Tree} {a b : Nat}
 (hn : (leaves S).Nodup) (aS : a ∈ leaves S) (bS : b ∈ leaves S) (nab : a ≠ b)
 (hU : restrict (coreLabels S a b) S = some U)
 (good : restrictionAgrees T S (coreLabels S a b) = true)
 (none : selectOutside T S a b = none) : Caterpillar U ∧ (cherries U).length = 1 := by
 have hnU : (leaves U).Nodup := by rw [restrict_leaves hU]; exact hn.filter _
 have no : NoSeparatedCherries U := by
   intro i j p q r s cp cr sep
   have one := no_outside_core_cherry_only hn aS bS nab hU cp good none
   have two := no_outside_core_cherry_only hn aS bS nab hU cr good none
   rcases one with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;>
     rcases two with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> simp_all
 have cat := caterpillar_of_no_separated hnU no
 cases U with
 | leaf x =>
   obtain ⟨V,hV,cab⟩ := core_has_cherry hn aS bS nab
   have eU : V = .leaf x := Option.some.inj (hV.symm.trans hU)
   subst V
   cases cab
 | node l r => exact ⟨cat,caterpillar_nonleaf_unique cat⟩

end Universal233.Rule5Classification
