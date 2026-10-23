import Rule4PathPrune
import GroupEmbedding

namespace Universal233.Rule4
open RMAF VertexGeometry CoreGraph Integration HardParent BinaryExchange CutRealization

def graft (a b : Nat) : Tree → Tree
  | .leaf x => if x = a then .node (.leaf a) (.leaf b) else .leaf x
  | .node l r => .node (graft a b l) (graft a b r)

theorem graft_iso (a b : Nat) {s t : Tree} (h : RootedIso s t) :
    RootedIso (graft a b s) (graft a b t) := by
  induction h with
  | leaf x => exact (sameShape_correct _ _).1 (sameShape_refl _)
  | straight _ _ il ir => exact .straight il ir
  | swapped _ _ il ir => exact .swapped il ir

theorem iso_trans {s t u : Tree} (h : RootedIso s t) (k : RootedIso t u) : RootedIso s u := by
  induction h generalizing u with
  | leaf x => exact k
  | straight h1 h2 i1 i2 =>
    cases k with
    | straight k1 k2 => exact .straight (i1 k1) (i2 k2)
    | swapped k1 k2 => exact .swapped (i1 k1) (i2 k2)
  | swapped h1 h2 i1 i2 =>
    cases k with
    | straight k1 k2 => exact .swapped (i1 k2) (i2 k1)
    | swapped k1 k2 => exact .straight (i1 k2) (i2 k1)

theorem optIso_refl (u : Option Tree) : OptIso u u := by
  cases u with
  | none => trivial
  | some t => exact (sameShape_correct t t).1 (sameShape_refl t)

theorem map_graft_join (a b : Nat) (x y : Option Tree) :
    (joinOpt x y).map (graft a b) = joinOpt (x.map (graft a b)) (y.map (graft a b)) := by
  cases x <;> cases y <;> rfl

theorem graft_restrict_absent (a b : Nat) (K : List Nat) (T : Tree) (ha : a ∉ leaves T) :
    (restrict K T).map (graft a b) = restrict K T := by
  induction T with
  | leaf x =>
    have hxa : x ≠ a := fun h => ha (by simp [leaves,h])
    simp only [restrict]
    split <;> simp [graft,hxa]
  | node l r il ir =>
    have hal : a ∉ leaves l := fun h => ha (List.mem_append_left _ h)
    have har : a ∉ leaves r := fun h => ha (List.mem_append_right _ h)
    rw [restrict_node,map_graft_join,il hal,ir har]

theorem restrict_adjoin_absent (b : Nat) (K : List Nat) (T : Tree) (hb : b ∉ leaves T) :
    restrict (b :: K) T = restrict K T := by
  apply BinaryExchange.restrict_congr
  intro x hx
  have hxb : x ≠ b := fun h => hb (h ▸ hx)
  simp [hxb]

/-- Adjoining the missing original cherry sibling is a literal leaf graft on
the agreed K restriction. Child orientation is admitted through RootedIso. -/
theorem restrict_cherry_graft {T : Tree} {a b : Nat} (hc : HasCherry a b T)
    (hn : (leaves T).Nodup) (K : List Nat) (ha : a ∈ K) (hb : b ∉ K) :
    OptIso (restrict (b :: K) T) ((restrict K T).map (graft a b)) := by
  induction hc with
  | here =>
    have hab : a ≠ b := by simpa [leaves] using hn
    simp [restrict,ha,hb,graft,OptIso,hab]
    exact .straight (.leaf a) (.leaf b)
  | swap =>
    have hab : b ≠ a := by simpa [leaves] using hn
    simp [restrict,ha,hb,graft,OptIso,hab]
    exact .swapped (.leaf b) (.leaf a)
  | @left l r hc ih =>
    obtain ⟨hnl,hnr,hdis⟩ := List.nodup_append.1 hn
    have hal := (hasCherry_labels hc).1
    have hbl := (hasCherry_labels hc).2
    have har : a ∉ leaves r := fun h => hdis a hal a h rfl
    have hbr : b ∉ leaves r := fun h => hdis b hbl b h rfl
    rw [restrict_node,restrict_adjoin_absent b K r hbr]
    rw [restrict_node,map_graft_join,graft_restrict_absent a b K r har]
    exact optIso_join (ih hnl) (optIso_refl _)
  | @right l r hc ih =>
    obtain ⟨hnl,hnr,hdis⟩ := List.nodup_append.1 hn
    have har := (hasCherry_labels hc).1
    have hbr := (hasCherry_labels hc).2
    have hal : a ∉ leaves l := fun h => hdis a h a har rfl
    have hbl : b ∉ leaves l := fun h => hdis b h b hbr rfl
    rw [restrict_node,restrict_adjoin_absent b K l hbl]
    rw [restrict_node,map_graft_join,graft_restrict_absent a b K l hal]
    exact optIso_join (optIso_refl _) (ih hnr)

/-- Two actual cherries and an agreed K give an agreed K-plus-sibling E. -/
theorem common_cherry_graft_agrees {T S : Tree} {a b : Nat}
    (hcT : HasCherry a b T) (hcS : HasCherry a b S)
    (hnT : (leaves T).Nodup) (hnS : (leaves S).Nodup)
    (K : List Nat) (ha : a ∈ K) (hb : b ∉ K)
    (hK : restrictionAgrees T S K = true) :
    restrictionAgrees T S (b :: K) = true := by
  have ht := restrict_cherry_graft hcT hnT K ha hb
  have hs := restrict_cherry_graft hcS hnS K ha hb
  unfold restrictionAgrees at hK ⊢
  cases tk : restrict K T <;> cases sk : restrict K S <;> simp only [tk,sk] at hK
  all_goals try contradiction
  rename_i U V
  have hi : RootedIso U V := (sameShape_correct U V).1 hK
  have hg := graft_iso a b hi
  cases te : restrict (b :: K) T <;> cases se : restrict (b :: K) S
  all_goals simp only [tk,sk,te,se,Option.map,OptIso] at ht hs
  all_goals try contradiction
  rename_i E F
  exact (sameShape_correct E F).2 (iso_trans ht (iso_trans hg (iso_symm hs)))

/-- A cherry may be syntactically left/right or have its children swapped. -/
theorem hasCherry_address {T : Tree} {a b : Nat} (hc : HasCherry a b T) :
    ∃ p, CherryAt T p a b ∨ CherryAt T p b a := by
  induction hc with
  | here => exact ⟨[],Or.inl rfl⟩
  | swap => exact ⟨[],Or.inr rfl⟩
  | left h ih =>
    obtain ⟨p,hp | hp⟩ := ih
    · exact ⟨false :: p,Or.inl hp⟩
    · exact ⟨false :: p,Or.inr hp⟩
  | right h ih =>
    obtain ⟨p,hp | hp⟩ := ih
    · exact ⟨true :: p,Or.inl hp⟩
    · exact ⟨true :: p,Or.inr hp⟩
end Universal233.Rule4

namespace Universal233.Rule4
open RMAF VertexGeometry CoreGraph Integration HardParent BinaryExchange CutRealization

theorem target_mutual_clear_right {T : Tree} (hn : (leaves T).Nodup)
    {p : RMAF.Vertex} {a b : Nat} (hc : CherryAt T p b a)
    (D K E : List Nat) (ha : a ∈ K) (hna : a ∉ D) (hnb : b ∉ D)
    (hDK : disjointVertices (minimalVertices D T) (minimalVertices K T) = true)
    (hE : ∀ x, x ∈ E → x ∈ K ∨ x = b) :
    disjointVertices (minimalVertices D T) (minimalVertices E T) = true := by
  have hold := (executable_disjointVertices T D K).1 hDK
  have hparent := cherry_parent_clear hc D hnb hna
  have hanchor : selectedLeaves K T (p ++ [true]) :=
    (selected_at_leaf K T _ a (cherry_right hc)).2 ha
  have hsub : ∀ v, selectedLeaves E T v → selectedLeaves K T v ∨ v = p ++ [false] := by
    intro v hv
    obtain ⟨x,hx,hvx⟩ := (selected_decompose_label E T v).1 hv
    have hl : LeafAt T v x := (leafAt_selected T v x).2 hvx
    rcases hE x hx with hx | rfl
    · exact Or.inl ((selected_at_leaf K T v x hl).2 hx)
    · exact Or.inr (leaf_unique hn hl (cherry_left hc))
  apply (executable_disjointVertices T D E).2
  intro v hv
  rcases hull_adjoin_subset (selectedLeaves K T) (selectedLeaves E T)
    (p ++ [true]) (p ++ [false]) hanchor hsub v hv.2 with hh | hh
  · exact hold v ⟨hv.1,hh⟩
  · have hdv := (minimalVertices_correct D T v).2 hv.1
    rcases sibling_path_cases (path_sym hh) with rfl | rfl | rfl
    · exact hnb ((minimalVertices_terminal D T _ b (cherry_left hc)).1 hdv)
    · exact hparent hdv
    · exact hna ((minimalVertices_terminal D T _ a (cherry_right hc)).1 hdv)

theorem extension_clear_unordered {T : Tree} (hn : (leaves T).Nodup)
    {a b : Nat} (hc : HasCherry a b T) (H K E : List Nat)
    (ha : a ∈ K) (hna : a ∉ H) (hnb : b ∉ H)
    (hHK : disjointVertices (minimalVertices H T) (minimalVertices K T) = true)
    (hE : ∀ x, x ∈ E → x ∈ K ∨ x = b) :
    disjointVertices (minimalVertices H T) (minimalVertices E T) = true := by
  obtain ⟨p,hp | hp⟩ := hasCherry_address hc
  · exact target_mutual_clear hn hp H K E ha hna hnb hHK hE
  · exact target_mutual_clear_right hn hp H K E ha hna hnb hHK hE

/-- Derive global ORIGINAL source clearance through the actual retained source
restriction. Only literal original K/H disjointness is supplied; no desired
E/H clearance or exchange property is an input. -/
theorem retained_source_extension_clear {S U : Tree} (hn : (leaves S).Nodup)
    (C : List Nat) (hU : restrict C S = some U) {a b : Nat}
    (hc : HasCherry a b U) (H K : List Nat) (hHC : H ⊆ C) (hKC : K ⊆ C)
    (hbC : b ∈ C) (haK : a ∈ K) (haH : a ∉ H) (hbH : b ∉ H)
    (hHK : disjointVertices (minimalVertices H S) (minimalVertices K S) = true) :
    disjointVertices (minimalVertices H S) (minimalVertices (b :: K) S) = true := by
  have hE : (b :: K) ⊆ C := by intro x hx; rcases List.mem_cons.1 hx with rfl | hx; exact hbC; exact hKC hx
  have hUn := RestrictionBridge.restricted_nodup S U C hU hn
  have hlocal := (RestrictionBridge.disjoint_transport S U C H K hU hHC hKC).1 hHK
  have hnew := extension_clear_unordered hUn hc H K (b :: K) haK haH hbH hlocal
    (by intro x hx; simpa [List.mem_cons,or_comm] using hx)
  exact (RestrictionBridge.disjoint_transport S U C H (b :: K) hU hHC hE).2 hnew
end Universal233.Rule4

namespace Universal233.Rule4
open RMAF VertexGeometry CoreGraph Integration HardParent BinaryExchange CutRealization

theorem retained_cherry_graft_agrees {T S U : Tree}
    (hnT : (leaves T).Nodup) (hnS : (leaves S).Nodup) {a b : Nat}
    (hcT : HasCherry a b T) (C : List Nat) (hU : restrict C S = some U)
    (hcU : HasCherry a b U) (K : List Nat) (hKC : K ⊆ C) (hbC : b ∈ C)
    (haK : a ∈ K) (hbK : b ∉ K) (hK : restrictionAgrees T S K = true) :
    restrictionAgrees T S (b :: K) = true := by
  have hUn := RestrictionBridge.restricted_nodup S U C hU hnS
  have hKU : restrict K U = restrict K S :=
    RestrictionBridge.restrict_inside S U C K hU hKC
  have hK' : restrictionAgrees T U K = true := by
    simpa only [restrictionAgrees,hKU] using hK
  have he := common_cherry_graft_agrees hcT hcU hnT hUn K haK hbK hK'
  have hEC : (b :: K) ⊆ C := by
    intro x hx; rcases List.mem_cons.1 hx with rfl | hx; exact hbC; exact hKC hx
  have hEU : restrict (b :: K) U = restrict (b :: K) S :=
    RestrictionBridge.restrict_inside S U C (b :: K) hU hEC
  simpa only [restrictionAgrees,hEU] using he
end Universal233.Rule4
