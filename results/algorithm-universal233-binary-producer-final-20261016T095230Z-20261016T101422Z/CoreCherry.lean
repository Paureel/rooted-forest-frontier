import SourceBranches
namespace Universal233.CherryBranching
open RMAF CoreGraph Integration VertexGeometry CutRealization HardParent

theorem first_exit (H : RMAF.Vertex → Prop) (v : RMAF.Vertex)
 (hroot : H []) (hout : ¬H v) :
 ∃ q, q ≠ [] ∧ q <+: v ∧ H q.dropLast ∧ ¬H q := by
 classical
 rcases List.eq_nil_or_concat v with hv | ⟨p,s,he⟩
 · subst v; exact False.elim (hout hroot)
 · have hvs : v = p ++ [s] := by simpa only [List.concat_eq_append] using he
   by_cases hp : H p
   · exact ⟨v,by rw [hvs]; simp,List.prefix_rfl,by simpa [hvs],hout⟩
   · obtain ⟨q,hne,hpre,hparent,hq⟩ := first_exit H p hroot hp
     exact ⟨q,hne,hpre.trans (by rw [hvs]; exact List.prefix_append _ _),hparent,hq⟩
termination_by v.length
 decreasing_by simp [hvs]

theorem excluded_root_only {S : Tree} {D : List Nat} {a b : Nat}
 (he : PendantExcluded D a b S) (hr : [] ∈ minimalVertices [a,b] S) :
 ∀ x, x ∈ leaves S → x ∈ D → x = a ∨ x = b := by
 intro x hx hD
 by_cases h : x = a ∨ x = b
 · exact h
 · obtain ⟨v,hv⟩ := leaf_exists hx
   have hout : v ∉ minimalVertices [a,b] S := by
     rw [minimalVertices_terminal _ S v x hv]
     simpa using h
   obtain ⟨q,hq,hpre,hparent,ho⟩ := first_exit (fun v => v ∈ minimalVertices [a,b] S) v hr hout
   exact False.elim (he q hq hparent ho x ((subtreeLabels_prefix S q x).2 ⟨v,hv,hpre⟩) hD)

theorem tree_only_leaf (U : Tree) (hn : (leaves U).Nodup) (a : Nat)
 (only : ∀ x, x ∈ leaves U → x = a) : U = .leaf a := by
 cases U with
 | leaf x => have he := only x (by simp [leaves]); subst x; rfl
 | node l r =>
   obtain ⟨x,hx⟩ := List.exists_mem_of_ne_nil _ (CutRealization.leaves_nonempty l)
   obtain ⟨y,hy⟩ := List.exists_mem_of_ne_nil _ (CutRealization.leaves_nonempty r)
   have ex := only x (by simp [leaves,hx])
   have ey := only y (by simp [leaves,hy])
   obtain ⟨_,_,hd⟩ := List.nodup_append.1 hn
   exact False.elim (hd x hx y hy (ex.trans ey.symm))

theorem restrict_only_leaf {S : Tree} {D : List Nat} {a : Nat}
 (hn : (leaves S).Nodup) (ha : a ∈ leaves S) (hD : a ∈ D)
 (only : ∀ x, x ∈ leaves S → x ∈ D → x = a) : restrict D S = some (.leaf a) := by
 obtain ⟨U,hU⟩ := materialization_exists ha hD
 have hu : U = .leaf a := tree_only_leaf U (by rw [restrict_leaves hU]; exact hn.filter _) a (by
   intro x hx
   obtain ⟨hxs,hxD⟩ := (restrict_mem hU x).1 hx
   exact only x hxs hxD)
 simpa [hu] using hU

theorem excluded_descend_left {D : List Nat} {a b : Nat} {l r : Tree}
 (hal : a ∈ leaves l) (hbl : b ∈ leaves l)
 (har : a ∉ leaves r) (hbr : b ∉ leaves r)
 (he : PendantExcluded D a b (.node l r)) : PendantExcluded D a b l := by
 have hm := pairSpan_left hal hbl har hbr
 intro q hq hp ho x hx hD
 have hne : false :: q ≠ [] := by simp
 have hparent : (false :: q).dropLast ∈ minimalVertices [a,b] (.node l r) := by
   cases q with
   | nil => contradiction
   | cons t tail => simpa [hm,prependSide] using hp
 have hoff : false :: q ∉ minimalVertices [a,b] (.node l r) := by simpa [hm,prependSide] using ho
 exact he (false::q) hne hparent hoff x hx hD

theorem excluded_descend_right {D : List Nat} {a b : Nat} {l r : Tree}
 (har : a ∈ leaves r) (hbr : b ∈ leaves r)
 (hal : a ∉ leaves l) (hbl : b ∉ leaves l)
 (he : PendantExcluded D a b (.node l r)) : PendantExcluded D a b r := by
 have hm := pairSpan_right har hbr hal hbl
 intro q hq hp ho x hx hD
 have hne : true :: q ≠ [] := by simp
 have hparent : (true :: q).dropLast ∈ minimalVertices [a,b] (.node l r) := by
   cases q with
   | nil => contradiction
   | cons t tail => simpa [hm,prependSide] using hp
 have hoff : true :: q ∉ minimalVertices [a,b] (.node l r) := by simpa [hm,prependSide] using ho
 exact he (true::q) hne hparent hoff x hx hD

/-- No selected original label below an outgoing path edge means that the
actual restricted source retains a,b as a rooted cherry, with arbitrary
original siblings above their LCA. -/
theorem restrict_cherry_of_excluded {S : Tree} {D : List Nat} {a b : Nat}
 (hn : (leaves S).Nodup) (ha : a ∈ leaves S) (hb : b ∈ leaves S)
 (hab : a ≠ b) (haD : a ∈ D) (hbD : b ∈ D)
 (he : PendantExcluded D a b S) : ∃ U, restrict D S = some U ∧ HasCherry a b U := by
 induction S with
 | leaf x => simp [leaves] at ha hb; exact False.elim (hab (ha.trans hb.symm))
 | node l r ihl ihr =>
   obtain ⟨hnl,hnr,hd⟩ := List.nodup_append.1 hn
   rcases List.mem_append.1 ha with hal | har
   · have har : a ∉ leaves r := fun hh => hd a hal a hh rfl
     rcases List.mem_append.1 hb with hbl | hbr
     · have hbr : b ∉ leaves r := fun hh => hd b hbl b hh rfl
       obtain ⟨U,hU,hch⟩ := ihl hnl hal hbl (excluded_descend_left hal hbl har hbr he)
       cases hR : restrict D r with
       | none => exact ⟨U,by simp [restrict,hU,hR],hch⟩
       | some V => exact ⟨.node U V,by simp [restrict,hU,hR],.left hch⟩
     · have hbl : b ∉ leaves l := fun hh => hd b hh b hbr rfl
       have hL := rootspan_nonempty hal (by simp : a ∈ [a,b])
       have hR := rootspan_nonempty hbr (by simp : b ∈ [a,b])
       have root : [] ∈ minimalVertices [a,b] (.node l r) := by simp [minimalVertices,hL,hR]
       have only := excluded_root_only he root
       have rl := restrict_only_leaf hnl hal haD (by
         intro x hx hxD
         rcases only x (by simp [leaves,hx]) hxD with e | e
         · exact e
         · exact False.elim (hbl (e ▸ hx)))
       have rr := restrict_only_leaf hnr hbr hbD (by
         intro x hx hxD
         rcases only x (by simp [leaves,hx]) hxD with e | e
         · exact False.elim (har (e ▸ hx))
         · exact e)
       exact ⟨_,by simp [restrict,rl,rr],.here⟩
   · have hal : a ∉ leaves l := fun hh => hd a hh a har rfl
     rcases List.mem_append.1 hb with hbl | hbr
     · have hbr : b ∉ leaves r := fun hh => hd b hbl b hh rfl
       have hL := rootspan_nonempty hbl (by simp : b ∈ [a,b])
       have hR := rootspan_nonempty har (by simp : a ∈ [a,b])
       have root : [] ∈ minimalVertices [a,b] (.node l r) := by simp [minimalVertices,hL,hR]
       have only := excluded_root_only he root
       have rl := restrict_only_leaf hnl hbl hbD (by
         intro x hx hxD
         rcases only x (by simp [leaves,hx]) hxD with e | e
         · exact False.elim (hal (e ▸ hx))
         · exact e)
       have rr := restrict_only_leaf hnr har haD (by
         intro x hx hxD
         rcases only x (by simp [leaves,hx]) hxD with e | e
         · exact e
         · exact False.elim (hbr (e ▸ hx)))
       exact ⟨_,by simp [restrict,rl,rr],.swap⟩
     · obtain ⟨U,hU,hch⟩ := ihr hnr har hbr (excluded_descend_right har hbr hal (fun hh => hd b hh b hbr rfl) he)
       cases hL : restrict D l with
       | none => exact ⟨U,by simp [restrict,hL,hU],hch⟩
       | some V => exact ⟨.node V U,by simp [restrict,hL,hU],.right hch⟩

theorem core_excluded (S : Tree) (a b : Nat) : PendantExcluded (coreLabels S a b) a b S := by
 intro q hq hp ho x hx hcore
 have hl := (mem_core S a b x).1 hcore
 have hvalid : Valid S q := by
   obtain ⟨v,hv,hpre⟩ := (subtreeLabels_prefix S q x).1 hx
   exact valid_ancestor hv.valid hpre
 have hm : q ∈ cuts S a b := (cuts_spec S a b q).2 ⟨hvalid,hq,hp,ho⟩
 exact hl.2 q hm hx

theorem core_has_cherry {S : Tree} {a b : Nat} (hn : (leaves S).Nodup)
 (ha : a ∈ leaves S) (hb : b ∈ leaves S) (hab : a ≠ b) :
 ∃ U, restrict (coreLabels S a b) S = some U ∧ HasCherry a b U :=
 restrict_cherry_of_excluded hn ha hb hab (endpoint_core (Or.inl rfl) ha)
   (endpoint_core (Or.inr rfl) hb) (core_excluded S a b)
end Universal233.CherryBranching
