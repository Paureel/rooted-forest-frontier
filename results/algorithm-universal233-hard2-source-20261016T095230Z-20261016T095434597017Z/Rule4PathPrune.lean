import Rule4OriginalExchange

/-! Cutting all actual outgoing path arcs makes the retained pair an actual
cherry after restriction, including arbitrary original context above its LCA. -/
namespace Universal233.Rule4
open RMAF VertexGeometry CoreGraph Integration HardParent CutRealization

def RootPathExcluded (S : Tree) (a : Nat) (L : List Nat) : Prop :=
  ∀ q, Valid S q → q ≠ [] → q.dropLast ∈ rootedSpan [a] S →
    q ∉ rootedSpan [a] S → ∀ x, x ∈ subtreeLabels S q → x ∉ L

def PairPathExcluded (S : Tree) (a b : Nat) (L : List Nat) : Prop :=
  ∀ q, Valid S q → q ≠ [] → q.dropLast ∈ minimalVertices [a,b] S →
    q ∉ minimalVertices [a,b] S → ∀ x, x ∈ subtreeLabels S q → x ∉ L

theorem cons_dropLast (s : Bool) (q : RMAF.Vertex) (hq : q ≠ []) :
    (s :: q).dropLast = s :: q.dropLast := by
  cases q with
  | nil => contradiction
  | cons t q => rfl

theorem prune_root_path {S : Tree} (hn : (leaves S).Nodup) (a : Nat)
    (ha : a ∈ leaves S) (L : List Nat) (haL : a ∈ L)
    (he : RootPathExcluded S a L) : restrict L S = some (.leaf a) := by
  induction S with
  | leaf x =>
    have hx : a = x := by simpa [leaves] using ha
    subst x
    simp [restrict,haL]
  | node l r ihl ihr =>
    obtain ⟨hnl,hnr,hdis⟩ := List.nodup_append.1 hn
    rcases List.mem_append.1 ha with hal | har
    · have har : a ∉ leaves r := fun hh => hdis a hal a hh rfl
      have hrspan : rootedSpan [a] r = [] := rootspan_empty (by intro x hx; simpa using (show x ≠ a from fun h => har (h ▸ hx)))
      have hlne : (rootedSpan [a] l).isEmpty = false := rootspan_nonempty hal (by simp)
      have hroot : [] ∈ rootedSpan [a] (.node l r) := by simp [rootedSpan,hlne]
      have hout : [true] ∉ rootedSpan [a] (.node l r) := by
        intro hh
        have h := (rootedSpan_child [a] l r true []).1 hh
        simp [hrspan] at h
      have hrnone : restrict L r = none := (BinaryExchange.restrict_none_iff L r).2
        (by intro x hx; exact he [true] (valid_root r) (by decide) hroot hout x hx)
      have hex : RootPathExcluded l a L := by
        intro q hq hne hp ho x hx
        have hp' : (false :: q).dropLast ∈ rootedSpan [a] (.node l r) := by
          rw [cons_dropLast false q hne]
          exact (rootedSpan_child [a] l r false _).2 hp
        have ho' : false :: q ∉ rootedSpan [a] (.node l r) :=
          fun hh => ho ((rootedSpan_child [a] l r false q).1 hh)
        exact he (false :: q) hq (by simp) hp' ho' x hx
      have hl := ihl hnl hal hex
      simp [restrict,hl,hrnone]
    · have hal : a ∉ leaves l := fun hh => hdis a hh a har rfl
      have hlspan : rootedSpan [a] l = [] := rootspan_empty (by intro x hx; simpa using (show x ≠ a from fun h => hal (h ▸ hx)))
      have hrne : (rootedSpan [a] r).isEmpty = false := rootspan_nonempty har (by simp)
      have hroot : [] ∈ rootedSpan [a] (.node l r) := by simp [rootedSpan,hlspan,hrne]
      have hout : [false] ∉ rootedSpan [a] (.node l r) := by
        intro hh
        have h := (rootedSpan_child [a] l r false []).1 hh
        simp [hlspan] at h
      have hlnone : restrict L l = none := (BinaryExchange.restrict_none_iff L l).2
        (by intro x hx; exact he [false] (valid_root l) (by decide) hroot hout x hx)
      have hex : RootPathExcluded r a L := by
        intro q hq hne hp ho x hx
        have hp' : (true :: q).dropLast ∈ rootedSpan [a] (.node l r) := by
          rw [cons_dropLast true q hne]
          exact (rootedSpan_child [a] l r true _).2 hp
        have ho' : true :: q ∉ rootedSpan [a] (.node l r) :=
          fun hh => ho ((rootedSpan_child [a] l r true q).1 hh)
        exact he (true :: q) hq (by simp) hp' ho' x hx
      have hr := ihr hnr har hex
      simp [restrict,hlnone,hr]

theorem prune_pair_path {S : Tree} (hn : (leaves S).Nodup) (a b : Nat)
    (ha : a ∈ leaves S) (hb : b ∈ leaves S) (hab : a ≠ b)
    (L : List Nat) (haL : a ∈ L) (hbL : b ∈ L)
    (he : PairPathExcluded S a b L) :
    ∃ U, restrict L S = some U ∧ HasCherry a b U := by
  induction S with
  | leaf x => simp [leaves] at ha hb; exact False.elim (hab (ha.trans hb.symm))
  | node l r ihl ihr =>
    obtain ⟨hnl,hnr,hdis⟩ := List.nodup_append.1 hn
    have liftLeft (hm : ∀ v, false :: v ∈ minimalVertices [a,b] (.node l r) ↔ v ∈ minimalVertices [a,b] l) :
        PairPathExcluded l a b L := by
      intro q hq hne hp ho x hx
      apply he (false :: q) hq (by simp)
      · rw [cons_dropLast false q hne]; exact (hm _).2 hp
      · exact fun hh => ho ((hm _).1 hh)
      · exact hx
    have liftRight (hm : ∀ v, true :: v ∈ minimalVertices [a,b] (.node l r) ↔ v ∈ minimalVertices [a,b] r) :
        PairPathExcluded r a b L := by
      intro q hq hne hp ho x hx
      apply he (true :: q) hq (by simp)
      · rw [cons_dropLast true q hne]; exact (hm _).2 hp
      · exact fun hh => ho ((hm _).1 hh)
      · exact hx
    have split (hal : a ∈ leaves l) (hbr : b ∈ leaves r)
        (har : a ∉ leaves r) (hbl : b ∉ leaves l) :
        ∃ U, restrict L (.node l r) = some U ∧ HasCherry a b U := by
      have hlne : (rootedSpan [a,b] l).isEmpty = false := rootspan_nonempty hal (by simp)
      have hrne : (rootedSpan [a,b] r).isEmpty = false := rootspan_nonempty hbr (by simp)
      have hmaskl : rootedSpan [a,b] l = rootedSpan [a] l :=
        rootedSpan_ext [a,b] [a] l (by intro x hx; simp; exact fun hh => False.elim (hbl (hh ▸ hx)))
      have hmaskr : rootedSpan [a,b] r = rootedSpan [b] r :=
        rootedSpan_ext [a,b] [b] r (by intro x hx; simp; exact fun hh => False.elim (har (hh ▸ hx)))
      have hml : ∀ v, false :: v ∈ minimalVertices [a,b] (.node l r) ↔ v ∈ rootedSpan [a] l := by
        intro v
        simp only [minimalVertices,hlne,hrne,Bool.false_eq_true,↓reduceIte]
        simp [prependSide,hmaskl]
      have hmr : ∀ v, true :: v ∈ minimalVertices [a,b] (.node l r) ↔ v ∈ rootedSpan [b] r := by
        intro v
        simp only [minimalVertices,hlne,hrne,Bool.false_eq_true,↓reduceIte]
        simp [prependSide,hmaskr]
      have hleft : RootPathExcluded l a L := by
        intro q hq hne hp ho x hx
        apply he (false :: q) hq (by simp)
        · rw [cons_dropLast false q hne]; exact (hml _).2 hp
        · exact fun hh => ho ((hml _).1 hh)
        · exact hx
      have hright : RootPathExcluded r b L := by
        intro q hq hne hp ho x hx
        apply he (true :: q) hq (by simp)
        · rw [cons_dropLast true q hne]; exact (hmr _).2 hp
        · exact fun hh => ho ((hmr _).1 hh)
        · exact hx
      have hl := prune_root_path hnl a hal L haL hleft
      have hr := prune_root_path hnr b hbr L hbL hright
      exact ⟨.node (.leaf a) (.leaf b),by simp [restrict,hl,hr],.here⟩
    rcases List.mem_append.1 ha with hal | har
    · have harn : a ∉ leaves r := fun hh => hdis a hal a hh rfl
      rcases List.mem_append.1 hb with hbl | hbr
      · have hbrn : b ∉ leaves r := fun hh => hdis b hbl b hh rfl
        have hm := pairSpan_left hal hbl harn hbrn
        have hlift := liftLeft (by intro v; simp [hm,prependSide])
        obtain ⟨U,hU,hcU⟩ := ihl hnl hal hbl hlift
        cases hR : restrict L r with
        | none => exact ⟨U,by simp [restrict,hU,hR],hcU⟩
        | some V => exact ⟨.node U V,by simp [restrict,hU,hR],.left hcU⟩
      · exact split hal hbr harn (fun hh => hdis b hh b hbr rfl)
    · have haln : a ∉ leaves l := fun hh => hdis a hh a har rfl
      rcases List.mem_append.1 hb with hbl | hbr
      · -- Symmetric split: exchange endpoint names in the rooted-path argument.
        have hlne : (rootedSpan [a,b] l).isEmpty = false := rootspan_nonempty hbl (by simp)
        have hrne : (rootedSpan [a,b] r).isEmpty = false := rootspan_nonempty har (by simp)
        have hbrn : b ∉ leaves r := fun hh => hdis b hbl b hh rfl
        have hmaskl : rootedSpan [a,b] l = rootedSpan [b] l :=
          rootedSpan_ext [a,b] [b] l (by intro x hx; simp; exact fun hh => False.elim (haln (hh ▸ hx)))
        have hmaskr : rootedSpan [a,b] r = rootedSpan [a] r :=
          rootedSpan_ext [a,b] [a] r (by intro x hx; simp; exact fun hh => False.elim (hbrn (hh ▸ hx)))
        have hml : ∀ v, false :: v ∈ minimalVertices [a,b] (.node l r) ↔ v ∈ rootedSpan [b] l := by
          intro v
          simp only [minimalVertices,hlne,hrne,Bool.false_eq_true,↓reduceIte]
          simp [prependSide,hmaskl]
        have hmr : ∀ v, true :: v ∈ minimalVertices [a,b] (.node l r) ↔ v ∈ rootedSpan [a] r := by
          intro v
          simp only [minimalVertices,hlne,hrne,Bool.false_eq_true,↓reduceIte]
          simp [prependSide,hmaskr]
        have hleft : RootPathExcluded l b L := by
          intro q hq hne hp ho x hx
          apply he (false :: q) hq (by simp)
          · rw [cons_dropLast false q hne]; exact (hml _).2 hp
          · exact fun hh => ho ((hml _).1 hh)
          · exact hx
        have hright : RootPathExcluded r a L := by
          intro q hq hne hp ho x hx
          apply he (true :: q) hq (by simp)
          · rw [cons_dropLast true q hne]; exact (hmr _).2 hp
          · exact fun hh => ho ((hmr _).1 hh)
          · exact hx
        have hl := prune_root_path hnl b hbl L hbL hleft
        have hr := prune_root_path hnr a har L haL hright
        exact ⟨.node (.leaf b) (.leaf a),by simp [restrict,hl,hr],.swap⟩
      · have hbln : b ∉ leaves l := fun hh => hdis b hh b hbr rfl
        have hm := pairSpan_right har hbr haln hbln
        have hlift := liftRight (by intro v; simp [hm,prependSide])
        obtain ⟨V,hV,hcV⟩ := ihr hnr har hbr hlift
        cases hL : restrict L l with
        | none => exact ⟨V,by simp [restrict,hL,hV],hcV⟩
        | some U => exact ⟨.node U V,by simp [restrict,hL,hV],.right hcV⟩
end Universal233.Rule4

namespace Universal233.Rule4
open RMAF VertexGeometry CoreGraph Integration HardParent CutRealization

theorem literal_root_cherry {S : Tree} (hn : (leaves S).Nodup)
    {a b : Nat} (ha : a ∈ leaves S) (hb : b ∈ leaves S) (hab : a ≠ b)
    {q r : RMAF.Vertex} (hcuts : (pendantOriginal S a b).Perm [q,r]) :
    let C := (leaves S).filter (fun x => !(subtreeLabels S q).contains x && !(subtreeLabels S r).contains x)
    ∃ U, restrict C S = some U ∧ HasCherry a b U := by
  let C := (leaves S).filter (fun x => !(subtreeLabels S q).contains x && !(subtreeLabels S r).contains x)
  have hq : q ∈ pendantOriginal S a b := two_cut_mem_left hcuts
  have hr : r ∈ pendantOriginal S a b := two_cut_mem_right hcuts
  have hend := hard2_endpoints_in_root hq hr ha hb
  apply prune_pair_path hn a b ha hb hab C hend.1 hend.2
  intro v hv hne hp ho x hx
  have hmem : v ∈ pendantOriginal S a b := (pendantOriginal_spec S a b v).2 ⟨hv,hne,hp,ho⟩
  have he : v = q ∨ v = r := two_cut_cases hcuts hmem
  rcases he with rfl | rfl <;> simp [C,hx]
end Universal233.Rule4
