import EraseLift

/-! One-shot executable state invariant: every grouped origin is an unrepeated
original source vertex address. This does not yet realize recorded cuts. -/
namespace Universal233.Integration
open RMAF CoreGraph CoreProgram List

theorem fromTree_origin_suffix (color : Nat → Nat) (p : RMAF.Vertex) (t : Tree)
    (v : RMAF.Vertex) (hv : v ∈ origins (fromTree color p t)) :
    ∃ q, v = p ++ q := by
  induction t generalizing p with
  | leaf x =>
    have he : v = p := by simpa [fromTree,origins] using hv
    exact ⟨[],by simpa using he⟩
  | node l r ihl ihr =>
    simp only [fromTree,origins,List.mem_cons,List.mem_append] at hv
    rcases hv with he | hv | hv
    · exact ⟨[],by simpa using he⟩
    · obtain ⟨q,hq⟩ := ihl (p ++ [false]) hv
      exact ⟨false :: q,by simpa [List.append_assoc] using hq⟩
    · obtain ⟨q,hq⟩ := ihr (p ++ [true]) hv
      exact ⟨true :: q,by simpa [List.append_assoc] using hq⟩

theorem fromTree_origins_nodup (color : Nat → Nat) (p : RMAF.Vertex) (t : Tree) :
    (origins (fromTree color p t)).Nodup := by
  induction t generalizing p with
  | leaf x => simp [fromTree,origins]
  | node l r ihl ihr =>
    apply List.nodup_cons.2
    constructor
    · intro hp
      simp only [List.mem_append] at hp
      rcases hp with hp | hp
      · obtain ⟨q,hq⟩ := fromTree_origin_suffix color (p ++ [false]) l p hp
        have he := congrArg List.length hq
        simp only [List.length_append,List.length_singleton] at he
        omega
      · obtain ⟨q,hq⟩ := fromTree_origin_suffix color (p ++ [true]) r p hp
        have he := congrArg List.length hq
        simp only [List.length_append,List.length_singleton] at he
        omega
    · apply List.nodup_append.2
      refine ⟨ihl _,ihr _,?_⟩
      intro a ha b hb he
      obtain ⟨qa,hqa⟩ := fromTree_origin_suffix color (p ++ [false]) l a ha
      obtain ⟨qb,hqb⟩ := fromTree_origin_suffix color (p ++ [true]) r b hb
      have hc : p ++ (false :: qa) = p ++ (true :: qb) := by
        simpa [List.append_assoc] using hqa.symm.trans (he.trans hqb)
      have hh := List.append_cancel_left hc
      cases hh

theorem normalize_origins_sublist (t : GTree) : origins (normalize t) <+ origins t := by
  induction t with
  | leaf g => exact .refl _
  | node p l r ihl ihr =>
    have hs : origins (.node p (normalize l) (normalize r)) <+ origins (.node p l r) :=
      (ihl.append ihr).cons_cons p
    cases hl : normalize l with
    | leaf a =>
      cases hr : normalize r with
      | leaf b =>
        simp only [normalize,hl,hr]
        split
        next hc => exact ((List.nil_sublist _).cons_cons p).trans hs
        next hc => simpa only [hl,hr] using hs
      | node q a b => simp only [normalize,hl,hr]; simpa only [hl,hr] using hs
    | node q a b => cases hr : normalize r <;> simp only [normalize,hl,hr] <;> simpa only [hl,hr] using hs

theorem normalize_origins_nodup (t : GTree) (h : (origins t).Nodup) :
    (origins (normalize t)).Nodup := (normalize_origins_sublist t).nodup h

theorem erase_origins_sublist (t : GTree) (chosen : RMAF.Vertex) (u : GTree)
    (hu : erase chosen t = some u) : origins u <+ origins t := by
  induction t generalizing u with
  | leaf g =>
    simp only [erase] at hu
    split at hu
    next => contradiction
    next => have he := Option.some.inj hu; subst u; exact .refl _
  | node p l r ihl ihr =>
    simp only [erase] at hu
    split at hu
    next => contradiction
    next =>
      cases el : erase chosen l with
      | none =>
        cases er : erase chosen r with
        | none => simp [el,er] at hu
        | some b =>
          simp only [el,er] at hu
          have he := Option.some.inj hu
          subst u
          exact ((ihr b er).trans (List.sublist_append_right _ _)).cons p
      | some a =>
        cases er : erase chosen r with
        | none =>
          simp only [el,er] at hu
          have he := Option.some.inj hu
          subst u
          exact ((ihl a el).trans (List.sublist_append_left _ _)).cons p
        | some b =>
          simp only [el,er] at hu
          have he := Option.some.inj hu
          subst u
          exact ((ihl a el).append (ihr b er)).cons_cons p

theorem erase_origins_nodup (t : GTree) (chosen : RMAF.Vertex) (u : GTree)
    (hu : erase chosen t = some u) (hn : (origins t).Nodup) : (origins u).Nodup :=
  (erase_origins_sublist t chosen u hu).nodup hn

/-- Original addresses are retained as actual vertices through both operations;
no claim about nonredundant original cut components is made here. -/
theorem reachable_origins_actual (color : Nat → Nat) (T : Tree) (current : GTree)
    (hs : origins current <+ origins (fromTree color [] T)) :
    ∀ v, v ∈ origins current → Valid T v := by
  intro v hv
  have hm := hs.subset hv
  have he : ∀ (p : RMAF.Vertex) (t : Tree) (a : RMAF.Vertex),
      a ∈ origins (fromTree color p t) → ∃ q, a = p ++ q ∧ Valid t q := by
    intro p t
    induction t generalizing p with
    | leaf x =>
      intro a ha
      have hpa : a = p := by simpa [fromTree,origins] using ha
      exact ⟨[],by simpa using hpa,valid_root _⟩
    | node l r ihl ihr =>
      intro a ha
      simp only [fromTree,origins,List.mem_cons,List.mem_append] at ha
      rcases ha with hp | ha | ha
      · exact ⟨[],by simpa using hp,valid_root _⟩
      · obtain ⟨q,hq,hv⟩ := ihl (p ++ [false]) a ha
        exact ⟨false :: q,by simpa [List.append_assoc] using hq,hv⟩
      · obtain ⟨q,hq,hv⟩ := ihr (p ++ [true]) a ha
        exact ⟨true :: q,by simpa [List.append_assoc] using hq,hv⟩
  obtain ⟨q,hq,hv⟩ := he [] T v hm
  simpa using hq ▸ hv

end Universal233.Integration
