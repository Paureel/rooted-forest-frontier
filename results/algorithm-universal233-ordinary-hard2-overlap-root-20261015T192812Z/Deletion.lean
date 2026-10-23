import Clip
namespace OrdinaryCommonSplit
open RMAF RestrictionBridge

theorem relabelForest_twice (f : Nat → Nat) (inv : ∀ x, f (f x)=x)
    (F : List (List Nat)) : relabelForest f (relabelForest f F)=F := by
  simp [relabelForest,List.map_map,Function.comp_def,inv]

theorem relabelForest_length (f : Nat → Nat) (F : List (List Nat)) :
    (relabelForest f F).length=F.length := by simp [relabelForest]

/-- Delete the actual fresh marker from an arbitrary agreement of the literal
marked pair. This is a forest-producing lower bound, not an assumed minimum
relation or just a projection of computed values. -/
theorem marked_deletion_spec (T S t s mt ms : Tree) (X : List Nat) (y rho : Nat)
    (ht : restrict X T=some t) (hs : restrict X S=some s)
    (hmt : marked T X y rho=some mt) (hms : marked S X y rho=some ms)
    (F : List (List Nat)) (ha : agreement mt ms F=true) :
    agreement t s (clip X (relabelForest (swap y rho) F))=true ∧
      (clip X (relabelForest (swap y rho) F)).length≤F.length := by
  cases hvT : restrict (y::X) T with
  | none => simp [marked,hvT] at hmt
  | some vT =>
    cases hvS : restrict (y::X) S with
    | none => simp [marked,hvS] at hms
    | some vS =>
      simp only [marked,hvT,Option.map_some,Option.some.injEq] at hmt
      simp only [marked,hvS,Option.map_some,Option.some.injEq] at hms
      subst mt;subst ms
      have hback := agreement_relabel_swap y rho
        (relabel (swap y rho) vT) (relabel (swap y rho) vS) F
      rw [relabel_twice _ (swap_involution y rho),
        relabel_twice _ (swap_involution y rho)] at hback
      have hag : agreement vT vS (relabelForest (swap y rho) F)=true := hback.trans ha
      have hvt : restrict X vT=some t :=
        (restrict_inside T vT (y::X) X hvT (by intro x hx;exact List.mem_cons_of_mem y hx)).trans ht
      have hvs : restrict X vS=some s :=
        (restrict_inside S vS (y::X) X hvS (by intro x hx;exact List.mem_cons_of_mem y hx)).trans hs
      have hclip := agreement_clip vT vS t s X (relabelForest (swap y rho) F) hvt hvs hag
      exact ⟨hclip.1,
        by simpa only [relabelForest_length] using hclip.2⟩

theorem marked_deletion (T S t s mt ms : Tree) (X : List Nat) (y rho : Nat)
    (ht : restrict X T=some t) (hs : restrict X S=some s)
    (hmt : marked T X y rho=some mt) (hms : marked S X y rho=some ms)
    (F : List (List Nat)) (ha : agreement mt ms F=true) :
    ∃ G, agreement t s G=true ∧ G.length≤F.length :=
  ⟨clip X (relabelForest (swap y rho) F),
    marked_deletion_spec T S t s mt ms X y rho ht hs hmt hms F ha⟩

theorem marked_singleton_deletion (T S t s mt ms : Tree) (X : List Nat) (y rho : Nat)
    (ht : restrict X T=some t) (hs : restrict X S=some s)
    (hmt : marked T X y rho=some mt) (hms : marked S X y rho=some ms)
    (F : List (List Nat)) (ha : agreement mt ms F=true) (hn : y∉X) (hm : [rho]∈F) :
    ∃ G, agreement t s G=true ∧ G.length<F.length := by
  have hswy : swap y rho rho=y := by by_cases h : rho=y <;> simp [swap,h]
  have hy : [y]∈relabelForest (swap y rho) F :=
    List.mem_map.2 ⟨[rho],hm,by simp [hswy]⟩
  have hl : (clip X (relabelForest (swap y rho) F)).length<
      (relabelForest (swap y rho) F).length :=
    List.length_filterMap_lt_length_iff_exists.2 ⟨[y],hy,by simp [clipBlock,hn]⟩
  exact ⟨clip X (relabelForest (swap y rho) F),
    (marked_deletion_spec T S t s mt ms X y rho ht hs hmt hms F ha).1,
    by simpa only [relabelForest_length] using hl⟩
end OrdinaryCommonSplit
