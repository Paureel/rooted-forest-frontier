import MarkerSingleton
namespace OrdinaryCommonSplit
open RMAF RestrictionBridge

theorem restricted_perm (t u : Tree) (X : List Nat) (hr : restrict X t=some u)
    (nd : (leaves t).Nodup) (nx : X.Nodup) (sub : X⊆leaves t) :
    (leaves u).Perm X := by
  apply (List.perm_ext_iff_of_nodup (restricted_nodup t u X hr nd) nx).2
  intro x
  rw [restricted_labels_exact t u X hr]
  exact ⟨And.right,fun hx => ⟨sub hx,hx⟩⟩

/-- Actual ordinary marked input extension. The constructed result contains
the renamed local forest plus a fresh singleton marker; it has exactly one
extra block, independently of whether a cheaper attachment is possible. -/
theorem marked_extension (T S t s mt ms : Tree) (X : List Nat) (y rho : Nat)
    (nt : (leaves T).Nodup) (ns : (leaves S).Nodup) (nx : X.Nodup)
    (subT : X⊆leaves T) (subS : X⊆leaves S)
    (hyT : y∈leaves T) (hyS : y∈leaves S) (hn : y∉X)
    (ht : restrict X T=some t) (hs : restrict X S=some s)
    (hmt : marked T X y rho=some mt) (hms : marked S X y rho=some ms)
    (F : List (List Nat)) (ha : agreement t s F=true) :
    ∃ G, agreement mt ms G=true ∧ G.length=F.length+1 := by
  cases hvT : restrict (y::X) T with
  | none => simp [marked,hvT] at hmt
  | some vT =>
    cases hvS : restrict (y::X) S with
    | none => simp [marked,hvS] at hms
    | some vS =>
      simp only [marked,hvT,Option.map_some,Option.some.injEq] at hmt
      simp only [marked,hvS,Option.map_some,Option.some.injEq] at hms
      subst mt;subst ms
      have nyX : (y::X).Nodup := List.nodup_cons.2 ⟨hn,nx⟩
      have subYT : y::X⊆leaves T := by
        intro x hx
        rcases List.mem_cons.1 hx with rfl | hx
        · exact hyT
        · exact subT hx
      have subYS : y::X⊆leaves S := by
        intro x hx
        rcases List.mem_cons.1 hx with rfl | hx
        · exact hyS
        · exact subS hx
      have hvt : restrict X vT=some t :=
        (restrict_inside T vT (y::X) X hvT (by intro x hx;exact List.mem_cons_of_mem y hx)).trans ht
      have hvs : restrict X vS=some s :=
        (restrict_inside S vS (y::X) X hvS (by intro x hx;exact List.mem_cons_of_mem y hx)).trans hs
      have hext := singleton_extension vT vS t s X y
        (restricted_nodup T vT _ hvT nt) (restricted_nodup S vS _ hvS ns) hn
        (restricted_perm T vT _ hvT nt nyX subYT) (restricted_perm S vS _ hvS ns nyX subYS)
        (restricted_perm T t X ht nt nx subT) (restricted_perm S s X hs ns nx subS)
        hvt hvs F ha
      refine ⟨relabelForest (swap y rho) ([y]::F),?_,?_⟩
      · rw [agreement_relabel_swap]
        exact hext
      · simp [relabelForest]

/-- A stated minimum means an actual original agreement witness and a bound
against every actual agreement; no executable oracle is supplied by this
definition. -/
def IsMinimum (T S : Tree) (m : Nat) : Prop :=
  (∃ F, agreement T S F=true ∧ F.length-1=m) ∧
  ∀ F, agreement T S F=true → m≤F.length-1

theorem marked_minimum_bounds (T S t s mt ms : Tree) (X : List Nat) (y rho m mr : Nat)
    (nt : (leaves T).Nodup) (ns : (leaves S).Nodup) (nx : X.Nodup)
    (subT : X⊆leaves T) (subS : X⊆leaves S)
    (hyT : y∈leaves T) (hyS : y∈leaves S) (hn : y∉X)
    (ht : restrict X T=some t) (hs : restrict X S=some s)
    (hmt : marked T X y rho=some mt) (hms : marked S X y rho=some ms)
    (hm : IsMinimum t s m) (hr : IsMinimum mt ms mr) : m≤mr ∧ mr≤m+1 := by
  obtain ⟨F,hF,hFc⟩ := hr.1
  obtain ⟨G,hG,hGc⟩ := marked_deletion T S t s mt ms X y rho ht hs hmt hms F hF
  have low := hm.2 G hG
  obtain ⟨H,hH,hHc⟩ := hm.1
  obtain ⟨K,hK,hKc⟩ := marked_extension T S t s mt ms X y rho nt ns nx subT subS
    hyT hyS hn ht hs hmt hms H hH
  have high := hr.2 K hK
  have hHne := Universal233.DepthOne.agreement_nonempty t s H hH
  have hHpos : 0<H.length := List.length_pos_iff.2 hHne
  omega
end OrdinaryCommonSplit
