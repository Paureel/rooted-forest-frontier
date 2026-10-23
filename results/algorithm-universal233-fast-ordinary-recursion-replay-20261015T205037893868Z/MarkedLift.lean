import ForestMerge
namespace OrdinaryCommonSplit
open RMAF RestrictionBridge

/-- Lift the entire actual marked agreement family to full original addresses
after undoing the explicit marker swap. It is a partition of y::X, not of the
whole original label set; no whole original agreement is claimed here. -/
theorem marked_family_lift (T S mt ms : Tree) (X : List Nat) (y rho : Nat)
    (nt : (leaves T).Nodup) (ns : (leaves S).Nodup) (nx : X.Nodup)
    (subT : X⊆leaves T) (subS : X⊆leaves S)
    (hyT : y∈leaves T) (hyS : y∈leaves S) (hn : y∉X)
    (hmt : marked T X y rho=some mt) (hms : marked S X y rho=some ms)
    (F : List (List Nat)) (ha : agreement mt ms F=true) :
    let G := relabelForest (swap y rho) F
    partitionCheck (y::X) G=true ∧ pairwiseEmbeddings T G=true ∧
      pairwiseEmbeddings S G=true ∧ ∀B∈G,restrictionAgrees T S B=true := by
  dsimp only
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
      have hh := hag
      simp only [agreement,Bool.and_eq_true] at hh
      have subYT : y::X⊆leaves T := by
        intro x hx
        rcases List.mem_cons.1 hx with rfl | hx
        · exact hyT
        · exact subT hx
      have labelsT := restricted_perm T vT (y::X) hvT nt (List.nodup_cons.2 ⟨hn,nx⟩) subYT
      have hpart := (partition_labels_congr (leaves vT) (y::X)
        (relabelForest (swap y rho) F) (fun _ => labelsT.mem_iff)).1 hh.1.1.1.1
      have sub : ∀ B∈relabelForest (swap y rho) F, B⊆y::X := by
        intro B hB x hx
        exact checked_label _ _ hpart hB hx
      refine ⟨hpart,(pairwise_transport T vT _ _ hvT sub).2 hh.1.2,
        (pairwise_transport S vS _ _ hvS sub).2 hh.2,?_⟩
      intro B hB
      rw [←sameShape_restrict_inside T S vT vS _ B hvT hvS (sub B hB)]
      exact List.all_eq_true.1 hh.1.1.2 B hB
end OrdinaryCommonSplit
