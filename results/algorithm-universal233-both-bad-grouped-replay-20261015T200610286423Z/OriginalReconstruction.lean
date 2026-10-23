import Indexing

namespace Universal233.MafScheduler
open RMAF PaidQueries RestrictionBridge

theorem recursive_sound (T S : Tree) (Q : Forest) (t s : List Nat → Tree)
    (m : List Nat → Nat) (solve : Tree → Tree → Nat → Option Forest)
    (ht : ∀ U∈Q, restrict U T=some (t U)) (hs : ∀ U∈Q, restrict U S=some (s U))
    (hsolve : ∀ U∈Q, ∀ b F, solve (t U) (s U) b=some F →
      agreement (t U) (s U) F=true ∧ F.length-1=m U) :
    ∀ U∈Q, ∀ b c F, recursive T S solve U b=some (c,F) →
      c=m U ∧ LocalValid t s m U F := by
  intro U hU b c F he
  simp only [recursive,ht U hU,hs U hU] at he
  cases hr : solve (t U) (s U) b with
  | none => simp [hr] at he
  | some G =>
    have hh : G.length-1=c ∧ G=F := by simpa [hr] using he
    rcases hh with ⟨hgc,hgf⟩
    subst G
    have hv := hsolve U hU b F hr
    exact ⟨by omega,hv⟩

theorem recursive_complete (T S : Tree) (Q : Forest) (t s : List Nat → Tree)
    (m : List Nat → Nat) (solve : Tree → Tree → Nat → Option Forest)
    (ht : ∀ U∈Q, restrict U T=some (t U)) (hs : ∀ U∈Q, restrict U S=some (s U))
    (hsolve : ∀ U∈Q, ∀ b, m U≤b → ∃ F, solve (t U) (s U) b=some F) :
    ∀ U∈Q, ∀ b, m U≤b → ∃ x, recursive T S solve U b=some x := by
  intro U hU b hb
  obtain ⟨F,hF⟩ := hsolve U hU b hb
  exact ⟨(F.length-1,F),by simp [recursive,ht U hU,hs U hU,hF]⟩

/-- Literal concatenation of the caller's returned list, with both original
    embedding premises retained. No target disjointness is inferred from a
    clearing request. The selector function f occurs only in this proof. -/
theorem answers_original_reconstruction (T S : Tree) (Q : Forest)
    (pt : (leaves T).Nodup) (ps : (leaves S).Nodup)
    (hQT : partitionCheck (leaves T) Q=true) (hQS : partitionCheck (leaves S) Q=true)
    (eT : pairwiseEmbeddings T Q=true) (eS : pairwiseEmbeddings S Q=true)
    (t s : List Nat → Tree) (m : List Nat → Nat)
    (ht : ∀ U∈Q, restrict U T=some (t U)) (hs : ∀ U∈Q, restrict U S=some (s U))
    (js : List (Job (List Nat) Forest)) (xs : List (Nat × Forest))
    (hkeys : js.map Job.problem=Q) (ha : AnswersFor m (LocalValid t s m) js xs) :
    agreement T S (xs.flatMap Prod.snd)=true ∧
      (xs.flatMap Prod.snd).length-Q.length=answerCost xs ∧
      Refines (xs.flatMap Prod.snd) Q := by
  have hnd : (js.map Job.problem).Nodup := hkeys ▸ checked_family_nodup (leaves T) Q hQT
  obtain ⟨f,hf,hvalid⟩ := answers_indexed m (LocalValid t s m) js xs ha hnd
  have hu : ∀ U∈Q, (f U).1=m U ∧ LocalValid t s m U (f U).2 := by
    intro U hU
    rw [←hkeys] at hU
    obtain ⟨j,hj,rfl⟩ := List.mem_map.1 hU
    exact hvalid j hj
  have hxs : Q.map f=xs := by simpa only [hkeys] using hf
  let G : List Nat → Forest := fun U => (f U).2
  have hg : ∀ U∈Q, agreement (t U) (s U) (G U)=true := fun U hU => (hu U hU).2.1
  have hc : ∀ U∈Q, (f U).1=(f U).2.length-1 := by
    intro U hU
    have hh := hu U hU
    exact hh.1.trans hh.2.2.symm
  obtain ⟨hglobal,hcost,_,_⟩ := reverse_reconstruction T S Q G t s pt ps hQT hQS eT eS ht hs hg
  have hflat : xs.flatMap Prod.snd=Q.flatMap G := by rw [←hxs]; simp [List.flatMap_map,G]
  have hsum := indexed_cost_flatten Q f hc
  rw [hxs] at hsum
  have href : Refines (Q.flatMap G) Q := by
    intro B hB
    obtain ⟨U,hU,hB⟩ := List.mem_flatMap.1 hB
    have hl := hg U hU
    simp only [agreement,Bool.and_eq_true] at hl
    have hp := local_checked_labels T (t U) U Q (G U) pt hQT hU (ht U hU) hl.1.1.1.1
    exact ⟨U,hU,fun x hx => checked_label U (G U) hp hB hx⟩
  rw [hflat]
  exact ⟨hglobal,hcost.symm.trans hsum.symm,href⟩
end Universal233.MafScheduler
