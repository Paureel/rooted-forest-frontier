import ForestCorrespondenceV3

namespace SourceForestV3
open RMAF ForestState GenericForest GenericForest.FrontierWork
open Universal233.PaidQueries SourceCouplingV2 SourceDisjointV2 SourceForestSingletonV2

variable {OrdExec : Tree → Tree → Nat → Option F → Prop} {mode : Mode}

-- Totality is required only where the callback is enabled. A paid refusal must
-- not smuggle in a totality/C premise for a forbidden equal-budget child.
theorem run_exists_enabled {P A : Type} {Child : P → Nat → Option (Nat × A) → Prop}
    (total : ∀ p b, enabled mode b=true → ∃ a, Child p b a)
    (b k : Nat) (js : List (Job P A)) : ∃ r slots ticks, Run Child mode b k js r slots ticks := by
  induction js generalizing k with
  | nil => exact ⟨_,_,_,Run.nil⟩
  | cons j js ih =>
    cases j with
    | resolved p c a =>
      obtain ⟨r,slots,ticks,hr⟩ := ih k
      exact ⟨_,_,_,Run.resolved hr⟩
    | hard p =>
      cases he : enabled mode b with
      | false => exact ⟨_,_,_,Run.refused he⟩
      | true =>
        obtain ⟨a,ha⟩ := total p b he
        cases a with
        | none => exact ⟨_,_,_,Run.failed he ha⟩
        | some x =>
          obtain ⟨r,slots,ticks,hr⟩ := ih (k+1)
          exact ⟨_,_,_,Run.success he ha hr⟩

theorem scheduleAt_exists_enabled {P A : Type} {Child : P → Nat → Option (Nat × A) → Prop}
    (total : ∀ p b, enabled mode b=true → ∃ a, Child p b a)
    (q k : Nat) (js : List (Job P A)) : ∃ r slots, ScheduleAt Child mode q js k r slots := by
  by_cases hs : q<knownCost js+2*pending js
  · exact ⟨_,_,ScheduleAt.refused hs⟩
  · obtain ⟨r,slots,ticks,hr⟩ := run_exists_enabled total (allocated q js) k js
    exact ⟨_,_,ScheduleAt.run hs hr⟩

theorem invoke_exists_enabled
    (total : ∀ T S b, enabled mode b=true → ∃ a, OrdExec T S b a)
    (k : Nat) (p : Tree × Tree) (b : Nat) : ∃ a slot, Invoke OrdExec mode k p b a slot := by
  cases he : enabled mode b with
  | false => exact ⟨_,_,Invoke.refused he⟩
  | true =>
    obtain ⟨a,ha⟩ := total p.1 p.2 b he
    exact ⟨_,_,Invoke.returned he ha⟩

theorem branches_exists (q : Nat)
    (lower : ∀ b, b<q → ∀ k T ss, ∃ out, ForestExec OrdExec mode k T ss b out)
    (k : Nat) (T : Option Tree) (ss : List Tree) (bs : List B) :
    ∃ answers debit slots, BranchesExec OrdExec mode k T ss q bs answers debit slots := by
  induction bs generalizing k with
  | nil => exact ⟨_,_,_,BranchesExec.nil⟩
  | cons io bs ih =>
    by_cases good : eligible q io
    · obtain ⟨out,hout⟩ := lower (q-cutCount io) (by have g:=good; dsimp [eligible] at g; omega)
        k T (replace ss io.1 io.2.partition)
      obtain ⟨answers,debit,slots,htail⟩ := ih (k+out.slots.length)
      exact ⟨_,_,_,BranchesExec.take good hout htail⟩
    · obtain ⟨answers,debit,slots,htail⟩ := ih k
      exact ⟨_,_,_,BranchesExec.skip good htail⟩

theorem nonsingle_exists (q : Nat)
    (lower : ∀ b, b<q → ∀ k T ss, ∃ out, ForestExec OrdExec mode k T ss b out)
    (total : ∀ T S b, enabled mode b=true → ∃ a, OrdExec T S b a)
    (k : Nat) (t : Tree) (ss : List Tree)
    (hp : proper (some t) ss=true) (ha : agrees (some t) ss (ss.map leaves)=false)
    (hn : ss.length≠1) : ∃ out, ForestExec OrdExec mode k (some t) ss q out := by
  cases ho : overlap t ss with
  | none =>
    cases hj : jobs t ss with
    | none => exact ⟨_,ForestExec.noJobs hp ha hn ho hj⟩
    | some js =>
      have pairTotal : ∀ p b, enabled mode b=true → ∃ a, PairChild OrdExec p b a := by
        intro p b he
        obtain ⟨a,ha⟩ := total p.1 p.2 b he
        exact ⟨_,PairChild.returned ha⟩
      obtain ⟨r,slots,hr⟩ := scheduleAt_exists_enabled pairTotal q k js
      exact ⟨_,ForestExec.disjoint hp ha hn ho hj hr⟩
  | some h =>
    obtain ⟨answers,debit,slots,hbranches⟩ := branches_exists q lower k (some t) ss (branches t ss h q)
    exact ⟨_,ForestExec.overlap hp ha hn ho hbranches⟩

theorem forest_exists
    (total : ∀ T S b, enabled mode b=true → ∃ a, OrdExec T S b a)
    (q : Nat) : ∀ k T ss, ∃ out, ForestExec OrdExec mode k T ss q out := by
  refine Nat.strongRecOn q ?_
  intro q lower k T ss
  cases hp : proper T ss with
  | false => exact ⟨_,ForestExec.improper hp⟩
  | true =>
    cases ha : agrees T ss (ss.map leaves) with
    | true => exact ⟨_,ForestExec.agreed hp ha⟩
    | false =>
      cases T with
      | none => exact ⟨_,ForestExec.absent hp ha⟩
      | some t =>
        cases ss with
        | nil => exact nonsingle_exists q lower total k t [] hp ha (by decide)
        | cons s rest =>
          cases rest with
          | nil =>
            obtain ⟨a,slot,hinvoke⟩ := invoke_exists_enabled total k (t,s) q
            exact ⟨_,ForestExec.singleton hp ha hinvoke⟩
          | cons u rest =>
            exact nonsingle_exists q lower total k t (s::u::rest) hp ha (by simp)

end SourceForestV3
