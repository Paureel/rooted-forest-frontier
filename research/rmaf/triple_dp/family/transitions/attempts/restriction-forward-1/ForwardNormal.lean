import RestrictionDefs
import MergeContract

namespace TripleDP.Transitions.Restriction
open TripleDP.CostRoute

variable {α I J : Type} {l r : BTree α}

theorem closeBoth_normal (f : Family l I) (g : Family r J) :
    OpenBranchLive (closeBoth f g) := by
  intro o ho
  change none = some o at ho
  cases ho

theorem extendLeft_normal (f : Family l I) (g : Family r J)
    (o : I) (ho : f.boundary = some o) :
    OpenBranchLive (extendLeft f g o ho) := by
  intro i hi side hh
  change some (.inl o) = some i at hi
  have he := Option.some.inj hi
  subst i
  cases side with
  | false =>
    rcases f.labelled o with ⟨a, x, hx, ha⟩
    refine ⟨a, x, hx, ?_⟩
    exact Or.inr ⟨rfl, ha⟩
  | true =>
    rcases hh with ⟨a, ha⟩
    simp [extendLeft, adjoinRoot, adjoinRootSupport, closeBoth, closedSupport,
      liftSupport] at ha

theorem extendRight_normal (f : Family l I) (g : Family r J)
    (o : J) (ho : g.boundary = some o) :
    OpenBranchLive (extendRight f g o ho) := by
  intro i hi side hh
  change some (.inr o) = some i at hi
  have he := Option.some.inj hi
  subst i
  cases side with
  | false =>
    rcases hh with ⟨a, ha⟩
    simp [extendRight, adjoinRoot, adjoinRootSupport, closeBoth, closedSupport,
      liftSupport] at ha
  | true =>
    rcases g.labelled o with ⟨a, x, hx, ha⟩
    refine ⟨a, x, hx, ?_⟩
    exact Or.inr ⟨rfl, ha⟩

theorem merge_normal [DecidableEq J] (f : Family l I) (g : Family r J)
    (o : I) (p : J) (ho : f.boundary = some o) (hp : g.boundary = some p) :
    OpenBranchLive (merge f g o p ho hp) := by
  intro i hi side _
  change some (.inl o) = some i at hi
  have he := Option.some.inj hi
  subst i
  cases side with
  | false =>
    rcases f.labelled o with ⟨a, x, hx, ha⟩
    exact ⟨a, x, hx, Or.inl ⟨rfl, ha⟩⟩
  | true =>
    rcases g.labelled p with ⟨a, x, hx, ha⟩
    exact ⟨a, x, hx, Or.inr ⟨rfl, Or.inr ⟨rfl, ha⟩⟩⟩

#print axioms closeBoth_normal
#print axioms extendLeft_normal
#print axioms extendRight_normal
#print axioms merge_normal
end TripleDP.Transitions.Restriction
