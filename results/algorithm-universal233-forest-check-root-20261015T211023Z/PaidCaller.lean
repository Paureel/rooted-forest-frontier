import PaidGuard
import RoleBinding
namespace Universal233.Case322PaidGuard
open RMAF CoreGraph Integration VertexGeometry CutRealization HardParent CherryBranching
open Universal233.Rule5Local Universal233.Rule5Case322 Universal233.Case322Extraction
set_option maxRecDepth 24000

/-- Only original source/core/terminal/frontier data are recorded. No cover,
guard, saving or nonredundancy conclusion is a field. -/
structure LiteralGeometry (T S : Tree) where
 X : Tree
 C : Tree
 w : RMAF.Vertex
 r : RMAF.Vertex
 qa : RMAF.Vertex
 ub : RMAF.Vertex
 uc : RMAF.Vertex
 sa : Bool
 sc : Bool
 sb : Bool
 a : Nat
 b : Nat
 c : Nat
 properT : (leaves T).Nodup
 properS : (leaves S).Nodup
 same : ∀ x, x ∈ leaves T ↔ x ∈ leaves S
 source : subtree S w = some (bottom sa sc sb a b c X)
 cherry : ActualCherry T a b
 two : (cuts S a b).length = 2
 core : subtree T r = some C
 coreLabels : ∀ x, x ∈ leaves T → (x ∈ leaves C ↔ x ∉ leaves X ∧ x ≠ c)
 bC : b ∈ leaves C
 cC : c ∉ leaves C
 leafA : LeafAt T qa a
 leafB : LeafAt T ub b
 leafC : LeafAt T uc c
 frontier : incident T (leaves X) = [r,uc] ∨ incident T (leaves X) = [uc,r]
 tailR : r.dropLast ∈ minimalVertices (leaves X) T
 tailC : uc.dropLast ∈ minimalVertices (leaves X) T
 offR : r ∉ minimalVertices (leaves X) T
 offC : uc ∉ minimalVertices (leaves X) T

def literalPlan {T S : Tree} (D : LiteralGeometry T S) : List Branch :=
 rawPlan T S D.a D.b D.c D.qa (bArc D.w D.sb) D.ub D.uc

/-- Actual current-guard filtering, preserving branch order and multiplicity. -/
def guardedPlan {T S : Tree} (D : LiteralGeometry T S) : List Branch :=
 (literalPlan D).filter (currentGuard T S)

theorem literalPlan_guards {T S : Tree} (D : LiteralGeometry T S) :
 ∀ child, child ∈ literalPlan D → currentGuard T S child = true :=
 literal_rawPlan_currentGuards D.properT D.properS D.same D.source D.cherry D.two
   D.core D.coreLabels D.bC D.cC D.leafA D.leafB D.leafC D.frontier D.tailR D.tailC D.offR D.offC

theorem guardedPlan_eq {T S : Tree} (D : LiteralGeometry T S) : guardedPlan D = literalPlan D :=
 List.filter_eq_self.2 (literalPlan_guards D)

theorem guarded_original_cover {T S : Tree} (D : LiteralGeometry T S)
 {F : List (List Nat)} (ha : agreement T S F = true) :
 ∃ child, child ∈ guardedPlan D ∧ OriginalCover T S F child.partition := by
 rw [guardedPlan_eq]
 exact rawPlan_original_cover D.properT D.properS D.same D.source D.cherry D.two
   D.core D.coreLabels D.bC D.cC D.leafA D.leafB D.leafC ha

/-- Every original q-feasible agreement forest is covered by an affordable
actual guarded query. The budget is q minus the FULL original cut-list length.
The final recovery of those cuts is a separate, one-time operation. -/
theorem guarded_affordable_cover {T S : Tree} (D : LiteralGeometry T S) (q : Nat)
 {F : List (List Nat)} (ha : agreement T S F = true) (budget : F.length-1 ≤ q) :
 ∃ child, child ∈ guardedPlan D ∧ paid child ≤ q ∧
   ∃ G, agreement T S G = true ∧ G.length ≤ F.length ∧ Refines G child.partition ∧
     G.length-child.partition.length ≤ q-paid child := by
 obtain ⟨child,hc,G,hG,len,ref⟩ := guarded_original_cover D ha
 have guard : currentGuard T S child = true := (List.mem_filter.1 hc).2
 have id := guarded_paid_budget_identity guard hG ref
 have gle : G.length-1 ≤ q := Nat.le_trans (Nat.sub_le_sub_right len 1) budget
 have cost : paid child ≤ q := by omega
 refine ⟨child,hc,cost,G,hG,len,ref,?_⟩
 omega

/-- Conditional recursive-child minimum for the ACTUAL guarded list. The IH
remains explicit: this local theorem does not claim a whole recursive solver. -/
theorem guarded_conditional_minimum {T S : Tree} (D : LiteralGeometry T S)
 (solve : Branch → List (List Nat))
 (ih : ∀ child, child ∈ guardedPlan D → ExactChild T S child (solve child))
 (best : List (List Nat))
 (chosen : ∃ child, child ∈ guardedPlan D ∧ best = solve child)
 (least : ∀ child, child ∈ guardedPlan D → best.length ≤ (solve child).length) :
 agreement T S best = true ∧ ∀ F, agreement T S F = true → best.length ≤ F.length := by
 exact child_IH_minimum (fun F ha => guarded_original_cover D ha) solve ih best chosen least

theorem guarded_cost_classes {T S : Tree} (D : LiteralGeometry T S) :
 (guardedPlan D).map paid = [2,1,2,2] ∨
 ∃ d, 2 ≤ d ∧ (guardedPlan D).map paid = [2,1,d] := by
 rw [guardedPlan_eq]
 exact rawPlan_cost_classes D.two

theorem guarded_query_decrease {T S : Tree} (D : LiteralGeometry T S) {q n : Nat}
 (mem : n ∈ callbackRequests q (guardedPlan D)) : n < q := by
 rw [guardedPlan_eq] at mem
 exact rawPlan_callbacks_decrease D.two mem

theorem guarded_query_LIST_mass {T S : Tree} (D : LiteralGeometry T S) (q : Nat) (weight : Nat → Nat) :
 ((callbackRequests q (guardedPlan D)).map weight).sum ≤
   ((guardedPlan D).map (fun child => weight (q-paid child))).sum :=
 guarded_callback_LIST_mass weight q (guardedPlan D)

theorem guarded_cost_LIST_mass {T S : Tree} (D : LiteralGeometry T S) (weight : Nat → Nat)
 (decay : ∀ d, 2 ≤ d → weight d ≤ weight 2) :
 rawMass weight ((guardedPlan D).map paid) ≤ weight 1+3*weight 2 := by
 rw [guardedPlan_eq]
 exact rawPlan_LIST_mass_bound D.two weight decay

/-- Conditional child query on the original current partition. Recursive
implementation is supplied by the caller; the two directions express exactly
its required original-label refinement semantics. -/
def ChildQueryCorrect (T S : Tree) (child : Branch) (q : Nat)
 (answer : Option (List (List Nat))) : Prop :=
 (∀ G, answer = some G → agreement T S G = true ∧ Refines G child.partition ∧
   G.length-child.partition.length ≤ q) ∧
 ((∃ G, agreement T S G = true ∧ Refines G child.partition ∧
   G.length-child.partition.length ≤ q) → ∃ G, answer = some G)

def guardedQuery {T S : Tree} (D : LiteralGeometry T S) (q : Nat)
 (solve : Branch → Nat → Option (List (List Nat))) : Bool :=
 (guardedPlan D).any fun child => if paid child ≤ q then (solve child (q-paid child)).isSome else false

/-- Exact q=k-1 feasibility of the actual guarded conditional branch query.
The full paid original cut list is subtracted before every child request. -/
theorem guardedQuery_spec {T S : Tree} (D : LiteralGeometry T S) (q : Nat)
 (solve : Branch → Nat → Option (List (List Nat)))
 (ih : ∀ child, child ∈ guardedPlan D → paid child ≤ q →
   ChildQueryCorrect T S child (q-paid child) (solve child (q-paid child))) :
 guardedQuery D q solve = true ↔ ∃ F, agreement T S F = true ∧ F.length-1 ≤ q := by
 constructor
 · intro success
   obtain ⟨child,hc,test⟩ := List.any_eq_true.1 success
   by_cases affordable : paid child ≤ q
   · simp only [affordable,ite_true] at test
     cases answer : solve child (q-paid child) with
     | none => simp [answer] at test
     | some G =>
       obtain ⟨hG,ref,budget⟩ := (ih child hc affordable).1 G answer
       have guard := (List.mem_filter.1 hc).2
       have id := guarded_paid_budget_identity guard hG ref
       exact ⟨G,hG,by omega⟩
   · simp [affordable] at test
 · rintro ⟨F,hF,budget⟩
   obtain ⟨child,hc,affordable,G,hG,len,ref,budgetG⟩ := guarded_affordable_cover D q hF budget
   obtain ⟨H,answer⟩ := (ih child hc affordable).2 ⟨G,hG,ref,budgetG⟩
   apply List.any_eq_true.2
   exact ⟨child,hc,by simp [affordable,answer]⟩

/-- Explicit role metadata transport binds the same physical current trees,
partitions, original cuts and paid requests after exchanging input roles. -/
def swappedGuardedPlan {T S : Tree} (D : LiteralGeometry T S) : List Branch :=
 (guardedPlan D).map swapBranch

theorem swapped_guarded_binding {T S : Tree} (D : LiteralGeometry T S) :
 ∀ child, child ∈ swappedGuardedPlan D → currentGuard S T child = true := by
 intro child hc
 obtain ⟨orig,ho,rfl⟩ := List.mem_map.1 hc
 rw [guard_swap]
 exact (List.mem_filter.1 ho).2

theorem swapped_guard_filter_eq {T S : Tree} (D : LiteralGeometry T S) :
 (swappedGuardedPlan D).filter (currentGuard S T) = swappedGuardedPlan D :=
 List.filter_eq_self.2 (swapped_guarded_binding D)

theorem swapped_guarded_cover {T S : Tree} (D : LiteralGeometry T S)
 {F : List (List Nat)} (ha : agreement S T F = true) :
 ∃ child, child ∈ swappedGuardedPlan D ∧ OriginalCover S T F child.partition := by
 obtain ⟨child,hc,cover⟩ := guarded_original_cover D (agreement_roles_swap ha)
 exact ⟨swapBranch child,List.mem_map.2 ⟨child,hc,rfl⟩,originalCover_roles_swap cover⟩

theorem swapped_conditional_minimum {T S : Tree} (D : LiteralGeometry T S)
 (solve : Branch → List (List Nat))
 (ih : ∀ child, child ∈ swappedGuardedPlan D → ExactChild S T child (solve child))
 (best : List (List Nat))
 (chosen : ∃ child, child ∈ swappedGuardedPlan D ∧ best = solve child)
 (least : ∀ child, child ∈ swappedGuardedPlan D → best.length ≤ (solve child).length) :
 agreement S T best = true ∧ ∀ F, agreement S T F = true → best.length ≤ F.length := by
 exact child_IH_minimum (fun F ha => swapped_guarded_cover D ha) solve ih best chosen least

theorem swapped_callbacks_exact {T S : Tree} (D : LiteralGeometry T S) (q : Nat) :
 callbackRequests q (swappedGuardedPlan D) = callbackRequests q (guardedPlan D) :=
 callbacks_swap q (guardedPlan D)

end Universal233.Case322PaidGuard
