import LiteralPlan
namespace Universal233.Case322Extraction
open RMAF CoreGraph Integration VertexGeometry CutRealization HardParent CherryBranching
open Universal233.Rule5Local Universal233.Rule5Case322
set_option maxRecDepth 15000

theorem tree_leaves_nonempty (T : Tree) : leaves T ≠ [] := by
 have member : ∃ x, x ∈ leaves T := by
   induction T with
   | leaf x => exact ⟨x,by simp [leaves]⟩
   | node L R ihL ihR =>
     obtain ⟨x,hx⟩ := ihL
     exact ⟨x,List.mem_append_left _ hx⟩
 obtain ⟨x,hx⟩ := member
 intro e
 rw [e] at hx
 exact List.not_mem_nil hx

theorem original_self_agreement (T : Tree) (hn : (leaves T).Nodup) : agreement T T [leaves T] = true := by
 have hp : partitionCheck (leaves T) [leaves T] = true := by
   apply BinaryExchange.partition_intro
   · intro B hB; have e : B = leaves T := by simpa using hB
     subst B; exact tree_leaves_nonempty T
   · intro x hx; simpa using (hn.count (a:=x)).trans (by simp [hx])
   · intro x hx; simpa using hx
 have full := restrict_of_contains T (leaves T) (by intro x hx; exact List.contains_iff_mem.2 hx)
 simp [agreement,hp,restrictionAgrees,full,sameShape_refl,pairwiseEmbeddings]

theorem split_current_self_agreement {T : Tree} (hn : (leaves T).Nodup)
 (qs : List RMAF.Vertex) (P : List (List Nat))
 (valid : ∀ q, q ∈ qs → Valid T q) (ha : agreement T T P = true) :
 agreement T T (arcPartitionFrom T qs P) = true := by
 induction qs generalizing P with
 | nil => exact ha
 | cons q qs ih =>
   obtain ⟨U,hU⟩ := valid q (by simp)
   have next := (split_original_agreement hn hU ha).1
   rw [←source_subtree_labels hU] at next
   exact ih _ (fun r hr => valid r (by simp [hr])) next

/-- Source partition/embedding validity of the materialized current forest is
proved for ANY list of valid original arcs, including nested ones. This does
not assert that all those cuts are nonredundant or paid. -/
theorem arcPartition_current_checks {T : Tree} (hn : (leaves T).Nodup)
 (qs : List RMAF.Vertex) (valid : ∀ q, q ∈ qs → Valid T q) :
 partitionCheck (leaves T) (arcPartition T qs) = true ∧ pairwiseEmbeddings T (arcPartition T qs) = true := by
 have self := split_current_self_agreement hn qs [leaves T] valid (original_self_agreement T hn)
 have parts := BinaryExchange.agreement_parts T T _ self
 exact ⟨parts.1,(executable_pairwiseEmbeddings T _).2 parts.2.2.2.1⟩

/-- Universal guard reduction. All current-source checks are discharged by
original splitting; the exact nonredundant component count remains an explicit
consumer and cannot be replaced by an arbitrary saving field. -/
theorem target_currentGuard_of_nonredundant {T S : Tree} (hn : (leaves T).Nodup)
 (qs : List RMAF.Vertex) (nodup : qs.Nodup)
 (valid : ∀ q, q ∈ qs → Valid T q) (nonroot : ∀ q, q ∈ qs → q ≠ [])
 (components : (arcPartition T qs).length = qs.length+1) :
 currentGuard T S (targetBranch T qs) = true := by
 have checks := arcPartition_current_checks hn qs valid
 have arcs : qs.all (fun q => !q.isEmpty && (subtree T q).isSome) = true := by
   apply List.all_eq_true.2
   intro q hq
   obtain ⟨U,hU⟩ := valid q hq
   have nr : q.isEmpty = false := by cases e : q with | nil => exact False.elim (nonroot q hq e) | cons s tail => rfl
   simp [nr,hU]
 simpa [currentGuard,targetBranch,current,paid,nodup,arcs,checks.1,checks.2,components]

/-- Literal selection never deduplicates paid callback occurrences. The
existing conditional minimum/decrease/list-mass theorems consume this exact
computed list once universal current guards have been supplied. -/
theorem rawPlan_conditional_minimum {T S X C : Tree} {w r qa qb ub uc : RMAF.Vertex} {sa sc sb : Bool}
 {a b c : Nat}
 (hnT : (leaves T).Nodup) (hnS : (leaves S).Nodup)
 (same : ∀ x, x ∈ leaves T ↔ x ∈ leaves S)
 (he : subtree S w = some (bottom sa sc sb a b c X))
 (ch : ActualCherry T a b) (two : (cuts S a b).length = 2)
 (core : subtree T r = some C)
 (coreLabels : ∀ x, x ∈ leaves T → (x ∈ leaves C ↔ x ∉ leaves X ∧ x ≠ c))
 (bC : b ∈ leaves C) (cC : c ∉ leaves C)
 (leafA : LeafAt T qa a) (lb : LeafAt T ub b) (lc : LeafAt T uc c)
 (solve : Branch → List (List Nat))
 (ih : ∀ child, child ∈ rawPlan T S a b c qa qb ub uc → ExactChild T S child (solve child))
 (best : List (List Nat))
 (chosen : ∃ child, child ∈ rawPlan T S a b c qa qb ub uc ∧ best = solve child)
 (least : ∀ child, child ∈ rawPlan T S a b c qa qb ub uc → best.length ≤ (solve child).length) :
 agreement T S best = true ∧ ∀ F, agreement T S F = true → best.length ≤ F.length := by
 exact child_IH_minimum (fun F ha => rawPlan_original_cover hnT hnS same he ch two core coreLabels bC cC leafA lb lc ha)
   solve ih best chosen least
end Universal233.Case322Extraction
