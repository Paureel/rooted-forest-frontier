import SelectorConsumer
namespace Universal233.Rule5PaidSelector
open RMAF CoreGraph Integration VertexGeometry CutRealization HardParent CherryBranching
open Rule5Case322 Rule5Local Rule5Classification Rule5FinalClassification Case322Extraction Case322PaidGuard
set_option maxRecDepth 24000

def opposite (T S : Tree) (c : Branch) : Tree := if c.role=.source then T else S

structure PaidRequest where
 branch : Branch
 target : Tree
 sources : List Tree
 residual : Nat
 deriving DecidableEq, Repr

def requestFor (T S : Tree) (q : Nat) (c : Branch) : Option PaidRequest :=
 if paid c≤q then some ⟨c,opposite T S c,Rule5Case322.sourceForest T S c,q-paid c⟩ else none

def requests {T S : Tree} (D : LiteralGeometry T S) (q : Nat) : List PaidRequest :=
 (guardedPlan D).filterMap (requestFor T S q)

theorem guard_current_parts {T S : Tree} {c : Branch} (h : currentGuard T S c=true) :
 partitionCheck (leaves (current T S c)) c.partition=true ∧
 pairwiseEmbeddings (current T S c) c.partition=true ∧ c.partition.length=paid c+1 := by
 have full : c.originalCuts.Nodup ∧
   c.originalCuts.all (fun q => !q.isEmpty && (subtree (current T S c) q).isSome)=true ∧
   partitionCheck (leaves (current T S c)) c.partition=true ∧
   pairwiseEmbeddings (current T S c) c.partition=true ∧ c.partition.length=paid c+1 ∧
   c.partition=arcPartition (current T S c) c.originalCuts := by
   simpa only [currentGuard,Bool.and_eq_true,decide_eq_true_eq,beq_iff_eq,and_assoc] using h
 exact ⟨full.2.2.1,full.2.2.2.1,full.2.2.2.2.1⟩

/-- Literal full current-source-forest semantics for either operational role. -/
theorem full_state_iff {T S : Tree} (D : LiteralGeometry T S) (c : Branch)
 (guard : currentGuard T S c=true) (F : List (List Nat)) :
 ForestState.agrees (some (opposite T S c)) (Rule5Case322.sourceForest T S c) F=true ↔
 agreement T S F=true ∧ Refines F c.partition := by
 have checks := guard_current_parts guard
 cases c with
 | mk role qs P =>
   cases role with
   | source =>
     exact OutputState.agrees_iff_original T S P F D.properT D.properS D.same checks.1 checks.2.1
   | target =>
     have hh := OutputState.agrees_iff_original S T P F D.properS D.properT (fun x => (D.same x).symm) checks.1 checks.2.1
     constructor
     · intro h
       obtain ⟨ha,ref⟩ := hh.1 h
       exact ⟨agreement_roles_swap ha,ref⟩
     · rintro ⟨ha,ref⟩
       exact hh.2 ⟨agreement_roles_swap ha,ref⟩

theorem full_state_proper {T S : Tree} (D : LiteralGeometry T S) (c : Branch)
 (guard : currentGuard T S c=true) :
 ForestState.proper (some (opposite T S c)) (Rule5Case322.sourceForest T S c)=true := by
 have checks := guard_current_parts guard
 cases c with
 | mk role qs P =>
   cases role with
   | source => exact OutputState.sourceForest_proper T S P D.properT D.properS D.same checks.1
   | target => exact OutputState.sourceForest_proper S T P D.properS D.properT (fun x => (D.same x).symm) checks.1

theorem full_state_cost {T S : Tree} (D : LiteralGeometry T S) (c : Branch)
 (guard : currentGuard T S c=true) (F : List (List Nat)) :
 ForestState.additionalCost (Rule5Case322.sourceForest T S c) F=F.length-c.partition.length := by
 have checks := guard_current_parts guard
 have hn : (leaves (current T S c)).Nodup := by
   cases c with
   | mk role qs P => cases role with
     | source => exact D.properS
     | target => exact D.properT
 exact OutputState.exact_additional_cost (current T S c) c.partition F hn checks.1

/-- The residual budget subtracts the whole original cut list. -/
theorem full_state_paid_budget {T S : Tree} (D : LiteralGeometry T S) (c : Branch) (q : Nat)
 (guard : currentGuard T S c=true) (affordable : paid c≤q) (F : List (List Nat)) :
 (ForestState.agrees (some (opposite T S c)) (Rule5Case322.sourceForest T S c) F=true ∧
  ForestState.additionalCost (Rule5Case322.sourceForest T S c) F≤q-paid c) ↔
 (agreement T S F=true ∧ Refines F c.partition ∧ F.length-1≤q) := by
 rw [full_state_iff D c guard F,full_state_cost D c guard F]
 constructor
 · rintro ⟨⟨ha,ref⟩,budget⟩
   have id := guarded_paid_budget_identity guard ha ref
   exact ⟨ha,ref,by omega⟩
 · rintro ⟨ha,ref,budget⟩
   have id := guarded_paid_budget_identity guard ha ref
   exact ⟨⟨ha,ref⟩,by omega⟩

theorem requestFor_binding {T S : Tree} {q : Nat} {c : Branch} {Q : PaidRequest}
 (h : requestFor T S q c=some Q) :
 paid c≤q ∧ Q.branch=c ∧ Q.target=opposite T S c ∧
 Q.sources=Rule5Case322.sourceForest T S c ∧ Q.residual=q-paid c := by
 unfold requestFor at h
 split at h
 · rename_i affordable
   cases Option.some.inj h
   exact ⟨affordable,rfl,rfl,rfl,rfl⟩
 · contradiction

/-- The actual selected paid list is universally covered by correctly paid
queries on full materialized current source forests. No callback is assumed. -/
theorem selected_full_request_cover {T S : Tree} {a b : Nat} {R : SelectedPaid T S}
 (built : buildSelected T S a b=some R) (q : Nat) {F : List (List Nat)}
 (ha : agreement T S F=true) (budget : F.length-1≤q) :
 ∃ Q∈requests R.geometry q, ForestState.proper (some Q.target) Q.sources=true ∧
 ∃ G,ForestState.agrees (some Q.target) Q.sources G=true ∧
 G.length≤F.length ∧ ForestState.additionalCost Q.sources G≤Q.residual ∧
 Q.residual=q-Q.branch.originalCuts.length := by
 obtain ⟨c,hc,aff,G,hG,len,ref,hbudget⟩ := selected_affordable_cover built q ha budget
 have guard := selected_actual_guards built c hc
 let Q : PaidRequest := ⟨c,opposite T S c,Rule5Case322.sourceForest T S c,q-paid c⟩
 have qm : Q∈requests R.geometry q := List.mem_filterMap.2 ⟨c,hc,by simp [requestFor,aff,Q]⟩
 exact ⟨Q,qm,full_state_proper R.geometry c guard,G,(full_state_iff R.geometry c guard G).2 ⟨hG,ref⟩,
   len,by rw [full_state_cost R.geometry c guard G]; exact hbudget,rfl⟩

theorem selected_full_request_sound {T S : Tree} {a b : Nat} {R : SelectedPaid T S}
 (built : buildSelected T S a b=some R) {q : Nat} {Q : PaidRequest}
 (mem : Q∈requests R.geometry q) {G : List (List Nat)}
 (ha : ForestState.agrees (some Q.target) Q.sources G=true)
 (budget : ForestState.additionalCost Q.sources G≤Q.residual) :
 agreement T S G=true ∧ G.length-1≤q := by
 obtain ⟨c,hc,hQ⟩ := List.mem_filterMap.1 mem
 obtain ⟨aff,branch,target,sources,residual⟩ := requestFor_binding hQ
 have guard := selected_actual_guards built c hc
 rw [target,sources] at ha
 rw [sources,residual] at budget
 have h := (full_state_paid_budget R.geometry c q guard aff G).1 ⟨ha,budget⟩
 exact ⟨h.1,h.2.2⟩

end Universal233.Rule5PaidSelector
