import Case322Cover
namespace Universal233.Rule5Case322
open RMAF CoreGraph Integration VertexGeometry CutRealization HardParent CherryBranching
open Universal233.Rule5Local
set_option maxRecDepth 10000

theorem agreement_roles_swap {T S : Tree} {F : List (List Nat)}
 (ha : agreement T S F = true) : agreement S T F = true := by
 obtain ⟨hpT,hpS,top,embT,embS⟩ := BinaryExchange.agreement_parts T S F ha
 have top' : ∀ B, B ∈ F → restrictionAgrees S T B = true := by
   intro B hB
   have h := top B hB
   unfold restrictionAgrees at h ⊢
   cases et : restrict B T <;> cases es : restrict B S <;> simp only [et,es] at h ⊢
   all_goals try contradiction
   exact (sameShape_correct _ _).2 (BinaryExchange.iso_symm ((sameShape_correct _ _).1 h))
 simp only [agreement,Bool.and_eq_true,List.all_eq_true,executable_pairwiseEmbeddings]
 exact ⟨⟨⟨⟨hpS,hpT⟩,top'⟩,embS⟩,embT⟩

/-- Original cover is invariant under an explicit input-role swap. -/
theorem originalCover_roles_swap {T S : Tree} {F : List (List Nat)} {P : List (List Nat)}
 (h : OriginalCover T S F P) : OriginalCover S T F P := by
 obtain ⟨G,ha,len,ref⟩ := h
 exact ⟨G,agreement_roles_swap ha,len,ref⟩

inductive Role where | target | source deriving DecidableEq,Repr
structure Branch where
 role : Role
 originalCuts : List RMAF.Vertex
 partition : List (List Nat)
 deriving DecidableEq,Repr

def current (T S : Tree) (c : Branch) : Tree := if c.role = .source then S else T
def paid (c : Branch) := c.originalCuts.length
def sourceForest (T S : Tree) (c : Branch) := OutputState.sourceForest (current T S c) c.partition

def hardBranch (S : Tree) (a b : Nat) : Branch := ⟨.source,cuts S a b,pendantPartition S a b⟩
def bBranch (S : Tree) (b : Nat) (qb : RMAF.Vertex) : Branch := ⟨.source,[qb],singletonPartition S b⟩
def targetBranch (T : Tree) (qs : List RMAF.Vertex) : Branch := ⟨.target,qs,arcPartition T qs⟩
def typeIBranches (T S : Tree) (a b : Nat) (qa qb q r : RMAF.Vertex) :=
 [hardBranch S a b,bBranch S b qb,targetBranch T [qa,q],targetBranch T [qa,r]]
def typeIIBranches (T S : Tree) (a b : Nat) (qa qb : RMAF.Vertex) (qs : List RMAF.Vertex) :=
 [hardBranch S a b,bBranch S b qb,targetBranch T (qa::qs)]

/-- This executable guard retains original nonroot valid distinct arcs and
checks the exact current source partition, embeddings and nonredundant cost.
No saving or safe-cover premise appears in this guard. The geometric caller
must prove it for its materialized literal branches. -/
def currentGuard (T S : Tree) (c : Branch) : Bool :=
 decide c.originalCuts.Nodup &&
 c.originalCuts.all (fun q => !q.isEmpty && (subtree (current T S c) q).isSome) &&
 partitionCheck (leaves (current T S c)) c.partition &&
 pairwiseEmbeddings (current T S c) c.partition &&
 (c.partition.length == paid c + 1)

theorem typeI_raw_costs {T S : Tree} {a b : Nat} {qa qb q r : RMAF.Vertex}
 (two : (cuts S a b).length = 2) :
 (typeIBranches T S a b qa qb q r).map paid = [2,1,2,2] := by
 simp [typeIBranches,hardBranch,bBranch,targetBranch,paid,two]
theorem typeII_raw_costs {T S : Tree} {a b : Nat} {qa qb : RMAF.Vertex} {qs : List RMAF.Vertex}
 (two : (cuts S a b).length = 2) :
 (typeIIBranches T S a b qa qb qs).map paid = [2,1,qs.length+1] := by
 simp [typeIIBranches,hardBranch,bBranch,targetBranch,paid,two]

theorem typeI_binding (T S : Tree) (a b : Nat) (qa qb q r : RMAF.Vertex) :
 (typeIBranches T S a b qa qb q r).map Branch.partition = typeIChildren T S a b qa q r := rfl
theorem typeII_binding (T S : Tree) (a b : Nat) (qa qb : RMAF.Vertex) (qs : List RMAF.Vertex) :
 (typeIIBranches T S a b qa qb qs).map Branch.partition = typeIIChildren T S a b qa qs := rfl

/-- Exact child IH is deliberately conditional. It solves original AFs
refining this literal branch, without asserting any recursive algorithm. -/
def ExactChild (T S : Tree) (c : Branch) (G : List (List Nat)) : Prop :=
 agreement T S G = true ∧ Refines G c.partition ∧
 ∀ H, agreement T S H = true → Refines H c.partition → G.length ≤ H.length

theorem child_IH_minimum {T S : Tree} {cs : List Branch}
 (cover : ∀ F, agreement T S F = true → ∃ c, c ∈ cs ∧ OriginalCover T S F c.partition)
 (solve : Branch → List (List Nat))
 (ih : ∀ c, c ∈ cs → ExactChild T S c (solve c))
 (best : List (List Nat)) (chosen : ∃ c, c ∈ cs ∧ best = solve c)
 (least : ∀ c, c ∈ cs → best.length ≤ (solve c).length) :
 agreement T S best = true ∧ ∀ F, agreement T S F = true → best.length ≤ F.length := by
 obtain ⟨c,hc,rfl⟩ := chosen
 refine ⟨(ih c hc).1,?_⟩
 intro F ha
 obtain ⟨d,hd,G,hG,len,ref⟩ := cover F ha
 exact Nat.le_trans (least d hd) (Nat.le_trans ((ih d hd).2.2 G hG ref) len)

/-- Original cost telescoping uses the actual current source and guard.
Every member of the literal cut LIST is paid, including type3(ii) a+x+y. -/
theorem guarded_paid_budget_identity {T S : Tree} {c : Branch} {F : List (List Nat)}
 (guard : currentGuard T S c = true) (ha : agreement T S F = true)
 (ref : Refines F c.partition) : paid c + (F.length-c.partition.length) = F.length-1 := by
 have fields : (decide c.originalCuts.Nodup = true ∧
   c.originalCuts.all (fun q => !q.isEmpty && (subtree (current T S c) q).isSome) = true) ∧
   partitionCheck (leaves (current T S c)) c.partition = true ∧
   pairwiseEmbeddings (current T S c) c.partition = true ∧ c.partition.length = paid c + 1 := by
   simpa only [currentGuard,Bool.and_eq_true,beq_iff_eq,and_assoc] using guard
 have currentAgree : agreement (if c.role = .source then T else S) (current T S c) F = true := by
   by_cases role : c.role = .source
   · simpa [current,role] using ha
   · simpa [current,role] using agreement_roles_swap ha
 have len := refined_length fields.2.1 fields.2.2.1 currentAgree ref
 omega

/-- Only paid children emit recursive callback requests. Order and duplicate
requests are retained; the original branch list is never deduplicated. -/
def callbackRequests (q : Nat) (cs : List Branch) : List Nat :=
 cs.filterMap fun c => if paid c ≤ q then some (q-paid c) else none

theorem callback_strict_decrease {q r : Nat} {cs : List Branch}
 (positive : ∀ c, c ∈ cs → 0 < paid c) (hr : r ∈ callbackRequests q cs) : r < q := by
 obtain ⟨c,hc,out⟩ := List.mem_filterMap.1 hr
 change (if paid c ≤ q then some (q-paid c) else none) = some r at out
 split at out
 · have eq : q-paid c = r := Option.some.inj out
   have pos := positive c hc
   omega
 · contradiction

def rawMass (weight : Nat → Nat) (costs : List Nat) := (costs.map weight).sum

theorem typeI_LIST_mass (weight : Nat → Nat) : rawMass weight [2,1,2,2] = weight 1 + 3*weight 2 := by
 simp [rawMass]; omega
theorem typeII_LIST_mass (weight : Nat → Nat) (n : Nat) :
 rawMass weight [2,1,n+1] = weight 1 + weight 2 + weight (n+1) := by simp [rawMass]; omega
theorem typeIII_LIST_mass (weight : Nat → Nat) : rawMass weight [2,1,2] = weight 1 + 2*weight 2 := by
 simp [rawMass]; omega

def scaled233Mass (exponent : Nat) (costs : List Nat) : Nat :=
 (costs.map fun d => 100^d * 233^(exponent-d)).sum
/-- Exact local LIST arithmetic only; these are not a whole-algorithm bound. -/
theorem typeI_mass233 : scaled233Mass 2 [2,1,2,2] = 53300 ∧ 53300 < 233^2 := by decide
theorem typeII_cost3_mass233 : scaled233Mass 3 [2,1,3] = 8758900 ∧ 8758900 < 233^3 := by decide
theorem typeIII_mass233 : scaled233Mass 2 [2,1,2] = 43300 ∧ 43300 < 233^2 := by decide

/-- Guarding may delete callback attempts, while preserving every retained
occurrence and its order. The mass is the sum over that raw request LIST. -/
theorem guarded_callback_LIST_mass (weight : Nat → Nat) (q : Nat) (cs : List Branch) :
 ((callbackRequests q cs).map weight).sum ≤ (cs.map fun c => weight (q-paid c)).sum := by
 induction cs with
 | nil => simp [callbackRequests]
 | cons c cs ih =>
   unfold callbackRequests at ih ⊢
   by_cases h : paid c ≤ q
   · simpa [h] using Nat.add_le_add_left ih (weight (q-paid c))
   · have nonneg : 0 ≤ weight (q-paid c) := Nat.zero_le _
     simpa [h] using Nat.le_trans ih (Nat.le_add_left (List.sum (List.map (fun c => weight (q-paid c)) cs)) (weight (q-paid c)))

theorem partition_cover_to_branch_cover {T S : Tree} {cs : List Branch} {F : List (List Nat)}
 (h : ∃ P, P ∈ cs.map Branch.partition ∧ OriginalCover T S F P) :
 ∃ c, c ∈ cs ∧ OriginalCover T S F c.partition := by
 obtain ⟨P,hP,cover⟩ := h
 obtain ⟨c,hc,eq⟩ := List.mem_map.1 hP
 exact ⟨c,hc,eq ▸ cover⟩
end Universal233.Rule5Case322
