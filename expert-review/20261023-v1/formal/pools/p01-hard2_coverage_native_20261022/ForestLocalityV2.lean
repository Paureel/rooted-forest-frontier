import CleanApartCriterionV7
open RMAF ForestState Universal233 Universal233.HardParent Universal233.CherryBranching
open IndependentGeometry IndependentOneExchange ContactedClade ContactedRepair
namespace ContactedSource

def within (Y B : List Nat) := B.all Y.contains
def coreForest (Y : List Nat) (G : List (List Nat)) := G.filter (within Y)
def otherForest (Y : List Nat) (G : List (List Nat)) := G.filter (fun B=>!within Y B)

theorem within_iff (Y B : List Nat) : within Y B=true ↔ ∀x∈B,x∈Y := by
 simp only [within,List.all_eq_true,List.contains_iff_mem]

theorem forest_partition_perm (Y : List Nat) (G : List (List Nat)) :
 G.Perm (coreForest Y G++otherForest Y G) := by
 induction G with
 | nil => exact .nil
 | cons B rest ih =>
  cases h : within Y B
  · simp only [coreForest,otherForest,List.filter_cons,h,Bool.not_false,ite_false,ite_true]
    exact (List.Perm.cons B ih).trans (List.perm_middle.symm)
  · simp only [coreForest,otherForest,List.filter_cons,h,Bool.not_true,ite_true,ite_false,List.cons_append]
    exact List.Perm.cons B ih

theorem pairwise_iff (T : Tree) (G : List (List Nat)) :
 pairwiseEmbeddings T G=true ↔
 G.Pairwise (fun A B=>disjointVertices (minimalVertices A T) (minimalVertices B T)=true) := by
 induction G with
 | nil => exact ⟨fun _=>.nil,fun _=>rfl⟩
 | cons B rest ih =>
  simp only [pairwiseEmbeddings,Bool.and_eq_true,List.all_eq_true,List.pairwise_cons,ih]

theorem pairwise_perm {T : Tree} {G H : List (List Nat)} (perm : G.Perm H)
 (old : pairwiseEmbeddings T G=true) : pairwiseEmbeddings T H=true :=
 (pairwise_iff T H).2 (((pairwise_iff T G).1 old).perm perm (fun h=>disjoint_sym h))

theorem partition_labels {L : List Nat} {G : List (List Nat)} (h : partitionCheck L G=true) :
 ∀B∈G,∀x∈B,x∈L := by
 simp only [partitionCheck,Bool.and_eq_true] at h
 intro B hb x hx
 exact List.contains_iff_mem.1 (List.all_eq_true.1 h.2 x (List.mem_flatten.2 ⟨B,hb,hx⟩))

theorem partition_nonempty {L : List Nat} {G : List (List Nat)} (h : partitionCheck L G=true) :
 ∀B∈G,B≠[] := by
 simp only [partitionCheck,Bool.and_eq_true] at h
 intro B hb empty
 have yes := List.all_eq_true.1 h.1.1 B hb
 simp only [empty,List.isEmpty_nil,Bool.not_true,Bool.false_eq_true] at yes

theorem core_flatten (Y : List Nat) (G : List (List Nat))
 (sides : ∀B∈G,(∀x∈B,x∈Y) ∨ (∀x∈B,x∉Y)) :
 (coreForest Y G).flatten=G.flatten.filter Y.contains := by
 induction G with
 | nil => rfl
 | cons B rest ih =>
  have tail := ih (fun D hd=>sides D (by simp only [List.mem_cons];exact Or.inr hd))
  rcases sides B (List.mem_cons_self) with yes|no
  · have guard := (within_iff Y B).2 yes
    have same : B.filter Y.contains=B := List.filter_eq_self.2 (fun x hx=>List.contains_iff_mem.2 (yes x hx))
    simp only [coreForest,List.filter_cons,guard,ite_true,List.flatten_cons,List.filter_append,same] at tail ⊢
    exact congrArg (B++·) tail
  · have zero : B.filter Y.contains=[] := List.filter_eq_nil_iff.2 (fun x hx=>by simpa only [List.contains_iff_mem,Bool.not_eq_true] using no x hx)
    by_cases ne : B=[]
    · subst B
      simp only [coreForest,within,List.all_nil,List.filter_cons,ite_true,List.flatten_cons,List.nil_append,List.filter_append,List.filter_nil] at tail ⊢
      exact tail
    · have guard : within Y B=false := by
       cases h : within Y B
       · rfl
       · obtain ⟨x,hx⟩ := List.exists_mem_of_ne_nil B ne
         exact False.elim (no x hx ((within_iff Y B).1 h x hx))
      simp only [coreForest,List.filter_cons,guard,Bool.false_eq_true,ite_false,List.flatten_cons,List.filter_append,zero,List.nil_append] at tail ⊢
      exact tail

theorem restriction_on_core {T S R Q : Tree} {Y B : List Nat}
 (rt : restrict Y T=some R) (rs : restrict Y S=some Q) (sub : ∀x∈B,x∈Y) :
 restrictionAgrees R Q B=restrictionAgrees T S B := by
 have ht := restrict_subset T sub
 have hs := restrict_subset S sub
 simp only [rt,rs,restrictOption,Option.bind_some] at ht hs
 unfold restrictionAgrees
 rw [ht,hs]

theorem core_projection {T S R Q : Tree} {Y : List Nat} {G : List (List Nat)}
 (proper : DepthOne.proper T S=true) (hG : agreement T S G=true)
 (rt : restrict Y T=some R) (rs : restrict Y S=some Q)
 (sides : ∀B∈G,(∀x∈B,x∈Y) ∨ (∀x∈B,x∉Y)) :
 agreement R Q (coreForest Y G)=true := by
 obtain ⟨nt,ns,perm⟩ := IndependentReconstruction.proper_parts proper
 have checks := hG
 simp only [agreement,Bool.and_eq_true] at checks
 have flat := IndependentCommon.flatten_from_partition _ G nt checks.1.1.1.1
 have fl : (coreForest Y G).flatten.Perm (leaves R) := by
  rw [core_flatten Y G sides]
  have eq := restrict_leaves_eq T Y
  simp only [rt,optionLeaves] at eq
  rw [eq]
  exact flat.filter Y.contains
 have properRQ := restricted_pair_proper proper Y rt rs
 have nd := IndependentReconstruction.proper_parts properRQ
 have ne : ∀B∈coreForest Y G,B≠[] := fun B hb=>partition_nonempty checks.1.1.1.1 B (List.mem_filter.1 hb).1
 have partR := IndependentCommon.partition_from_flatten _ _ nd.1 ne fl
 have partQ := IndependentCommon.partition_from_flatten _ _ nd.2.1 ne (fl.trans nd.2.2)
 have sub : ∀B∈coreForest Y G,∀x∈B,x∈Y := fun B hb=>(within_iff Y B).1 (List.mem_filter.1 hb).2
 have shapes : (coreForest Y G).all (restrictionAgrees R Q)=true := by
  apply List.all_eq_true.2
  intro B hb
  rw [restriction_on_core rt rs (sub B hb)]
  exact List.all_eq_true.1 checks.1.1.2 B (List.mem_filter.1 hb).1
 have embT := pairwise_filter T G (within Y) checks.1.2
 have embS := pairwise_filter S G (within Y) checks.2
 have lift (V W : Tree) (rw : restrict Y V=some W)
  (before : pairwiseEmbeddings V (coreForest Y G)=true) : pairwiseEmbeddings W (coreForest Y G)=true := by
   apply (pairwise_iff W _).2
   have pw := (pairwise_iff V _).1 before
   apply List.Pairwise.imp_of_mem _ pw
   intro A B ha hb old
   exact (hull_disjoint_restrict (sub A ha) (sub B hb) rw).1 old
 simp only [agreement,Bool.and_eq_true]
 exact ⟨⟨⟨⟨partR,partQ⟩,shapes⟩,lift T R rt embT⟩,lift S Q rs embS⟩
end ContactedSource

-- Author integration type/axiom reports; proof text above is unchanged apart from recorded import edits.
set_option pp.universes true
#check @ContactedSource.within_iff
#print axioms ContactedSource.within_iff
#check @ContactedSource.forest_partition_perm
#print axioms ContactedSource.forest_partition_perm
#check @ContactedSource.pairwise_iff
#print axioms ContactedSource.pairwise_iff
#check @ContactedSource.pairwise_perm
#print axioms ContactedSource.pairwise_perm
#check @ContactedSource.partition_labels
#print axioms ContactedSource.partition_labels
#check @ContactedSource.partition_nonempty
#print axioms ContactedSource.partition_nonempty
#check @ContactedSource.core_flatten
#print axioms ContactedSource.core_flatten
#check @ContactedSource.restriction_on_core
#print axioms ContactedSource.restriction_on_core
#check @ContactedSource.core_projection
#print axioms ContactedSource.core_projection
