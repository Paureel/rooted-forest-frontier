import PartitionRefine
import Budget
import Pretest
namespace FreshResidual
open RMAF ForestState OutputState

theorem tree_leaves_ne (S : Tree) : leaves S ≠ [] := by
 induction S with
 | leaf x => simp [leaves]
 | node l r il ir => simp [leaves,il]

def optionLeaves : Option Tree → List Nat
 | none => []
 | some S => leaves S

theorem restriction_leaves (B : List Nat) (S : Tree) :
 optionLeaves (restrict B S) = (leaves S).filter B.contains := by
 induction S with
 | leaf x => by_cases hx : x∈B <;> simp [restrict,leaves,optionLeaves,hx]
 | node l r il ir =>
   cases hl : restrict B l <;> cases hr : restrict B r <;>
    simp_all [restrict,optionLeaves,leaves,List.filter_append]

theorem count_le_flatten {P : List (List Nat)} {U : List Nat} (hu : U∈P) (x : Nat) :
 U.count x ≤ P.flatten.count x := by
 induction P with
 | nil => simp at hu
 | cons V P ih =>
   simp only [List.mem_cons] at hu
   simp only [List.flatten_cons,List.count_append]
   rcases hu with rfl|hu
   · omega
   · have h := ih hu; omega

theorem nodup_of_count (L : List Nat) (h : ∀x, L.count x ≤ 1) : L.Nodup := by
 induction L with
 | nil => simp
 | cons a L ih =>
   simp only [List.nodup_cons]
   constructor
   · intro ha
     have hpos := List.count_pos_iff.mpr ha
     have hh := h a
     simp only [List.count_cons_self] at hh
     omega
   · apply ih
     intro x
     have hh := h x
     simp only [List.count_cons] at hh
     omega

theorem partition_count {L : List Nat} {P : List (List Nat)}
 (hp : partitionCheck L P=true) {x : Nat} (hx : x∈L) : P.flatten.count x=1 := by
 simp only [partitionCheck,Bool.and_eq_true] at hp
 exact (beq_iff_eq.mp ((List.all_eq_true.mp hp.1.2) x hx))

theorem partition_nonempty {L : List Nat} {P : List (List Nat)}
 (hp : partitionCheck L P=true) {U : List Nat} (hu : U∈P) : U≠[] := by
 simp only [partitionCheck,Bool.and_eq_true] at hp
 have h := (List.all_eq_true.mp hp.1.1) U hu
 simpa [List.isEmpty_iff] using h

theorem partition_block_nodup {L : List Nat} {P : List (List Nat)}
 (hp : partitionCheck L P=true) {U : List Nat} (hu : U∈P) : U.Nodup := by
 apply nodup_of_count
 intro x
 by_cases hx : x∈U
 · have hl := FreshClade.partition_labels hp hu x hx
   have hc := partition_count hp hl
   have hh := count_le_flatten hu x
   omega
 · simp [List.count_eq_zero.mpr hx]

theorem restriction_materialized {S : Tree} {P : List (List Nat)}
 (ns : (leaves S).Nodup) (hp : partitionCheck (leaves S) P=true)
 {U : List Nat} (hu : U∈P) : ∃s, restrict U S=some s ∧ (leaves s).Perm U := by
 have ne := partition_nonempty hp hu
 have labs := FreshClade.partition_labels hp hu
 have hn : restrict U S≠none := by
   cases U with
   | nil => contradiction
   | cons x U => exact FreshClade.restrict_selected _ _ (by simp) (labs x (by simp))
 cases hr : restrict U S with
 | none => exact False.elim (hn hr)
 | some s =>
   refine ⟨s,rfl,?_⟩
   have he := restriction_leaves U S
   simp only [hr,optionLeaves] at he
   rw [he]
   apply (List.perm_ext_iff_of_nodup (List.Nodup.sublist (List.filter_sublist) ns) (partition_block_nodup hp hu)).mpr
   intro x
   simp only [List.mem_filter,List.contains_iff_mem]
   exact ⟨fun h=>h.2,fun h=>⟨labs x h,h⟩⟩

theorem materialized_length_aux (S : Tree) (P : List (List Nat))
 (he : ∀ U∈P, ∃s, restrict U S=some s) : (sourceForest S P).length=P.length := by
 induction P with
 | nil => rfl
 | cons U P ih =>
   rcases he U (by simp) with ⟨s,hs⟩
   have ht : ∀V∈P, ∃s, restrict V S=some s := fun V h=>he V (by simp [h])
   simpa [sourceForest,hs] using congrArg Nat.succ (ih ht)

theorem sourceForest_length {S : Tree} {P : List (List Nat)}
 (ns : (leaves S).Nodup) (hp : partitionCheck (leaves S) P=true) :
 (sourceForest S P).length=P.length :=
 materialized_length_aux S P (fun U hu=>by rcases restriction_materialized ns hp hu with ⟨s,h,_⟩; exact ⟨s,h⟩)

theorem materialized_flatten_aux (S : Tree) (P : List (List Nat))
 (he : ∀U∈P, ∃s, restrict U S=some s ∧ (leaves s).Perm U) :
 ((sourceForest S P).map leaves).flatten.Perm P.flatten := by
 induction P with
 | nil => exact .nil
 | cons U P ih =>
   rcases he U (by simp) with ⟨s,hs,hp⟩
   have ht : ∀V∈P, ∃s, restrict V S=some s ∧ (leaves s).Perm V := fun V h=>he V (by simp [h])
   simpa [sourceForest,hs] using hp.append (ih ht)

theorem partition_labels_perm (L M : List Nat) (P : List (List Nat)) (h : L.Perm M) :
 partitionCheck L P=partitionCheck M P := by
 have hc : L.contains=M.contains := by
   funext x
   apply FreshClade.bool_ext
   simpa only [List.contains_iff_mem] using h.mem_iff
 unfold partitionCheck
 rw [h.all_eq,hc]

theorem sourceForest_partition {S : Tree} {P : List (List Nat)}
 (ns : (leaves S).Nodup) (hp : partitionCheck (leaves S) P=true) :
 partitionCheck (leaves S) ((sourceForest S P).map leaves)=true := by
 have he := materialized_flatten_aux S P (fun U hu=>restriction_materialized ns hp hu)
 simp only [partitionCheck,Bool.and_eq_true,List.all_eq_true] at hp ⊢
 refine ⟨⟨?_,?_⟩,?_⟩
 · intro U hU
   rcases List.mem_map.mp hU with ⟨s,hs,rfl⟩
   simpa [List.isEmpty_iff] using tree_leaves_ne s
 · intro x hx
   simpa only [he.count_eq] using hp.1.2 x hx
 · intro x hx
   exact hp.2 x (he.mem_iff.mp hx)

theorem sourceForest_proper {T S : Tree} {P : List (List Nat)}
 (proper : Universal233.DepthOne.proper T S=true)
 (hp : partitionCheck (leaves S) P=true) : ForestState.proper (some T) (sourceForest S P)=true := by
 simp only [Universal233.DepthOne.proper,Bool.and_eq_true,decide_eq_true_eq] at proper
 unfold ForestState.proper ForestState.labels
 rw [partition_labels_perm (leaves T) (leaves S) _ proper.2]
 simp only [Bool.and_eq_true,decide_eq_true_eq]
 exact ⟨proper.1.1,sourceForest_partition proper.1.2 hp⟩
end FreshResidual

-- Author integration type/axiom reports; proof text above is unchanged apart from recorded import edits.
set_option pp.universes true
#check @FreshResidual.tree_leaves_ne
#print axioms FreshResidual.tree_leaves_ne
#check @FreshResidual.restriction_leaves
#print axioms FreshResidual.restriction_leaves
#check @FreshResidual.count_le_flatten
#print axioms FreshResidual.count_le_flatten
#check @FreshResidual.nodup_of_count
#print axioms FreshResidual.nodup_of_count
#check @FreshResidual.partition_count
#print axioms FreshResidual.partition_count
#check @FreshResidual.partition_nonempty
#print axioms FreshResidual.partition_nonempty
#check @FreshResidual.partition_block_nodup
#print axioms FreshResidual.partition_block_nodup
#check @FreshResidual.restriction_materialized
#print axioms FreshResidual.restriction_materialized
#check @FreshResidual.materialized_length_aux
#print axioms FreshResidual.materialized_length_aux
#check @FreshResidual.sourceForest_length
#print axioms FreshResidual.sourceForest_length
#check @FreshResidual.materialized_flatten_aux
#print axioms FreshResidual.materialized_flatten_aux
#check @FreshResidual.partition_labels_perm
#print axioms FreshResidual.partition_labels_perm
#check @FreshResidual.sourceForest_partition
#print axioms FreshResidual.sourceForest_partition
#check @FreshResidual.sourceForest_proper
#print axioms FreshResidual.sourceForest_proper
