/- Independently reconstruct label-partition transport under actual expandBlock.
Restriction isomorphism, original-hull separation and coarsening stay open. -/
import CommonRuleV2
open RMAF ForestState Universal233 Universal233.HardParent
namespace IndependentCommon

def leafExpansion (a b z x : Nat) : List Nat := if x==z then [a,b] else [x]

theorem flatten_from_partition (L : List Nat) (G : List (List Nat)) (hn : L.Nodup)
 (hp : partitionCheck L G=true) : G.flatten.Perm L := by
 simp only [partitionCheck,Bool.and_eq_true] at hp
 apply List.perm_iff_count.2
 intro x
 by_cases mem : x∈L
 · have count : G.flatten.count x=1 := beq_iff_eq.1 (List.all_eq_true.1 hp.1.2 x mem)
   rw [count,hn.count_of_mem mem]
 · have noG : x∉G.flatten := by
    intro hG
    exact mem (List.contains_iff.1 (List.all_eq_true.1 hp.2 x hG))
   rw [List.count_eq_zero_of_not_mem noG,List.count_eq_zero_of_not_mem mem]

theorem partition_from_flatten (L : List Nat) (G : List (List Nat)) (hn : L.Nodup)
 (nonempty : ∀ B∈G,B≠[]) (same : G.flatten.Perm L) : partitionCheck L G=true := by
 simp only [partitionCheck,Bool.and_eq_true]
 refine ⟨⟨?_,?_⟩,?_⟩
 · apply List.all_eq_true.2
   intro B hB
   simp [nonempty B hB]
 · apply List.all_eq_true.2
   intro x hx
   exact beq_iff_eq.2 ((same.count_eq x).trans (hn.count_of_mem hx))
 · apply List.all_eq_true.2
   intro x hx
   exact List.contains_iff.2 (same.mem_iff.1 hx)

theorem expanded_flatten (G : List (List Nat)) (a b z : Nat) :
 (G.map (expandBlock a b z)).flatten=G.flatten.flatMap (leafExpansion a b z) := by
 induction G with
 | nil => rfl
 | cons B rest ih =>
  simp only [List.map_cons,List.flatten_cons,ih,List.flatMap_append]
  rfl

theorem expansion_fixes_rest (rest : List Nat) (a b z : Nat) (fresh : z∉rest) :
 rest.flatMap (leafExpansion a b z)=rest := by
 induction rest with
 | nil => rfl
 | cons x xs ih =>
  have xz : x≠z := by intro e; exact fresh (by simp [e])
  have tail : z∉xs := fun hz=>fresh (by simp [hz])
  simp [leafExpansion,xz,ih tail]

theorem expanded_partition {a b z : Nat} {T : Tree} (hc : HasCherry a b T)
 (hn : (leaves T).Nodup) (fresh : z∉leaves T) (G : List (List Nat))
 (hp : partitionCheck (leaves (contract a b z T)) G=true) :
 partitionCheck (leaves T) (G.map (expandBlock a b z))=true := by
 obtain ⟨rest,original,contracted⟩ := contraction_normal hc z hn
 have nc := (contraction_unique_and_smaller hc hn fresh).1
 have pG := flatten_from_partition _ G nc hp
 have restFresh : z∉rest := by
  intro hz
  exact fresh (original.mem_iff.2 (by simp [hz]))
 have replaced : (z::rest).flatMap (leafExpansion a b z)=a::b::rest := by
  simp [leafExpansion,expansion_fixes_rest rest a b z restFresh]
 have expandPerm := List.Perm.flatMap_right (leafExpansion a b z) (pG.trans contracted)
 have exactLabels : (G.map (expandBlock a b z)).flatten.Perm (leaves T) := by
  rw [expanded_flatten]
  exact (replaced ▸ expandPerm).trans original.symm
 have nonempty : ∀ B∈G,B≠[] := by
  intro B hB empty
  have allB : G.all (fun B=>!B.isEmpty)=true := by
   simp only [partitionCheck,Bool.and_eq_true] at hp
   exact hp.1.1
  have check := List.all_eq_true.1 allB B hB
  simp [empty] at check
 apply partition_from_flatten _ _ hn ?_ exactLabels
 intro D hD
 obtain ⟨B,hB,rfl⟩ := List.mem_map.1 hD
 cases B with
 | nil => exact False.elim (nonempty [] hB rfl)
 | cons x rest =>
  by_cases xz : x=z <;> simp [expandBlock,xz]
end IndependentCommon
