import CoarsenMinimalV4
open RMAF ForestState Universal233 Universal233.HardParent
namespace IndependentGeometry

def coarsen (a b z : Nat) (F : List (List Nat)) :=
 (F.map (shrinkBlock a b z)).filter (fun B=>!B.isEmpty)

theorem shrink_rest (rest : List Nat) (a b z : Nat) (na : a∉rest) (nb : b∉rest) :
 shrinkBlock a b z rest=rest := by
 induction rest with
 | nil => rfl
 | cons x xs ih =>
  have xa : x≠a := by intro e;exact na (by simp [e])
  have xb : x≠b := by intro e;exact nb (by simp [e])
  have ta : a∉xs := fun h=>na (by simp [h])
  have tb : b∉xs := fun h=>nb (by simp [h])
  simpa [shrinkBlock,xa,xb] using congrArg (x::·) (ih ta tb)

theorem shrink_labels {a b z : Nat} {T : Tree} (hc : HasCherry a b T)
 (hn : (leaves T).Nodup) : (shrinkBlock a b z (leaves T)).Perm (leaves (contract a b z T)) := by
 obtain ⟨rest,old,new⟩ := IndependentCommon.contraction_normal hc z hn
 have nd := old.nodup hn
 have ab : a≠b := by intro e;exact (List.nodup_cons.1 nd).1 (by simp [e])
 have ar : a∉rest := fun ha=>(List.nodup_cons.1 nd).1 (by simp [ha])
 have br : b∉rest := (List.nodup_cons.1 (List.nodup_cons.1 nd).2).1
 have mapped := List.Perm.map (fun x=>if x==a then z else x)
   (List.Perm.filter (fun x=>x != b) old)
 have norm : shrinkBlock a b z (a::b::rest)=z::rest := by
  simpa [shrinkBlock,ab] using congrArg (z::·) (shrink_rest rest a b z ar br)
 exact (show (shrinkBlock a b z (leaves T)).Perm (z::rest) from norm ▸ mapped).trans new.symm

theorem shrink_flatten (F : List (List Nat)) (a b z : Nat) :
 (F.map (shrinkBlock a b z)).flatten=shrinkBlock a b z F.flatten := by
 induction F with
 | nil => rfl
 | cons B rest ih => simp [List.flatten_cons,ih,shrinkBlock,List.filter_append,List.map_append]

theorem nonempty_flatten (F : List (List Nat)) :
 (F.filter (fun B=>!B.isEmpty)).flatten=F.flatten := by
 induction F with
 | nil => rfl
 | cons B rest ih => cases B <;> simp [ih]

theorem coarsen_length (F : List (List Nat)) (a b z : Nat) :
 (coarsen a b z F).length≤F.length := by
 simpa only [coarsen,List.length_map] using List.length_filter_le (fun B : List Nat=>!B.isEmpty) (F.map (shrinkBlock a b z))

theorem coarsen_partition {a b z : Nat} {T : Tree} (hc : HasCherry a b T)
 (hn : (leaves T).Nodup) (fresh : z∉leaves T) (F : List (List Nat))
 (hp : partitionCheck (leaves T) F=true) :
 partitionCheck (leaves (contract a b z T)) (coarsen a b z F)=true := by
 have orig := IndependentCommon.flatten_from_partition _ _ hn hp
 have mapped := List.Perm.map (fun x=>if x==a then z else x)
   (List.Perm.filter (fun x=>x != b) orig)
 have same : (coarsen a b z F).flatten.Perm (leaves (contract a b z T)) := by
  rw [coarsen,nonempty_flatten,shrink_flatten]
  exact mapped.trans (shrink_labels hc hn)
 apply IndependentCommon.partition_from_flatten _ _
  (IndependentCommon.contraction_unique_and_smaller hc hn fresh).1 ?_ same
 intro B hB
 have hb := (List.mem_filter.1 hB).2
 intro empty
 simp [empty] at hb
end IndependentGeometry
