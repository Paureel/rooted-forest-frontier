import Projection
namespace OrdinaryCommonSplit
open RMAF RestrictionBridge Universal233.CoreGraph

theorem split_ne (labels X Y : List Nat) (hp : partitionCheck labels [X,Y]=true) : X≠Y := by
  have nd := checked_family_nodup labels [X,Y] hp
  simpa using (List.nodup_cons.1 nd).1

theorem split_disjoint (labels X Y : List Nat) (hp : partitionCheck labels [X,Y]=true) :
    ∀x,x∈X→x∉Y :=
  BinaryExchange.parent_disjoint labels [X,Y] hp X Y (by simp) (by simp) (split_ne labels X Y hp)

theorem split_labels (labels X Y : List Nat) (hp : partitionCheck labels [X,Y]=true) (x : Nat) :
    x∈labels ↔ x∈X ∨ x∈Y := by
  have h := BinaryExchange.partition_mem labels [X,Y] hp x
  simpa only [List.flatten_cons,List.flatten_nil,List.append_nil,List.mem_append] using h.symm

theorem Port.labels_of_cut (c : Port) (u : Tree) (X Y : List Nat)
    (nd : (leaves (c.plug u)).Nodup) (hp : partitionCheck (leaves (c.plug u)) [X,Y]=true)
    (hy : (leaves u).Perm Y) : ∀x,x∈c.labels ↔ x∈X := by
  have ndc := List.nodup_append.1 ((c.leaves_perm u).nodup_iff.1 nd)
  have disj := split_disjoint _ X Y hp
  intro x
  constructor
  · intro hx
    have hfull : x∈leaves (c.plug u) := (c.leaves_perm u).mem_iff.2 (List.mem_append_left _ hx)
    rcases (split_labels _ X Y hp x).1 hfull with hxX | hxY
    · exact hxX
    · exact False.elim (ndc.2.2 x hx x (hy.mem_iff.2 hxY) rfl)
  · intro hx
    have hfull : x∈leaves (c.plug u) := (split_labels _ X Y hp x).2 (Or.inl hx)
    rcases List.mem_append.1 ((c.leaves_perm u).mem_iff.1 hfull) with hxC | hxU
    · exact hxC
    · exact False.elim (disj x hx (hy.mem_iff.1 hxU))

/-- Actual common-cut input, with both possible descendant-side orientations.
Only literal original address/labels are fields; no coverage, projection,
gluing, minimum or runtime property is assumed. -/
def OriginalSplit (T : Tree) (X Y : List Nat) : Prop :=
  ∃ p u, p≠[] ∧ subtree T p=some u ∧ ((leaves u).Perm Y ∨ (leaves u).Perm X)

theorem split_filter_perm (labels X Y B : List Nat)
    (hp : partitionCheck labels [X,Y]=true) (sub : B⊆labels) :
    (B.filter (X.contains ·)++B.filter (Y.contains ·)).Perm B := by
  have hf : B.filter (Y.contains ·)=B.filter (fun x => !(X.contains x)) := by
    apply List.filter_congr
    intro x hx
    have hcover := (split_labels labels X Y hp x).1 (sub hx)
    have hd := split_disjoint labels X Y hp x
    by_cases hxX : x∈X
    · have hxY : x∉Y := hd hxX
      simp [hxX,hxY]
    · have hxY : x∈Y := hcover.elim (fun h => False.elim (hxX h)) id
      simp [hxX,hxY]
  rw [hf]
  exact List.filter_append_perm _ _

theorem restrict_split_filters (T : Tree) (labels X Y B : List Nat)
    (hp : partitionCheck labels [X,Y]=true) (sub : B⊆labels) :
    restrict (B.filter (X.contains ·)++B.filter (Y.contains ·)) T=restrict B T :=
  Universal233.DepthOne.restrict_members _ _ _
    (fun _ => (split_filter_perm labels X Y B hp sub).mem_iff)
end OrdinaryCommonSplit
