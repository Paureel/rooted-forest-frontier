/- Reused own frozen proof body; slim import slice, permanently CONTACTED. -/
/- Actual common expansion validity, assembled from independent geometry. -/
import SlimHullProjectionV7
open RMAF ForestState Universal233 Universal233.HardParent
namespace IndependentGeometry

theorem grow_fixed (T : Tree) {a b z : Nat}
 (na : a∉leaves T) (nb : b∉leaves T) (nz : z∉leaves T) : Grow a b z T T := by
 induction T with
 | leaf x =>
  refine .fixed ?_ ?_ ?_
  · simpa [leaves,eq_comm] using na
  · simpa [leaves,eq_comm] using nb
  · simpa [leaves,eq_comm] using nz
 | node l r il ir =>
  have pa : a∉leaves l ∧ a∉leaves r := by simpa [leaves] using na
  have pb : b∉leaves l ∧ b∉leaves r := by simpa [leaves] using nb
  have pz : z∉leaves l ∧ z∉leaves r := by simpa [leaves] using nz
  exact .node (il pa.1 pb.1 pz.1) (ir pa.2 pb.2 pz.2)

theorem actual_grow {a b z : Nat} {T : Tree} (hc : HasCherry a b T)
 (hn : (leaves T).Nodup) (fresh : z∉leaves T) : Grow a b z (contract a b z T) T := by
 induction hc with
 | here => simpa [contract] using (Grow.cherry (a:=a) (b:=b) (z:=z))
 | swap => simpa [contract] using (Grow.swapped (a:=a) (b:=b) (z:=z))
 | @left l r hc ih =>
  have parts := List.nodup_append.1 (show (leaves l++leaves r).Nodup from hn)
  have ar : a∉leaves r := fun hr=>parts.2.2 a (IndependentCommon.syntax_labels hc).1 a hr rfl
  have br : b∉leaves r := fun hr=>parts.2.2 b (IndependentCommon.syntax_labels hc).2 b hr rfl
  have zl : z∉leaves l := fun hz=>fresh (by simp [leaves,hz])
  have zr : z∉leaves r := fun hz=>fresh (by simp [leaves,hz])
  have la := IndependentCommon.syntax_not_leaf hc a
  have lb := IndependentCommon.syntax_not_leaf hc b
  have guard : ((l==.leaf a && r==.leaf b)||(l==.leaf b && r==.leaf a))=false := by simp [la,lb]
  simpa [contract,guard,IndependentCommon.contract_absent r a b z ar] using
   Grow.node (ih parts.1 zl) (grow_fixed r ar br zr)
 | @right l r hc ih =>
  have parts := List.nodup_append.1 (show (leaves l++leaves r).Nodup from hn)
  have al : a∉leaves l := fun hl=>parts.2.2 a hl a (IndependentCommon.syntax_labels hc).1 rfl
  have bl : b∉leaves l := fun hl=>parts.2.2 b hl b (IndependentCommon.syntax_labels hc).2 rfl
  have zl : z∉leaves l := fun hz=>fresh (by simp [leaves,hz])
  have zr : z∉leaves r := fun hz=>fresh (by simp [leaves,hz])
  have ra := IndependentCommon.syntax_not_leaf hc a
  have rb := IndependentCommon.syntax_not_leaf hc b
  have guard : ((l==.leaf a && r==.leaf b)||(l==.leaf b && r==.leaf a))=false := by simp [ra,rb]
  simpa [contract,guard,IndependentCommon.contract_absent l a b z al] using
   Grow.node (grow_fixed l al bl zl) (ih parts.2.1 zr)

theorem grow_no_endpoints {a b z : Nat} {C T : Tree} (h : Grow a b z C T)
 (az : a≠z) (bz : b≠z) : a∉leaves C ∧ b∉leaves C := by
 induction h with
 | fixed xa xb xz => simp [leaves,Ne.symm xa,Ne.symm xb]
 | cherry => simp [leaves,az,bz]
 | swapped => simp [leaves,az,bz]
 | node hl hr il ir => simpa [leaves] using And.intro (And.intro il.1 ir.1) (And.intro il.2 ir.2)

theorem block_no_endpoints {a b : Nat} {C : Tree} {G : List (List Nat)}
 (na : a∉leaves C) (nb : b∉leaves C) (hp : partitionCheck (leaves C) G=true)
 {B : List Nat} (hB : B∈G) : a∉B ∧ b∉B := by
 have allG : ∀ x∈G.flatten,x∈leaves C := by
  simp only [partitionCheck,Bool.and_eq_true] at hp
  intro x hx
  exact List.contains_iff_mem.1 (List.all_eq_true.1 hp.2 x hx)
 constructor
 · intro ha;exact na (allG a (List.mem_flatten.2 ⟨B,hB,ha⟩))
 · intro hb;exact nb (allG b (List.mem_flatten.2 ⟨B,hB,hb⟩))

theorem disjoint_expand {a b z : Nat} {C T : Tree} (gt : Grow a b z C T)
 {B D : List Nat} (ba : a∉B) (bb : b∉B) (da : a∉D) (db : b∉D)
 (h : disjointVertices (minimalVertices B C) (minimalVertices D C)=true) :
 disjointVertices (minimalVertices (expandBlock a b z B) T)
   (minimalVertices (expandBlock a b z D) T)=true := by
 apply List.all_eq_true.2
 intro v hv
 cases hd : (minimalVertices (expandBlock a b z D) T).contains v with
 | false => rfl
 | true =>
  have pb := minimal_projects gt B ba bb v hv
  have pd := minimal_projects gt D da db v (List.contains_iff_mem.1 hd)
  have no := List.all_eq_true.1 h (project C v) pb
  have yes : (minimalVertices D C).contains (project C v)=true := List.contains_iff_mem.2 pd
  simp at no
  exact False.elim (no pd)

theorem pairwise_expand {a b z : Nat} {C T : Tree} (gt : Grow a b z C T)
 (G : List (List Nat)) (noAB : ∀B∈G,a∉B ∧ b∉B)
 (h : pairwiseEmbeddings C G=true) :
 pairwiseEmbeddings T (G.map (expandBlock a b z))=true := by
 induction G with
 | nil => rfl
 | cons B rest ih =>
  simp only [pairwiseEmbeddings,Bool.and_eq_true] at h
  simp only [List.map_cons,pairwiseEmbeddings,Bool.and_eq_true]
  constructor
  · apply List.all_eq_true.2
    intro E hE
    obtain ⟨D,hD,rfl⟩ := List.mem_map.1 hE
    have bn := noAB B (by simp)
    have dn := noAB D (by simp [hD])
    exact disjoint_expand gt bn.1 bn.2 dn.1 dn.2 (List.all_eq_true.1 h.1 D hD)
  · exact ih (fun D hD=>noAB D (by simp [hD])) h.2

theorem common_expansion {a b z : Nat} {T U : Tree}
 (ht : HasCherry a b T) (hu : HasCherry a b U)
 (hp : DepthOne.proper T U=true) (fresh : z∉leaves T) (G : List (List Nat))
 (h : agreement (contract a b z T) (contract a b z U) G=true) :
 agreement T U (G.map (expandBlock a b z))=true := by
 obtain ⟨nt,nu,perm⟩ := IndependentReconstruction.proper_parts hp
 have fu : z∉leaves U := fun hz=>fresh (perm.mem_iff.2 hz)
 have gt := actual_grow ht nt fresh
 have gu := actual_grow hu nu fu
 have az : a≠z := by intro eq;exact fresh (eq ▸ (IndependentCommon.syntax_labels ht).1)
 have bz : b≠z := by intro eq;exact fresh (eq ▸ (IndependentCommon.syntax_labels ht).2)
 have no := grow_no_endpoints gt az bz
 simp only [agreement,Bool.and_eq_true] at h ⊢
 have noAB : ∀B∈G,a∉B ∧ b∉B := fun B hB=>block_no_endpoints no.1 no.2 h.1.1.1.1 hB
 refine ⟨⟨⟨⟨IndependentCommon.expanded_partition ht nt fresh G h.1.1.1.1,
  IndependentCommon.expanded_partition hu nu fu G h.1.1.1.2⟩,?_⟩,
  pairwise_expand gt G noAB h.1.2⟩,pairwise_expand gu G noAB h.2⟩
 apply List.all_eq_true.2
 intro E hE
 obtain ⟨B,hB,rfl⟩ := List.mem_map.1 hE
 exact restriction_agrees_grow gt gu B (noAB B hB).1 (noAB B hB).2
  (List.all_eq_true.1 h.1.1.2 B hB)

end IndependentGeometry

-- Author integration type/axiom reports; proof text above is unchanged apart from recorded import edits.
set_option pp.universes true
#check @IndependentGeometry.grow_fixed
#print axioms IndependentGeometry.grow_fixed
#check @IndependentGeometry.actual_grow
#print axioms IndependentGeometry.actual_grow
#check @IndependentGeometry.grow_no_endpoints
#print axioms IndependentGeometry.grow_no_endpoints
#check @IndependentGeometry.block_no_endpoints
#print axioms IndependentGeometry.block_no_endpoints
#check @IndependentGeometry.disjoint_expand
#print axioms IndependentGeometry.disjoint_expand
#check @IndependentGeometry.pairwise_expand
#print axioms IndependentGeometry.pairwise_expand
#check @IndependentGeometry.common_expansion
#print axioms IndependentGeometry.common_expansion
