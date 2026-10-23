/- Independent leaf-multiset proof of contraction invariants. -/
import ControlFlowV4
open RMAF ForestState Universal233 Universal233.HardParent
namespace IndependentCommon

theorem syntax_labels {a b : Nat} {T : Tree} (hc : HasCherry a b T) :
 a∈leaves T ∧ b∈leaves T := by
 induction hc with
 | here => simp [leaves]
 | swap => simp [leaves]
 | left h ih => exact ⟨by simp [leaves,ih.1],by simp [leaves,ih.2]⟩
 | right h ih => exact ⟨by simp [leaves,ih.1],by simp [leaves,ih.2]⟩

theorem syntax_not_leaf {a b : Nat} {T : Tree} (hc : HasCherry a b T) (x : Nat) :
 T≠.leaf x := by
 intro eq
 cases eq
 cases hc

theorem contract_absent (T : Tree) (a b z : Nat) (na : a∉leaves T) :
 contract a b z T=T := by
 induction T with
 | leaf x => rfl
 | node l r il ir =>
  have nl : a∉leaves l := fun hx=>na (by simp [leaves,hx])
  have nr : a∉leaves r := fun hx=>na (by simp [leaves,hx])
  have guard : ((l==.leaf a && r==.leaf b)||(l==.leaf b && r==.leaf a))=false := by
   cases h : ((l==.leaf a && r==.leaf b)||(l==.leaf b && r==.leaf a)) with
   | false => rfl
   | true =>
    simp only [Bool.or_eq_true,Bool.and_eq_true,beq_iff_eq] at h
    rcases h with ⟨hl,_⟩|⟨_,hr⟩
    · exact False.elim (nl (by simp [hl,leaves]))
    · exact False.elim (nr (by simp [hr,leaves]))
  simp [contract,guard,il nl,ir nr]

theorem contraction_normal {a b : Nat} {T : Tree} (hc : HasCherry a b T)
 (z : Nat) (hn : (leaves T).Nodup) : ∃ rest : List Nat,
 (leaves T).Perm (a::b::rest) ∧ (leaves (contract a b z T)).Perm (z::rest) := by
 induction hc with
 | here => exact ⟨[],by simp [leaves],by simp [contract,leaves]⟩
 | swap =>
  refine ⟨[],?_,by simp [contract,leaves]⟩
  simpa [leaves] using (List.Perm.swap a b [])
 | @left l r hc ih =>
  have parts := List.nodup_append.1 (show (leaves l++leaves r).Nodup from hn)
  obtain ⟨rest,old,new⟩ := ih parts.1
  have absent : a∉leaves r := fun hr=>parts.2.2 a (syntax_labels hc).1 a hr rfl
  have fixed := contract_absent r a b z absent
  have la := syntax_not_leaf hc a
  have lb := syntax_not_leaf hc b
  have guard : ((l==.leaf a && r==.leaf b)||(l==.leaf b && r==.leaf a))=false := by simp [la,lb]
  refine ⟨rest++leaves r,?_,?_⟩
  · simpa [leaves] using List.Perm.append_right (leaves r) old
  · simpa [contract,guard,leaves,fixed] using List.Perm.append_right (leaves r) new
 | @right l r hc ih =>
  have parts := List.nodup_append.1 (show (leaves l++leaves r).Nodup from hn)
  obtain ⟨rest,old,new⟩ := ih parts.2.1
  have absent : a∉leaves l := fun hl=>parts.2.2 a hl a (syntax_labels hc).1 rfl
  have fixed := contract_absent l a b z absent
  have ra := syntax_not_leaf hc a
  have rb := syntax_not_leaf hc b
  have guard : ((l==.leaf a && r==.leaf b)||(l==.leaf b && r==.leaf a))=false := by simp [ra,rb]
  refine ⟨rest++leaves l,?_,?_⟩
  · have p := (List.Perm.append_left (leaves l) old).trans List.perm_append_comm
    simpa [leaves] using p
  · have p := (List.Perm.append_left (leaves l) new).trans List.perm_append_comm
    simpa [contract,guard,leaves,fixed] using p

theorem contraction_unique_and_smaller {a b z : Nat} {T : Tree}
 (hc : HasCherry a b T) (hn : (leaves T).Nodup) (fresh : z∉leaves T) :
 (leaves (contract a b z T)).Nodup ∧
 (leaves (contract a b z T)).length+1=(leaves T).length := by
 obtain ⟨rest,old,new⟩ := contraction_normal hc z hn
 have nd := old.nodup hn
 have nr : rest.Nodup := (List.nodup_cons.1 (List.nodup_cons.1 nd).2).2
 have nz : z∉rest := by
  intro hz
  apply fresh
  exact old.mem_iff.2 (by simp [hz])
 have clean : (z::rest).Nodup := List.nodup_cons.2 ⟨nz,nr⟩
 refine ⟨new.symm.nodup clean,?_⟩
 have h1 := old.length_eq
 have h2 := new.length_eq
 simp only [List.length_cons] at h1 h2
 omega

theorem contraction_pair {a b z : Nat} {T S : Tree}
 (ct : HasCherry a b T) (cs : HasCherry a b S)
 (hp : DepthOne.proper T S=true) (fresh : z∉leaves T) :
 DepthOne.proper (contract a b z T) (contract a b z S)=true ∧
 (leaves (contract a b z T)).length<(leaves T).length := by
 obtain ⟨nt,ns,perm⟩ := IndependentReconstruction.proper_parts hp
 have fS : z∉leaves S := fun hz=>fresh (perm.mem_iff.2 hz)
 have tInv := contraction_unique_and_smaller ct nt fresh
 have sInv := contraction_unique_and_smaller cs ns fS
 obtain ⟨rt,ot,ct'⟩ := contraction_normal ct z nt
 obtain ⟨rs,os,cs'⟩ := contraction_normal cs z ns
 have cancel : rt.Perm rs := (ot.symm.trans (perm.trans os)).cons_inv.cons_inv
 have reduced : (leaves (contract a b z T)).Perm (leaves (contract a b z S)) :=
  ct'.trans ((List.Perm.cons z cancel).trans cs'.symm)
 constructor
 · simpa only [DepthOne.proper,Bool.and_eq_true,decide_eq_true_eq,and_assoc] using
    And.intro tInv.1 (And.intro sInv.1 reduced)
 · omega

theorem maximum_bound (L : List Nat) {x : Nat} (hx : x∈L) :
 x≤OrdinaryCommonSplit.Source.labelMax L := by
 induction L with
 | nil => simp at hx
 | cons y ys ih =>
  rcases List.mem_cons.1 hx with rfl|hx
  · exact Nat.le_max_left _ _
  · exact Nat.le_trans (ih hx) (Nat.le_max_right _ _)

theorem common_fresh (T : Tree) : OrdinaryDispatch.commonFresh T∉leaves T := by
 intro member
 have bound := maximum_bound (leaves T) member
 unfold OrdinaryDispatch.commonFresh at bound
 omega

theorem duplicate_uniqueness_required :
 let T := Tree.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 0) (.leaf 1))
 (leaves (contract 0 1 3 T)).length+1≠(leaves T).length := by decide

theorem fresh_name_required :
 ¬(leaves (contract 0 1 2 (.node (.node (.leaf 0) (.leaf 1)) (.leaf 2)))).Nodup := by decide

example : leaves (contract 0 1 3 (.node (.node (.leaf 0) (.leaf 1)) (.leaf 2)))=[3,2] := rfl
example : leaves (contract 0 1 3 (.node (.leaf 2) (.node (.leaf 1) (.leaf 0))))=[2,3] := rfl
end IndependentCommon
