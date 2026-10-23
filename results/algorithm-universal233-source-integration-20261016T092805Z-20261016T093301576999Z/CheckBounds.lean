import CheckAssembly
namespace GenericForest.CheckCorrespondence
open RMAF ForestState RestrictionBridge Universal233 WholeSourceWork CoreWork

theorem pow_mono (N a b : Nat) (h : a≤b) : (N+1)^a≤(N+1)^b :=
 Nat.pow_le_pow_right (by omega) h
theorem cap_lift (N k a b x : Nat) (h : x≤k*(N+1)^a) (ab : a≤b) : x≤k*(N+1)^b :=
 Nat.le_trans h (Nat.mul_le_mul_left k (pow_mono N a b ab))
theorem cap_all {α : Type} (f : α→Charged Bool) (xs : List α) (N k p : Nat)
 (len : xs.length≤N) (point : ∀x∈xs,(f x).work≤k*(N+1)^p) :
 (meterAll f xs).work≤(k+4)*(N+1)^(p+1) := by
 have h:=meterAll_bound f xs (k*(N+1)^p) point
 have pos : 1≤(N+1)^p:=Nat.one_le_pow _ _ (by omega)
 have coef : k*(N+1)^p+4≤(k+4)*(N+1)^p:=by simp only [Nat.add_mul];omega
 have product:=Nat.mul_le_mul coef (Nat.add_le_add_right len 1)
 exact Nat.le_trans h (by simpa only [Nat.pow_succ,Nat.mul_assoc] using product)
theorem cap_any {α : Type} (f : α→Charged Bool) (xs : List α) (N k p : Nat)
 (len : xs.length≤N) (point : ∀x∈xs,(f x).work≤k*(N+1)^p) :
 (meterAny f xs).work≤(k+4)*(N+1)^(p+1) := by
 have h:=meterAny_bound f xs (k*(N+1)^p) point
 have pos : 1≤(N+1)^p:=Nat.one_le_pow _ _ (by omega)
 have coef : k*(N+1)^p+4≤(k+4)*(N+1)^p:=by simp only [Nat.add_mul];omega
 have product:=Nat.mul_le_mul coef (Nat.add_le_add_right len 1)
 exact Nat.le_trans h (by simpa only [Nat.pow_succ,Nat.mul_assoc] using product)

theorem meterLeaves_cap (T : Tree) (N : Nat) (tn : treeNodes T≤N) :
 (meterLeaves T).work≤8*(N+1)^2 := by
 have h:=meterLeaves_bound T N tn
 have k:=Nat.mul_le_mul_left (8*(N+1)) (Nat.le_trans tn (Nat.le_succ N))
 exact Nat.le_trans h (by simpa only [Nat.pow_two,Nat.mul_assoc] using k)
theorem meterLabels_cap (T : Option Tree) (N : Nat) (tn : targetNodes T≤N) :
 (meterLabels T).work≤8*(N+1)^2 := by
 cases T with
 | none=>have pos : 1≤(N+1)^2:=Nat.one_le_pow _ _ (by omega);simp only [meterLabels];omega
 | some t=>exact meterLeaves_cap t N tn

theorem labels_nodes (T : Option Tree) : (labels T).length≤targetNodes T := by
 cases T with
 | none=>simp [labels,targetNodes]
 | some t=>exact leaves_nodes t

theorem block_cells (F : Forest) (B : List Nat) (h : B∈F) : B.length≤F.flatten.length := by
 induction F with
 | nil=>simp at h
 | cons C F ih=>
  simp only [List.mem_cons] at h
  rcases h with rfl|h
  · simp
  · have a:=ih h;simp only [List.flatten_cons,List.length_append];omega

theorem meterFamily_cap (U : List Nat) (F : Forest) (N : Nat)
 (ul : U.length≤N) (fl : F.length≤N) (cells : F.flatten.length≤N) :
 (meterFamily U F).work≤14*(N+1)^3 := by
 have h:=meterFamily_bound U F N ul (fun B hb=>Nat.le_trans (block_cells F B hb) cells)
 have pos : 1≤(N+1)^2:=Nat.one_le_pow _ _ (by omega)
 have coef : 8*(N+1)^2+6≤14*(N+1)^2:=by omega
 have k:=Nat.mul_le_mul coef (Nat.add_le_add_right fl 1)
 exact Nat.le_trans h (by simpa only [Nat.pow_succ,Nat.mul_assoc] using k)

theorem meterProper_cap (T : Option Tree) (ss : List Tree) (N : Nat)
 (tn : targetNodes T≤N) (sn : sourceNodes ss≤N) (sl : ss.length≤N) :
 (meterProper T ss).work≤164*(N+1)^3 := by
 have lab : (labels T).length≤N:=Nat.le_trans (labels_nodes T) tn
 have a:=cap_lift N 8 2 3 _ (meterLabels_cap T N tn) (by decide)
 have b0:=meterNodup_bound (labels T)
 have b1:=Nat.mul_le_mul_left 8 (Nat.pow_le_pow_left (Nat.add_le_add_right lab 1) 2)
 have b:=cap_lift N 8 2 3 _ (Nat.le_trans b0 b1) (by decide)
 have c0:=meterSourceLeaves_bound ss N sn
 have c1:=Nat.mul_le_mul_left (8*(N+1)) (Nat.le_trans sn (Nat.le_succ N))
 have c2 : (meterSourceLeaves ss).work≤13*(N+1)^2:=by
  have p:=pow_mono N 1 2 (by decide)
  simp only [Nat.pow_one] at p
  simp only [Nat.succ_eq_add_one,Nat.pow_two,Nat.mul_assoc] at c0 c1 p ⊢
  omega
 have c:=cap_lift N 13 2 3 _ c2 (by decide)
 have d0:=meterPartition_bound (labels T) (ss.map leaves) N lab (by simpa using sl)
   (Nat.le_trans (source_leaves_cells ss) sn)
 have d:=cap_lift N 128 2 3 _ d0 (by decide)
 have pos : 1≤(N+1)^3:=Nat.one_le_pow _ _ (by omega)
 simp only [meterProper,meterLabels_value,meterSourceLeaves_value];omega

theorem meterTargetAgrees_cap (T : Option Tree) (s : Tree) (B : List Nat) (N : Nat)
 (tn : targetNodes T≤N) (sn : treeNodes s≤N) (bl : B.length≤N) :
 (meterTargetAgrees T s B).work≤128*(N+1)^2 := by
 cases T with
 | none=>have pos : 1≤(N+1)^2:=Nat.one_le_pow _ _ (by omega);simp only [meterTargetAgrees];omega
 | some t=>exact meterRestrictionAgrees_bound t s B N (by change treeNodes t≤N at tn;omega) (by omega) bl

theorem meterTargetEmbeddings_cap (T : Option Tree) (F : Forest) (N : Nat)
 (tn : targetNodes T≤N) (fl : F.length≤N) (cells : F.flatten.length≤N) :
 (meterTargetEmbeddings T F).work≤120*(N+1)^5 := by
 cases T with
 | none=>have pos : 1≤(N+1)^5:=Nat.one_le_pow _ _ (by omega);simp only [meterTargetEmbeddings];omega
 | some t=>
  exact meterPairwise_polynomial t F N tn (Nat.le_trans (leaves_nodes t) tn) fl
    (fun B hb=>Nat.le_trans (block_cells F B hb) cells)

theorem meterSourceCheck_cap (T : Option Tree) (F : Forest) (s : Tree) (N : Nat)
 (tn : targetNodes T≤N) (sn : treeNodes s≤N) (fl : F.length≤N) (cells : F.flatten.length≤N) :
 (meterSourceCheck T F s).work≤418*(N+1)^5 := by
 have sl:=Nat.le_trans (leaves_nodes s) sn
 have gfl:=Nat.le_trans (family_length (leaves s) F) fl
 have gcells:=Nat.le_trans (family_cells (leaves s) F) cells
 have a:=cap_lift N 8 2 5 _ (meterLeaves_cap s N sn) (by decide)
 have g:=cap_lift N 14 3 5 _ (meterFamily_cap (leaves s) F N sl fl cells) (by decide)
 have p0:=meterPartition_bound (leaves s) (family (leaves s) F) N sl gfl gcells
 have p:=cap_lift N 128 2 5 _ p0 (by decide)
 have r0:=cap_all (meterTargetAgrees T s) (family (leaves s) F) N 128 2 gfl
   (fun B hb=>meterTargetAgrees_cap T s B N tn sn (Nat.le_trans (block_cells _ B hb) gcells))
 have r:=cap_lift N 132 3 5 _ r0 (by decide)
 have e:=meterPairwise_polynomial s (family (leaves s) F) N sn sl gfl
   (fun B hb=>Nat.le_trans (block_cells _ B hb) gcells)
 have pos : 1≤(N+1)^5:=Nat.one_le_pow _ _ (by omega)
 simp only [meterSourceCheck,meterLeaves_value,meterFamily_value];omega

theorem meterSourceContainment_cap (B : List Nat) (ss : List Tree) (N : Nat)
 (bl : B.length≤N) (sn : sourceNodes ss≤N) (sl : ss.length≤N) :
 (meterSourceContainment B ss).work≤22*(N+1)^3 := by
 apply cap_any _ ss N 18 2 sl
 intro s hs
 have nodes:=Nat.le_trans (source_node_member ss s hs) sn
 have a:=meterLeaves_cap s N nodes
 have b:=meterContained_bound B (leaves s) N bl (Nat.le_trans (leaves_nodes s) nodes)
 have pos : 1≤(N+1)^2:=Nat.one_le_pow _ _ (by omega)
 simp only [meterLeaves_value];omega

theorem meterAgrees_cap (T : Option Tree) (ss : List Tree) (F : Forest) (N : Nat)
 (tn : targetNodes T≤N) (sn : sourceNodes ss≤N) (sl : ss.length≤N)
 (fl : F.length≤N) (cells : F.flatten.length≤N) :
 (meterAgrees T ss F).work≤888*(N+1)^6 := by
 have p:=cap_lift N 164 3 6 _ (meterProper_cap T ss N tn sn sl) (by decide)
 have a:=cap_lift N 8 2 6 _ (meterLabels_cap T N tn) (by decide)
 have f:=cap_lift N 128 2 6 _ (meterPartition_bound (labels T) F N
   (Nat.le_trans (labels_nodes T) tn) fl cells) (by decide)
 have c0:=cap_all (fun B=>meterSourceContainment B ss) F N 22 3 fl
   (fun B hb=>meterSourceContainment_cap B ss N (Nat.le_trans (block_cells F B hb) cells) sn sl)
 have c:=cap_lift N 26 4 6 _ c0 (by decide)
 have e:=cap_lift N 120 5 6 _ (meterTargetEmbeddings_cap T F N tn fl cells) (by decide)
 have s:=cap_all (meterSourceCheck T F) ss N 418 5 sl
   (fun s hs=>meterSourceCheck_cap T F s N tn (Nat.le_trans (source_node_member ss s hs) sn) fl cells)
 change (meterAll (meterSourceCheck T F) ss).work≤422*(N+1)^6 at s
 have pos : 1≤(N+1)^6:=Nat.one_le_pow _ _ (by omega)
 simp only [meterAgrees,meterLabels_value];omega

theorem meterChecked_cap (T : Option Tree) (ss : List Tree) (q : Nat) (F : Forest) (N : Nat)
 (tn : targetNodes T≤N) (sn : sourceNodes ss≤N) (sl : ss.length≤N)
 (fl : F.length≤N) (cells : F.flatten.length≤N) :
 (meterChecked T ss q F).work≤908*(N+1)^6 := by
 have h:=meterAgrees_cap T ss F N tn sn sl fl cells
 have pos:=pow_mono N 1 6 (by decide)
 simp only [Nat.pow_one] at pos
 simp only [meterChecked,meterAccepted];omega
end GenericForest.CheckCorrespondence
