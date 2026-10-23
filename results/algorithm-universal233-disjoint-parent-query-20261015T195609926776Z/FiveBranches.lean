import UniqueCherry
namespace Universal233.Rule5Classification
open RMAF CoreGraph Integration VertexGeometry CutRealization HardParent CherryBranching Rule5Local

theorem restrictionAgrees_symm (T S : Tree) (X : List Nat) :
 restrictionAgrees T S X = restrictionAgrees S T X := by
 cases ht : restrict X T <;> cases hs : restrict X S <;> simp only [restrictionAgrees,ht,hs]
 rename_i U V
 have hh : sameShape U V = true ↔ sameShape V U = true := by
   rw [sameShape_correct,sameShape_correct]
   exact ⟨BinaryExchange.iso_symm,BinaryExchange.iso_symm⟩
 cases h1 : sameShape U V <;> cases h2 : sameShape V U <;> simp_all

theorem agreement_symm {T S : Tree} {F : List (List Nat)}
 (ha : agreement T S F = true) : agreement S T F = true := by
 have p := BinaryExchange.agreement_parts T S F ha
 have top : F.all (restrictionAgrees S T) = true := by
   apply List.all_eq_true.2
   intro B hB
   rw [←restrictionAgrees_symm]
   exact p.2.2.1 B hB
 simp only [agreement,Bool.and_eq_true]
 exact ⟨⟨⟨⟨p.2.1,p.1⟩,top⟩,(executable_pairwiseEmbeddings S F).2 p.2.2.2.2⟩,
   (executable_pairwiseEmbeddings T F).2 p.2.2.2.1⟩

def pairPartition (S : Tree) (x y : Nat) : List (List Nat) :=
 [[x],[y],(leaves S).filter fun z => z != x && z != y]
def pairChild (S : Tree) (x y : Nat) : Child := makeChild S (pairPartition S x y) 2
def fiveChildren (S : Tree) (a b p q : Nat) : List Child :=
 [pendantChild S a b,pairChild S p a,pairChild S p b,pairChild S q a,pairChild S q b]
def pairSourceBranch (S : Tree) (x y : Nat) : Option SourceBranch :=
 (terminalCut S x).bind fun u => (terminalCut S y).map fun v => ⟨pairChild S x y,[u,v]⟩

theorem pair_literal {S : Tree} {x y : Nat}
 (hx : x ∈ leaves S) (hy : y ∈ leaves S) (hne : x ≠ y) :
 ∃ u v br, pairSourceBranch S x y = some br ∧ br.child = pairChild S x y ∧
 br.originalCuts = [u,v] ∧ br.child.paid = br.originalCuts.length ∧
 LeafAt S u x ∧ LeafAt S v y ∧ u ≠ [] ∧ v ≠ [] ∧ u ≠ v := by
 obtain ⟨u,hu,hux⟩ := terminalCut_exists hx
 obtain ⟨v,hv,hvy⟩ := terminalCut_exists hy
 refine ⟨u,v,⟨pairChild S x y,[u,v]⟩,by simp [pairSourceBranch,hu,hv],rfl,rfl,rfl,hux,hvy,
   terminal_nonroot hux hy hne,terminal_nonroot hvy hx hne.symm,?_⟩
 intro e
 subst v
 unfold LeafAt at hux hvy
 rw [hux] at hvy
 exact hne (Tree.leaf.inj (Option.some.inj hvy))

/-- The two paid terminal arcs produce exactly the two singleton original
components and the original root remainder. Every residual component has a
taxon, witnessed here without suppression or an incoming root edge. -/
theorem pair_components {S : Tree} {u v : RMAF.Vertex} {x y z : Nat}
 (hu : LeafAt S u x) (hv : LeafAt S v y) (hz : z ∈ leaves S)
 (nxy : x ≠ y) (nzx : z ≠ x) (nzy : z ≠ y) :
 (∀ w, ResidualWalk S [u,v] u w ↔ w = u) ∧
 (∀ w, ResidualWalk S [u,v] v w ↔ w = v) ∧
 (∀ w, ResidualWalk S [u,v] [] w ↔ Valid S w ∧ w ≠ u ∧ w ≠ v) ∧
 (∀ w, Valid S w → ∃ t a, LeafAt S t a ∧ ResidualWalk S [u,v] w t) := by
 have hx := leafAt_label S u x hu
 have hy := leafAt_label S v y hv
 have un := terminal_nonroot hu hy nxy
 have vn := terminal_nonroot hv hx nxy.symm
 have allnr : ∀ q, q ∈ [u,v] → q ≠ [] := by
   intro q hq
   have hh : q = u ∨ q = v := by simpa using hq
   rcases hh with rfl | rfl <;> assumption
 have sing {q : RMAF.Vertex} {a : Nat} (hq : LeafAt S q a) (qm : q ∈ [u,v]) :
   ∀ w, ResidualWalk S [u,v] q w ↔ w = q := by
   intro w
   rw [region_component (Or.inr qm) hq.valid ⟨List.prefix_rfl,fun _ _ h => h⟩]
   constructor
   · rintro ⟨hw,reg⟩; exact leaf_valid_descendant hq hw reg.1
   · rintro rfl; exact ⟨hq.valid,⟨List.prefix_rfl,fun _ _ h => h⟩⟩
 have root : ∀ w, ResidualWalk S [u,v] [] w ↔ Valid S w ∧ w ≠ u ∧ w ≠ v := by
   intro w
   rw [region_component (Or.inl rfl) (valid_root S) ⟨List.prefix_rfl,fun _ _ h => h⟩,
     region_root _ _ allnr]
   constructor
   · rintro ⟨hw,live⟩
     exact ⟨hw,fun e => live u (by simp) (e ▸ List.prefix_rfl),
       fun e => live v (by simp) (e ▸ List.prefix_rfl)⟩
   · rintro ⟨hw,nu,nv⟩
     refine ⟨hw,?_⟩
     intro q hq hqw
     have hh : q = u ∨ q = v := by simpa using hq
     rcases hh with rfl | rfl
     · exact nu (leaf_valid_descendant hu hw hqw)
     · exact nv (leaf_valid_descendant hv hw hqw)
 refine ⟨sing hu (by simp),sing hv (by simp),root,?_⟩
 intro w hw
 by_cases wu : w = u
 · subst w; exact ⟨u,x,hu,.refl hu.valid⟩
 · by_cases wv : w = v
   · subst w; exact ⟨v,y,hv,.refl hv.valid⟩
   · obtain ⟨t,ht⟩ := leaf_exists hz
     have tu : t ≠ u := by
       intro e; subst t
       unfold LeafAt at hu ht
       rw [hu] at ht
       exact nzx (Tree.leaf.inj (Option.some.inj ht)).symm
     have tv : t ≠ v := by
       intro e; subst t
       unfold LeafAt at hv ht
       rw [hv] at ht
       exact nzy (Tree.leaf.inj (Option.some.inj ht)).symm
     exact ⟨t,z,ht,((root w).2 ⟨hw,wu,wv⟩).reverse.trans ((root t).2 ⟨ht.valid,tu,tv⟩)⟩

theorem pair_partition_check {S : Tree} {x y z : Nat}
 (hn : (leaves S).Nodup) (hx : x ∈ leaves S) (hy : y ∈ leaves S) (hz : z ∈ leaves S)
 (nxy : x ≠ y) (nzx : z ≠ x) (nzy : z ≠ y) :
 partitionCheck (leaves S) (pairPartition S x y) = true := by
 let C := (leaves S).filter fun z => z != x && z != y
 have ndC : C.Nodup := hn.filter _
 have zC : z ∈ C := by simp [C,hz,nzx,nzy]
 have neC : (!C.isEmpty) = true := by
   cases hc : C with
   | nil => rw [hc] at zC; contradiction
   | cons t ts => rfl
 simp only [pairPartition,partitionCheck,List.all_cons,List.all_nil,List.isEmpty_cons,
   Bool.not_false,Bool.and_true,Bool.and_eq_true]
 refine ⟨⟨⟨True.intro,True.intro,neC⟩,?_⟩,?_⟩
 · apply List.all_eq_true.2
   intro t ht
   apply beq_iff_eq.2
   simp only [List.flatten_cons,List.flatten_nil,List.append_nil,List.singleton_append]
   change (x :: y :: C).count t = 1
   by_cases tx : t = x
   · subst t
     have nx : x ∉ C := by simp [C]
     simp [List.count_append,ndC.count,nx,nxy,Ne.symm nxy]
   · by_cases ty : t = y
     · subst t
       have ny : y ∉ C := by simp [C]
       simp [List.count_append,ndC.count,ny,nxy,Ne.symm nxy]
     · have tc : t ∈ C := by simp [C,ht,tx,ty]
       simp [List.count_cons,ndC.count,tc,tx,ty,Ne.symm tx,Ne.symm ty]
 · apply List.all_eq_true.2
   intro t ht
   apply List.contains_iff_mem.2
   have hh : t = x ∨ t = y ∨ t ∈ C := by simpa [C] using ht
   rcases hh with rfl | rfl | hh
   · exact hx
   · exact hy
   · exact (List.mem_filter.1 hh).1

theorem singleton_disj_absent {S : Tree} {x : Nat} {B : List Nat}
 (hn : (leaves S).Nodup) (no : x ∉ B) : BinaryExchange.Disj S [x] B := by
 intro v ⟨hv,hw⟩
 obtain ⟨u,w,hu,hw',hp⟩ := hv
 have one : ∀ u, selectedLeaves [x] S u → LeafAt S u x := by
   intro u hu
   obtain ⟨t,ht,hs⟩ := (selected_decompose_label [x] S u).1 hu
   have e : t = x := by simpa using ht
   subst t
   exact (leafAt_selected S u x).2 hs
 have e := leaf_unique hn (one u hu) (one w hw')
 subst w
 have ve := path_identical v u hp
 subst v
 exact no ((minimalVertices_terminal B S u x (one u hu)).1 ((minimalVertices_correct B S u).2 hw))

theorem pair_source_embeddings {S : Tree} {x y : Nat}
 (hn : (leaves S).Nodup) (hne : x ≠ y) : pairwiseEmbeddings S (pairPartition S x y) = true := by
 apply (executable_pairwiseEmbeddings S _).2
 simp only [pairPartition,List.pairwise_cons,List.mem_cons,List.not_mem_nil,or_false]
 refine ⟨?_,?_,by simp⟩
 · intro C hC
   rcases hC with rfl | rfl
   · exact singleton_disj_absent hn (by simpa)
   · exact singleton_disj_absent hn (by simp)
 · intro C hC
   subst C
   exact singleton_disj_absent hn (by simp)

theorem pair_refinement {T S : Tree} {F : List (List Nat)} {x y : Nat}
 (ha : agreement T S F = true) (sx : [x] ∈ F) (sy : [y] ∈ F) : Refines F (pairPartition S x y) := by
 have hp := (source_agreement_checks ha).1
 intro B hB
 by_cases xm : x ∈ B
 · have e := ForestState.checked_unique_block (leaves S) F hp B [x] hB sx x xm (by simp)
   exact ⟨[x],by simp [pairPartition],by simpa [e]⟩
 · by_cases ym : y ∈ B
   · have e := ForestState.checked_unique_block (leaves S) F hp B [y] hB sy y ym (by simp)
     exact ⟨[y],by simp [pairPartition],by simpa [e]⟩
   · refine ⟨(leaves S).filter (fun z => z != x && z != y),by simp [pairPartition],?_⟩
     intro z hz
     have nzx : z ≠ x := fun e => xm (e ▸ hz)
     have nzy : z ≠ y := fun e => ym (e ▸ hz)
     simp [block_labels hp hB hz,nzx,nzy]

theorem attachment_refinement {T : Tree} {X Y Z : List Nat} {p q : Nat} {u v : RMAF.Vertex}
 {F : List (List Nat)} (cutsEq : cuts T p q = [u,v])
 (att : (((∀ x, x ∈ subtreeLabels T u ↔ x ∈ Y) ∧ (∀ x, x ∈ subtreeLabels T v ↔ x ∈ Z)) ∨
  ((∀ x, x ∈ subtreeLabels T u ↔ x ∈ Z) ∧ (∀ x, x ∈ subtreeLabels T v ↔ x ∈ Y))))
 (core : ∀ x, x ∈ coreLabels T p q ↔ x ∈ X)
 (hf : Refines F (pendantPartition T p q)) : Refines F [X,Y,Z] := by
 intro B hB
 obtain ⟨C,hC,sub⟩ := hf B hB
 have cc : C = subtreeLabels T u ∨ C = subtreeLabels T v ∨ C = coreLabels T p q := by
   simpa [pendantPartition,cutsEq] using hC
 rcases cc with rfl | rfl | rfl
 · rcases att with ⟨uy,vz⟩ | ⟨uz,vy⟩
   · exact ⟨Y,by simp,fun x hx => (uy x).1 (sub x hx)⟩
   · exact ⟨Z,by simp,fun x hx => (uz x).1 (sub x hx)⟩
 · rcases att with ⟨uy,vz⟩ | ⟨uz,vy⟩
   · exact ⟨Z,by simp,fun x hx => (vz x).1 (sub x hx)⟩
   · exact ⟨Y,by simp,fun x hx => (vy x).1 (sub x hx)⟩
 · exact ⟨X,by simp,fun x hx => (core x).1 (sub x hx)⟩

/-- Five cost-two alternatives from two actual original cherries. The good
block's attachment and the cover are both constructed from the guards. This
also serves an outside second cherry whenever that original cherry has been
derived from its core restriction. -/
theorem guarded_five_cover {T S : Tree} {X Y Z : List Nat}
 {i j : RMAF.Vertex} {a b p q : Nat} {F : List (List Nat)}
 (hnT : (leaves T).Nodup) (hnS : (leaves S).Nodup)
 (hp : partitionCheck (leaves T) [X,Y,Z] = true)
 (he : pairwiseEmbeddings T [X,Y,Z] = true)
 (permP : ∀ B, B ∈ [X,Y,Z] ↔ B ∈ pendantPartition S a b)
 (early : earlierClear S T = true) (good : restrictionAgrees T S X = true)
 (cab : CherryAt T i a b) (cpq : CherryAt S j p q) (pX : p ∈ X) (qX : q ∈ X)
 (ha : agreement T S F = true) :
 ∃ c, c ∈ fiveChildren S a b p q ∧ feasible T S c F := by
 obtain ⟨u,v,hc,att,core⟩ := guarded_good_cherry_attachment hnT hp he early good cpq pX qX
 have refineP : Refines F (pendantPartition T p q) → Refines F (pendantPartition S a b) := by
   intro h B hB
   obtain ⟨C,hC,sub⟩ := attachment_refinement hc att core h B hB
   exact ⟨C,(permP C).1 hC,sub⟩
 rcases actual_pendant_safety hnS ha cab with sa | sb | hhard
 · rcases actual_pendant_safety hnT (agreement_symm ha) cpq with sp | sq | hpq
   · exact ⟨pairChild S p a,by simp [fiveChildren],ha,pair_refinement ha sp sa⟩
   · exact ⟨pairChild S q a,by simp [fiveChildren],ha,pair_refinement ha sq sa⟩
   · exact ⟨pendantChild S a b,by simp [fiveChildren],ha,refineP hpq⟩
 · rcases actual_pendant_safety hnT (agreement_symm ha) cpq with sp | sq | hpq
   · exact ⟨pairChild S p b,by simp [fiveChildren],ha,pair_refinement ha sp sb⟩
   · exact ⟨pairChild S q b,by simp [fiveChildren],ha,pair_refinement ha sq sb⟩
   · exact ⟨pendantChild S a b,by simp [fiveChildren],ha,refineP hpq⟩
 · exact ⟨pendantChild S a b,by simp [fiveChildren],ha,hhard⟩

theorem five_checks {T S : Tree} {i : RMAF.Vertex} {a b p q : Nat}
 (hnT : (leaves T).Nodup) (hnS : (leaves S).Nodup)
 (same : ∀ x, x ∈ leaves T ↔ x ∈ leaves S)
 (cab : CherryAt T i a b) (pS : p ∈ leaves S) (qS : q ∈ leaves S)
 (sep : p ≠ a ∧ p ≠ b ∧ q ≠ a ∧ q ≠ b)
 (hard2 : (cuts S a b).length = 2) {c : Child} (hc : c ∈ fiveChildren S a b p q) :
 partitionCheck (leaves S) c.partition = true ∧ pairwiseEmbeddings S c.partition = true ∧
 c.paid = 2 ∧ c.partition.length = 3 := by
 have aS := (same a).1 (leafAt_label T _ a (cherry_left cab))
 have bS := (same b).1 (leafAt_label T _ b (cherry_right cab))
 have nab := cherry_distinct hnT cab
 have cc : c = pendantChild S a b ∨ c = pairChild S p a ∨ c = pairChild S p b ∨
   c = pairChild S q a ∨ c = pairChild S q b := by simpa [fiveChildren] using hc
 rcases cc with rfl | rfl | rfl | rfl | rfl
 · refine ⟨pendant_partition_check hnS aS,source_embeddings hnS,hard2,?_⟩
   have paid : (pendantChild S a b).paid = 2 := hard2
   have len := (pendant_paid S a b).2
   rw [paid] at len
   exact len
 · exact ⟨pair_partition_check hnS pS aS bS sep.1 sep.2.1.symm nab.symm,
     pair_source_embeddings hnS sep.1,rfl,rfl⟩
 · exact ⟨pair_partition_check hnS pS bS aS sep.2.1 sep.1.symm nab,
     pair_source_embeddings hnS sep.2.1,rfl,rfl⟩
 · exact ⟨pair_partition_check hnS qS aS bS sep.2.2.1 sep.2.2.2.symm nab.symm,
     pair_source_embeddings hnS sep.2.2.1,rfl,rfl⟩
 · exact ⟨pair_partition_check hnS qS bS aS sep.2.2.2 sep.2.2.1.symm nab,
     pair_source_embeddings hnS sep.2.2.2,rfl,rfl⟩

/-- Child-specific exact minimum contracts consume the constructed graph
cover; no global recursive solver is assumed. -/
theorem guarded_five_minimum {T S : Tree} {X Y Z : List Nat}
 {i j : RMAF.Vertex} {a b p q : Nat}
 (hnT : (leaves T).Nodup) (hnS : (leaves S).Nodup)
 (hp : partitionCheck (leaves T) [X,Y,Z] = true)
 (he : pairwiseEmbeddings T [X,Y,Z] = true)
 (permP : ∀ B, B ∈ [X,Y,Z] ↔ B ∈ pendantPartition S a b)
 (early : earlierClear S T = true) (good : restrictionAgrees T S X = true)
 (cab : CherryAt T i a b) (cpq : CherryAt S j p q) (pX : p ∈ X) (qX : q ∈ X)
 (solve : Child → List (List Nat))
 (ih : ∀ c, c ∈ fiveChildren S a b p q → ExactChild T S c (solve c))
 (best : List (List Nat))
 (chosen : ∃ c, c ∈ fiveChildren S a b p q ∧ best = solve c)
 (least : ∀ c, c ∈ fiveChildren S a b p q → best.length ≤ (solve c).length) :
 agreement T S best = true ∧ ∀ F, agreement T S F = true → best.length ≤ F.length := by
 obtain ⟨c,hc,rfl⟩ := chosen
 refine ⟨(ih c hc).1.1,?_⟩
 intro F ha
 obtain ⟨d,hd,hF⟩ := guarded_five_cover hnT hnS hp he permP early good cab cpq pX qX ha
 exact Nat.le_trans (least d hd) ((ih d hd).2 F hF)

theorem guarded_five_budget {T S : Tree} {X Y Z : List Nat}
 {i j : RMAF.Vertex} {a b p q : Nat}
 (hnT : (leaves T).Nodup) (hnS : (leaves S).Nodup)
 (same : ∀ x, x ∈ leaves T ↔ x ∈ leaves S)
 (hp : partitionCheck (leaves T) [X,Y,Z] = true)
 (he : pairwiseEmbeddings T [X,Y,Z] = true)
 (permP : ∀ B, B ∈ [X,Y,Z] ↔ B ∈ pendantPartition S a b)
 (early : earlierClear S T = true) (good : restrictionAgrees T S X = true)
 (cab : CherryAt T i a b) (cpq : CherryAt S j p q) (pX : p ∈ X) (qX : q ∈ X)
 (sep : p ≠ a ∧ p ≠ b ∧ q ≠ a ∧ q ≠ b) (hard2 : (cuts S a b).length = 2)
 (k : Nat) : OriginalWithin T S k ↔ ∃ c, c ∈ fiveChildren S a b p q ∧
 ∃ r, remaining k c = some r ∧ ChildWithin T S c r := by
 have pS := (hasCherry_labels (actual_hasCherry cpq)).1
 have qS := (hasCherry_labels (actual_hasCherry cpq)).2
 constructor
 · rintro ⟨F,ha,hk⟩
   obtain ⟨c,hc,hF⟩ := guarded_five_cover hnT hnS hp he permP early good cab cpq pX qX ha
   obtain ⟨hp,he,paid,len⟩ := five_checks hnT hnS same cab pS qS sep hard2 hc
   exact ⟨c,hc,(remaining_correct k hp he (by omega)).1 ⟨F,hF,hk⟩⟩
 · rintro ⟨c,hc,hr⟩
   obtain ⟨hp,he,paid,len⟩ := five_checks hnT hnS same cab pS qS sep hard2 hc
   obtain ⟨F,hF,hk⟩ := (remaining_correct k hp he (by omega)).2 hr
   exact ⟨F,hF.1,hk⟩

theorem guarded_five_child_solver {T S : Tree} {X Y Z : List Nat}
 {i j : RMAF.Vertex} {a b p q : Nat}
 (hnT : (leaves T).Nodup) (hnS : (leaves S).Nodup)
 (same : ∀ x, x ∈ leaves T ↔ x ∈ leaves S)
 (hp : partitionCheck (leaves T) [X,Y,Z] = true)
 (he : pairwiseEmbeddings T [X,Y,Z] = true)
 (permP : ∀ B, B ∈ [X,Y,Z] ↔ B ∈ pendantPartition S a b)
 (early : earlierClear S T = true) (good : restrictionAgrees T S X = true)
 (cab : CherryAt T i a b) (cpq : CherryAt S j p q) (pX : p ∈ X) (qX : q ∈ X)
 (sep : p ≠ a ∧ p ≠ b ∧ q ≠ a ∧ q ≠ b) (hard2 : (cuts S a b).length = 2)
 (solver : Child → Nat → Option (List (List Nat)))
 (ih : ∀ c, c ∈ fiveChildren S a b p q → ExactBoundedChild T S solver c) (k : Nat) :
 OriginalWithin T S k ↔ ∃ c, c ∈ fiveChildren S a b p q ∧ ∃ G, childCall solver k c = some G := by
 rw [guarded_five_budget hnT hnS same hp he permP early good cab cpq pX qX sep hard2 k]
 constructor
 · rintro ⟨c,hc,hr⟩; exact ⟨c,hc,(child_call_success (ih c hc) k).2 hr⟩
 · rintro ⟨c,hc,hG⟩; exact ⟨c,hc,(child_call_success (ih c hc) k).1 hG⟩

end Universal233.Rule5Classification
