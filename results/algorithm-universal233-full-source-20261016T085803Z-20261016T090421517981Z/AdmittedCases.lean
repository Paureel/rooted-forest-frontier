import FiveBranches
namespace Universal233.Rule5Classification
open RMAF CoreGraph Integration VertexGeometry CutRealization HardParent CherryBranching Rule5Local

structure SizeTwoSelection where
 sourceArc : RMAF.Vertex
 p : Nat
 q : Nat
 deriving Repr, DecidableEq

def sizeTwoAt (T S : Tree) (e : RMAF.Vertex) : Option SizeTwoSelection :=
 if restrictionAgrees T S (subtreeLabels S e) then
   match subtree S e with
   | some (.node (.leaf p) (.leaf q)) => some ⟨e,p,q⟩
   | _ => none
 else none
def sizeTwoCandidates (T S : Tree) (a b : Nat) := (cuts S a b).filterMap (sizeTwoAt T S)
def selectSizeTwo (T S : Tree) (a b : Nat) : Option SizeTwoSelection :=
 (sizeTwoCandidates T S a b).head?

theorem sizeTwoAt_sound {T S : Tree} {e : RMAF.Vertex} {c : SizeTwoSelection}
 (h : sizeTwoAt T S e = some c) :
 c.sourceArc = e ∧ CherryAt S e c.p c.q ∧
 restrictionAgrees T S (subtreeLabels S e) = true := by
 unfold sizeTwoAt at h
 split at h
 · rename_i hg
   cases hs : subtree S e with
   | none => simp [hs] at h
   | some U =>
     cases U with
     | leaf x => simp [hs] at h
     | node l r =>
       cases l <;> cases r <;> simp only [hs] at h
       all_goals try contradiction
       have hc := Option.some.inj h
       subst c
       exact ⟨rfl,hs,hg⟩
 · contradiction

theorem sizeTwoCandidate_sound {T S : Tree} {a b : Nat} {c : SizeTwoSelection}
 (h : c ∈ sizeTwoCandidates T S a b) :
 c.sourceArc ∈ cuts S a b ∧ CherryAt S c.sourceArc c.p c.q ∧
 restrictionAgrees T S (subtreeLabels S c.sourceArc) = true := by
 obtain ⟨e,he,hh⟩ := List.mem_filterMap.1 h
 obtain ⟨ce,ch,good⟩ := sizeTwoAt_sound hh
 subst e
 exact ⟨he,ch,good⟩

theorem selectSizeTwo_sound {T S : Tree} {a b : Nat} {c : SizeTwoSelection}
 (h : selectSizeTwo T S a b = some c) : c ∈ sizeTwoCandidates T S a b := by
 obtain ⟨tail,ht⟩ := List.head?_eq_some_iff.1 h
 rw [ht]
 simp

theorem leaves_length_positive (T : Tree) : 0 < (leaves T).length :=
 List.length_pos_iff.2 (CutRealization.leaves_nonempty T)

theorem leaves_one_leaf {T : Tree} (h : (leaves T).length = 1) : ∃ x, T = .leaf x := by
 cases T with
 | leaf x => exact ⟨x,rfl⟩
 | node l r =>
   have hl := leaves_length_positive l
   have hr := leaves_length_positive r
   simp only [leaves,List.length_append] at h
   omega

theorem leaves_two_cherry {T : Tree} (h : (leaves T).length = 2) :
 ∃ p q, T = .node (.leaf p) (.leaf q) := by
 cases T with
 | leaf x => simp [leaves] at h
 | node l r =>
   have hl := leaves_length_positive l
   have hr := leaves_length_positive r
   simp only [leaves,List.length_append] at h
   obtain ⟨p,rfl⟩ := leaves_one_leaf (T:=l) (by omega)
   obtain ⟨q,rfl⟩ := leaves_one_leaf (T:=r) (by omega)
   exact ⟨p,q,rfl⟩

/-- The actual finite scan finds a good pendant of size two, without taking
the selected cherry or its original parent as an input. -/
theorem sizeTwo_selector_complete {T S : Tree} {a b : Nat} {e : RMAF.Vertex}
 (he : e ∈ cuts S a b) (good : restrictionAgrees T S (subtreeLabels S e) = true)
 (size : (subtreeLabels S e).length = 2) : ∃ c, selectSizeTwo T S a b = some c := by
 obtain ⟨U,hU⟩ := ((cuts_spec S a b e).1 he).1
 have su : (leaves U).length = 2 := by rw [←source_subtree_labels hU]; exact size
 obtain ⟨p,q,rfl⟩ := leaves_two_cherry su
 have hm : (⟨e,p,q⟩ : SizeTwoSelection) ∈ sizeTwoCandidates T S a b := by
   apply List.mem_filterMap.2
   exact ⟨e,he,by simp [sizeTwoAt,good,hU]⟩
 cases hs : sizeTwoCandidates T S a b with
 | nil => rw [hs] at hm; contradiction
 | cons c tail => exact ⟨c,by simp [selectSizeTwo,hs]⟩

theorem admitted_ordered_checks {T S : Tree} {i : RMAF.Vertex} {a b : Nat}
 (ha : admitted T S a b = true) (ch : CherryAt T i a b) :
 partitionCheck (leaves T) (pendantPartition S a b) = true ∧
 partitionCheck (leaves S) (pendantPartition S a b) = true := by
 have prop := properPair_parts (admitted_parts ha).1
 have aS := (prop.2.2 a).1 (leafAt_label T _ a (cherry_left ch))
 have ps := pendant_partition_check (b:=b) prop.2.1 aS
 exact ⟨(RestrictionBridge.partition_labels_congr (leaves S) (leaves T) _ (fun x => (prop.2.2 x).symm)).1 ps,ps⟩

theorem admitted_pendant_context {T S : Tree} {i e : RMAF.Vertex} {a b : Nat}
 (ha : admitted T S a b = true) (ch : CherryAt T i a b) (em : e ∈ cuts S a b) :
 ∃ Y Z, partitionCheck (leaves T) [subtreeLabels S e,Y,Z] = true ∧
 pairwiseEmbeddings T [subtreeLabels S e,Y,Z] = true ∧
 (∀ B, B ∈ [subtreeLabels S e,Y,Z] ↔ B ∈ pendantPartition S a b) := by
 have parts := admitted_parts ha
 obtain ⟨u,v,cutEq⟩ := list_two_named (cuts S a b) parts.2.2.2.2
 have P : pendantPartition S a b = [subtreeLabels S u,subtreeLabels S v,coreLabels S a b] := by
   simp only [pendantPartition,cutEq,List.map_cons,List.map_nil,List.cons_append,List.nil_append]
 have hp := P ▸ (admitted_ordered_checks ha ch).1
 have he := P ▸ parts.2.2.2.1
 have ee : e = u ∨ e = v := by simpa [cutEq] using em
 rcases ee with eu | ev
 · subst e
   exact ⟨subtreeLabels S v,coreLabels S a b,hp,he,by intro B; simp [P]⟩
 · subst e
   refine ⟨subtreeLabels S u,coreLabels S a b,?_,embeddings_swap_first T _ _ _ he,?_⟩
   · rw [←partition_swap_first]; exact hp
   · intro B; simp [P,or_comm,or_left_comm,or_assoc]

/-- A good actual pendant selected by the executable size-two scan provides
the checked partition and both original cherries used by the five-cover.
The partition permutation is computed from the actual two-cut source list. -/
theorem admitted_sizeTwo_context {T S : Tree} {i : RMAF.Vertex} {a b : Nat} {c : SizeTwoSelection}
 (ha : admitted T S a b = true) (ch : CherryAt T i a b)
 (sel : c ∈ sizeTwoCandidates T S a b) :
 ∃ Y Z, partitionCheck (leaves T) [subtreeLabels S c.sourceArc,Y,Z] = true ∧
 pairwiseEmbeddings T [subtreeLabels S c.sourceArc,Y,Z] = true ∧
 (∀ B, B ∈ [subtreeLabels S c.sourceArc,Y,Z] ↔ B ∈ pendantPartition S a b) ∧
 (c.p ≠ a ∧ c.p ≠ b ∧ c.q ≠ a ∧ c.q ≠ b) ∧
 c.p ∈ subtreeLabels S c.sourceArc ∧ c.q ∈ subtreeLabels S c.sourceArc := by
 obtain ⟨cm,cpq,good⟩ := sizeTwoCandidate_sound sel
 have parts := admitted_parts ha
 have prop := properPair_parts parts.1
 obtain ⟨u,v,cutEq⟩ := list_two_named (cuts S a b) parts.2.2.2.2
 have pX : c.p ∈ subtreeLabels S c.sourceArc := by rw [source_subtree_labels cpq]; simp [leaves]
 have qX : c.q ∈ subtreeLabels S c.sourceArc := by rw [source_subtree_labels cpq]; simp [leaves]
 have aS := (prop.2.2 a).1 (leafAt_label T _ a (cherry_left ch))
 have bS := (prop.2.2 b).1 (leafAt_label T _ b (cherry_right ch))
 have anX := source_label_outside_pendant cm (Or.inl rfl) aS
 have bnX := source_label_outside_pendant cm (Or.inr rfl) bS
 have sep : c.p ≠ a ∧ c.p ≠ b ∧ c.q ≠ a ∧ c.q ≠ b :=
   ⟨fun e => anX (e ▸ pX),fun e => bnX (e ▸ pX),fun e => anX (e ▸ qX),fun e => bnX (e ▸ qX)⟩
 have P : pendantPartition S a b = [subtreeLabels S u,subtreeLabels S v,coreLabels S a b] := by
   simp only [pendantPartition,cutEq,List.map_cons,List.map_nil,List.cons_append,List.nil_append]
 have hp : partitionCheck (leaves T) [subtreeLabels S u,subtreeLabels S v,coreLabels S a b] = true :=
   P ▸ (admitted_ordered_checks ha ch).1
 have he : pairwiseEmbeddings T [subtreeLabels S u,subtreeLabels S v,coreLabels S a b] = true := P ▸ parts.2.2.2.1
 have ce : c.sourceArc = u ∨ c.sourceArc = v := by simpa [cutEq] using cm
 rcases ce with ce | ce
 · refine ⟨subtreeLabels S v,coreLabels S a b,ce.symm ▸ hp,ce.symm ▸ he,?_,sep,pX,qX⟩
   intro B; simp [ce,P]
 · refine ⟨subtreeLabels S u,coreLabels S a b,?_,?_,?_,sep,pX,qX⟩
   · rw [ce,←partition_swap_first]; exact hp
   · rw [ce]; exact embeddings_swap_first T _ _ _ he
   · intro B; simp [ce,P,or_comm,or_left_comm,or_assoc]

theorem admitted_sizeTwo_cover {T S : Tree} {i : RMAF.Vertex} {a b : Nat} {c : SizeTwoSelection}
 {F : List (List Nat)} (ha : admitted T S a b = true) (ch : CherryAt T i a b)
 (sel : selectSizeTwo T S a b = some c) (hF : agreement T S F = true) :
 ∃ d, d ∈ fiveChildren S a b c.p c.q ∧ feasible T S d F := by
 have sc := selectSizeTwo_sound sel
 obtain ⟨Y,Z,hp,he,perm,sep,pX,qX⟩ := admitted_sizeTwo_context ha ch sc
 have parts := admitted_parts ha
 have prop := properPair_parts parts.1
 obtain ⟨_,cpq,good⟩ := sizeTwoCandidate_sound sc
 exact guarded_five_cover prop.1 prop.2.1 hp he perm parts.2.2.1 good ch cpq pX qX hF

theorem admitted_sizeTwo_child_solver {T S : Tree} {i : RMAF.Vertex} {a b : Nat} {c : SizeTwoSelection}
 (ha : admitted T S a b = true) (ch : CherryAt T i a b)
 (sel : selectSizeTwo T S a b = some c)
 (solver : Child → Nat → Option (List (List Nat)))
 (ih : ∀ d, d ∈ fiveChildren S a b c.p c.q → ExactBoundedChild T S solver d) (k : Nat) :
 OriginalWithin T S k ↔ ∃ d, d ∈ fiveChildren S a b c.p c.q ∧ ∃ G, childCall solver k d = some G := by
 have sc := selectSizeTwo_sound sel
 obtain ⟨Y,Z,hp,he,perm,sep,pX,qX⟩ := admitted_sizeTwo_context ha ch sc
 have parts := admitted_parts ha
 have prop := properPair_parts parts.1
 obtain ⟨_,cpq,good⟩ := sizeTwoCandidate_sound sc
 exact guarded_five_child_solver prop.1 prop.2.1 prop.2.2 hp he perm parts.2.2.1 good ch cpq pX qX sep parts.2.2.2.2 solver ih k

end Universal233.Rule5Classification
