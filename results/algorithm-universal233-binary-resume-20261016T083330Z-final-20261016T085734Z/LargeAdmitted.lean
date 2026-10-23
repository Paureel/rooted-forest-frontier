import LargeExchange
namespace Universal233.Rule5Classification
open RMAF CoreGraph Integration VertexGeometry CutRealization HardParent CherryBranching Rule5Local

def largeCandidates (T S : Tree) (a b : Nat) :=
 (cuts S a b).filter fun e => restrictionAgrees T S (subtreeLabels S e) && 3 ≤ (subtreeLabels S e).length
def selectLarge (T S : Tree) (a b : Nat) : Option RMAF.Vertex := (largeCandidates T S a b).head?

theorem selectLarge_sound {T S : Tree} {a b : Nat} {e : RMAF.Vertex}
 (h : selectLarge T S a b = some e) :
 e ∈ cuts S a b ∧ restrictionAgrees T S (subtreeLabels S e) = true ∧ 3 ≤ (subtreeLabels S e).length := by
 obtain ⟨tail,he⟩ := List.head?_eq_some_iff.1 h
 have em : e ∈ largeCandidates T S a b := by rw [he]; simp
 simpa [largeCandidates] using em

theorem selectLarge_complete {T S : Tree} {a b : Nat} {e : RMAF.Vertex}
 (em : e ∈ cuts S a b) (good : restrictionAgrees T S (subtreeLabels S e) = true)
 (size : 3 ≤ (subtreeLabels S e).length) : ∃ f, selectLarge T S a b = some f := by
 have mem : e ∈ largeCandidates T S a b := by simp [largeCandidates,em,good,size]
 cases hs : largeCandidates T S a b with
 | nil => rw [hs] at mem; contradiction
 | cons f tail => exact ⟨f,by simp [selectLarge,hs]⟩

/-- Source Case1 directly from executable admitted guards and a literal good
original pendant of size at least three. Every geometric and saving input of
the preceding local lemmas is derived here. -/
theorem admitted_large_exchange {T S : Tree} {i e : RMAF.Vertex} {a b : Nat} {F : List (List Nat)}
 (ha : admitted T S a b = true) (cab : CherryAt T i a b) (em : e ∈ cuts S a b)
 (good : restrictionAgrees T S (subtreeLabels S e) = true) (size : 3 ≤ (subtreeLabels S e).length)
 (hF : agreement T S F = true) :
 ∃ G, agreement T S G = true ∧ G.length ≤ F.length ∧ Refines G (pendantPartition S a b) := by
 have parts := admitted_parts ha
 have prop := properPair_parts parts.1
 obtain ⟨Y,Z,hp,he,permP⟩ := admitted_pendant_context ha cab em
 obtain ⟨U,hU,catU,_⟩ := admitted_good_pendant_caterpillar ha em good
 have hxU : leaves U = subtreeLabels S e := (source_subtree_labels hU).symm
 have ru : restrict (subtreeLabels S e) S = some U := hxU ▸ restrict_original_subtree prop.2.1 hU
 cases hV : restrict (subtreeLabels S e) T with
 | none => simp [restrictionAgrees,hV,ru] at good
 | some V =>
   have iso : RootedIso V U := (sameShape_correct V U).1 (by simpa [restrictionAgrees,hV,ru] using good)
   have catV := caterpillar_iso (BinaryExchange.iso_symm iso) catU
   have nonleaf : ∃ l r, U = .node l r := by
     cases U with
     | leaf x => simp [←hxU,leaves] at size
     | node l r => exact ⟨l,r,rfl⟩
   obtain ⟨l,r,ulr⟩ := nonleaf
   have chU : ∃ j p q, CherryAt U j p q := by rw [ulr]; exact node_contains_cherry l r
   obtain ⟨j,p,q,chU⟩ := chU
   have labs := hasCherry_labels (actual_hasCherry chU)
   have pX : p ∈ subtreeLabels S e := hxU ▸ labs.1
   have qX : q ∈ subtreeLabels S e := hxU ▸ labs.2
   have cpq : CherryAt S (e ++ j) p q := by unfold CherryAt; rw [subtree_append hU]; exact chU
   have chV := iso_hasCherry (BinaryExchange.iso_symm iso) (actual_hasCherry chU)
   obtain ⟨u,v,cutEq,att,core⟩ := guarded_good_cherry_attachment prop.1 hp he parts.2.2.1 good cpq pX qX
   have mapP : ∀ C, C ∈ pendantPartition T p q → ∃ D, D ∈ pendantPartition S a b ∧ C ⊆ D := by
     intro C hC
     have ref : Refines [C] (pendantPartition T p q) := by
       intro B hB
       have bc : B = C := by simpa using hB
       subst B
       exact ⟨C,hC,fun _ hx => hx⟩
     obtain ⟨D,hD,sub⟩ := attachment_refinement cutEq att core ref C (by simp)
     exact ⟨D,(permP D).1 hD,fun {x} hx => sub x hx⟩
   have xm : subtreeLabels S e ∈ pendantPartition S a b :=
     List.mem_append_left _ (List.mem_map.2 ⟨e,em,rfl⟩)
   exact large_good_cherry_exchange prop.1 prop.2.1 prop.2.2 hU hxU hV catV chV cpq cutEq core mapP good
     (admitted_ordered_checks ha cab).2 (parts.2.2.2.1) (source_embeddings prop.2.1) xm size hF

theorem admitted_large_budget {T S : Tree} {i e : RMAF.Vertex} {a b : Nat}
 (ha : admitted T S a b = true) (cab : CherryAt T i a b) (sel : selectLarge T S a b = some e)
 (k : Nat) : OriginalWithin T S k ↔ ∃ r,
 remaining k (pendantChild S a b) = some r ∧ ChildWithin T S (pendantChild S a b) r := by
 have sc := selectLarge_sound sel
 have prop := properPair_parts (admitted_parts ha).1
 obtain ⟨hp,he,paid⟩ := pendant_checks prop.1 prop.2.1 prop.2.2 cab
 rw [←remaining_correct k hp he paid]
 constructor
 · rintro ⟨F,hF,hk⟩
   obtain ⟨G,hG,hlen,href⟩ := admitted_large_exchange ha cab sc.1 sc.2.1 sc.2.2 hF
   exact ⟨G,⟨hG,href⟩,by omega⟩
 · rintro ⟨F,hF,hk⟩; exact ⟨F,hF.1,hk⟩

theorem admitted_large_child_solver {T S : Tree} {i e : RMAF.Vertex} {a b : Nat}
 (ha : admitted T S a b = true) (cab : CherryAt T i a b) (sel : selectLarge T S a b = some e)
 (solver : Child → Nat → Option (List (List Nat)))
 (ih : ExactBoundedChild T S solver (pendantChild S a b)) (k : Nat) :
 OriginalWithin T S k ↔ ∃ G, childCall solver k (pendantChild S a b) = some G := by
 rw [admitted_large_budget ha cab sel k]
 exact (child_call_success ih k).symm

theorem admitted_large_minimum {T S : Tree} {i e : RMAF.Vertex} {a b : Nat} {G : List (List Nat)}
 (ha : admitted T S a b = true) (cab : CherryAt T i a b) (sel : selectLarge T S a b = some e)
 (ih : ExactChild T S (pendantChild S a b) G) :
 agreement T S G = true ∧ ∀ F, agreement T S F = true → G.length ≤ F.length := by
 have sc := selectLarge_sound sel
 refine ⟨ih.1.1,?_⟩
 intro F hF
 obtain ⟨H,hH,hlen,href⟩ := admitted_large_exchange ha cab sc.1 sc.2.1 sc.2.2 hF
 exact Nat.le_trans (ih.2 H ⟨hH,href⟩) hlen

end Universal233.Rule5Classification
