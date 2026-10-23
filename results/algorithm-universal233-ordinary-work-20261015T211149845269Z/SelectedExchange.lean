import SourceTransport321
namespace Universal233.Rule5SourceOrientation
open RMAF CoreGraph Integration VertexGeometry CutRealization HardParent CherryBranching Rule5Local Rule5Classification Rule5FinalClassification

theorem unordered_safety {T S : Tree} {F : List (List Nat)} {a b : Nat}
 (hnS : (leaves S).Nodup) (ha : agreement T S F=true) (ch : ActualCherry T a b) :
 [a]∈F ∨ [b]∈F ∨ Refines F (pendantPartition S a b) := by
 obtain ⟨p,h|h⟩ := ch
 · exact actual_pendant_safety hnS ha h
 · rcases actual_pendant_safety hnS ha h with hs|hs|hr
   · exact Or.inr (Or.inl hs)
   · exact Or.inl hs
   · exact Or.inr (Or.inr (by rw [pendantPartition_swap S a b]; exact hr))

theorem unordered_saving_a {T S : Tree} {F : List (List Nat)} {q r : RMAF.Vertex} {a b : Nat}
 (hnT : (leaves T).Nodup) (hnS : (leaves S).Nodup)
 (same : ∀x,x∈leaves T ↔ x∈leaves S) (ha : agreement T S F=true) (ch : ActualCherry T a b)
 (cut : cuts S a b=[q,r] ∨ cuts S a b=[r,q]) (single : [a]∈F)
 (save : (splitTwo F S q r).length ≤ F.length+1) :
 ∃G,agreement T S G=true ∧ G.length≤F.length ∧ Refines G (pendantPartition S a b) := by
 obtain ⟨p,h|h⟩ := ch
 · exact actual_hard2_exchange_from_split_saving hnT hnS same ha h cut single save
 · have cut' : cuts S b a=[q,r] ∨ cuts S b a=[r,q] := by rw [←cuts_swap S a b]; exact cut
   obtain ⟨G,hG,hl,hr⟩ := actual_hard2_exchange_from_split_saving_b hnT hnS same ha h cut' single save
   exact ⟨G,hG,hl,by rw [pendantPartition_swap S a b]; exact hr⟩

theorem unordered_saving_b {T S : Tree} {F : List (List Nat)} {q r : RMAF.Vertex} {a b : Nat}
 (hnT : (leaves T).Nodup) (hnS : (leaves S).Nodup)
 (same : ∀x,x∈leaves T ↔ x∈leaves S) (ha : agreement T S F=true) (ch : ActualCherry T a b)
 (cut : cuts S a b=[q,r] ∨ cuts S a b=[r,q]) (single : [b]∈F)
 (save : (splitTwo F S q r).length ≤ F.length+1) :
 ∃G,agreement T S G=true ∧ G.length≤F.length ∧ Refines G (pendantPartition S a b) := by
 have ch' : ActualCherry T b a := by obtain ⟨p,h|h⟩ := ch; exact ⟨p,Or.inr h⟩; exact ⟨p,Or.inl h⟩
 have cut' : cuts S b a=[q,r] ∨ cuts S b a=[r,q] := by rw [←cuts_swap S a b]; exact cut
 obtain ⟨G,hG,hl,hr⟩ := unordered_saving_a hnT hnS same ha ch' cut' single save
 exact ⟨G,hG,hl,by rw [pendantPartition_swap S a b]; exact hr⟩

theorem first_exchange {T S X W : Tree} {v w q r : RMAF.Vertex} {s t : Bool} {F : List (List Nat)} {a b c : Nat}
 (hnT : (leaves T).Nodup) (hnS : (leaves S).Nodup) (same : ∀x,x∈leaves T ↔ x∈leaves S)
 (base : subtree S v=some (fork t (fork s (.leaf a) X) (.leaf c)))
 (target : subtree T w=some W) (labels : ∀x,x∈leaves W ↔ x∈leaves X ∨ x=c)
 (ch : ActualCherry T a b) (cut : cuts S a b=[q,r] ∨ cuts S a b=[r,q])
 (ql : subtreeLabels S q=leaves X) (rl : subtreeLabels S r=[c]) (ha : agreement T S F=true) :
 [a]∈F ∨ ∃G,agreement T S G=true ∧ G.length≤F.length ∧ Refines G (pendantPartition S a b) := by
 by_cases single : [a]∈F
 · exact Or.inl single
 · right
   rcases unordered_safety hnS ha ch with hs|hs|hr
   · contradiction
   · apply unordered_saving_b hnT hnS same ha ch cut hs
     rw [splitTwo,ql,rl]
     exact case321_split_saving hnT hnS base target labels ha single
   · exact ⟨F,ha,Nat.le_refl _,hr⟩

theorem third_exchange {S X U : Tree} {v q r : RMAF.Vertex} {s t z : Bool} {F : List (List Nat)} {a b c : Nat}
 (hnT : (leaves (fork z U (.leaf c))).Nodup) (hnS : (leaves S).Nodup)
 (same : ∀x,x∈leaves (fork z U (.leaf c)) ↔ x∈leaves S)
 (base : subtree S v=some (fork t (fork s (.leaf a) X) (.leaf c)))
 (ch : ActualCherry (fork z U (.leaf c)) a b) (cut : cuts S a b=[q,r] ∨ cuts S a b=[r,q])
 (ql : subtreeLabels S q=leaves X) (rl : subtreeLabels S r=[c]) (ha : agreement (fork z U (.leaf c)) S F=true) :
 [b]∈F ∨ ∃G,agreement (fork z U (.leaf c)) S G=true ∧ G.length≤F.length ∧ Refines G (pendantPartition S a b) := by
 rcases unordered_safety hnS ha ch with hs|hs|hr
 · right
   apply unordered_saving_a hnT hnS same ha ch cut hs
   rw [splitTwo,ql,rl]
   exact case323_split_saving hnT hnS base ha hs
 · exact Or.inl hs
 · exact Or.inr ⟨F,ha,Nat.le_refl _,hr⟩

theorem region_first_cluster {T : Tree} {X C : List Nat} {c : Nat} {q : RMAF.Vertex}
 (hp : partitionCheck (leaves T) [X,[c],C]=true) (he : pairwiseEmbeddings T [X,[c],C]=true)
 (inc : q∈incident T X) (region : InRegion T X q C) :
 ∃W,subtree T q=some W ∧ ∀x,x∈leaves W ↔ x∈X ∨ x=c := by
 obtain ⟨W,hW⟩ := ((incident_spec T X q).1 inc).1
 refine ⟨W,hW,?_⟩
 intro x
 have dis := (executable_pairwiseEmbeddings T [X,[c],C]).1 he
 constructor
 · intro xW
   have xq : x∈subtreeLabels T q := by rw [source_subtree_labels hW]; exact xW
   have xT := (subtreeLabels_sublist T q).subset xq
   obtain ⟨B,hB,xB⟩ := partitionCheck_covers (leaves T) [X,[c],C] hp x xT
   have bb : B=X ∨ B=[c] ∨ B=C := by simpa using hB
   rcases bb with rfl|rfl|rfl
   · exact Or.inl xB
   · exact Or.inr (by simpa using xB)
   · exact False.elim (((region.2 x xT).2 xB) xq)
 · intro hx
   have xT : x∈leaves T := by rcases hx with h|h; exact block_labels hp (by simp) h; exact block_labels hp (B:=[c]) (by simp) (by simp [h])
   have noC : x∉C := by
     intro xC
     rcases hx with xX|xc
     · have dj := (List.pairwise_cons.1 dis).1 C (by simp)
       obtain ⟨p,hp⟩ := leaf_exists xT
       exact dj p ⟨(minimalVertices_correct X T p).1 ((minimalVertices_terminal X T p x hp).2 xX),(minimalVertices_correct C T p).1 ((minimalVertices_terminal C T p x hp).2 xC)⟩
     · have dj := (List.pairwise_cons.1 (List.pairwise_cons.1 dis).2).1 C (by simp)
       obtain ⟨p,hp⟩ := leaf_exists xT
       exact dj p ⟨(minimalVertices_correct [c] T p).1 ((minimalVertices_terminal [c] T p x hp).2 (by simp [xc])),(minimalVertices_correct C T p).1 ((minimalVertices_terminal C T p x hp).2 xC)⟩
   have xq : x∈subtreeLabels T q := Classical.byContradiction (fun no => noC ((region.2 x xT).1 no))
   rwa [source_subtree_labels hW] at xq
end Universal233.Rule5SourceOrientation
