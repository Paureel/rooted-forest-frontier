import SourceOrientation
namespace Universal233.Case322Extraction
open RMAF CoreGraph Integration VertexGeometry CutRealization HardParent CherryBranching
open Universal233.Rule5Local Universal233.Rule5Case322
set_option maxRecDepth 15000

theorem VC_mem (sa sc : Bool) (a c x : Nat) (X : Tree) :
 x ∈ leaves (VC sa sc a c X) ↔ x = a ∨ x ∈ leaves X ∨ x = c := by
 simp only [VC,AX,orient_mem,leaves,List.mem_singleton,or_assoc]
theorem bottom_mem (sa sc sb : Bool) (a b c x : Nat) (X : Tree) :
 x ∈ leaves (bottom sa sc sb a b c X) ↔ x = a ∨ x ∈ leaves X ∨ x = c ∨ x = b := by
 simp only [bottom,orient_mem,VC_mem,leaves,List.mem_singleton,or_assoc]

theorem orient_fork_occupies {T A B : Tree} {q : RMAF.Vertex} {s : Bool}
 {D : List Nat} {x y : Nat} (he : subtree T q = some (orient s A B))
 (hx : x ∈ leaves A) (hy : y ∈ leaves B) (xD : x ∈ D) (yD : y ∈ D) :
 q ∈ minimalVertices D T := by
 cases s
 · exact original_fork_occupies he hx hy xD yD
 · exact original_fork_occupies he hy hx yD xD

theorem oriented_mixedX_occupies {S X : Tree} {w : RMAF.Vertex} {sa sc sb : Bool}
 {F : List (List Nat)} {D : List Nat} {a b c : Nat}
 (hn : (leaves S).Nodup) (he : subtree S w = some (bottom sa sc sb a b c X))
 (hp : partitionCheck (leaves S) F = true) (single : [a] ∈ F) (hD : D ∈ F)
 (mixed : BinaryExchange.mixed D (leaves X).contains = true) :
 vRoot w sb ∈ minimalVertices D S := by
 obtain ⟨xa,xc,hac,bV⟩ := bottom_proper hn he
 obtain ⟨⟨x,xD,xX⟩,⟨y,yD,yX⟩⟩ := (BinaryExchange.mixed_iff D (leaves X).contains).1 mixed
 have xi : x ∈ leaves X := List.contains_iff_mem.1 xX
 have yo : y ∉ leaves X := by simpa using yX
 have xna : x ≠ a := by intro e; subst x; exact xa xi
 have noA := singleton_excludes_other hp single hD xD xna
 have yna : y ≠ a := by intro e; subst y; exact noA yD
 have hv := bottom_v_lookup he
 by_cases yc : y = c
 · subst y
   exact orient_fork_occupies hv ((orient_mem sa (.leaf a) X x).2 (Or.inr xi)) (by simp [leaves]) xD yD
 · have yV : y ∉ leaves (VC sa sc a c X) := by simp [VC_mem,yna,yo,yc]
   have xV : x ∈ leaves (VC sa sc a c X) := (VC_mem sa sc a c x X).2 (Or.inr (Or.inl xi))
   have atV : BinaryExchange.treeAt S (vRoot w sb) = some (VC sa sc a c X) := by rw [source_treeAt]; exact hv
   exact BinaryExchange.crossing_occupies S _ _ D hn atV (fun z hz => block_labels hp hD hz)
     ⟨⟨x,xD,xV⟩,⟨y,yD,yV⟩⟩

theorem oriented_cmixed_occupies {S X : Tree} {w : RMAF.Vertex} {sa sc sb : Bool}
 {F : List (List Nat)} {D : List Nat} {a b c : Nat}
 (hn : (leaves S).Nodup) (he : subtree S w = some (bottom sa sc sb a b c X))
 (hp : partitionCheck (leaves S) F = true) (single : [a] ∈ F) (hD : D ∈ F)
 (cD : c ∈ D) (noX : ∀ x, x ∈ D → x ∉ leaves X)
 (other : ∃ y, y ∈ D ∧ y ≠ c) : vRoot w sb ∈ minimalVertices D S := by
 obtain ⟨xa,xc,hac,bV⟩ := bottom_proper hn he
 obtain ⟨y,yD,ync⟩ := other
 have noA := singleton_excludes_other hp single hD cD (Ne.symm hac)
 have yna : y ≠ a := by intro e; subst y; exact noA yD
 have yV : y ∉ leaves (VC sa sc a c X) := by simp [VC_mem,yna,noX y yD,ync]
 have cV : c ∈ leaves (VC sa sc a c X) := by simp [VC_mem]
 have atV : BinaryExchange.treeAt S (vRoot w sb) = some (VC sa sc a c X) := by rw [source_treeAt]; exact bottom_v_lookup he
 exact BinaryExchange.crossing_occupies S _ _ D hn atV (fun z hz => block_labels hp hD hz)
   ⟨⟨c,cD,cV⟩,⟨y,yD,yV⟩⟩

theorem oriented_three_contains_b {T S X : Tree} {w : RMAF.Vertex} {sa sc sb : Bool}
 {F : List (List Nat)} {D : List Nat} {a b c x d : Nat}
 (hn : (leaves S).Nodup) (he : subtree S w = some (bottom sa sc sb a b c X))
 (ha : agreement T S F = true) (hD : D ∈ F) (xD : x ∈ D) (dD : d ∈ D)
 (xX : x ∈ leaves X) (dV : d ∉ leaves (VC sa sc a c X)) (nonsingle : [b] ∉ F) : b ∈ D := by
 apply Classical.byContradiction
 intro noB
 have parts := BinaryExchange.agreement_parts T S F ha
 have hp := parts.2.1
 have lb := bottom_b_lookup he
 obtain ⟨B,hB,bB⟩ := partitionCheck_covers _ F hp b (leafAt_label S _ b lb)
 have occB : w ∈ minimalVertices B S := nonsingleton_block_parent lb hp hB bB nonsingle
 have dnb : d ≠ b := by intro e; subst d; exact noB dD
 have dW : d ∉ leaves (bottom sa sc sb a b c X) := by
   intro hh
   rcases (orient_mem sb (VC sa sc a c X) (.leaf b) d).1 hh with hh | hh
   · exact dV hh
   · exact dnb (by simpa [leaves] using hh)
 have xW : x ∈ leaves (bottom sa sc sb a b c X) := by simp [bottom_mem,xX]
 have atW : BinaryExchange.treeAt S w = some (bottom sa sc sb a b c X) := by rw [source_treeAt]; exact he
 have occD := BinaryExchange.crossing_occupies S _ w D hn atW (fun z hz => block_labels hp hD hz)
   ⟨⟨x,xD,xW⟩,⟨d,dD,dW⟩⟩
 have ne : D ≠ B := by intro e; exact noB (e ▸ bB)
 have dj := BinaryExchange.pairwise_mem (fun _ _ h => BinaryExchange.disj_symm h) F parts.2.2.2.2 D B hD hB ne
 exact dj w ⟨(minimalVertices_correct D S w).1 occD,(minimalVertices_correct B S w).1 occB⟩

/-- Saving for all local source sibling patterns, derived from original
occupancy. No normalised-source agreement or assumed saving is imported. -/
theorem oriented_split_saving {T S X : Tree} {w : RMAF.Vertex} {sa sc sb : Bool}
 {F : List (List Nat)} {a b c : Nat}
 (hn : (leaves S).Nodup) (he : subtree S w = some (bottom sa sc sb a b c X))
 (ha : agreement T S F = true) (single : [a] ∈ F) (nonsingle : [b] ∉ F)
 (noBCX : ∀ D, D ∈ F → b ∈ D → c ∈ D → ∀ x, x ∈ D → x ∈ leaves X → False) :
 (splitForest (splitForest F (leaves X)) [c]).length ≤ F.length+1 := by
 obtain ⟨xa,xc,hac,bV⟩ := bottom_proper hn he
 have parts := BinaryExchange.agreement_parts T S F ha
 have hp := parts.2.1
 have emb := parts.2.2.2.2
 have first := split_original_agreement hn (bottom_x_lookup he) ha
 let H := splitForest F (leaves X)
 change (splitForest H [c]).length ≤ F.length+1
 change agreement T S H = true ∧ H.length ≤ F.length+1 at first
 have second := split_original_agreement hn (bottom_c_lookup he) first.1
 change agreement T S (splitForest H [c]) = true ∧ (splitForest H [c]).length ≤ H.length+1 at second
 by_cases hasMixed : ∃ C, C ∈ H ∧ BinaryExchange.mixed C [c].contains = true
 · obtain ⟨C,hC,hmC⟩ := hasMixed
   obtain ⟨D,hD,hDC⟩ := List.mem_flatMap.1 hC
   have sub := BinaryExchange.split_sub D C (leaves X).contains hDC
   obtain ⟨⟨z,zC,zc⟩,⟨d,dC,dc⟩⟩ := (BinaryExchange.mixed_iff C [c].contains).1 hmC
   have ze : z = c := by simpa using zc
   subst z
   have dnc : d ≠ c := by simpa using dc
   have cD := sub c zC
   have dD := sub d dC
   have noA := singleton_excludes_other hp single hD cD (Ne.symm hac)
   have dna : d ≠ a := by intro e; subst d; exact noA dD
   have CnoX : ∀ y, y ∈ C → y ∉ leaves X := by
     rcases BinaryExchange.split_mono D (leaves X).contains C hDC with hy | hn
     · exact False.elim (xc (List.contains_iff_mem.1 (hy c zC)))
     · intro y hy; have hh := hn y hy; simpa using hh
   have DnoX : ∀ y, y ∈ D → y ∉ leaves X := by
     intro y yD yX
     have dV : d ∉ leaves (VC sa sc a c X) := by simp [VC_mem,dna,CnoX d dC,dnc]
     have bD := oriented_three_contains_b hn he ha hD yD dD yX dV nonsingle
     exact noBCX D hD bD cD y yD yX
   have occD := oriented_cmixed_occupies hn he hp single hD cD DnoX ⟨d,dD,dnc⟩
   have noFirst : ∀ B, B ∈ F → BinaryExchange.mixed B (leaves X).contains ≠ true := by
     intro B hB mixedB
     have occB := oriented_mixedX_occupies hn he hp single hB mixedB
     have neBD : B ≠ D := by
       intro e
       obtain ⟨⟨y,yB,yX⟩,_⟩ := (BinaryExchange.mixed_iff B (leaves X).contains).1 mixedB
       exact DnoX y (e ▸ yB) (List.contains_iff_mem.1 yX)
     have dj := BinaryExchange.pairwise_mem (fun _ _ h => BinaryExchange.disj_symm h) F emb B D hB hD neBD
     exact dj (vRoot w sb) ⟨(minimalVertices_correct B S _).1 occB,(minimalVertices_correct D S _).1 occD⟩
   have empty : F.filter (fun B => BinaryExchange.mixed B (leaves X).contains) = [] := List.filter_eq_nil_iff.2 noFirst
   have len := BinaryExchange.splitAll_length F (leaves X).contains
   rw [empty] at len
   have Hlen : H.length ≤ F.length := by simpa [H,splitForest] using len
   omega
 · have empty : H.filter (fun C => BinaryExchange.mixed C [c].contains) = [] := by
     apply List.filter_eq_nil_iff.2
     intro C hC
     exact fun hm => hasMixed ⟨C,hC,hm⟩
   have len := BinaryExchange.splitAll_length H [c].contains
   rw [empty] at len
   have endlen : (splitForest H [c]).length ≤ H.length := by simpa [splitForest] using len
   omega
end Universal233.Case322Extraction
