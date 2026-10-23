import PriorityFacts
namespace Universal233.OrdinaryPriorityBridge
open RMAF CoreGraph Integration VertexGeometry CutRealization HardParent CherryBranching Rule5Local Rule5Classification Rule5FinalClassification

theorem two_member_perm {A : Type} {L : List A} {q : A}
 (two : L.length=2) (mem : q∈L) : ∃r,L.Perm [q,r] := by
 obtain ⟨u,v,eq⟩ := list_two_named L two
 have qm : q=u ∨ q=v := by simpa [eq] using mem
 rcases qm with rfl|rfl
 · exact ⟨v,eq ▸ List.Perm.refl _⟩
 · refine ⟨u,?_⟩
   rw [eq]
   exact List.Perm.swap _ _ []

theorem singleton_mate_selects {T S : Tree} {p q : RMAF.Vertex} {a b x : Nat}
 (priority : Rule4.Priority T S) (ch : CherryAt T p a b)
 (two : (cuts S a b).length=2) (mem : q∈cuts S a b)
 (lab : subtreeLabels S q=[x]) (mate : HasCherry a x S ∨ HasCherry b x S) :
 ∃s,Rule4.select T S=some s := by
 obtain ⟨r,perm⟩ := two_member_perm two mem
 have perm0 : (pendantOriginal S a b).Perm [q,r] := perm
 have ne := cherry_distinct priority.1 ch
 rcases mate with mate|mate
 · apply Rule4.select_complete priority ⟨a,b,x,q,r⟩
   exact ⟨Rule4.orderedCherries_complete (actual_hasCherry ch),Rule4.orderedCherries_complete mate,ne,perm0,lab⟩
 · apply Rule4.select_complete priority ⟨b,a,x,q,r⟩
   have reversed : (pendantOriginal S b a).Perm [q,r] := by rw [pendantOriginal_swap S b a]; exact perm0
   exact ⟨Rule4.orderedCherries_complete (cherry_symm (actual_hasCherry ch)),Rule4.orderedCherries_complete mate,ne.symm,reversed,lab⟩

/-- The literal boolean scan implies an actual selector result. Both possible
endpoint mates and either singleton position in the two original cuts survive. -/
theorem rule4_scan_selects {T S : Tree} (priority : Rule4.Priority T S)
 (scan : Rule5Local.rule4 T S=true) : ∃s,Rule4.select T S=some s := by
 obtain ⟨c,hc,hit⟩ := List.any_eq_true.1 scan
 have actual := candidate_sound hc
 simp only [Bool.and_eq_true] at hit
 obtain ⟨two,has⟩ := hit
 have len : (cuts S c.a c.b).length=2 := by rw [←actual.2]; exact beq_iff_eq.1 two
 obtain ⟨q,hq,check⟩ := List.any_eq_true.1 has
 have qm : q∈cuts S c.a c.b := by rw [←actual.2]; exact hq
 cases lab : subtreeLabels S q with
 | nil => simp [lab] at check
 | cons x tail =>
   cases tail with
   | nil =>
     have mate : hasCherry S c.a x=true ∨ hasCherry S c.b x=true := by
       simpa only [lab,Bool.or_eq_true] using check
     apply singleton_mate_selects priority actual.1 len qm lab
     exact mate.elim (fun h => Or.inl (hasCherry_scan_sound h)) (fun h => Or.inr (hasCherry_scan_sound h))
   | cons y tail => simp [lab] at check

theorem rule4_scan_isSome {T S : Tree} (priority : Rule4.Priority T S)
 (scan : Rule5Local.rule4 T S=true) : (Rule4.select T S).isSome=true := by
 obtain ⟨s,hs⟩ := rule4_scan_selects priority scan
 simp [hs]

theorem rule4_none_scan_false {T S : Tree} (priority : Rule4.Priority T S)
 (none : Rule4.select T S=none) : Rule5Local.rule4 T S=false := by
 cases h : Rule5Local.rule4 T S
 · rfl
 · obtain ⟨s,hs⟩ := rule4_scan_selects priority h
   rw [none] at hs
   contradiction

theorem actual_no_rule4 {T S : Tree} {c d : Candidate}
 (proper : DepthOne.proper T S=true)
 (forward : CherryBranching.select T S=some (.hard2,c))
 (reverse : CherryBranching.select S T=some (.hard2,d))
 (noT : Rule4.select T S=none) (noS : Rule4.select S T=none) :
 Rule5Local.rule4 T S=false ∧ Rule5Local.rule4 S T=false := by
 exact ⟨rule4_none_scan_false (actual_rule4_priority proper forward reverse) noT,
   rule4_none_scan_false (actual_rule4_priority (proper_reverse proper) reverse forward) noS⟩
end Universal233.OrdinaryPriorityBridge
