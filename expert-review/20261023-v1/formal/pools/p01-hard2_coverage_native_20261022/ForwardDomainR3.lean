import ForwardControlsR3
open RMAF ForestState OutputState Universal233 Universal233.HardParent Universal233.CherryBranching
open OrdinaryDispatch OrdinaryDispatch.FastOrdinary IndependentGeometry ContactedRepair ContactedSource
namespace ContactedForward

/- Contacted source-derived enumeration proof; author helper not applied. -/
theorem ordered_sound_own (T : Tree) : ∀a b,(a,b)∈Rule4.orderedCherries T→HasCherry a b T := by
 induction T with
 | leaf x => intro a b h;cases h
 | node l r il ir =>
  intro a b h
  simp only [Rule4.orderedCherries,List.mem_append,or_assoc] at h
  rcases h with hh|hh|hh
  · cases l with
    | node u v => cases hh
    | leaf x =>
     cases r with
     | node u v => cases hh
     | leaf y =>
      have cases : (a=x ∧ b=y)∨(a=y ∧ b=x) := by
       simpa only [List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] using hh
      rcases cases with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
      · exact .here
      · exact .swap
  · exact .left (il _ _ hh)
  · exact .right (ir _ _ hh)

theorem ordered_complete_own {T : Tree} {a b : Nat} (h : HasCherry a b T) :
 (a,b)∈Rule4.orderedCherries T := by
 induction h with
 | here => simp only [Rule4.orderedCherries,List.append_nil];exact List.mem_cons_self
 | swap => simp only [Rule4.orderedCherries,List.append_nil];exact List.mem_cons_of_mem _ List.mem_cons_self
 | left h ih => exact List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inr ih)))
 | right h ih => exact List.mem_append.2 (Or.inr ih)

theorem cherry_address_own {T : Tree} {a b : Nat} (h : HasCherry a b T) :
 ∃p,CoreGraph.CherryAt T p a b ∨ CoreGraph.CherryAt T p b a := by
 induction h with
 | here => exact ⟨[],Or.inl rfl⟩
 | swap => exact ⟨[],Or.inr rfl⟩
 | left h ih =>
  obtain ⟨p,hp⟩ := ih
  exact ⟨false::p,hp⟩
 | right h ih =>
  obtain ⟨p,hp⟩ := ih
  exact ⟨true::p,hp⟩

theorem cherry_ne_own {T : Tree} {a b : Nat} (h : HasCherry a b T) (nd : (leaves T).Nodup) : a≠b := by
 induction h with
 | here =>
  change (a::b::[]).Nodup at nd
  simpa only [List.mem_singleton] using (List.nodup_cons.1 nd).1
 | swap =>
  have ne : b≠a := by
   change (b::a::[]).Nodup at nd
   simpa only [List.mem_singleton] using (List.nodup_cons.1 nd).1
  exact Ne.symm ne
 | left h ih => exact ih (List.nodup_append.1 nd).1
 | right h ih => exact ih (List.nodup_append.1 nd).2.1

theorem choice_proper {T S : Tree} (s : Rule4.Choice T S) : DepthOne.proper T S=true := by
 exact (by simpa only [DepthOne.proper,Bool.and_eq_true,decide_eq_true_eq,and_assoc] using
  And.intro (choice_priority_own s).1 (And.intro (choice_priority_own s).2.1 (choice_priority_own s).2.2.1))

theorem zero_pendant_cherry {T : Tree} {a b : Nat} (nd : (leaves T).Nodup)
 (ne : a≠b) (aT : a∈leaves T) (bT : b∈leaves T) (zero : cuts T a b=[]) : HasCherry a b T := by
 have core : coreLabels T a b=leaves T := by
  simp only [coreLabels,zero,List.map_nil,List.flatten_nil,List.contains_nil,Bool.not_false]
  exact List.filter_eq_self.2 (fun _ _=>rfl)
 apply clean_two_labels_cherry T (source_core_clean T a b) nd ne aT bT
 intro x hx
 by_cases xa : x=a
 · exact Or.inl xa
 · by_cases xb : x=b
   · exact Or.inr (Or.inl xb)
   · exact Or.inr (Or.inr (List.mem_filter.2 ⟨core.symm ▸ hx,by simp only [bne_iff_ne,Bool.and_eq_true];exact ⟨xa,xb⟩⟩))

theorem actual_forward_domain {T S : Tree} (s : Rule4.Choice T S) :
 DepthOne.proper T S=true ∧ HasCherry s.raw.a s.raw.b T ∧ HasCherry s.raw.a s.raw.c S ∧
 (cuts S s.raw.a s.raw.b).Perm [s.raw.cHead,s.raw.xHead] ∧
 subtreeLabels S s.raw.cHead=[s.raw.c] ∧
 2≤(cuts T s.raw.a s.raw.c).length := by
 have ab := ordered_sound_own T _ _ (choice_admission_own s).1
 have ac := ordered_sound_own S _ _ (choice_admission_own s).2.1
 have labels := IndependentCommon.syntax_labels ac
 have aT := (choice_priority_own s).2.2.1.mem_iff.2 labels.1
 have cT := (choice_priority_own s).2.2.1.mem_iff.2 labels.2
 have no1 : (cuts T s.raw.a s.raw.c).length≠1 := by
  have h := List.all_eq_true.1 (choice_priority_own s).2.2.2.2.2 _ (choice_admission_own s).2.1
  simpa only [cuts,bne_iff_ne] using h
 have no0 : (cuts T s.raw.a s.raw.c).length≠0 := by
  intro zero
  have ch := zero_pendant_cherry (choice_priority_own s).1 (cherry_ne_own ac (choice_priority_own s).2.1) aT cT (List.length_eq_zero_iff.1 zero)
  have mem := ordered_complete_own ch
  have absent := List.all_eq_true.1 (choice_priority_own s).2.2.2.1 _ mem
  have forbidden := List.contains_iff_mem.2 (choice_admission_own s).2.1
  rw [forbidden] at absent
  cases absent
 refine ⟨choice_proper s,ab,ac,(choice_admission_own s).2.2.2.1,(choice_admission_own s).2.2.2.2,?_⟩
 omega

theorem emitted_costs {T S : Tree} (s : Rule4.Choice T S) :
 (Rule4.branches s).map Rule4.Branch.cost=[2,1,(cuts T s.raw.a s.raw.c).length] := rfl

theorem emitted_paid_positive {T S : Tree} (s : Rule4.Choice T S) :
 ∀b∈Rule4.branches s,1≤b.cost := by
 intro b hb
 have count := (actual_forward_domain s).2.2.2.2.2
 simp only [Rule4.branches,List.mem_cons,List.not_mem_nil,or_false] at hb
 rcases hb with rfl|rfl|rfl
 · change 1≤2;omega
 · change 1≤1;exact Nat.le_refl _
 · change 1≤(cuts T s.raw.a s.raw.c).length
   omega

theorem actual_callback_budget {T S : Tree} (s : Rule4.Choice T S) {b : Rule4.Branch}
 (member : b∈Rule4.branches s) {q : Nat} (affordable : b.cost≤q) :
 q-b.cost<q ∧ b.cost+(q-b.cost)=q := by
 have positive := emitted_paid_positive s b member
 omega

end ContactedForward

-- Author integration type/axiom reports; proof text above is unchanged apart from recorded import edits.
set_option pp.universes true
#check @ContactedForward.ordered_sound_own
#print axioms ContactedForward.ordered_sound_own
#check @ContactedForward.ordered_complete_own
#print axioms ContactedForward.ordered_complete_own
#check @ContactedForward.cherry_address_own
#print axioms ContactedForward.cherry_address_own
#check @ContactedForward.cherry_ne_own
#print axioms ContactedForward.cherry_ne_own
#check @ContactedForward.choice_proper
#print axioms ContactedForward.choice_proper
#check @ContactedForward.zero_pendant_cherry
#print axioms ContactedForward.zero_pendant_cherry
#check @ContactedForward.actual_forward_domain
#print axioms ContactedForward.actual_forward_domain
#check @ContactedForward.emitted_costs
#print axioms ContactedForward.emitted_costs
#check @ContactedForward.emitted_paid_positive
#print axioms ContactedForward.emitted_paid_positive
#check @ContactedForward.actual_callback_budget
#print axioms ContactedForward.actual_callback_budget
