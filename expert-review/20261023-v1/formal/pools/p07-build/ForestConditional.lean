import ForestSelection
namespace GenericForest
open RMAF RestrictionBridge ForestState OutputState ForestGroups VertexGeometry
open Universal233 Universal233.CoreProgram Universal233.Assembly

theorem branch_solution_lifts (t : Tree) (ss : List Tree)
    (hp : proper (some t) ss = true) (h : Overlap) (hh : overlap t ss = some h)
    (q i : Nat) (o : Output) (hm : (i,o) ∈ branches t ss h q) (F : Forest)
    (ha : agrees (some t) (replace ss i o.partition) F = true) :
    agrees (some t) ss F = true ∧
    additionalCost ss F = o.sourceCuts.length + additionalCost (replace ss i o.partition) F := by
  obtain ⟨s,r,hi,hj,_,_,_⟩ := selected_parents_distinct t ss hp h hh
  have one (i : Nat) (s : Tree) (hi : ss[i]? = some s)
      (ho : o ∈ (generate s (colorLabel t h.vertex) q).outputs)
      (ha : agrees (some t) (replace ss i o.partition) F = true) :
      agrees (some t) ss F = true ∧
      additionalCost ss F = o.sourceCuts.length + additionalCost (replace ss i o.partition) F := by
    have he := replace_at_source ss i s o.partition hi
    have split := split_at_source ss i s hi
    have hv := generated_source_valid s (colorLabel t h.vertex) q o ho
    have hn : agrees (some t) (replaced (ss.take i) s (ss.drop (i+1)) o.partition) F = true := by
      simpa [he] using ha
    have hr := replacement_reverse t (ss.take i) s (ss.drop (i+1)) o.partition F
      (by simpa [split] using hp) hv.1 hv.2 hn
    exact ⟨by simpa [split] using hr.1,
      by simpa [he,split] using emitted_replacement_cost t (ss.take i) s (ss.drop (i+1)) _ q o ho F hn⟩
  simp only [branches,List.mem_append,List.mem_map] at hm
  rcases hm with ⟨a,ha',he⟩ | ⟨a,ha',he⟩
  · cases he
    exact one h.left s hi (by simpa [raw,hi] using ha') ha
  · cases he
    exact one h.right r hj (by simpa [raw,hj] using ha') ha

theorem singleton_ordinary_proper (t s : Tree) (hp : proper (some t) [s] = true) :
    Universal233.DepthOne.proper t s = true := by
  have ht : (leaves t).Nodup := (proper_parts _ _ hp).1
  have hs := (proper_source_labels t [s] hp s (by simp)).1
  have hperm := checked_flatten_perm (leaves t) [leaves s] ht (proper_parts _ _ hp).2
  simp only [List.flatten_cons,List.flatten_nil,List.append_nil] at hperm
  simp [Universal233.DepthOne.proper,ht,hs,hperm.symm]

/-- Downstream conditional. `DisjointExact` is a visibly additional OPEN
assembly premise, not a theorem supplied by `OrdinaryIH` in this package. -/
theorem conditional_exact (ordinary : Tree → Tree → Nat → Option Forest)
    (ho : OrdinaryIH ordinary) (hd : DisjointExact ordinary) : ExactAt (solve ordinary) := by
  refine ⟨solve_sound ordinary,?_⟩
  intro T ss q
  induction q using Nat.strongRecOn generalizing T ss with
  | ind q ih =>
    intro G ha hq
    have hp := (agrees_parts _ _ _ ha).1
    by_cases done : agrees T ss (ss.map leaves) = true
    · exact ⟨ss.map leaves,by simp [solve.eq_def,hp,done],by
        simpa using sources_le_blocks T ss G ha⟩
    · have nDone : agrees T ss (ss.map leaves) = false := by cases hh : agrees T ss (ss.map leaves) <;> simp_all
      cases T with
      | none =>
        have hempty : ss = [] := by
          have he := checked_empty (ss.map leaves) (proper_parts _ _ hp).2
          simpa using he
        subst ss
        simp [agrees,proper,labels,partitionCheck,targetEmbeddings] at done
      | some t =>
        cases ss with
        | nil =>
          obtain ⟨x,hx⟩ := List.exists_mem_of_ne_nil (leaves t) (RestrictionBridge.leaves_nonempty t)
          have hc := checked_covers _ _ (proper_parts _ _ hp).2 hx
          simp at hc
        | cons s tail =>
          cases tail with
          | nil =>
            have pg := (initial_state_agreement_iff t s G hp).1 ha
            have pp := singleton_ordinary_proper t s hp
            obtain ⟨F,hF⟩ := ho.complete t s q G pp pg (by simpa [additionalCost] using hq)
            obtain ⟨hf,hb,hm⟩ := ho.sound t s q F pp hF
            have fs := (initial_state_agreement_iff t s F hp).2 hf
            have ac : accepted (some t) [s] q F = true := by simpa [accepted,additionalCost] using And.intro fs hb
            refine ⟨F,?_,hm G pg⟩
            rw [solve.eq_def]
            simp only [hp,ite_true,nDone,Bool.false_eq_true,ite_false,hF,Option.bind_some,checked,ac]
          | cons r rest =>
            cases hh : overlap t (s :: r :: rest) with
            | none =>
              obtain ⟨F,hF,hmin⟩ := hd t _ q G ha (no_overlap_clear t _ hh) hq
              refine ⟨F,?_,hmin⟩
              rw [solve.eq_def]
              simpa only [hp,ite_true,nDone,Bool.false_eq_true,ite_false,hh] using hF
            | some h =>
              obtain ⟨i,o,hm,hpos,hbudget,hnew,hcost,hres⟩ := overlap_child_covers t _ G ha h hh q hq
              have hlt : q-o.sourceCuts.length < q := by omega
              obtain ⟨F,hF,hFG⟩ := ih _ hlt (some t) (replace (s :: r :: rest) i o.partition) G hnew hres
              have hsnd := solve_sound ordinary _ _ _ F hF
              have hlift := branch_solution_lifts t _ hp h hh q i o hm F hsnd.1
              have fac : accepted (some t) (s :: r :: rest) q F = true := by
                simp only [accepted,Bool.and_eq_true,decide_eq_true_eq]
                exact ⟨hlift.1,by omega⟩
              let answers := (branches t (s :: r :: rest) h q).filterMap fun io =>
                let d := io.2.sourceCuts.length
                if _hd : 1 ≤ d ∧ d ≤ q then solve ordinary (some t) (replace (s :: r :: rest) io.1 io.2.partition) (q-d)
                else none
              have memF : F ∈ answers := List.mem_filterMap.2 ⟨(i,o),hm,by
                simp only [show 1 ≤ o.sourceCuts.length ∧ o.sourceCuts.length ≤ q from ⟨hpos,hbudget⟩]
                exact hF⟩
              obtain ⟨J,hJ⟩ := best_exists List.length (accepted (some t) (s :: r :: rest) q) answers F memF fac
              have hmin := (best_spec List.length _ answers J hJ).2.2 F memF fac
              refine ⟨J,?_,Nat.le_trans hmin hFG⟩
              rw [solve.eq_def]
              simpa only [hp,ite_true,nDone,Bool.false_eq_true,ite_false,hh] using hJ

end GenericForest
