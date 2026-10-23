import OverheadBound
namespace GenericForest.FrontierSize
open RMAF ForestState Universal233 Universal233.PaidQueries FrontierWork

theorem schedule_query_support (ordinary : Ordinary) (t : Tree) (ss : List Tree) (q : Nat)
 (hp : proper (some t) ss=true) (js : List (Job (Tree × Tree) Forest)) (jobsEq : jobs t ss=some js)
 (p : Tree × Tree) (r : Nat) (mem : (p,r)∈(meterSchedule (pairCallback ordinary) (fun _ _=>0) q js).queries) :
 (∀x,x∈leaves p.1 → x∈leaves t) ∧ (∀x,x∈leaves p.2 → x∈leaves t) := by
 unfold meterSchedule at mem
 split at mem
 · simp at mem
 · obtain ⟨_,j,hj,key⟩:=meter_run_query_keys _ _ _ js p r mem
   obtain ⟨s,hs,comp⟩:=jobs_actual t ss js jobsEq j hj
   obtain ⟨u,hu,_,perm,_⟩:=component_pair_proper t ss hp s hs
   have ep : (u,s)=p:=Option.some.inj (hu.symm.trans (by simpa [key] using comp))
   have support:=(proper_source_labels t ss hp s hs).2
   rw [←ep]
   exact ⟨fun x hx=>support (perm.mem_iff.1 hx),fun _ hx=>support hx⟩

/-- No new query labels arise from any actual paid forest replacement. -/
theorem frontier_query_support (ordinary : Ordinary) (T : Option Tree) (ss : List Tree) (q : Nat)
 (hp : proper T ss=true) (p : Tree × Tree) (r : Nat) (mem : (p,r)∈frontier ordinary T ss q) :
 (∀x,x∈leaves p.1 → x∈labels T) ∧ (∀x,x∈leaves p.2 → x∈labels T) := by
 induction q using Nat.strongRecOn generalizing ss with
 | ind q ih =>
  rw [frontier.eq_def] at mem
  split at mem
  · rename_i active
    split at mem
    · simp at mem
    · rename_i t s
      have eq : (p,r)=((t,s),q):=by simpa using mem
      cases eq
      exact ⟨fun _ hx=>hx,fun _ hx=>(proper_source_labels t [s] hp s (by simp)).2 hx⟩
    · rename_i _ _ t notsingle
      split at mem
      · split at mem
        · simp at mem
        · rename_i js jobsEq
          exact schedule_query_support ordinary t ss q hp js jobsEq p r mem
      · rename_i h hh
        obtain ⟨io,hio,mem⟩:=List.mem_flatMap.1 mem
        dsimp only at mem
        split at mem
        · rename_i hd
          have paid:=branch_paid_proper t ss hp h hh q io.1 io.2 hio
          exact ih (q-io.2.sourceCuts.length) (by omega) (replace ss io.1 io.2.partition) paid.2.2 mem
        · simp at mem
  · simp at mem

theorem frontier_query_size (ordinary : Ordinary) (T : Option Tree) (ss : List Tree) (q : Nat)
 (hp : proper T ss=true) (p : Tree × Tree) (r : Nat) (mem : (p,r)∈frontier ordinary T ss q) :
 (leaves p.1).length≤(labels T).length ∧ (leaves p.2).length≤(labels T).length := by
 have valid:=(frontier_queries_proper ordinary T ss q hp p r mem).2
 have nd : (leaves p.1).Nodup ∧ (leaves p.2).Nodup ∧ (leaves p.1).Perm (leaves p.2) := by
  simpa only [DepthOne.proper,Bool.and_eq_true,decide_eq_true_eq,and_assoc] using valid
 have support:=frontier_query_support ordinary T ss q hp p r mem
 exact ⟨nd.1.length_le_of_subset support.1,nd.2.1.length_le_of_subset support.2⟩
end GenericForest.FrontierSize
