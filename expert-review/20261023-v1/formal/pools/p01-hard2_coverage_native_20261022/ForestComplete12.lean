-- Actual solver case induction at exactly bounded callback correctness.
-- Source-guided continuation; all reused geometry helpers separately admitted.
import DisjointLocal10
open RMAF ForestState GenericForest ForestGroups RestrictionBridge
namespace ForestContinuation

theorem forest_complete_local (K : Nat) (ordinary : Tree→Tree→Nat→Option GenericForest.Forest)
 (ho : ForestMinCompletion.LocalOrdinaryIH K ordinary) :
 ∀q,q≤K → ∀T ss G,agrees T ss G=true → additionalCost ss G≤q →
 ∃F,solve ordinary T ss q=some F ∧ F.length≤G.length := by
 intro q
 induction q using Nat.strongRecOn with
 | ind q ih =>
   intro qK T ss G ha hq
   have hp:=(agrees_parts _ _ _ ha).1
   by_cases done : agrees T ss (ss.map leaves)=true
   · exact ⟨ss.map leaves,by simp [GenericForest.solve.eq_def,hp,done],by simpa using sources_le_blocks T ss G ha⟩
   · have nDone : agrees T ss (ss.map leaves)=false := by
       cases hh : agrees T ss (ss.map leaves) <;> simp_all
     cases T with
     | none =>
       have hempty : ss=[] := by
         have he:=checked_empty (ss.map leaves) (proper_parts _ _ hp).2
         simpa using he
       subst ss
       simp [agrees,proper,labels,partitionCheck,targetEmbeddings] at done
     | some t =>
       cases ss with
       | nil =>
         obtain ⟨x,hx⟩:=List.exists_mem_of_ne_nil (leaves t) (RestrictionBridge.leaves_nonempty t)
         have hc:=checked_covers _ _ (proper_parts _ _ hp).2 hx
         simp at hc
       | cons s tail =>
         cases tail with
         | nil =>
           have pg:=(initial_state_agreement_iff t s G hp).mp ha
           have pp:=singleton_ordinary_proper t s hp
           obtain ⟨F,hF⟩:=ho.complete t s q G qK pp pg (by simpa [additionalCost] using hq)
           obtain ⟨hf,hb,hm⟩:=ho.sound t s q F qK pp hF
           have fs:=(initial_state_agreement_iff t s F hp).mpr hf
           have ac : accepted (some t) [s] q F=true := by simpa [accepted,additionalCost] using And.intro fs hb
           refine ⟨F,?_,hm G pg⟩
           rw [GenericForest.solve.eq_def]
           simp only [hp,ite_true,nDone,Bool.false_eq_true,ite_false,hF,Option.bind_some,checked,ac]
         | cons r rest =>
           cases hh : overlap t (s::r::rest) with
           | none =>
             obtain ⟨F,hF,hmin⟩:=disjoint_complete_local K ordinary ho t _ q G qK ha (no_overlap_clear t _ hh) hq
             refine ⟨F,?_,hmin⟩
             rw [GenericForest.solve.eq_def]
             simpa only [hp,ite_true,nDone,Bool.false_eq_true,ite_false,hh] using hF
           | some h =>
             obtain ⟨i,o,hm,hpos,hbudget,hnew,hcost,hres⟩:=overlap_child_covers t _ G ha h hh q hq
             have hlt : q-o.sourceCuts.length<q := by omega
             obtain ⟨F,hF,hFG⟩:=ih _ hlt (by omega) (some t) (replace (s::r::rest) i o.partition) G hnew hres
             have hsnd:=GenericForest.solve_sound ordinary _ _ _ F hF
             have hlift:=branch_solution_lifts t _ hp h hh q i o hm F hsnd.1
             have fac : accepted (some t) (s::r::rest) q F=true := by
               simp only [accepted,Bool.and_eq_true,decide_eq_true_eq]
               exact ⟨hlift.1,by omega⟩
             let answers:=(branches t (s::r::rest) h q).filterMap fun io=>
               let d:=io.2.sourceCuts.length
               if _hd:1≤d ∧ d≤q then solve ordinary (some t) (replace (s::r::rest) io.1 io.2.partition) (q-d)
               else none
             have memF : F∈answers := List.mem_filterMap.mpr ⟨(i,o),hm,by
               simp only [show 1≤o.sourceCuts.length ∧ o.sourceCuts.length≤q from ⟨hpos,hbudget⟩]
               exact hF⟩
             obtain ⟨J,hJ⟩:=best_exists List.length (accepted (some t) (s::r::rest) q) answers F memF fac
             have hmin:=(best_spec List.length _ answers J hJ).2.2 F memF fac
             refine ⟨J,?_,Nat.le_trans hmin hFG⟩
             rw [GenericForest.solve.eq_def]
             simpa only [hp,ite_true,nDone,Bool.false_eq_true,ite_false,hh] using hJ

end ForestContinuation

-- Author integration type/axiom reports; proof text above is unchanged apart from recorded import edits.
set_option pp.universes true
#check @ForestContinuation.forest_complete_local
#print axioms ForestContinuation.forest_complete_local
