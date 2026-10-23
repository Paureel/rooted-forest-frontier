import GroupedExact
import OppositeGroups
import Equivalence
namespace Universal233.GroupedFullQuery
open RMAF ForestState ForestGroups RestrictionBridge PaidQueries
open VertexGeometry BinaryExchange

theorem merge_ab_partition (L A B C : List Nat) (hp : partitionCheck L [A,B,C]=true) :
 partitionCheck L [A++B,C]=true := by
 have hA := checked_nonempty L [A,B,C] hp A (by simp)
 have hC := checked_nonempty L [A,B,C] hp C (by simp)
 have hAB : A++B≠[] := by intro h;exact hA (List.append_eq_nil_iff.1 h).1
 have hh := hp
 simp only [partitionCheck,Bool.and_eq_true] at hh ⊢
 exact ⟨⟨by simp [hAB,hC],by simpa [List.append_assoc] using hh.1.2⟩,
   by simpa [List.append_assoc] using hh.2⟩

/-- Original A/B pieces may overlap on the target. Only A-C and B-C
clearance is used; C topology is entirely unrestricted. -/
theorem abc_geometry (T S : Tree) (P : Forest) (A B C : List Nat)
 (hs : (leaves S).Nodup) (ht : (leaves T).Nodup)
 (same : ∀ x,x∈leaves T ↔ x∈leaves S)
 (hP : partitionCheck (leaves S) P=true)
 (hp : partitionCheck (leaves S) [A,B,C]=true)
 (refines : SourceCoverage.RefinesBlocks P [A,B,C])
 (hac : Disj T A C) (hbc : Disj T B C) :
 let ss := OutputState.sourceForest S P
 proper (some T) ss=true ∧ partitionCheck (labels (some T)) [A++B,C]=true ∧
 Owns ss [A++B,C] ∧ CrossClear (some T) ss [A++B,C] := by
 let ss := OutputState.sourceForest S P
 have own3 : Owns ss [A,B,C] := OutputState.original_source_ownership S P [A,B,C] hs hP refines
 have hqt : partitionCheck (labels (some T)) [A++B,C]=true :=
   (partition_labels_congr _ _ _ same).2 (merge_ab_partition _ A B C hp)
 have own2 : Owns ss [A++B,C] := by
   intro s hs'
   obtain ⟨V,hV,sub⟩ := own3 s hs'
   simp only [List.mem_cons,List.not_mem_nil,or_false] at hV
   rcases hV with hv|hv|hv
   · subst V
     exact ⟨A++B,by simp,fun x hx => List.mem_append_left B (sub hx)⟩
   · subst V
     exact ⟨A++B,by simp,fun x hx => List.mem_append_right A (sub hx)⟩
   · subst V
     exact ⟨C,by simp,sub⟩
 have ne : A++B≠C := by
   intro eq
   have hn := checked_family_nodup _ _ hqt
   simp [eq] at hn
 have ac : Clear (minimalVertices A T) (minimalVertices C T) :=
   (clear_iff _ _).1 ((executable_disjointVertices T A C).2 hac)
 have bc : Clear (minimalVertices B T) (minimalVertices C T) :=
   (clear_iff _ _).1 ((executable_disjointVertices T B C).2 hbc)
 have across : ∀ s∈owned ss (A++B),∀ r∈owned ss C,
   Clear (minimalVertices (leaves s) T) (minimalVertices (leaves r) T) := by
   intro s hs' r hr
   obtain ⟨hss,sAB⟩ := (mem_owned s ss (A++B)).1 hs'
   have rC := ((mem_owned r ss C).1 hr).2
   obtain ⟨V,hV,sV⟩ := own3 s hss
   simp only [List.mem_cons,List.not_mem_nil,or_false] at hV
   rcases hV with hv|hv|hv
   · subst V
     intro v hv hw
     exact ac v (executable_span_monotone T (leaves s) A sV v hv)
       (executable_span_monotone T (leaves r) C rC v hw)
   · subst V
     intro v hv hw
     exact bc v (executable_span_monotone T (leaves s) B sV v hv)
       (executable_span_monotone T (leaves r) C rC v hw)
   · subst V
     exact False.elim (ne (block_group_owner _ _ hqt (A++B) C (leaves s)
       (by simp) (by simp) (leaves_nonempty s) sAB sV))
 refine ⟨OutputState.sourceForest_proper T S P ht hs same hP,hqt,own2,?_⟩
 intro t he U hU V hV hne s hs' r hr
 have eq : t=T := Option.some.inj he.symm
 subst t
 simp only [List.mem_cons,List.not_mem_nil,or_false] at hU hV
 rcases hU with rfl|rfl <;> rcases hV with rfl|rfl
 all_goals try exact False.elim (hne rfl)
 · exact across s hs' r hr
 · exact (clear_symm _ _).1 (across r hr s hs')

theorem original_grouped_complete (actual : Ordinary) (parentq b : Nat)
 (below : BelowIH parentq actual) (bb : b≤parentq)
 (T S : Tree) (P : Forest) (A B C : List Nat)
 (hs : (leaves S).Nodup) (ht : (leaves T).Nodup)
 (same : ∀ x,x∈leaves T ↔ x∈leaves S)
 (hP : partitionCheck (leaves S) P=true) (eP : pairwiseEmbeddings S P=true)
 (hp : partitionCheck (leaves S) [A,B,C]=true)
 (refines : SourceCoverage.RefinesBlocks P [A,B,C]) (hac : Disj T A C) (hbc : Disj T B C)
 (js : List (Job Problem Forest))
 (prep : prepare (groupProblems (some T) (OutputState.sourceForest S P) [A++B,C])=some js)
 (bad : 2≤badSlots js) (F : Forest) (ha : agreement T S F=true)
 (href : RestrictionBridge.Refines F P) (budget : F.length-P.length≤b) :
 ∃ xs,(schedule (callback actual) b js).answers=some xs ∧
   agreement T S (xs.flatMap Prod.snd)=true ∧ RestrictionBridge.Refines (xs.flatMap Prod.snd) P ∧
   (xs.flatMap Prod.snd).length-1≤(P.length-1)+b ∧
   (xs.flatMap Prod.snd).length≤F.length := by
 obtain ⟨proper,hq,own,cross⟩ := abc_geometry T S P A B C hs ht same hP hp refines hac hbc
 have belowb : BelowIH b actual := fun r hr => below r (Nat.lt_of_lt_of_le hr bb)
 have fstate := OutputState.original_to_state T S P F ht hs same hP ha href
 have costF := OutputState.exact_additional_cost S P F hs hP
 obtain ⟨xs,result,bill⟩ := grouped_complete actual b belowb (some T) _ [A++B,C] js prep bad hq own F fstate (by omega)
 obtain ⟨valid,costs,budgetH,least⟩ := grouped_sound actual b belowb (some T) _ [A++B,C] js
   prep bad proper hq own cross xs result
 obtain ⟨orig,ref⟩ := OutputState.state_to_original T S P _ hs same hP eP valid
 have eqcost := OutputState.exact_additional_cost S P (xs.flatMap Prod.snd) hs hP
 have ppos : 0<P.length := by
   obtain ⟨x,hx⟩ := List.exists_mem_of_ne_nil (leaves S) (leaves_nonempty S)
   obtain ⟨K,hK,_⟩ := checked_covers _ _ hP hx
   exact List.length_pos_iff.2 (List.ne_nil_of_mem hK)
 have len := sources_le_blocks _ _ _ valid
 rw [(OutputState.checked_materialization S P hs hP).1] at len
 exact ⟨xs,result,orig,ref,by omega,least F fstate⟩

theorem original_grouped_paid_budget (actual : Ordinary) (P : Forest) (parentq b paid : Nat)
 (paid_eq : paid=P.length-1) (full_paid : paid+b=parentq)
 (H : Forest) (budget : H.length-1≤(P.length-1)+b) : H.length-1≤parentq := by
 omega
end Universal233.GroupedFullQuery
