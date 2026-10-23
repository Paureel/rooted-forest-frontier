-- Explicit helly_four scope extension only for the actual 111 search case.
import IsolatedCompletenessV2
open RMAF VertexGeometry
namespace ContactedHard2Overlap

theorem common_complete (xs ys zs : List RMAF.Vertex)
 (common : ∃v,v∈xs ∧ v∈ys ∧ v∈zs) :
 ∃w,findCommon xs ys zs=some w ∧ w∈xs ∧ w∈ys ∧ w∈zs := by
 induction xs with
 | nil => obtain ⟨v,hv,_,_⟩:=common;simp at hv
 | cons a tail ih =>
  by_cases test : (ys.contains a && zs.contains a)=true
  · have both : ys.contains a=true ∧ zs.contains a=true := by simpa only [Bool.and_eq_true] using test
    exact ⟨a,by simp only [findCommon,test,ite_true],List.mem_cons_self,
      List.contains_iff_mem.mp both.1,List.contains_iff_mem.mp both.2⟩
  · obtain ⟨v,hv,hy,hz⟩:=common
    have inside : v∈tail := by
     rcases List.mem_cons.mp hv with eq|hin
     · subst v
       have yes : (ys.contains a && zs.contains a)=true := by
        simp only [Bool.and_eq_true]
        exact ⟨List.contains_iff_mem.mpr hy,List.contains_iff_mem.mpr hz⟩
       exact False.elim (test yes)
     · exact hin
    obtain ⟨w,found,hwt,hwy,hwz⟩:=ih ⟨v,inside,hy,hz⟩
    exact ⟨w,by simp only [findCommon,if_neg test,found],List.mem_cons_of_mem _ hwt,hwy,hwz⟩

theorem clique_search_complete (T : Tree) (A B C : List Nat) (v w z : RMAF.Vertex)
 (hab : overlap T A B=some v) (hbc : overlap T B C=some w) (hac : overlap T A C=some z) :
 ∃r,select T A B C=some (.clique r) ∧ r∈minimalVertices A T ∧ r∈minimalVertices B T ∧ r∈minimalVertices C T := by
 have ab:=repeated_common_some _ _ v hab
 have bc:=repeated_common_some _ _ w hbc
 have ac:=repeated_common_some _ _ z hac
 let HA:=Hull (selectedLeaves A T)
 let HB:=Hull (selectedLeaves B T)
 let HC:=Hull (selectedLeaves C T)
 have hab' : ∃u,HA u ∧ HB u := ⟨v,(minimalVertices_correct A T v).mp ab.1,(minimalVertices_correct B T v).mp ab.2⟩
 have hbc' : ∃u,HB u ∧ HC u := ⟨w,(minimalVertices_correct B T w).mp bc.1,(minimalVertices_correct C T w).mp bc.2⟩
 have hac' : ∃u,HA u ∧ HC u := ⟨z,(minimalVertices_correct A T z).mp ac.1,(minimalVertices_correct C T z).mp ac.2⟩
 have haa' : ∃u,HA u ∧ HA u := ⟨v,(minimalVertices_correct A T v).mp ab.1,(minimalVertices_correct A T v).mp ab.1⟩
 have hba' : ∃u,HB u ∧ HA u := ⟨v,(minimalVertices_correct B T v).mp ab.2,(minimalVertices_correct A T v).mp ab.1⟩
 have hca' : ∃u,HC u ∧ HA u := ⟨z,(minimalVertices_correct C T z).mp ac.2,(minimalVertices_correct A T z).mp ac.1⟩
 obtain ⟨r,ar,br,cr,_⟩:=PairGeometry.helly_four HA HB HC HA
  (hull_convex _) (hull_convex _) (hull_convex _) (hull_convex _) hab' hac' haa' hbc' hba' hca'
 have triple : ∃r,r∈minimalVertices A T ∧ r∈minimalVertices B T ∧ r∈minimalVertices C T :=
  ⟨r,(minimalVertices_correct A T r).mpr ar,(minimalVertices_correct B T r).mpr br,(minimalVertices_correct C T r).mpr cr⟩
 obtain ⟨u,found,au,bu,cu⟩:=common_complete _ _ _ triple
 exact ⟨u,by simp only [select,hab,hbc,hac,found,Option.map_some],au,bu,cu⟩
end ContactedHard2Overlap

-- Author integration type/axiom reports; proof text above is unchanged apart from recorded import edits.
set_option pp.universes true
#check @ContactedHard2Overlap.common_complete
#print axioms ContactedHard2Overlap.common_complete
#check @ContactedHard2Overlap.clique_search_complete
#print axioms ContactedHard2Overlap.clique_search_complete
