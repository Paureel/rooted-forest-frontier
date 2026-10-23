-- Own geometry for the exact original branches child record.
import Boundary16
import PoolClassificationSelector
open RMAF Universal233 VertexGeometry OwnHigh CherryBranching
namespace SourceBoundary
theorem same_block_of_label (F : List (List Nat)) (hn : F.flatten.Nodup)
    (P Q : List Nat) (hp : P ∈ F) (hq : Q ∈ F) (x : Nat) (hx : x ∈ P) (hy : x ∈ Q) : P=Q := by
  induction F with
  | nil => simp at hp
  | cons R F ih =>
    have hd := List.nodup_append.mp hn
    rcases List.mem_cons.mp hp with hp | hp
    · subst P
      rcases List.mem_cons.mp hq with hq | hq
      · exact hq.symm
      · exact False.elim (hd.2.2 x hx x (List.mem_flatten.mpr ⟨Q,hq,hy⟩) rfl)
    · rcases List.mem_cons.mp hq with hq | hq
      · subst Q
        exact False.elim (hd.2.2 x hy x (List.mem_flatten.mpr ⟨P,hp,hx⟩) rfl)
      · exact ih hd.2.1 hp hq
theorem singleton_refines (S : Tree) (F : List (List Nat)) (a : Nat)
    (hpart : partitionCheck (leaves S) F=true) (ha : [a] ∈ F) :
    Refines F (singletonPartition S a) := by
  intro P hp
  by_cases he : P=[a]
  · refine ⟨[a],by simp [singletonPartition],?_⟩
    intro x hx
    simpa [he] using hx
  · refine ⟨(leaves S).filter (fun x => x != a),by simp [singletonPartition],?_⟩
    intro x hx
    apply List.mem_filter.mpr
    refine ⟨block_subset (leaves S) F hpart P hp x hx,?_⟩
    have hxa : x≠a := by
      intro hxa
      have haP : a∈P := by simpa [hxa] using hx
      exact he (same_block_of_label F (partition_flat_nodup (leaves S) F hpart) P [a] hp ha a haP (by simp))
    simpa using hxa
theorem branches_geometry (T S : Tree) (p : RMAF.Vertex) (a b : Nat) (F : List (List Nat))
    (hproper : DepthOne.proper T S=true) (hc : CoreGraph.CherryAt T p a b)
    (hag : agreement T S F=true) :
    ∃ c ∈ branches S a b, Refines F c.partition := by
  have hp : partitionCheck (leaves S) F=true := by
    have h := hag
    simp only [agreement,Bool.and_eq_true] at h
    exact h.1.1.1.2
  rcases literal_dichotomy T S p a b F hproper hc hag with ha | hb | hpend
  · exact ⟨singletonChild S a, by simp [branches], singleton_refines S F a hp ha⟩
  · exact ⟨singletonChild S b, by simp [branches], singleton_refines S F b hp hb⟩
  · exact ⟨pendantChild S a b, by simp [branches], hpend⟩
#print axioms branches_geometry
#check branches_geometry
end SourceBoundary
