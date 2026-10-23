import RIInitial
namespace OrdinaryDispatch.RecoveryInitialBits
open RMAF Universal233 WholeSourceWork CoreProgram CoreWork
open OrdinaryDispatch.RecoveryBits

theorem initializeBits_some (W : Nat) (t : InputTree) (P : List (List (List Bool))) (budget q : List Bool) (tree : BitTree)
 (h : (initializeBits W t P budget).value=some (q,tree)) :
 q=(clipOwned W budget (inputLeaves t)).value ∧ tree=(build P [] t).value := by
 simp only [initializeBits,copyInput_value,copyForest_value,copyBits_value,initialCore,leafArrays_value] at h
 split at h
 · cases h;exact ⟨rfl,rfl⟩
 · contradiction

theorem initializeBits_refused (W : Nat) (t : InputTree) (P : List (List (List Bool))) (budget : List Bool) :
 (initializeBits W t P budget).value=none ↔ ¬(leaves (viewInput t)).Nodup := by
 simp only [initializeBits,copyInput_value,copyForest_value,copyBits_value,initialCore,leafArrays_value,ownedNodup_value,inputLeaves_view]
 by_cases h:(leaves (viewInput t)).Nodup <;> simp [h]

theorem initializeBits_output_words (W : Nat) (t : InputTree) (P : List (List (List Bool))) (budget q : List Bool) (tree : BitTree)
 (positive : 1≤W) (tw : InputWords W t) (pw : ForestWords W P) (bw : budget.length≤W)
 (h : (initializeBits W t P budget).value=some (q,tree)) :
 q.length≤W ∧ TreeWords W tree := by
 obtain ⟨a,b⟩:=initializeBits_some W t P budget q tree h
 subst q;subst tree
 exact ⟨clipOwned_length W budget (inputLeaves t) positive bw,build_words W P [] t tw pw⟩

/-- Retained result cells are derived from the actual source construction.
Temporary lifetimes are separately traversed and billed by the producer. -/
theorem initializeBits_retained_cells (W : Nat) (t : InputTree) (P : List (List (List Bool))) (budget q : List Bool) (tree : BitTree)
 (positive : 1≤W) (tw : InputWords W t) (pw : ForestWords W P) (bw : budget.length≤W)
 (h : (initializeBits W t P budget).value=some (q,tree)) :
 q.length+treeCells tree+3≤W+(W+4)*(inputNodes t*(inputNodes t+2))+3 := by
 have widths:=initializeBits_output_words W t P budget q tree positive tw pw bw h
 have some:=initializeBits_some W t P budget q tree h
 have cells:=treeCells_source_bound W tree widths.2
 rw [some.2,build_value] at cells
 have fp:=fromTree_footprint (FinalCutRecovery.blockColor (P.map (List.map decode))) [] (viewInput t)
 simp only [List.length_nil,Nat.zero_add,inputNodes_view] at fp
 have scale:=Nat.mul_le_mul_left (W+4) fp
 rw [some.2]
 omega

/-- Direct original stored input bound; no oracle coloring or initializer cost
premise appears. Count width and word widths are separate displayed premises. -/
theorem represented_initialization (W : Nat) (t : InputTree) (P : List (List (List Bool))) (budget : List Bool)
 (positive : 1≤W) (tw : InputWords W t) (pw : ForestWords W P) (bw : budget.length≤W)
 (fits : (inputLeaves t).length<2^W) :
 viewInit (initializeBits W t P budget).value=
 (OrdinaryDispatch.RecoveryLocalWork.meterInitial (OrdinaryDispatch.RecoveryLocalWork.meterColor (P.map (List.map decode)))
  (decode budget) (viewInput t)).value ∧
 (initializeBits W t P budget).work≤2048*(W+1)*(inputNodes t+P.flatten.length+P.length+1)^2 := by
 exact ⟨initializeBits_value W t P budget fits,
  initializeBits_work W (inputNodes t+P.flatten.length+P.length) t P budget positive tw pw bw (by omega) (by omega)⟩
end OrdinaryDispatch.RecoveryInitialBits
