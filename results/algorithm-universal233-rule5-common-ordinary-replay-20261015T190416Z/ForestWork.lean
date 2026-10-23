import ForestDisjoint
import ForestGeometryWork
namespace GenericForest
open RMAF RestrictionBridge ForestState OutputState ForestGroups VertexGeometry
open Universal233 Universal233.CoreProgram Universal233.PaidQueries
open Universal233.SourceCoverage Universal233.WholeSourceMass Universal233.CoreWork Universal233.WholeSourceWork

def sourceNodes (ss : List Tree) := (ss.map treeNodes).sum
def targetNodes : Option Tree → Nat | none => 0 | some t => treeNodes t

/-- Conservative source inspection sheet, not extracted-machine instructions.
Scalar operations are unit charged; arbitrary label/q bit costs must be paid by
the local contract coefficient. The term covers guards, depth01 preprocessing,
literal restrictions, final original checks, and minimum comparisons. -/
def inspectionBill (T : Option Tree) (ss : List Tree) (q : Nat) : Nat :=
  4096 * (targetNodes T + sourceNodes ss + ss.length + q + 1)^8

/-- All actual ordered source-pair span constructions and membership probes.
This overcharges pairs rejected by i<j and early successful membership probes. -/
def overlapBill (t : Tree) (ss : List Tree) : Nat :=
  (ss.map fun a => (ss.map fun b =>
    (meterMinimal (leaves a) t).work + (meterMinimal (leaves b) t).work +
    16 * (treeNodes t+1)^3).sum).sum

def generationBill (t : Tree) (ss : List Tree) (i : Nat) (v : RMAF.Vertex) (q : Nat) : Nat :=
  match ss[i]? with
  | none => 1
  | some s =>
    (meterGenerate s (colorLabel t v) q).measured.work +
      ((leaves s).map fun x => (meterColorLabel t v x).work).sum

def materializationBill (t : Tree) (ss : List Tree) (q i : Nat) (o : Output) : Nat :=
  inspectionBill (some t) ss q +
  inspectionBill (some t) (replace ss i o.partition) (q-o.sourceCuts.length) +
  256 * (o.partition.flatten.length + (o.sourceCuts.map List.length).sum + sourceNodes ss + 1)^4

def nonrecursiveBill (ordinary : Tree → Tree → Nat → Option Forest)
    (ordinaryWork : Tree → Tree → Nat → Nat) (T : Option Tree) (ss : List Tree) (q : Nat) : Nat :=
  inspectionBill T ss q +
  if proper T ss && !agrees T ss (ss.map leaves) then
    match T, ss with
    | none, _ => 0
    | some t, [s] => ordinaryWork t s q
    | some t, _ => match overlap t ss with
      | none => match jobs t ss with
        | none => 0
        | some js =>
          let m := meterSchedule
            (fun p b => (ordinary p.1 p.2 b).map (fun F => (F.length-1,F)))
            (fun p b => ordinaryWork p.1 p.2 b) q js
          m.callerWork + m.recursiveWork
      | some h => overlapBill t ss + generationBill t ss h.left h.vertex q +
          generationBill t ss h.right h.vertex q +
          ((branches t ss h q).map fun io => materializationBill t ss q io.1 io.2).sum +
          inspectionBill T ss q * ((branches t ss h q).length+1)
  else 0

/-- Natural source bills embedded in Rat. The recursive summation follows every
literal filterMap occurrence of the production program, including duplicates.
Core refusal/prune/prefix bills and exact paid ordinary-call bills occur above. -/
def sourceWork (ordinary : Tree → Tree → Nat → Option Forest)
    (ordinaryWork : Tree → Tree → Nat → Nat) (T : Option Tree) (ss : List Tree) (q : Nat) : Rat :=
  (nonrecursiveBill ordinary ordinaryWork T ss q : Rat) +
  if proper T ss && !agrees T ss (ss.map leaves) then
    match T, ss with
    | none, _ => 0
    | some _, [_] => 0
    | some t, _ => match overlap t ss with
      | none => 0
      | some h => ((branches t ss h q).map fun io =>
          let d := io.2.sourceCuts.length
          if _hd : 1 ≤ d ∧ d ≤ q then sourceWork ordinary ordinaryWork T (replace ss io.1 io.2.partition) (q-d)
          else 0).sum
  else 0
termination_by q
decreasing_by omega

theorem branch_paid_proper (t : Tree) (ss : List Tree) (hp : proper (some t) ss = true)
    (h : Overlap) (hh : overlap t ss = some h) (q i : Nat) (o : Output)
    (hm : (i,o) ∈ branches t ss h q) :
    1 ≤ o.sourceCuts.length ∧ o.sourceCuts.length ≤ q ∧
      proper (some t) (replace ss i o.partition) = true := by
  obtain ⟨s,r,hi,hj,hne,hv,hw⟩ := selected_parents_distinct t ss hp h hh
  have hs := List.mem_of_getElem? hi
  have hr := List.mem_of_getElem? hj
  have hn := actual_parent_regions t ss hp s r hs hr hne h.vertex hv hw
  have one (i : Nat) (s : Tree) (hi : ss[i]? = some s)
      (nonlabel : ¬selectedLeaves (leaves s) t h.vertex)
      (occupied : h.vertex ∈ minimalVertices (leaves s) t)
      (ho : o ∈ (generate s (colorLabel t h.vertex) q).outputs) :
      1 ≤ o.sourceCuts.length ∧ o.sourceCuts.length ≤ q ∧
        proper (some t) (replace ss i o.partition) = true := by
    have split := split_at_source ss i s hi
    have he := replace_at_source ss i s o.partition hi
    exact ⟨core_emission_positive t ss hp s (List.mem_of_getElem? hi) h.vertex nonlabel occupied q o ho,
      generate_output_budget s _ q o ho,by
        rw [he]
        exact proper_replaced t (ss.take i) s (ss.drop (i+1)) (by simpa [split] using hp)
          (Universal233.Assembly.generated_source_valid s _ q o ho).1⟩
  simp only [branches,List.mem_append,List.mem_map] at hm
  rcases hm with ⟨a,ha,he⟩ | ⟨a,ha,he⟩
  · cases he; exact one h.left s hi hn.1 hv (by simpa [raw,hi] using ha)
  · cases he; exact one h.right r hj hn.2.1 hw (by simpa [raw,hj] using ha)

theorem branch_mass_le_one (t : Tree) (ss : List Tree) (hp : proper (some t) ss = true)
    (h : Overlap) (hh : overlap t ss = some h) (q : Nat) (c : Rat) (hc : 2 ≤ c) :
    ((branches t ss h q).map fun io => c ^ (-(io.2.sourceCuts.length : Int))).sum ≤ 1 := by
  obtain ⟨s,r,hi,hj,hne,hv,hw⟩ := selected_parents_distinct t ss hp h hh
  have hm := two_actual_cores_mass t ss hp s r (List.mem_of_getElem? hi) (List.mem_of_getElem? hj)
    hne h.vertex hv hw q c hc
  have hmass : ((branches t ss h q).map fun io => c ^ (-(io.2.sourceCuts.length : Int))).sum ≤ 2*c^(-1 : Int) := by
    simpa [branches,raw,hi,hj,rawQMass,List.map_append,List.map_map,Function.comp_def,List.sum_append] using hm
  have cpos : 0 < c := by grind
  have htwo : 2*c^(-1 : Int) ≤ 1 := by
    rw [Rat.zpow_neg,Rat.zpow_one]
    apply Rat.le_of_mul_le_mul_right (c := c) _ cpos
    rw [Rat.mul_assoc,Rat.inv_mul_cancel c (Rat.ne_of_gt cpos),Rat.mul_one,Rat.one_mul]
    exact hc
  exact Rat.le_trans hmass htwo

def LocalBillBound (ordinary : Tree → Tree → Nat → Option Forest)
    (ordinaryWork : Tree → Tree → Nat → Nat) (T : Option Tree) (Q : Nat) (c K : Rat) : Prop :=
  ∀ ss q, q ≤ Q → proper T ss = true →
    (nonrecursiveBill ordinary ordinaryWork T ss q : Rat) ≤ K*c^q

end GenericForest
