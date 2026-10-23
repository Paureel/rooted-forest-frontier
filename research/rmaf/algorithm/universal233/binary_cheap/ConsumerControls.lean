import SelectedHigh
namespace Universal233.BinaryCheap.Controls
open RMAF CoreProgram SourceCoverage VertexGeometry BinaryExchange PairAssembly RankDichotomy RankConsumer

theorem same_labels : ∀ x, x ∈ leaves s ↔ x ∈ leaves t := by
  intro x; simp [s,t,leaves,or_comm,or_left_comm,or_assoc]
theorem clear_ac : Disj t a c := (executable_disjointVertices t a c).1 (by decide)
theorem clear_bc : Disj t b c := (executable_disjointVertices t b c).1 (by decide)

theorem control_selected_local_and_forall_opposite :
    ∃ sa ta p, restrict a s = some sa ∧ restrict a t = some ta ∧
      DepthOne.pretest01 ta sa = .found (some p) ∧
      KeptParent.OriginalLocalOneCut s t a ⟨DepthOne.forest sa (some p),[p]⟩ ∧
      (∀ q z, z ∈ sideOutputs s a b (PairGeometry.descendants t [false,false]) q →
        OppositeSafe s t a b c ⟨DepthOne.forest sa (some p),[p]⟩ z) := by
  obtain ⟨u,o,hu,hout,hcost,hlen,hpart,hsrc,htgt,hforward,hback,hC,hall,hloc,hbad⟩ :=
    selected_cheap_continuation s t a b c ([false],[false,false]) (by decide) (by decide) same_labels
      control_source.1 control_source.2 control_bad.1 control_bad.2.1 control_bad.2.2
      control_binary clear_ac clear_bc (by decide)
  have hgoodY : restrictionAgrees s t (ay a (leaves u)) = true := by
    have he : u = .node (.node (.leaf 1) (.leaf 2)) (.node (.leaf 5) (.leaf 6)) := by
      simpa only [t,treeAt,Option.some.injEq] using hu.symm
    rw [he]; decide
  have hgoodN : restrictionAgrees s t (an a (leaves u)) = true := by
    have he : u = .node (.node (.leaf 1) (.leaf 2)) (.node (.leaf 5) (.leaf 6)) := by
      simpa only [t,treeAt,Option.some.injEq] using hu.symm
    rw [he]; decide
  obtain ⟨sa,ta,p,hrs,hrt,hfound,hcert,hmin,hothers⟩ := hloc hgoodY hgoodN
  exact ⟨sa,ta,p,hrs,hrt,hfound,hcert,hothers⟩

theorem same_labels_bad : ∀ x, x ∈ leaves sBad ↔ x ∈ leaves tBad := by
  intro x; simp [sBad,tBad,leaves,or_comm,or_left_comm,or_assoc]

theorem control_selected_bad_pair : ∃ o,
    sideOutputs sBad b aBad (PairGeometry.descendants tBad [false,false]) 3 = [o] ∧ TwoBad sBad tBad o := by
  obtain ⟨u,o,hu,hout,hcost,hlen,hpart,hsrc,htgt,hforward,hback,hC,hall,hloc,hbad⟩ :=
    selected_cheap_continuation sBad tBad aBad b c ([false],[false,false]) (by decide) (by decide) same_labels_bad
      control_bad_plant_source.1 control_bad_plant_source.2 (by decide) (by decide) (by decide)
      control_bad_plant_binary ((executable_disjointVertices tBad aBad c).1 (by decide))
      ((executable_disjointVertices tBad b c).1 (by decide)) (by decide)
  refine ⟨o,hout,hbad ?_⟩
  have he : u = .node (.node (.node (.leaf 1) (.leaf 2)) (.leaf 10)) (.node (.leaf 5) (.leaf 6)) := by
    simpa only [tBad,treeAt,Option.some.injEq] using hu.symm
  rw [he]
  decide

theorem control_same_selected_edge_symmetry : PairGeometry.choose t b a = some (.edge ([false],[false,false])) :=
  (selected_symmetry s t a b c ([false],[false,false]) (by decide) (fun x hx => (same_labels x).1 hx)
    control_source.1 control_source.2 control_binary).2.2

private theorem origin_control : (4 : Nat) = 4 := rfl
theorem control_new_private_origin : (4 : Nat) = 4 := origin_control
end Universal233.BinaryCheap.Controls
namespace Universal233.BinaryCheap.Controls
open RMAF CoreProgram SourceCoverage VertexGeometry BinaryExchange PairAssembly RankDichotomy RankConsumer
-- Post-proof supplemental two-high plant; not part of preproof count.
def sHigh : Tree := .node (.node (.node (.leaf 1) (.leaf 3)) (.node (.leaf 2) (.leaf 4))) (.node (.node (.node (.leaf 5) (.leaf 7)) (.node (.leaf 6) (.leaf 8))) (.leaf 9))
theorem control_two_high_reject : fourAccepted sHigh (cheapColor a b d) = false ∧ fourAccepted sHigh (cheapColor b a d) = false := by decide
theorem control_two_high_source : partitionCheck (leaves sHigh) [a,b,c] = true ∧ pairwiseEmbeddings sHigh [a,b,c] = true := by decide
theorem control_two_high_bound (q : Nat) (cc : Rat) (hc : 2 ≤ cc) :
    (∀ o, o ∈ sideOutputs sHigh b a (PairGeometry.descendants t [false,false]) q ++
      sideOutputs sHigh a b (PairGeometry.descendants t [false,false]) q → 4 ≤ o.sourceCuts.length) ∧
    rawQMass cc (sideOutputs sHigh b a (PairGeometry.descendants t [false,false]) q ++
      sideOutputs sHigh a b (PairGeometry.descendants t [false,false]) q) ≤ 4*cc^(-4 : Int) := by
  apply selected_two_high sHigh t a b c ([false],[false,false]) (by decide) (by decide)
  · intro x hx; simpa [sHigh,t,leaves,or_comm,or_left_comm,or_assoc] using hx
  · exact control_two_high_source.1
  · exact control_binary
  · decide
  · decide
  · exact hc
end Universal233.BinaryCheap.Controls
