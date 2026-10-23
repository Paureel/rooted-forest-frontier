# Verbatim premise and consumer supplement

All snippets are extracted from the hash-bound freshly rebuilt v3 sources. Source line numbers refer to isolated-build-v1. OrdinaryIH is supplied only by the external ordinary callback theorem; LocalBillBound is the separate work premise. Other statements below are proved dependencies in the fresh 143-source rebuild, rather than new assumed oracle fields. The full exact types/bodies, including private/generated occurrences, are retained in the producer records.

## ForestProgram

### OrdinaryIH

Consuming source lines: 86.

```lean
structure OrdinaryIH (ordinary : Tree → Tree → Nat → Option Forest) where
```

ForestProgram.lean:86

```lean
structure OrdinaryIH (ordinary : Tree → Tree → Nat → Option Forest) where
  sound : ∀ t s q F, DepthOne.proper t s = true → ordinary t s q = some F →
    agreement t s F = true ∧ F.length-1 ≤ q ∧
      ∀ G, agreement t s G = true → F.length ≤ G.length
  complete : ∀ t s q G, DepthOne.proper t s = true → agreement t s G = true →
    G.length-1 ≤ q → ∃ F, ordinary t s q = some F
```

### ExactAt

Consuming source lines: 93.

```lean
def ExactAt (f : Option Tree → List Tree → Nat → Option Forest) : Prop :=
```

ForestProgram.lean:93

```lean
def ExactAt (f : Option Tree → List Tree → Nat → Option Forest) : Prop
```

### DisjointExact

Consuming source lines: 100.

```lean
def DisjointExact (ordinary : Tree → Tree → Nat → Option Forest) : Prop :=
```

ForestProgram.lean:100

```lean
def DisjointExact (ordinary : Tree → Tree → Nat → Option Forest) : Prop
```

## ForestReplace

### source_component

Consuming source lines: 52, 85.

```lean
  obtain ⟨U,hU,hr⟩ := (source_component s Q u).1 hu
```

```lean
      exact ⟨u,by simp [replaced,(source_component r Q u).2 ⟨U,hU,hu⟩],
```

Materialize.lean:5

```lean
theorem source_component (S : Tree) (Q : List (List Nat)) (s : Tree) :
    s ∈ sourceForest S Q ↔ ∃ U ∈ Q, restrict U S = some s
```

### component_labels

Consuming source lines: 53.

```lean
  have hl := component_labels s u U Q hr hsn hQ hU
```

GroupForward.lean:26

```lean
theorem component_labels (t u : Tree) (U : List Nat) (Q : List (List Nat))
    (hr : restrict U t = some u) (proper : (leaves t).Nodup)
    (hQ : partitionCheck (leaves t) Q = true) (hU : U ∈ Q) : (leaves u).Perm U
```

### local_partition

Consuming source lines: 58.

```lean
  refine ⟨⟨local_partition s u U (family (leaves s) F) Q hr hc.1.1 hQ href hU,?_⟩,?_⟩
```

GroupPartition.lean:96

```lean
theorem local_partition (t u : Tree) (U : List Nat) (F Q : List (List Nat))
    (hr : restrict U t = some u) (hF : partitionCheck (leaves t) F = true)
    (hQ : partitionCheck (leaves t) Q = true) (href : Refines F Q) (hU : U ∈ Q) :
    partitionCheck (leaves u) (family U F) = true
```

### source_topology

Consuming source lines: 62.

```lean
    rw [source_topology t s u U B hr hBU]
```

Equivalence.lean:5

```lean
theorem source_topology (T S s : Tree) (U B : List Nat)
    (hs : restrict U S = some s) (sub : B ⊆ U) :
    targetAgrees (some T) s B = restrictionAgrees T S B
```

### pairwise_transport

Consuming source lines: 64.

```lean
  · exact (pairwise_transport s u U _ hr
```

GroupEmbedding.lean:237

```lean
theorem pairwise_transport (t u : Tree) (U : List Nat) (F : List (List Nat))
    (hu : restrict U t = some u) (sub : ∀ B ∈ F, B ⊆ U) :
    pairwiseEmbeddings t F = true ↔ pairwiseEmbeddings u F = true
```

### generated_source_valid

Consuming source lines: 98.

```lean
  have hQ := (generated_source_valid s color q o ho).1
```

SourceValidity.lean:87

```lean
theorem generated_source_valid (T : Tree) (color : Nat → Nat) (q : Nat) (o : Output)
    (ho : o ∈ (generate T color q).outputs) :
    partitionCheck (leaves T) o.partition = true ∧ pairwiseEmbeddings T o.partition = true
```

### generate_original_realization

Consuming source lines: 105.

```lean
  obtain ⟨_,_,cs,_,_,_,_,_,_,_,hc⟩ := generate_original_realization s color q o ho
```

Realization.lean:109

```lean
theorem generate_original_realization (T : Tree) (color : Nat → Nat) (q : Nat)
    (o : Output) (ho : o ∈ (generate T color q).outputs) : RealizedOutput T o
```

### checked_materialization

Consuming source lines: 24, 104.

```lean
  have mat := checked_materialization s Q hsn hQ
```

```lean
  have hm := (checked_materialization s o.partition hn hQ).1
```

Materialize.lean:35

```lean
theorem checked_materialization (S : Tree) (Q : List (List Nat))
    (properS : (leaves S).Nodup) (hQ : partitionCheck (leaves S) Q = true) :
    (sourceForest S Q).length = Q.length ∧
    ((sourceForest S Q).map leaves).flatten.Perm Q.flatten ∧
    (∀ s ∈ sourceForest S Q, ∃ U ∈ Q, restrict U S = some s ∧
      (leaves s).Perm U ∧ (leaves s).Nodup ∧ leaves s ≠ [])
```

### checked_flatten_perm

Consuming source lines: 25.

```lean
  have loc := mat.2.1.trans (checked_flatten_perm (leaves s) Q hsn hQ)
```

GroupReconstruction.lean:7

```lean
theorem checked_flatten_perm (L : List Nat) (F : List (List Nat))
    (proper : L.Nodup) (hp : partitionCheck L F = true) : F.flatten.Perm L
```

Lemmas.lean:78

```lean
theorem checked_flatten_perm (L : List Nat) (F : List (List Nat))
    (hn : L.Nodup) (hp : partitionCheck L F = true) : F.flatten.Perm L
```

## ForestReverse

### cross_subblocks

Consuming source lines: 69.

```lean
    · exact cross_subblocks s Q sourceQ U V B C hU hV he hBU hCV
```

GroupReconstruction.lean:78

```lean
theorem cross_subblocks (t : Tree) (Q : List (List Nat))
    (hq : pairwiseEmbeddings t Q = true) (U V B C : List Nat)
    (hU : U ∈ Q) (hV : V ∈ Q) (hne : U ≠ V) (hBU : B ⊆ U) (hCV : C ⊆ V) :
    Clear (minimalVertices B t) (minimalVertices C t)
```

### checked_restrictions

Consuming source lines: 39, 50.

```lean
    obtain ⟨u,hu,hl⟩ := checked_restrictions s Q hsn hQ U hU
```

```lean
    obtain ⟨u,hu,hl⟩ := checked_restrictions s Q hsn hQ U hU
```

Materialize.lean:9

```lean
theorem checked_restrictions (S : Tree) (Q : List (List Nat))
    (properS : (leaves S).Nodup) (hQ : partitionCheck (leaves S) Q = true) :
    ∀ U ∈ Q, ∃ s, restrict U S = some s ∧ (leaves s).Perm U
```

### Refines

Consuming source lines: 34, 76, 95.

```lean
    (href : RestrictionBridge.Refines (family (leaves s) F) Q)
```

```lean
      RestrictionBridge.Refines (family (leaves s) F) Q := by
```

```lean
  have href : RestrictionBridge.Refines (family (leaves s) F) Q := by
```

CherryCoarsening.lean:158

```lean
def Refines {t} (P Q : SourcePartition t) : Prop
```

Composition.lean:7

```lean
def Refines (F Q : List (List Nat)) : Prop
```

GroupPartition.lean:7

```lean
def Refines (F Q : List (List Nat)) : Prop
```

Parents.lean:5

```lean
def Refines (F P : List (List Nat)) : Prop
```

## ForestOverlap

### disjoint_parent_overlap_nonlabel

Consuming source lines: 77.

```lean
  have hn := disjoint_parent_overlap_nonlabel _ _ t v
```

Bridge.lean:348

```lean
theorem disjoint_parent_overlap_nonlabel (D E : List Nat) (t : RMAF.Tree) (v : Vertex)
    (hDE : ∀ x, x ∈ D → x ∈ E → False)
    (hd : v ∈ RMAF.minimalVertices D t) (he : v ∈ RMAF.minimalVertices E t) :
    ¬selectedLeaves D t v ∧ ¬selectedLeaves E t v
```

### executable_region_count_two_or_three

Consuming source lines: 79, 80.

```lean
  exact ⟨hn.1,hn.2,executable_region_count_two_or_three _ t v hn.1 hv,
```

```lean
    executable_region_count_two_or_three _ t v hn.2 hw⟩
```

Bridge.lean:427

```lean
theorem executable_region_count_two_or_three (D : List Nat) (t : RMAF.Tree) (v : Vertex)
    (hn : ¬selectedLeaves D t v) (hv : v ∈ RMAF.minimalVertices D t) :
    (regions D t v).length = 2 ∨ (regions D t v).length = 3
```

### original_colors_at_least_two

Consuming source lines: 88, 100, 102.

```lean
  have hr := original_colors_at_least_two (leaves s) t v (proper_parts _ _ hp).1 hsupp hn hv
```

```lean
  have hsc := original_colors_at_least_two (leaves s) t v (proper_parts _ _ hp).1
```

```lean
  have hrc := original_colors_at_least_two (leaves r) t v (proper_parts _ _ hp).1
```

OriginalColors.lean:41

```lean
theorem original_colors_at_least_two (D : List Nat) (T : Tree) (v : RMAF.Vertex)
    (hn : (leaves T).Nodup) (hs : ∀ x, x ∈ D → x ∈ leaves T)
    (hnv : ¬selectedLeaves D T v) (hv : v ∈ minimalVertices D T) :
    2 ≤ (localColors D (colorLabel T v)).length
```

### generate_color_cost

Consuming source lines: 89.

```lean
  have hc := generate_color_cost s (colorLabel t v) q o ho
```

ColorBudget.lean:192

```lean
theorem generate_color_cost (t : Tree) (color : Nat → Nat) (q : Nat) (o : Output)
    (ho : o ∈ (generate t color q).outputs) :
    (dedupNat ((leaves t).map color)).length ≤ o.sourceCuts.length + 1
```

### generate_mass_of_count

Consuming source lines: 104, 105.

```lean
  have a := generate_mass_of_count s (colorLabel t v) q 1 c hc hsc
```

```lean
  have b := generate_mass_of_count r (colorLabel t v) q 1 c hc hrc
```

WholeMass.lean:51

```lean
theorem generate_mass_of_count (S : Tree) (color : Nat → Nat) (q L : Nat)
    (b : Rat) (hb : 2 ≤ b)
    (hr : L + 1 ≤ (dedupNat ((leaves S).map color)).length) :
    rawQMass b (generate S color q).outputs ≤ b ^ (-(L : Int))
```

### rawQMass_append

Consuming source lines: 106.

```lean
  rw [rawQMass_append]
```

WholeMass.lean:62

```lean
theorem rawQMass_append (b : Rat) (xs ys : List Output) :
    rawQMass b (xs ++ ys) = rawQMass b xs + rawQMass b ys
```

### original_label_avoids_iff

Consuming source lines: 148.

```lean
    exact (original_label_avoids_iff t B v (proper_parts _ _ hp).1
```

Bridge.lean:588

```lean
theorem original_label_avoids_iff (t : RMAF.Tree) (D : List Nat) (v : Vertex)
    (hn : (RMAF.leaves t).Nodup) (hlabels : ∀ x, x ∈ D → x ∈ RMAF.leaves t)
    (hno : ¬selectedLeaves D t v) :
    (v ∉ RMAF.minimalVertices D t) ↔ LabelMonochromatic (colorLabel t v) D
```

### generate_partition_coverage_paid

Consuming source lines: 152.

```lean
  obtain ⟨o,ho,href,hbudget⟩ := generate_partition_coverage_paid s (family (leaves s) F)
```

OutputBudget.lean:69

```lean
theorem generate_partition_coverage_paid (t : Tree) (bs : List (List Nat)) (color : Nat → Nat)
    (hnd : (leaves t).Nodup)
    (hp : partitionCheck (leaves t) bs = true) (he : pairwiseEmbeddings t bs = true)
    (hm : ∀ b, b ∈ bs → LabelMonochromatic color b)
    (q : Nat) (hq : bs.length - 1 ≤ q) :
    ∃ o, o ∈ (generate t color q).outputs ∧ RefinesBlocks bs o.partition ∧ o.sourceCuts.length ≤ q
```

## ForestConditional

### initial_state_agreement_iff

Consuming source lines: 72, 76.

```lean
            have pg := (initial_state_agreement_iff t s G hp).1 ha
```

```lean
            have fs := (initial_state_agreement_iff t s F hp).2 hf
```

GroupStateFacts.lean:126

```lean
theorem initial_state_agreement_iff (t s : Tree) (F : List (List Nat))
    (hp : proper (some t) [s] = true) :
    agrees (some t) [s] F = true ↔ agreement t s F = true
```

### sources_le_blocks

Consuming source lines: 54.

```lean
        simpa using sources_le_blocks T ss G ha⟩
```

GroupCostProof.lean:21

```lean
theorem sources_le_blocks (T : Option Tree) (ss : List Tree) (F : List (List Nat))
    (ha : agrees T ss F = true) : ss.length ≤ F.length
```

### OrdinaryIH

Consuming source lines: 43, 45, 74, 75.

```lean
assembly premise, not a theorem supplied by `OrdinaryIH` in this package. -/
```

```lean
    (ho : OrdinaryIH ordinary) (hd : DisjointExact ordinary) : ExactAt (solve ordinary) := by
```

```lean
            obtain ⟨F,hF⟩ := ho.complete t s q G pp pg (by simpa [additionalCost] using hq)
```

```lean
            obtain ⟨hf,hb,hm⟩ := ho.sound t s q F pp hF
```

ForestProgram.lean:86

```lean
structure OrdinaryIH (ordinary : Tree → Tree → Nat → Option Forest) where
  sound : ∀ t s q F, DepthOne.proper t s = true → ordinary t s q = some F →
    agreement t s F = true ∧ F.length-1 ≤ q ∧
      ∀ G, agreement t s G = true → F.length ≤ G.length
  complete : ∀ t s q G, DepthOne.proper t s = true → agreement t s G = true →
    G.length-1 ≤ q → ∃ F, ordinary t s q = some F
```

### DisjointExact

Consuming source lines: 42, 45.

```lean
/-- Downstream conditional. `DisjointExact` is a visibly additional OPEN
```

```lean
    (ho : OrdinaryIH ordinary) (hd : DisjointExact ordinary) : ExactAt (solve ordinary) := by
```

ForestProgram.lean:100

```lean
def DisjointExact (ordinary : Tree → Tree → Nat → Option Forest) : Prop
```

## ForestLocal

### local_proper

Consuming source lines: 52.

```lean
  have hh := local_proper (some t) ss (ss.map leaves) hp hQ own (leaves s) (List.mem_map.2 ⟨s,hs,rfl⟩)
```

GroupDefs.lean:67

```lean
theorem local_proper (T : Option Tree) (ss : List Tree) (Q : List (List Nat))
    (hp : proper T ss = true) (hq : partitionCheck (labels T) Q = true)
    (own : Owns ss Q) (U : List Nat) (hU : U ∈ Q) :
    proper (localTarget T U) (owned ss U) = true
```

### local_forward

Consuming source lines: 60.

```lean
  have hh := local_forward (some t) ss (ss.map leaves) G ha (proper_parts _ _ hp).2 own
```

GroupForwardProof.lean:22

```lean
theorem local_forward (T : Option Tree) (ss : List Tree) (Q F : List (List Nat))
    (ha : agrees T ss F = true) (hq : partitionCheck (labels T) Q = true)
    (own : Owns ss Q) (U : List Nat) (hU : U ∈ Q) :
    agrees (localTarget T U) (owned ss U) (family U F) = true
```

### reverse_reconstruction

Consuming source lines: 104.

```lean
  have hstate := reverse_reconstruction (some t) ss (ss.map leaves) H hp hQ own cross localValid
```

GroupReconstruction.lean:126

```lean
theorem reverse_reconstruction (T S : Tree) (Q : List (List Nat))
    (G : List Nat → List (List Nat)) (t s : List Nat → Tree)
    (properT : (leaves T).Nodup) (properS : (leaves S).Nodup)
    (hQT : partitionCheck (leaves T) Q = true)
    (hQS : partitionCheck (leaves S) Q = true)
    (eT : pairwiseEmbeddings T Q = true) (eS : pairwiseEmbeddings S Q = true)
    (ht : ∀ U ∈ Q, restrict U T = some (t U))
    (hs : ∀ U ∈ Q, restrict U S = some (s U))
    (ha : ∀ U ∈ Q, agreement (t U) (s U) (G U) = true) :
    agreement T S (Q.flatMap G) = true ∧
    (Q.map (fun U => (G U).length - 1)).sum = (Q.flatMap G).length - Q.length ∧
    (Q.flatMap G).flatten.Perm (leaves T) ∧ (Q.flatMap G).flatten.Perm (leaves S)
```

GroupReverseProof.lean:76

```lean
theorem reverse_reconstruction (T : Option Tree) (ss : List Tree) (Q : List (List Nat))
    (G : List Nat → List (List Nat)) (hp : proper T ss = true)
    (hq : partitionCheck (labels T) Q = true) (own : Owns ss Q)
    (cross : CrossClear T ss Q)
    (ha : ∀ U ∈ Q, agrees (localTarget T U) (owned ss U) (G U) = true) :
    agrees T ss (Q.flatMap G) = true
```

### reverse_exact_cost

Consuming source lines: 105.

```lean
  have hcost := reverse_exact_cost (some t) ss (ss.map leaves) H hp hQ own localValid
```

GroupCostProof.lean:66

```lean
theorem reverse_exact_cost (T : Option Tree) (ss : List Tree) (Q : List (List Nat))
    (G : List Nat → List (List Nat)) (hp : proper T ss = true)
    (hq : partitionCheck (labels T) Q = true) (own : Owns ss Q)
    (ha : ∀ U ∈ Q, agrees (localTarget T U) (owned ss U) (G U) = true) :
    (Q.map (fun U => additionalCost (owned ss U) (G U))).sum = additionalCost ss (Q.flatMap G)
```

### executable_span_monotone

Consuming source lines: 90, 91.

```lean
      (VertexGeometry.executable_span_monotone t _ U hA.2 v hv)
```

```lean
      (VertexGeometry.executable_span_monotone t _ V hB.2 v hw)
```

Composition.lean:20

```lean
theorem executable_span_monotone (t : RMAF.Tree) (P Q : List Nat)
    (hsub : ∀ x, x ∈ P → x ∈ Q) :
    ∀ v, v ∈ RMAF.minimalVertices P t → v ∈ RMAF.minimalVertices Q t
```

## ForestDisjointPlan

### LocalMinimum

Consuming source lines: 12.

```lean
    (mm : ∀ s ∈ ss, LocalMinimum (pair t s).1 (pair t s).2 (m (pair t s))) :
```

LocalSlots.lean:6

```lean
def LocalMinimum (t s : Tree) (m : Nat) : Prop
```

### Planned

Consuming source lines: 14, 35.

```lean
      ∀ j ∈ js, Planned m (PairValid m) j := by
```

```lean
        simpa [Planned,←hcost] using hl
```

QuerySpecification.lean:5

```lean
def Planned (minimum : P → Nat) (valid : P → A → Prop) : Job P A → Prop
  | .resolved p c a => c = minimum p ∧ valid p a ∧ c ≤ 1
  | .hard p => 2 ≤ minimum p

def totalMinimum (minimum : P → Nat) : List (Job P A) → Nat
  | [] => 0
  | j :: js => minimum j.problem + totalMinimum minimum js

inductive AnswersFor (minimum : P → Nat) (valid : P → A → Prop) :
    List (Job P A) → List (Nat × A) → Prop where
```

### refused_iff

Consuming source lines: 26.

```lean
      have hr := (DepthOne.refused_iff _ _).1 he
```

Optimality01.lean:119

```lean
theorem refused_iff (T S : Tree) : pretest01 T S = .refused ↔ proper T S = false
```

### rejected_lower_bound

Consuming source lines: 34.

```lean
        have hl := DepthOne.rejected_lower_bound _ _ he F hF
```

Optimality01.lean:100

```lean
theorem rejected_lower_bound (T S : Tree) (h : pretest01 T S = .rejected) :
    ∀ F, agreement T S F = true → 2 ≤ F.length - 1
```

### found_globally_minimum

Consuming source lines: 38.

```lean
      obtain ⟨ha,hcost,hminimal⟩ := DepthOne.found_globally_minimum _ _ c he
```

Optimality01.lean:75

```lean
theorem found_globally_minimum (T S : Tree) (c : Option Vertex)
    (h : pretest01 T S = .found c) :
    agreement T S (forest S c) = true ∧
    (forest S c).length - 1 = cutCost c ∧
    ∀ F, agreement T S F = true → cutCost c ≤ F.length - 1
```

### cutCost_le_one

Consuming source lines: 49.

```lean
        exact ⟨hcm,⟨ha,hcost.trans hcm⟩,DepthOne.cutCost_le_one c⟩
```

Optimality01.lean:71

```lean
theorem cutCost_le_one (c : Option Vertex) : cutCost c ≤ 1
```

## ForestDisjoint

### OrdinaryIH

Consuming source lines: 7, 106, 18, 20, 43, 52.

```lean
    (ho : OrdinaryIH ordinary) : DisjointExact ordinary := by
```

```lean
    (ho : OrdinaryIH ordinary) : ExactAt (solve ordinary) :=
```

```lean
    obtain ⟨F,hF⟩ := ho.complete _ _ ((family (leaves s) G).length-1) _
```

```lean
    obtain ⟨hf,hb,hminimal⟩ := ho.sound _ _ _ F (pair_actual t ss hp s hs).2.2 hF
```

```lean
    obtain ⟨hag,hbudget,hmin⟩ := ho.sound _ _ _ F (pproper p hpk) hH
```

```lean
    obtain ⟨F,hF⟩ := ho.complete _ _ b K (pproper p hpk) hK (by omega)
```

ForestProgram.lean:86

```lean
structure OrdinaryIH (ordinary : Tree → Tree → Nat → Option Forest) where
  sound : ∀ t s q F, DepthOne.proper t s = true → ordinary t s q = some F →
    agreement t s F = true ∧ F.length-1 ≤ q ∧
      ∀ G, agreement t s G = true → F.length ≤ G.length
  complete : ∀ t s q G, DepthOne.proper t s = true → agreement t s G = true →
    G.length-1 ≤ q → ∃ F, ordinary t s q = some F
```

### schedule_complete_on

Consuming source lines: 64.

```lean
  obtain ⟨xs,hxs⟩ := schedule_complete_on m (PairValid m) recPair keys recSound recComplete
```

Regional.lean:78

```lean
theorem schedule_complete_on (minimum : P → Nat) (valid : P → A → Prop)
    (solve : P → Nat → Option (Nat × A)) (Q : List P)
    (hs : ∀ p∈Q, ∀ b c a, solve p b=some (c,a) → c=minimum p ∧ valid p a)
    (hc : ∀ p∈Q, ∀ b, minimum p≤b → ∃ x, solve p b=some x)
    (q : Nat) (js : List (Job P A)) (hp : ∀ j∈js, Planned minimum valid j)
    (hkeys : ∀ j∈js, j.problem∈Q) (hq : totalMinimum minimum js≤q) :
    ∃ xs, (schedule solve q js).answers=some xs
```

### schedule_sound_on

Consuming source lines: 66.

```lean
  obtain ⟨hans,hansCost,haccepted⟩ := schedule_sound_on m (PairValid m) recPair keys recSound
```

Regional.lean:56

```lean
theorem schedule_sound_on (minimum : P → Nat) (valid : P → A → Prop)
    (solve : P → Nat → Option (Nat × A)) (Q : List P)
    (hs : ∀ p∈Q, ∀ b c a, solve p b=some (c,a) → c=minimum p ∧ valid p a)
    (q : Nat) (js : List (Job P A)) (hp : ∀ j∈js, Planned minimum valid j)
    (hkeys : ∀ j∈js, j.problem∈Q) (xs : List (Nat × A))
    (hr : (schedule solve q js).answers=some xs) :
    AnswersFor minimum valid js xs ∧ answerCost xs=totalMinimum minimum js ∧
      totalMinimum minimum js≤q
```

### answers_indexed

Consuming source lines: 72.

```lean
  obtain ⟨f,hf,hvalid⟩ := answers_indexed m (PairValid m) js xs hans keysND
```

Indexing.lean:6

```lean
theorem answers_indexed [DecidableEq P] [Inhabited A]
    (minimum : P → Nat) (valid : P → A → Prop)
    (js : List (Job P A)) (xs : List (Nat × A))
    (ha : AnswersFor minimum valid js xs) (hn : (js.map Job.problem).Nodup) :
    ∃ f : P → Nat × A, (js.map Job.problem).map f=xs ∧
      ∀ j∈js, (f j.problem).1=minimum j.problem ∧ valid j.problem (f j.problem).2
```

### totalMinimum_keys

Consuming source lines: 55.

```lean
    rw [totalMinimum_keys,hkeys,List.map_map]
```

Indexing.lean:35

```lean
theorem totalMinimum_keys (minimum : P → Nat) (js : List (Job P A)) :
    totalMinimum minimum js=((js.map Job.problem).map minimum).sum
```

### disjoint_exact_of_ordinary

Consuming source lines: 6, 107.

```lean
theorem disjoint_exact_of_ordinary (ordinary : Tree → Tree → Nat → Option Forest)
```

```lean
  conditional_exact ordinary ho (disjoint_exact_of_ordinary ordinary ho)
```

ForestDisjoint.lean:6

```lean
theorem disjoint_exact_of_ordinary (ordinary : Tree → Tree → Nat → Option Forest)
    (ho : OrdinaryIH ordinary) : DisjointExact ordinary
```

### conditional_exact

Consuming source lines: 107.

```lean
  conditional_exact ordinary ho (disjoint_exact_of_ordinary ordinary ho)
```

ForestConditional.lean:44

```lean
theorem conditional_exact (ordinary : Tree → Tree → Nat → Option Forest)
    (ho : OrdinaryIH ordinary) (hd : DisjointExact ordinary) : ExactAt (solve ordinary)
```

## ForestWork

### LocalBillBound

Consuming source lines: 121.

```lean
def LocalBillBound (ordinary : Tree → Tree → Nat → Option Forest)
```

ForestWork.lean:121

```lean
def LocalBillBound (ordinary : Tree → Tree → Nat → Option Forest)
    (ordinaryWork : Tree → Tree → Nat → Nat) (T : Option Tree) (Q : Nat) (c K : Rat) : Prop
```

### meterGenerate

Consuming source lines: 29.

```lean
    (meterGenerate s (colorLabel t v) q).measured.work +
```

Work.lean:408

```lean
def meterGenerate (t : Tree) (color : Nat → Nat) (budget : Nat) : Generated
```

### meterColorLabel

Consuming source lines: 30.

```lean
      ((leaves s).map fun x => (meterColorLabel t v x).work).sum
```

ForestColorWork.lean:124

```lean
def meterColorLabel (T : Tree) (v : RMAF.Vertex) (x : Nat) : Charged Nat
```

### meterMinimal

Consuming source lines: 22.

```lean
    (meterMinimal (leaves a) t).work + (meterMinimal (leaves b) t).work +
```

ForestGeometryWork.lean:63

```lean
def meterMinimal (D : List Nat) : Tree → Charged (List RMAF.Vertex)
  | .leaf x =>
    let m
```

### generate_output_budget

Consuming source lines: 96.

```lean
      generate_output_budget s _ q o ho,by
```

OutputBudget.lean:58

```lean
theorem generate_output_budget (t : Tree) (color : Nat → Nat) (q : Nat) (o : Output)
    (ho : o ∈ (generate t color q).outputs) : o.sourceCuts.length ≤ q
```

### two_actual_cores_mass

Consuming source lines: 109.

```lean
  have hm := two_actual_cores_mass t ss hp s r (List.mem_of_getElem? hi) (List.mem_of_getElem? hj)
```

ForestOverlap.lean:93

```lean
theorem two_actual_cores_mass (t : Tree) (ss : List Tree) (hp : proper (some t) ss = true)
    (s r : Tree) (hs : s ∈ ss) (hr : r ∈ ss) (hne : s ≠ r) (v : RMAF.Vertex)
    (hv : v ∈ minimalVertices (leaves s) t) (hw : v ∈ minimalVertices (leaves r) t)
    (q : Nat) (c : Rat) (hc : 2 ≤ c) :
    rawQMass c ((generate s (colorLabel t v) q).outputs ++
      (generate r (colorLabel t v) q).outputs) ≤ 2 * c ^ (-1 : Int)
```

## ForestWorkBound

### LocalBillBound

Consuming source lines: 19, 24, 31.

```lean
/-- Qualified source-operation bound. LocalBillBound covers ONLY the explicitly
```

```lean
    (hc : 2 ≤ c) (hK : 0 ≤ K) (hlocal : LocalBillBound ordinary ordinaryWork T Q c K)
```

```lean
    have hloc := hlocal ss q hqQ hp
```

ForestWork.lean:121

```lean
def LocalBillBound (ordinary : Tree → Tree → Nat → Option Forest)
    (ordinaryWork : Tree → Tree → Nat → Nat) (T : Option Tree) (Q : Nat) (c K : Rat) : Prop
```

### branch_paid_proper

Consuming source lines: 51.

```lean
        have paid := branch_paid_proper t ss (by simpa [ht] using hp) h hh q io.1 io.2 hio
```

ForestWork.lean:78

```lean
theorem branch_paid_proper (t : Tree) (ss : List Tree) (hp : proper (some t) ss = true)
    (h : Overlap) (hh : overlap t ss = some h) (q i : Nat) (o : Output)
    (hm : (i,o) ∈ branches t ss h q) :
    1 ≤ o.sourceCuts.length ∧ o.sourceCuts.length ≤ q ∧
      proper (some t) (replace ss i o.partition) = true
```

### branch_mass_le_one

Consuming source lines: 71.

```lean
      have hmass := branch_mass_le_one t ss (by simpa [ht] using hp) h hh q c hc
```

ForestWork.lean:105

```lean
theorem branch_mass_le_one (t : Tree) (ss : List Tree) (hp : proper (some t) ss = true)
    (h : Overlap) (hh : overlap t ss = some h) (q : Nat) (c : Rat) (hc : 2 ≤ c) :
    ((branches t ss h q).map fun io => c ^ (-(io.2.sourceCuts.length : Int))).sum ≤ 1
```

### qpow_clear

Consuming source lines: 66.

```lean
            rw [qpow_clear c (Rat.ne_of_gt cpos) q _ paid.2.1]
```

RationalMass.lean:153

```lean
theorem qpow_clear (b : Rat) (hb : b ≠ 0) (B d : Nat) (hd : d ≤ B) :
    b ^ (B - d) = b ^ B * b ^ (-(d : Int))
```

## ForestTrace

### meterSchedule

Consuming source lines: 41, 46.

```lean
    (hk : (p,k) ∈ (meterSchedule
```

```lean
  unfold meterSchedule at hk
```

QueryWork.lean:73

```lean
def meterSchedule (solve : P → Nat → Option (Nat × A)) (charge : P → Nat → Nat)
    (q : Nat) (js : List (Job P A)) : MeterReceipt P A
```

### meter_run_query_keys

Consuming source lines: 6, 49.

```lean
theorem meter_run_query_keys {P A : Type} (rec : P → Nat → Option (Nat × A))
```

```lean
  · obtain ⟨he,j,hjj,hjp⟩ := meter_run_query_keys _ _ _ js p k hk
```

ForestTrace.lean:6

```lean
theorem meter_run_query_keys {P A : Type} (rec : P → Nat → Option (Nat × A))
    (charge : P → Nat → Nat) (b : Nat) (js : List (Job P A)) :
    ∀ p k, (p,k) ∈ (meterRun rec charge b js).queries →
      k = b ∧ ∃ j ∈ js, j.problem = p
```

### jobs_proper_and_smaller

Consuming source lines: 51.

```lean
    have hh := jobs_proper_and_smaller t ss hp hmultiple js hj j hjj
```

ForestQueries.lean:67

```lean
theorem jobs_proper_and_smaller (t : Tree) (ss : List Tree) (hp : proper (some t) ss = true)
    (hmultiple : 2 ≤ ss.length) (js : List (Job (Tree × Tree) Forest)) (hj : jobs t ss = some js)
    (j : Job (Tree × Tree) Forest) (hjj : j ∈ js) :
    DepthOne.proper j.problem.1 j.problem.2 = true ∧
      (leaves j.problem.1).length < (leaves t).length ∧
      (leaves j.problem.2).length < (leaves t).length
```

## ForestResource

### treeNodes_le_twice_leaves

Consuming source lines: 11.

```lean
    have hs := treeNodes_le_twice_leaves s
```

Work.lean:82

```lean
theorem treeNodes_le_twice_leaves (t : Tree) :
    treeNodes t + 1 = 2 * (leaves t).length
```

### proper_source_size

Consuming source lines: 16.

```lean
theorem proper_source_size (T : Option Tree) (ss : List Tree) (hp : proper T ss = true) :
```

ForestResource.lean:16

```lean
theorem proper_source_size (T : Option Tree) (ss : List Tree) (hp : proper T ss = true) :
    sourceNodes ss + ss.length = 2*(labels T).length
```

