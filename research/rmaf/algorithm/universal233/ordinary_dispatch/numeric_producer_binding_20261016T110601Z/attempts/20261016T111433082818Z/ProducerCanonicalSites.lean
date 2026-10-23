import ProducerBudgetTrim
namespace OrdinaryDispatch.StoredNumeric.ProducerBinding
open GenericForest.ScalarBits GenericForest.BinaryProvider Universal233.WholeSourceWork
open GenericForest.BinaryProducer

/-- Concrete, charged boundary used by the new producer variants. The actual
array passed to f is the result of the finite trim, never a mathematical encode. -/
def canonicalCall {A : Type} (f : Bits→Charged A) (q : Bits) : Charged A :=
 let t:=trimBudget q;let r:=f t.value
 ⟨r.value,t.work+r.work+4⟩
@[simp] theorem canonicalCall_work {A : Type} (f : Bits→Charged A) (q : Bits) :
 (canonicalCall f q).work=(f (trimBudget q).value).work+8*q.length+5 := by simp [canonicalCall];omega
@[simp] theorem canonicalCall_value {A : Type} (f : Bits→Charged A) (q : Bits) :
 (canonicalCall f q).value=(f (trimBudget q).value).value := rfl

theorem canonicalCall_input_width (q : Bits) (Q : Nat) (h : decode q≤Q) :
 (trimBudget q).value.length≤Q := Nat.le_trans (trimBudget_semantic_width q) h

/-- Roots and every new budget edge are executable outputs. Arbitrarily many
payment/allocation edges need no event-depth D for this variant's width. -/
inductive CanonicalLineage (q0 : Bits) : Bits→Prop where
 | root : CanonicalLineage q0 (trimBudget q0).value
 | payment {q} : CanonicalLineage q0 q→(d : Bits)→CanonicalLineage q0 (subtractCanonical q d).value
 | allocation {q} : CanonicalLineage q0 q→(k p : Bits)→CanonicalLineage q0 (allocationCanonical q k p).value

theorem canonical_lineage (q0 : Bits) {q : Bits} (h : CanonicalLineage q0 q) :
 decode q≤decode q0 ∧ q.length≤decode q0 := by
 induction h with
 | root=>exact ⟨by simp,trimBudget_semantic_width _⟩
 | @payment q h d ih=>exact ⟨by simp only [subtractCanonical_value];omega,Nat.le_trans (subtractCanonical_width q d) ih.1⟩
 | @allocation q h k p ih=>exact ⟨by simp only [allocationCanonical_value];omega,Nat.le_trans (allocationCanonical_width q k p) ih.1⟩

/-- Initial physical storage is charged separately from decoded Q. -/
theorem initial_budget_storage (q0 : Bits) (Bq Q : Nat) (stored : q0.length≤Bq) (semantic : decode q0≤Q) :
 (trimBudget q0).work≤8*Bq+1 ∧ (trimBudget q0).value.length≤Q := by
 exact ⟨by simp only [trimBudget_work];omega,canonicalCall_input_width q0 Q semantic⟩

def rawCallbackCanonical
 (solve : Option GenericForest.BinaryProvider.Tree→List GenericForest.BinaryProvider.Tree→Bits→Charged (Option GenericForest.BinaryProvider.Forest))
 (T : Option GenericForest.BinaryProvider.Tree) (ss : List GenericForest.BinaryProvider.Tree) (q : Bits) := canonicalCall (solve T ss) q

theorem rawCallbackCanonical_refines
 (solve : Option GenericForest.BinaryProvider.Tree→List GenericForest.BinaryProvider.Tree→Bits→Charged (Option GenericForest.BinaryProvider.Forest))
 (native : Option RMAF.Tree→List RMAF.Tree→Nat→Option GenericForest.Forest)
 (ih : ∀T ss b,forestOptionValue (solve T ss b).value=native (targetValue T) (sourcesValue ss) (decode b)) :
 ∀T ss b,forestOptionValue (rawCallbackCanonical solve T ss b).value=native (targetValue T) (sourcesValue ss) (decode b) := by
 intro T ss b
 simpa only [rawCallbackCanonical,canonicalCall_value,trimBudget_value] using ih T ss (trimBudget b).value

/-- Exact raw-payment site: this is the array supplied to the underlying
recursive solver by rawCandidates with rawCallbackCanonical. -/
theorem raw_payment_site (q : Bits) (cuts : List RMAF.Vertex) :
 (trimBudget (subtractBits q (spineCounter cuts).value).value).value=(subtractCanonical q (spineCounter cuts).value).value ∧
 (trimBudget (subtractBits q (spineCounter cuts).value).value).value.length≤decode q ∧
 decode (trimBudget (subtractBits q (spineCounter cuts).value).value).value=decode q-cuts.length := by
 exact ⟨rfl,subtractCanonical_width _ _,by simp⟩

def rawParentCanonical
 (solve : Option GenericForest.BinaryProvider.Tree→List GenericForest.BinaryProvider.Tree→Bits→Charged (Option GenericForest.BinaryProvider.Forest))
 (T : Option GenericForest.BinaryProvider.Tree) (ss : List GenericForest.BinaryProvider.Tree) (q : Bits) (ios : List (Bits×Output)) :=
 canonicalCall (fun b=>rawParentProducer (rawCallbackCanonical solve) T ss b ios) q

theorem rawParentCanonical_value
 (solve : Option GenericForest.BinaryProvider.Tree→List GenericForest.BinaryProvider.Tree→Bits→Charged (Option GenericForest.BinaryProvider.Forest))
 (native : Option RMAF.Tree→List RMAF.Tree→Nat→Option GenericForest.Forest)
 (ih : ∀T ss b,forestOptionValue (solve T ss b).value=native (targetValue T) (sourcesValue ss) (decode b))
 (T : Option GenericForest.BinaryProvider.Tree) (ss : List GenericForest.BinaryProvider.Tree) (q : Bits) (ios : List (Bits×Output)) :
 forestOptionValue (rawParentCanonical solve T ss q ios).value=
 RMAF.best List.length (GenericForest.accepted (targetValue T) (sourcesValue ss) (decode q))
 ((ios.map branchValue).filterMap (fun io=>
  let d:=io.2.sourceCuts.length
  if 1≤d∧d≤decode q then native (targetValue T) (GenericForest.replace (sourcesValue ss) io.1 io.2.partition) (decode q-d) else none)) := by
 simpa only [rawParentCanonical,canonicalCall_value,trimBudget_value] using
  rawParentProducer_value (rawCallbackCanonical solve) native (rawCallbackCanonical_refines solve native ih) T ss (trimBudget q).value ios

def generatedRawParentCanonical
 (solve : Option GenericForest.BinaryProvider.Tree→List GenericForest.BinaryProvider.Tree→Bits→Charged (Option GenericForest.BinaryProvider.Forest))
 (T : GenericForest.BinaryProvider.Tree) (ss : List GenericForest.BinaryProvider.Tree) (h : OverlapBits) (q : Bits) :=
 canonicalCall (fun b=>generatedRawParent (rawCallbackCanonical solve) T ss h b) q

theorem generatedRawParentCanonical_value
 (solve : Option GenericForest.BinaryProvider.Tree→List GenericForest.BinaryProvider.Tree→Bits→Charged (Option GenericForest.BinaryProvider.Forest))
 (native : Option RMAF.Tree→List RMAF.Tree→Nat→Option GenericForest.Forest)
 (ih : ∀T ss b,forestOptionValue (solve T ss b).value=native (targetValue T) (sourcesValue ss) (decode b))
 (T : GenericForest.BinaryProvider.Tree) (ss : List GenericForest.BinaryProvider.Tree) (h : OverlapBits) (q : Bits) :
 forestOptionValue (generatedRawParentCanonical solve T ss h q).value=
 RMAF.best List.length (GenericForest.accepted (some (treeValue T)) (sourcesValue ss) (decode q))
 ((GenericForest.branches (treeValue T) (sourcesValue ss) (overlapValue h) (decode q)).filterMap (fun io=>
  let d:=io.2.sourceCuts.length
  if 1≤d∧d≤decode q then native (some (treeValue T)) (GenericForest.replace (sourcesValue ss) io.1 io.2.partition) (decode q-d) else none)) := by
 simpa only [generatedRawParentCanonical,canonicalCall_value,trimBudget_value] using
  generatedRawParent_value (rawCallbackCanonical solve) native (rawCallbackCanonical_refines solve native ih) T ss h (trimBudget q).value

/-- Scheduler boundary. runBits' early refusal and literal order are retained. -/
def scheduleCanonical {P A : Type} (solve : P→Bits→Charged (Option (Bits×A))) (q : Bits) (js : List (Job P A)) :=
 canonicalCall (fun b=>scheduleBits (fun p c=>canonicalCall (solve p) c) b js) q

theorem scheduleCanonical_value {P P' A A' : Type} (π : P→P') (ρ : A→A')
 (solve : P→Bits→Charged (Option (Bits×A))) (native : P'→Nat→Option (Nat×A'))
 (ih : ∀p b,(solve p b).value.map (pairValue ρ)=native (π p) (decode b)) (q : Bits) (js : List (Job P A)) :
 receiptValue ρ (scheduleCanonical solve q js).value=Universal233.PaidQueries.schedule native (decode q) (js.map (jobValue π ρ)) := by
 have h : ∀p b,(canonicalCall (solve p) b).value.map (pairValue ρ)=native (π p) (decode b):=by
  intro p b;simpa only [canonicalCall_value,trimBudget_value] using ih p (trimBudget b).value
 simpa only [scheduleCanonical,canonicalCall_value,trimBudget_value] using scheduleBits_value π ρ _ native h (trimBudget q).value js

/-- Exact allocated array supplied to the underlying solver by scheduleCanonical. -/
theorem scheduler_allocation_site (q : Bits) {P A : Type} (js : List (Job P A)) :
 let r:=(trimBudget q).value
 let b:=(allocationBits r (knownBits js).value (pendingBits js).value).value
 (trimBudget b).value=(allocationCanonical r (knownBits js).value (pendingBits js).value).value ∧
 (trimBudget b).value.length≤decode q := by
 dsimp only
 exact ⟨rfl,by change (allocationCanonical (trimBudget q).value (knownBits js).value (pendingBits js).value).value.length≤decode q;have h:=allocationCanonical_width (trimBudget q).value (knownBits js).value (pendingBits js).value;simpa only [trimBudget_value] using h⟩

def generateCanonical (S : GenericForest.BinaryProvider.Tree) (color : Bits→Charged Generator.Color) (q : Bits) :=
 canonicalCall (Generator.generateBits S color) q

theorem generateCanonical_value (S : GenericForest.BinaryProvider.Tree) (color : Bits→Charged Generator.Color) (native : Nat→Nat)
 (ih : ∀x,Generator.colorValue (color x).value=native (decode x)) (q : Bits) :
 Generator.receiptValue (generateCanonical S color q).value=Universal233.CoreProgram.generate (treeValue S) native (decode q) := by
 simpa only [generateCanonical,canonicalCall_value,trimBudget_value] using Generator.generateBits_value S color native ih (trimBudget q).value

/-- Generator fuel decrements never enlarge the initialized canonical budget;
no traversal-count bound or depth identification is needed for this local loop. -/
theorem generator_fuel_subtract_width (q : Bits) (B : Nat) (qw : q.length≤B) (bp : 1≤B) :
 (subtractBits q [true]).value.length≤B := by
 have h:=subtractBits_length q [true];simp only [List.length_cons,List.length_nil] at h;omega
end OrdinaryDispatch.StoredNumeric.ProducerBinding
