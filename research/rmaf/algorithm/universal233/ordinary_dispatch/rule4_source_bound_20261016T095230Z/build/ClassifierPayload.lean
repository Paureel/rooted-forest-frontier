import FinalClassifierWork
namespace Universal233.Rule5PendantLocalWork
open RMAF CoreGraph HardParent Rule5PrefixLocalWork CherryBranching Rule5Classification Rule5FinalClassification

def LocalPayload (S : Tree) : LocalSelection→Prop
 | .large e=>e.length+1≤(leaves S).length
 | .two c=>c.sourceArc.length+1≤(leaves S).length ∧ c.p∈leaves S ∧ c.q∈leaves S
 | .outside c=>c.parent.length+1≤(leaves S).length ∧ c.p∈leaves S ∧ c.q∈leaves S
 | .remaining=>True

theorem local_payload (fee : CheckRequest→Nat) (T S : Tree) (a b : Nat) {s : LocalSelection}
 (sel : (localMeter fee T S a b).value=some s) : LocalPayload S s := by
 rw [local_value] at sel
 have facts:=selectLocal_cases sel
 cases s with
 | large e=>
  have e:=selectLarge_sound facts.2
  exact cuts_address S a b (by rw [cuts_value];exact e.1)
 | two c=>
  have ds:=sizeTwoCandidate_sound (selectSizeTwo_sound facts.2.2)
  have row:=cherry_row_payload S c.sourceArc c.p c.q (by rw [cherries_value];exact cherries_complete S _ _ _ ds.2.1)
  exact ⟨cuts_address S a b (by rw [cuts_value];exact ds.1),row.2⟩
 | outside c=>
  have ds:=outsideCandidate_sound (selectOutside_sound facts.2.2.2)
  have row:=cherry_row_payload S c.parent c.p c.q (by rw [cherries_value];exact cherries_complete S _ _ _ ds.1)
  exact row
 | remaining=>trivial

def BoundaryPayload (T : Tree) : BoundarySelection→Prop
 | .one q=>q.length≤(leaves T).length
 | .first q r | .second q r | .third q r=>q.length≤(leaves T).length ∧ r.length≤(leaves T).length

def FinalPayload (T S : Tree) : FinalSelection→Prop
 | .prefix s=>LocalPayload S s
 | .remaining d z=>d.badArc.length+1≤(leaves S).length ∧
  d.singletonArc.length+1≤(leaves S).length ∧ d.c∈leaves S ∧ BoundaryPayload T z

/-- Actual stored selection cells, addresses and source labels are bounded;
no hypothesis silently supplies a preclassified geometry record. -/
theorem final_payload (fee : CheckRequest→Nat) (T S : Tree) (a b : Nat) {out : FinalSelection}
 (sel : (finalMeter fee T S a b).value=some out) : FinalPayload T S out := by
 simp only [finalMeter] at sel
 split at sel
 · contradiction
 · split at sel
   · contradiction
   · rename_i bad hd
     have source:=selectBad_sound (by rw [←select_bad_value fee];exact hd)
     have ba:=cuts_address S a b (by rw [cuts_value];exact source.1)
     have sa:=cuts_address S a b (by rw [cuts_value];exact source.2.1)
     have labs:=subtree_labels_payload S bad.singletonArc
     have cl : (subtreeLabelsMeter S bad.singletonArc).value=[bad.c] := by
      rw [subtree_labels_value,source_subtree_labels source.2.2.2.2]
      rfl
     have lc : bad.c∈leaves S := labs.2 (by rw [cl];simp)
     cases hz : (boundaryMeter T (subtreeLabelsMeter S bad.badArc).value bad.c).value with
     | none=>simp [hz] at sel
     | some z=>
      have bp : BoundaryPayload T z := by
       have addr:=boundary_addresses T (subtreeLabelsMeter S bad.badArc).value bad.c hz
       cases z <;> exact addr
      simp only [hz,Option.map_some] at sel
      cases Option.some.inj sel
      exact ⟨ba,sa,lc,bp⟩
 · rename_i s hne hl
   cases Option.some.inj sel
   exact local_payload fee T S a b hl

/-- Unit-source work is lifted only under a separately stated scalar/cell
correspondence. This multiplication asserts no native or compiler semantics. -/
theorem final_scaled_work (scalarFee : Nat) (fee : CheckRequest→Nat) (T S : Tree) (a b L K : Nat)
 (tlabs : ∀x,x∈leaves T →x<2^L) (slabs : ∀x,x∈leaves S →x<2^L)
 (primitive : ∀r,CheckDomain ((leaves T).length+(leaves S).length) L r →fee r≤K) :
 scalarFee*(finalMeter fee T S a b).work≤scalarFee*finalBudget (leaves T).length (leaves S).length K :=
 Nat.mul_le_mul_left scalarFee (final_work fee T S a b L K tlabs slabs primitive)
end Universal233.Rule5PendantLocalWork
