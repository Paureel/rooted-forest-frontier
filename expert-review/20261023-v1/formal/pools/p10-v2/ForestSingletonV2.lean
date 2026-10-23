import ChildrenCreditV2

namespace SourceForestSingletonV2
open RMAF ForestState GenericForest GenericForest.FrontierWork
open SourceCouplingV2 SourceDisjointV2

inductive Invoke (OrdExec : Tree → Tree → Nat → Option F → Prop) (mode : Mode)
    (k : Nat) (p : Tree × Tree) (b : Nat) : Option F → Slot (Tree × Tree) F → Prop
  | refused (off : enabled mode b = false) :
      Invoke OrdExec mode k p b none ⟨k,(p,b),none,false⟩
  | returned (on : enabled mode b = true) (execution : OrdExec p.1 p.2 b answer) :
      Invoke OrdExec mode k p b answer
        ⟨k,(p,b),answer.map (fun fs=>(fs.length-1,fs)),true⟩

theorem invoke_sound (h : Invoke OrdExec mode k p b answer slot)
    (sound : ∀ T S b a, OrdExec T S b a → a=base T S b) :
    answer = ordinarySpec mode base p.1 p.2 b := by
  cases h with
  | refused off => simp [ordinarySpec,off]
  | returned on execution => simpa [ordinarySpec,on] using sound _ _ _ _ execution

theorem invoke_index (h : Invoke OrdExec mode k p b answer slot) :
    slot.index=k ∧ slot.query=(p,b) := by
  cases h <;> exact ⟨rfl,rfl⟩

theorem invoke_exists (total : ∀ T S b, ∃ a, OrdExec T S b a)
    (mode : Mode) (k : Nat) (p : Tree × Tree) (b : Nat) :
    ∃ a slot, Invoke OrdExec mode k p b a slot := by
  cases he : enabled mode b with
  | false => exact ⟨_,_,Invoke.refused he⟩
  | true =>
    obtain ⟨a,ha⟩ := total p.1 p.2 b
    exact ⟨_,_,Invoke.returned he ha⟩

theorem singleton_value (h : Invoke OrdExec mode k (t,s) b answer slot)
    (sound : ∀ T S b a, OrdExec T S b a → a=base T S b)
    (hp : proper (some t) [s] = true)
    (ha : agrees (some t) [s] ([s].map leaves) = false) :
    answer.bind (checked (some t) [s] b) =
      GenericForest.solve (ordinarySpec mode base) (some t) [s] b := by
  have hv := invoke_sound h sound
  simp only [List.map_cons,List.map_nil] at ha
  simp [GenericForest.solve,hp,ha,←hv]

theorem singleton_debit (mode : Mode) (base : Tree → Tree → Nat → Option F)
    (hp : proper (some t) [s] = true)
    (ha : agrees (some t) [s] ([s].map leaves) = false) :
    inspectionBill (some t) [s] b + 0 =
      OrdinaryDispatch.WorkRecursion.forestWork (ordinarySpec mode base)
        (fun _ _ _=>0) (some t) [s] b := by
  simp only [List.map_cons,List.map_nil] at ha
  simp [OrdinaryDispatch.WorkRecursion.forestWork,nonrecursiveBill,hp,ha]

theorem singleton_index (h : Invoke OrdExec mode k (t,s) b answer slot)
    (hp : proper (some t) [s] = true)
    (ha : agrees (some t) [s] ([s].map leaves) = false) :
    [slot].map (fun x=>(x.index,x.query)) =
      CallbackPairingAuthor.indexFrom k (frontier (ordinarySpec mode base) (some t) [s] b) := by
  have hi := invoke_index h
  simp only [List.map_cons,List.map_nil] at ha
  simp [frontier,hp,ha,CallbackPairingAuthor.indexFrom,hi.1,hi.2]

end SourceForestSingletonV2
