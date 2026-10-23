import Std

/-! A concrete recursive cut-and-yield model. Trees retain original node IDs.
Cut marks denote incoming edges. Detached components are finite counting
functions, so order of component output is immaterial; node IDs and rooted
shapes remain part of each component. No AF premise is used. -/
namespace SecondExchange.YieldModel

inductive NormalTree where
  | empty : NormalTree
  | node : Nat → Option Nat → NormalTree → NormalTree → NormalTree
  deriving DecidableEq

inductive MarkedTree where
  | empty : MarkedTree
  | node : Nat → Option Nat → Bool → MarkedTree → MarkedTree → MarkedTree

def join (id : Nat) (label : Option Nat) (left right : NormalTree) : NormalTree :=
  match label, left, right with
  | none, .empty, t => t
  | none, t, .empty => t
  | _, l, r => .node id label l r

@[simp] theorem join_empty_right (id : Nat) (t : NormalTree) : join id none t .empty = t := by
  cases t <;> rfl

@[simp] theorem join_empty_left (id : Nat) (t : NormalTree) : join id none .empty t = t := rfl

abbrev Bag := NormalTree → Nat
abbrev Output := NormalTree × Bag

def add (a b : Bag) : Bag := fun t => a t + b t

def single (t : NormalTree) : Bag :=
  if t = .empty then fun _ => 0 else fun x => if x = t then 1 else 0

def emit (cut : Bool) (main : NormalTree) (rest : Bag) : Output :=
  if cut then (.empty, add (single main) rest) else (main, rest)

def finish (id : Nat) (label : Option Nat) (cut : Bool)
    (left right : Output) : Output :=
  emit cut (join id label left.1 right.1) (add left.2 right.2)

def evaluate : MarkedTree → Output
  | .empty => (.empty, fun _ => 0)
  | .node id label cut left right => finish id label cut (evaluate left) (evaluate right)

def total (out : Output) : Bag := add (single out.1) out.2

def augment (out : Output) (extra : Bag) : Output := (out.1, add out.2 extra)

def rootMark (mark : Bool) : MarkedTree → MarkedTree
  | .empty => .empty
  | .node id label _ left right => .node id label mark left right

theorem root_cut_detaches (tree : MarkedTree) :
    evaluate (rootMark true tree) = (.empty, total (evaluate tree)) := by
  cases tree with
  | empty =>
    simp [rootMark, evaluate, total, single]
    funext t
    simp [add]
  | node id label cut left right =>
    cases cut <;> simp [rootMark, evaluate, finish, emit, total, single]
    funext t
    simp [add]

theorem augment_total (out : Output) (extra : Bag) :
    total (augment out extra) = add (total out) extra := by
  funext t
  simp [total, augment, add, Nat.add_assoc]

theorem augment_twice (out : Output) (a b : Bag) :
    augment (augment out a) b = augment out (add a b) := by
  simp only [augment, Prod.mk.injEq, true_and]
  funext t
  simp [add, Nat.add_assoc]

theorem finish_augment_left (id : Nat) (label : Option Nat) (cut : Bool)
    (left right : Output) (extra : Bag) :
    finish id label cut (augment left extra) right =
      augment (finish id label cut left right) extra := by
  cases cut <;> simp [finish, augment, emit] <;>
    funext t <;> simp [add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem finish_augment_right (id : Nat) (label : Option Nat) (cut : Bool)
    (left right : Output) (extra : Bag) :
    finish id label cut left (augment right extra) =
      augment (finish id label cut left right) extra := by
  cases cut <;> simp [finish, augment, emit] <;>
    funext t <;> simp [add, Nat.add_assoc]

/-- A cut pendant subtree separates; its unlabelled unary parent suppresses.
The continuing subtree may itself contain arbitrary further cut marks. -/
theorem pendant_right (s : Nat) (continuing pendant : MarkedTree) :
    evaluate (.node s none false continuing (rootMark true pendant)) =
      augment (evaluate continuing) (total (evaluate pendant)) := by
  rw [evaluate, root_cut_detaches]
  simp [finish, emit, augment]

theorem pendant_left (s : Nat) (continuing pendant : MarkedTree) :
    evaluate (.node s none false (rootMark true pendant) continuing) =
      augment (evaluate continuing) (total (evaluate pendant)) := by
  rw [evaluate, root_cut_detaches]
  simp [finish, emit, augment]
  funext t
  simp [add, Nat.add_comm]

inductive Context where
  | hole : Context
  | left : Nat → Option Nat → Bool → Context → MarkedTree → Context
  | right : Nat → Option Nat → Bool → MarkedTree → Context → Context

def plug : Context → MarkedTree → MarkedTree
  | .hole, tree => tree
  | .left id label cut context right, tree => .node id label cut (plug context tree) right
  | .right id label cut left context, tree => .node id label cut left (plug context tree)

theorem context_augment (context : Context) (source target : MarkedTree) (extra : Bag)
    (h : evaluate source = augment (evaluate target) extra) :
    evaluate (plug context source) = augment (evaluate (plug context target)) extra := by
  induction context with
  | hole => exact h
  | left id label cut context right ih =>
    simp only [plug, evaluate, ih, finish_augment_left]
  | right id label cut left context ih =>
    simp only [plug, evaluate, ih, finish_augment_right]

/-- An explicitly witnessed local pendant deletion and unary suppression,
allowed in either child orientation and at any finite rooted context. -/
inductive PendantSplice : MarkedTree → MarkedTree → MarkedTree → Prop where
  | right (context : Context) (s : Nat) (continuing pendant : MarkedTree) :
      PendantSplice
        (plug context (.node s none false continuing (rootMark true pendant)))
        (plug context continuing) pendant
  | left (context : Context) (s : Nat) (continuing pendant : MarkedTree) :
      PendantSplice
        (plug context (.node s none false (rootMark true pendant) continuing))
        (plug context continuing) pendant

theorem splice_evaluate {source target pendant : MarkedTree}
    (h : PendantSplice source target pendant) :
    evaluate source = augment (evaluate target) (total (evaluate pendant)) := by
  cases h with
  | right context s continuing pendant =>
    exact context_augment context _ _ _ (pendant_right s continuing pendant)
  | left context s continuing pendant =>
    exact context_augment context _ _ _ (pendant_left s continuing pendant)

/-- Full concrete rooted-forest equality for two witnessed pendant splices.
The detached components may have arbitrary residual cuts inside them. -/
theorem two_splice_yield {source middle target b₁ b₂ : MarkedTree}
    (h₁ : PendantSplice source middle b₁)
    (h₂ : PendantSplice middle target b₂) :
    total (evaluate source) =
      add (total (evaluate target)) (add (total (evaluate b₁)) (total (evaluate b₂))) := by
  rw [splice_evaluate h₁, splice_evaluate h₂, augment_total, augment_total]
  funext t
  simp [add, Nat.add_comm, Nat.add_left_comm]

/-- The component attached at the root is identical, including all surviving
original IDs. Apply with the x/u root incoming mark cleared to compare their
descendant root fragments; this operation ignores an incoming edge cut. -/
theorem two_splice_root_component {source middle target b₁ b₂ : MarkedTree}
    (h₁ : PendantSplice source middle b₁)
    (h₂ : PendantSplice middle target b₂) :
    (evaluate source).1 = (evaluate target).1 := by
  rw [splice_evaluate h₁, splice_evaluate h₂]
  rfl

#print axioms join_empty_right
#print axioms join_empty_left
#print axioms root_cut_detaches
#print axioms augment_total
#print axioms augment_twice
#print axioms finish_augment_left
#print axioms finish_augment_right
#print axioms pendant_right
#print axioms pendant_left
#print axioms context_augment
#print axioms splice_evaluate
#print axioms two_splice_yield
#print axioms two_splice_root_component
end SecondExchange.YieldModel
