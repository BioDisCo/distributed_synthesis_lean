/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Formalizations.Definition.DefHistory

/-!
# Views

This file formalizes Definition `def:views` from `paper.tex`. In each round a
process records its own current input and whether it received a message. A
delivered message contains the other process's previous full view and current
input. The update retains the process's previous view, so its local history
determines the round number. Outputs are chosen after this update.
-/

namespace DistributedSynthesis

universe u v x y

/-- The complete information available to process `p`. The empty view precedes
the first round. A reception records both previous views and both current
inputs; a non-reception records only the process's previous view and current
input. Views reached by executions use the input tag belonging to each process. -/
inductive View (In₁ : Type u) (In₂ : Type v) : Proc -> Type (max u v) where
  | empty : (p : Proc) -> View In₁ In₂ p
  | recv : {p : Proc} ->
      View In₁ In₂ p ->
    PSum In₁ In₂ ->
      View In₁ In₂ p.other ->
    PSum In₁ In₂ ->
      View In₁ In₂ p
  | noRecv : {p : Proc} ->
      View In₁ In₂ p ->
    PSum In₁ In₂ ->
      View In₁ In₂ p

/-- The previous-view and current-input payloads of a view. The `pair` and
`quad` constructors still distinguish absence and presence of a received
payload, so this representation retains enough information to reconstruct
the original full view. -/
inductive NonFringeView (In₁ : Type u) (In₂ : Type v) : Proc -> Type (max u v) where
  | empty : (p : Proc) -> NonFringeView In₁ In₂ p
  | pair : {p : Proc} ->
      View In₁ In₂ p ->
    PSum In₁ In₂ ->
      NonFringeView In₁ In₂ p
  | quad : {p : Proc} ->
      View In₁ In₂ p ->
    PSum In₁ In₂ ->
      View In₁ In₂ p.other ->
    PSum In₁ In₂ ->
      NonFringeView In₁ In₂ p

namespace View

variable {In₁ : Type u} {In₂ : Type v} {p : Proc}

/-- The current receipt tag exposed by the outer constructor of a view. -/
def receiptTag : View In₁ In₂ p -> ReceiptTag
  | .empty _ => .noRecv
  | .recv .. => .recv
  | .noRecv .. => .noRecv

/-- Remove only the outermost receipt bit. -/
def nonFringe : View In₁ In₂ p -> NonFringeView In₁ In₂ p
  | .empty p => .empty p
  | .recv prevSelf inputSelf prevOther inputOther =>
      .quad prevSelf inputSelf prevOther inputOther
  | .noRecv prevSelf inputSelf =>
      .pair prevSelf inputSelf

end View

namespace NonFringeView

variable {In₁ : Type u} {In₂ : Type v} {p : Proc}

/--
Rebuild a full view from a non-fringe view and a current receipt tag.

For reachable non-fringe views the outer shape already determines whether a
payload is present; the receipt tag is the finite-fringe parameter used by the
strategy-translation interface.
-/
def withReceiptTag : NonFringeView In₁ In₂ p -> ReceiptTag -> View In₁ In₂ p
  | .empty _, _ => .empty p
  | .pair prevSelf inputSelf, _ => .noRecv prevSelf inputSelf
  | .quad prevSelf inputSelf prevOther inputOther, _ =>
      .recv prevSelf inputSelf prevOther inputOther

/-- Recover the previous full view of the same process from a non-fringe view. -/
def previousView : NonFringeView In₁ In₂ p -> View In₁ In₂ p
  | .empty _ => .empty p
  | .pair prevSelf _ => prevSelf
  | .quad prevSelf _ _ _ => prevSelf

/-- Recover the previous non-fringe view by stripping the recovered full view. -/
def previousNonFringe (nf : NonFringeView In₁ In₂ p) : NonFringeView In₁ In₂ p :=
  nf.previousView.nonFringe

/-- The smaller process view appears as the trailing pair inside the receiver's quad. -/
def DirectSubtupleOfReceiver {receiver : Proc}
    (small : NonFringeView In₁ In₂ receiver.other)
    (big : NonFringeView In₁ In₂ receiver) : Prop :=
  match small, big with
  | .pair prev input, .quad _ _ prev' input' => prev = prev' ∧ input = input'
  | _, _ => False

end NonFringeView

namespace View

variable {In₁ : Type u} {In₂ : Type v} {p : Proc}

/-- Removing the current receipt tag and rebuilding with that tag recovers the original view. -/
@[simp]
theorem withReceiptTag_nonFringe_receiptTag (view : View In₁ In₂ p) :
    view.nonFringe.withReceiptTag view.receiptTag = view := by
  cases view <;> rfl

end View

section Evaluation

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}

/-- One-step update of the two local views. -/
def advanceViews
    (views : View In₁ In₂ Proc.one × View In₁ In₂ Proc.two)
    (r : RoundRecord In₁ In₂ Graph Out₁ Out₂) :
    View In₁ In₂ Proc.one × View In₁ In₂ Proc.two :=
  let v₁ := views.1
  let v₂ := views.2
  match r.graph with
  | .left => (.recv v₁ (.inl r.inputOne) v₂ (.inr r.inputTwo), .noRecv v₂ (.inr r.inputTwo))
  | .right => (.noRecv v₁ (.inl r.inputOne), .recv v₂ (.inr r.inputTwo) v₁ (.inl r.inputOne))
  | .both => (.recv v₁ (.inl r.inputOne) v₂ (.inr r.inputTwo), .recv v₂ (.inr r.inputTwo) v₁ (.inl r.inputOne))

/-- Simultaneous evaluation of both local views along a history. -/
def viewPair (h : History In₁ In₂ Graph Out₁ Out₂) :
    View In₁ In₂ Proc.one × View In₁ In₂ Proc.two :=
  h.foldl advanceViews (.empty Proc.one, .empty Proc.two)

/-- The current view of process `p` after history `h`. -/
def currentView (p : Proc) (h : History In₁ In₂ Graph Out₁ Out₂) : View In₁ In₂ p :=
  match p with
  | .one => (viewPair h).1
  | .two => (viewPair h).2

/-- The non-fringe view of process `p` after history `h`. -/
def currentNonFringe (p : Proc) (h : History In₁ In₂ Graph Out₁ Out₂) : NonFringeView In₁ In₂ p :=
  (currentView p h).nonFringe

@[simp]
theorem viewPair_empty :
    viewPair (History.empty : History In₁ In₂ Graph Out₁ Out₂) =
      (.empty Proc.one, .empty Proc.two) :=
  rfl

@[simp]
theorem viewPair_append (h : History In₁ In₂ Graph Out₁ Out₂)
    (r : RoundRecord In₁ In₂ Graph Out₁ Out₂) :
    viewPair (History.append h r) = advanceViews (viewPair h) r := by
  simp [viewPair, History.append, advanceViews, List.foldl_append]

@[simp]
theorem currentView_one_empty :
    currentView Proc.one (History.empty : History In₁ In₂ Graph Out₁ Out₂) = .empty Proc.one :=
  rfl

@[simp]
theorem currentView_two_empty :
    currentView Proc.two (History.empty : History In₁ In₂ Graph Out₁ Out₂) = .empty Proc.two :=
  rfl

@[simp]
theorem currentView_one_append (h : History In₁ In₂ Graph Out₁ Out₂)
    (r : RoundRecord In₁ In₂ Graph Out₁ Out₂) :
    currentView Proc.one (History.append h r) =
      match r.graph with
      | .left => .recv (currentView Proc.one h) (.inl r.inputOne) (currentView Proc.two h) (.inr r.inputTwo)
      | .right => .noRecv (currentView Proc.one h) (.inl r.inputOne)
      | .both => .recv (currentView Proc.one h) (.inl r.inputOne) (currentView Proc.two h) (.inr r.inputTwo) := by
  cases hGraph : r.graph <;> simp [currentView, viewPair_append, advanceViews, hGraph]

@[simp]
theorem currentView_two_append (h : History In₁ In₂ Graph Out₁ Out₂)
    (r : RoundRecord In₁ In₂ Graph Out₁ Out₂) :
    currentView Proc.two (History.append h r) =
      match r.graph with
      | .left => .noRecv (currentView Proc.two h) (.inr r.inputTwo)
      | .right => .recv (currentView Proc.two h) (.inr r.inputTwo) (currentView Proc.one h) (.inl r.inputOne)
      | .both => .recv (currentView Proc.two h) (.inr r.inputTwo) (currentView Proc.one h) (.inl r.inputOne) := by
  cases hGraph : r.graph <;> simp [currentView, viewPair_append, advanceViews, hGraph]

@[simp]
theorem currentNonFringe_empty_one :
    currentNonFringe Proc.one (History.empty : History In₁ In₂ Graph Out₁ Out₂) =
      .empty Proc.one :=
  rfl

@[simp]
theorem currentNonFringe_empty_two :
    currentNonFringe Proc.two (History.empty : History In₁ In₂ Graph Out₁ Out₂) =
      .empty Proc.two :=
  rfl

@[simp]
theorem currentNonFringe_append (p : Proc) (h : History In₁ In₂ Graph Out₁ Out₂)
    (r : RoundRecord In₁ In₂ Graph Out₁ Out₂) :
    currentNonFringe p (History.append h r) = (currentView p (History.append h r)).nonFringe :=
  rfl

end Evaluation

end DistributedSynthesis
