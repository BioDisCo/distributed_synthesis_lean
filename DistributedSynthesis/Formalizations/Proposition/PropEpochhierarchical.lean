/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Formalizations.Proposition.PropDynhier
import DistributedSynthesis.Formalizations.Definition.DefEpochAbstractions
import DistributedSynthesis.Formalizations.Lemma.LemDirectreversalboundary
import DistributedSynthesis.Formalizations.Lemma.LemPastreceipt
import DistributedSynthesis.Formalizations.Lemma.LemReversaltwobits
import DistributedSynthesis.Formalizations.Theorem.ThmOnebitfringe

/-!
# Epoch summaries preserve dynamic hierarchy
-/

namespace DistributedSynthesis

universe u v x y

/-- The non-fringe containment order induced by the current communication graph. -/
def graphContainmentOrder : Graph -> NonFringeContainmentOrder
  | .left => .secondInFirst
  | .right => .firstInSecond
  | .both => .equivalent

/--
Semantic witness that the current non-fringe views of a history satisfy a
particular containment order.
-/
def CurrentNonFringeOrder
    {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
    (h : History In₁ In₂ Graph Out₁ Out₂)
    (order : NonFringeContainmentOrder) : Prop :=
  match order with
  | .secondInFirst =>
      NonFringeView.DirectSubtupleOfReceiver
        (currentNonFringe Proc.two h) (currentNonFringe Proc.one h)
  | .firstInSecond =>
      NonFringeView.DirectSubtupleOfReceiver
        (currentNonFringe Proc.one h) (currentNonFringe Proc.two h)
  | .equivalent =>
      ∃ prevOne prevTwo x₁ x₂,
        currentNonFringe Proc.one h = .quad prevOne x₁ prevTwo x₂ ∧
          currentNonFringe Proc.two h = .quad prevTwo x₂ prevOne x₁

/-- Every appended round realizes the containment order induced by its graph. -/
theorem currentNonFringeOrder_append
    {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
    (h : History In₁ In₂ Graph Out₁ Out₂)
    (r : RoundRecord In₁ In₂ Graph Out₁ Out₂) :
    CurrentNonFringeOrder (History.append h r)
      (graphContainmentOrder r.graph) := by
  cases hGraph : r.graph with
  | left =>
      exact dynhier_left h r hGraph
  | right =>
      exact dynhier_right h r hGraph
  | both =>
      exact dynhier_both h r hGraph

/-- The finite receipt/order component canonically induced by a history. -/
def currentReceiptOrderData
    {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
    (h : History In₁ In₂ Graph Out₁ Out₂)
    (order : NonFringeContainmentOrder) : ReceiptOrderData where
  receiptOne := (currentView Proc.one h).receiptTag
  receiptTwo := (currentView Proc.two h).receiptTag
  containmentOrder := order

/--
The canonical receipt/order component for an appended round uses the
graph-induced containment order.
-/
def currentReceiptOrderDataForAppend
    {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
    (h : History In₁ In₂ Graph Out₁ Out₂)
    (r : RoundRecord In₁ In₂ Graph Out₁ Out₂) : ReceiptOrderData :=
  currentReceiptOrderData (History.append h r) (graphContainmentOrder r.graph)

@[simp]
theorem currentReceiptOrderData_receiptOne
    {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
    (h : History In₁ In₂ Graph Out₁ Out₂)
    (order : NonFringeContainmentOrder) :
    (currentReceiptOrderData h order).receiptOne =
      (currentView Proc.one h).receiptTag := rfl

@[simp]
theorem currentReceiptOrderData_receiptTwo
    {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
    (h : History In₁ In₂ Graph Out₁ Out₂)
    (order : NonFringeContainmentOrder) :
    (currentReceiptOrderData h order).receiptTwo =
      (currentView Proc.two h).receiptTag := rfl

@[simp]
theorem currentReceiptOrderData_containmentOrder
    {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
    (h : History In₁ In₂ Graph Out₁ Out₂)
    (order : NonFringeContainmentOrder) :
    (currentReceiptOrderData h order).containmentOrder = order := rfl

theorem currentReceiptOrderDataForAppend_realizes_order
    {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
    (h : History In₁ In₂ Graph Out₁ Out₂)
    (r : RoundRecord In₁ In₂ Graph Out₁ Out₂) :
    CurrentNonFringeOrder (History.append h r)
      (currentReceiptOrderDataForAppend h r).containmentOrder := by
  simpa [currentReceiptOrderDataForAppend] using
    currentNonFringeOrder_append h r

/--
Concrete local handoff package for a direct reversal.

This is the history-level fact that the epoch-relative proof needs at the
reversal case: the new dominant's receive view determines the two previous
full views and current inputs, the frozen bit is readable as the new dominant's
own previous receipt, and the ordinary one-bit fringe bound still holds for
both local views.
-/
structure DirectReversalEpochRelativeHandoff
    {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
    (newDominant : Proc)
    (h : History In₁ In₂ Graph Out₁ Out₂)
    (r : RoundRecord In₁ In₂ Graph Out₁ Out₂) where
  graphMatchesDominant : r.graph = dominantGraph newDominant
  previousViewsAndInputsDetermined :
    ∀ h' : History In₁ In₂ Graph Out₁ Out₂,
      ∀ r' : RoundRecord In₁ In₂ Graph Out₁ Out₂,
        r'.graph = dominantGraph newDominant ->
        currentView newDominant (History.append h r) =
          currentView newDominant (History.append h' r') ->
          currentView Proc.one h = currentView Proc.one h' ∧
            currentView Proc.two h = currentView Proc.two h' ∧
            r.inputOne = r'.inputOne ∧ r.inputTwo = r'.inputTwo
  oldOwnReceiptRecoverable :
    (currentNonFringe newDominant (History.append h r)).previousView.receiptTag =
      (currentView newDominant h).receiptTag
  pendingCounterpartCopyBitReadable :
    pendingCopyOfReceipt
        ((currentNonFringe newDominant (History.append h r)).previousView.receiptTag) =
      pendingCopyOfReceipt ((currentView newDominant h).receiptTag)
  pendingCounterpartCopyGraphReadable :
    match newDominant with
    | .one =>
        graphForProcessTwoCopy
            (pendingCopyOfReceipt
              ((currentNonFringe Proc.one (History.append h r)).previousView.receiptTag)) =
          graphForProcessTwoCopy
            (pendingCopyOfReceipt ((currentView Proc.one h).receiptTag))
    | .two =>
        graphForProcessOneCopy
            (pendingCopyOfReceipt
              ((currentNonFringe Proc.two (History.append h r)).previousView.receiptTag)) =
          graphForProcessOneCopy
            (pendingCopyOfReceipt ((currentView Proc.two h).receiptTag))
  oneBitFringeOne :
    ∃ candidates : List (List Graph),
      candidates.length ≤ 2 ∧
      History.graphSequence (History.append h r) ∈ candidates ∧
      ∀ h' : History In₁ In₂ Graph Out₁ Out₂,
        currentView Proc.one h' = currentView Proc.one (History.append h r) ->
        History.graphSequence h' ∈ candidates
  oneBitFringeTwo :
    ∃ candidates : List (List Graph),
      candidates.length ≤ 2 ∧
      History.graphSequence (History.append h r) ∈ candidates ∧
      ∀ h' : History In₁ In₂ Graph Out₁ Out₂,
        currentView Proc.two h' = currentView Proc.two (History.append h r) ->
        History.graphSequence h' ∈ candidates

/--
Concrete local package for a bidirectional boundary.  At a `both` round either
process's full view determines both previous full views and the current input
pair, which is the local reset case for the epoch-relative hierarchy invariant.
-/
structure BidirectionalBoundaryEpochReset
    {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
    (h : History In₁ In₂ Graph Out₁ Out₂)
    (r : RoundRecord In₁ In₂ Graph Out₁ Out₂) where
  graphBoth : r.graph = .both
  procOneDeterminesPreviousViewsAndInputs :
    ∀ h' : History In₁ In₂ Graph Out₁ Out₂,
      ∀ r' : RoundRecord In₁ In₂ Graph Out₁ Out₂,
        r'.graph = .both ->
        currentView Proc.one (History.append h r) =
          currentView Proc.one (History.append h' r') ->
          currentView Proc.one h = currentView Proc.one h' ∧
            currentView Proc.two h = currentView Proc.two h' ∧
            r.inputOne = r'.inputOne ∧ r.inputTwo = r'.inputTwo
  procTwoDeterminesPreviousViewsAndInputs :
    ∀ h' : History In₁ In₂ Graph Out₁ Out₂,
      ∀ r' : RoundRecord In₁ In₂ Graph Out₁ Out₂,
        r'.graph = .both ->
        currentView Proc.two (History.append h r) =
          currentView Proc.two (History.append h' r') ->
          currentView Proc.one h = currentView Proc.one h' ∧
            currentView Proc.two h = currentView Proc.two h' ∧
            r.inputOne = r'.inputOne ∧ r.inputTwo = r'.inputTwo
  oneBitFringeOne :
    ∃ candidates : List (List Graph),
      candidates.length ≤ 2 ∧
      History.graphSequence (History.append h r) ∈ candidates ∧
      ∀ h' : History In₁ In₂ Graph Out₁ Out₂,
        currentView Proc.one h' = currentView Proc.one (History.append h r) ->
        History.graphSequence h' ∈ candidates
  oneBitFringeTwo :
    ∃ candidates : List (List Graph),
      candidates.length ≤ 2 ∧
      History.graphSequence (History.append h r) ∈ candidates ∧
      ∀ h' : History In₁ In₂ Graph Out₁ Out₂,
        currentView Proc.two h' = currentView Proc.two (History.append h r) ->
        History.graphSequence h' ∈ candidates

/-- Bidirectional boundaries restore common access for both processes. -/
theorem bidirectionalBoundary_epochReset
    {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
    (h : History In₁ In₂ Graph Out₁ Out₂)
    (r : RoundRecord In₁ In₂ Graph Out₁ Out₂)
    (hr : r.graph = .both) :
    BidirectionalBoundaryEpochReset h r where
  graphBoth := hr
  procOneDeterminesPreviousViewsAndInputs := by
    intro h' r' hr' hview
    exact bothBoundary_procOne_determines_previousViewsAndInputs
      h h' r r' hr hr' hview
  procTwoDeterminesPreviousViewsAndInputs := by
    intro h' r' hr' hview
    exact bothBoundary_procTwo_determines_previousViewsAndInputs
      h h' r r' hr hr' hview
  oneBitFringeOne := onebitfringe_procOne (History.append h r)
  oneBitFringeTwo := onebitfringe_procTwo (History.append h r)

/--
Concrete local package for an interior step of a one-sided epoch.  The
dominant side's non-fringe view contains the subordinate side's non-fringe
view as a direct subtuple, and the one-bit fringe bound is preserved.
-/
structure SameSideEpochInteriorStep
    {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
    (dominant : Proc)
    (h : History In₁ In₂ Graph Out₁ Out₂)
    (r : RoundRecord In₁ In₂ Graph Out₁ Out₂) where
  graphMatchesDominant : r.graph = dominantGraph dominant
  subordinateSubtuple :
    match dominant with
    | .one =>
        NonFringeView.DirectSubtupleOfReceiver
          (currentNonFringe Proc.two (History.append h r))
          (currentNonFringe Proc.one (History.append h r))
    | .two =>
        NonFringeView.DirectSubtupleOfReceiver
          (currentNonFringe Proc.one (History.append h r))
          (currentNonFringe Proc.two (History.append h r))
  oneBitFringeOne :
    ∃ candidates : List (List Graph),
      candidates.length ≤ 2 ∧
      History.graphSequence (History.append h r) ∈ candidates ∧
      ∀ h' : History In₁ In₂ Graph Out₁ Out₂,
        currentView Proc.one h' = currentView Proc.one (History.append h r) ->
        History.graphSequence h' ∈ candidates
  oneBitFringeTwo :
    ∃ candidates : List (List Graph),
      candidates.length ≤ 2 ∧
      History.graphSequence (History.append h r) ∈ candidates ∧
      ∀ h' : History In₁ In₂ Graph Out₁ Out₂,
        currentView Proc.two h' = currentView Proc.two (History.append h r) ->
        History.graphSequence h' ∈ candidates

/-- Interior one-sided epoch steps preserve the immediate non-fringe order. -/
theorem sameSide_epochInteriorStep
    {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
    (dominant : Proc)
    (h : History In₁ In₂ Graph Out₁ Out₂)
    (r : RoundRecord In₁ In₂ Graph Out₁ Out₂)
    (hr : r.graph = dominantGraph dominant) :
    SameSideEpochInteriorStep dominant h r where
  graphMatchesDominant := hr
  subordinateSubtuple := by
    cases dominant with
    | one =>
        exact dynhier_left h r hr
    | two =>
        exact dynhier_right h r hr
  oneBitFringeOne := onebitfringe_procOne (History.append h r)
  oneBitFringeTwo := onebitfringe_procTwo (History.append h r)

/--
Left-to-right direct reversal local package: the new dominant is process `2`.
-/
theorem directReversal_leftToRight_epochRelativeHandoff
    {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
    (h : History In₁ In₂ Graph Out₁ Out₂)
    (r : RoundRecord In₁ In₂ Graph Out₁ Out₂)
    (hr : r.graph = .right) :
    DirectReversalEpochRelativeHandoff Proc.two h r where
  graphMatchesDominant := hr
  previousViewsAndInputsDetermined := by
    intro h' r' hr' hview
    have hview' :
        currentView Proc.two (History.append h r) =
          currentView Proc.two (History.append h' r') := hview
    obtain ⟨hprevOne, hprevTwo, hinputOne, hinputTwo⟩ :=
      directReversal_leftToRight_receiver_determines_previousViewsAndInputs
        h h' r r' hr hr' hview'
    exact ⟨hprevOne, hprevTwo, hinputOne, hinputTwo⟩
  oldOwnReceiptRecoverable :=
    directReversal_leftToRight_receiver_recovers_oldOwnReceipt h r hr
  pendingCounterpartCopyBitReadable := by
    rw [directReversal_leftToRight_receiver_recovers_oldOwnReceipt h r hr]
  pendingCounterpartCopyGraphReadable :=
    leftToRight_pendingCounterpartCopyGraph_readBy_newDominant h r hr
  oneBitFringeOne := onebitfringe_procOne (History.append h r)
  oneBitFringeTwo := onebitfringe_procTwo (History.append h r)

/--
Right-to-left direct reversal local package: the new dominant is process `1`.
-/
theorem directReversal_rightToLeft_epochRelativeHandoff
    {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
    (h : History In₁ In₂ Graph Out₁ Out₂)
    (r : RoundRecord In₁ In₂ Graph Out₁ Out₂)
    (hr : r.graph = .left) :
    DirectReversalEpochRelativeHandoff Proc.one h r where
  graphMatchesDominant := hr
  previousViewsAndInputsDetermined := by
    intro h' r' hr' hview
    have hview' :
        currentView Proc.one (History.append h r) =
          currentView Proc.one (History.append h' r') := hview
    obtain ⟨hprevOne, hprevTwo, hinputOne, hinputTwo⟩ :=
      directReversal_rightToLeft_receiver_determines_previousViewsAndInputs
        h h' r r' hr hr' hview'
    exact ⟨hprevOne, hprevTwo, hinputOne, hinputTwo⟩
  oldOwnReceiptRecoverable :=
    directReversal_rightToLeft_receiver_recovers_oldOwnReceipt h r hr
  pendingCounterpartCopyBitReadable := by
    rw [directReversal_rightToLeft_receiver_recovers_oldOwnReceipt h r hr]
  pendingCounterpartCopyGraphReadable :=
    rightToLeft_pendingCounterpartCopyGraph_readBy_newDominant h r hr
  oneBitFringeOne := onebitfringe_procOne (History.append h r)
  oneBitFringeTwo := onebitfringe_procTwo (History.append h r)

/--
The proof-relevant local transition case used by the epoch-relative induction.
`previousDominant = none` means the previous round was a synchronizing boundary
or the history is empty, so a one-way round starts a fresh epoch.
-/
inductive EpochRelativeLocalCase
    {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
    (previousDominant : Option Proc)
    (h : History In₁ In₂ Graph Out₁ Out₂)
    (r : RoundRecord In₁ In₂ Graph Out₁ Out₂) : Type (max u v x y) where
  | boundary :
      BidirectionalBoundaryEpochReset h r ->
      EpochRelativeLocalCase previousDominant h r
  | interior :
      (dominant : Proc) ->
      (previousDominant = none ∨ previousDominant = some dominant) ->
      SameSideEpochInteriorStep dominant h r ->
      EpochRelativeLocalCase previousDominant h r
  | directReversal :
      (oldDominant : Proc) ->
      previousDominant = some oldDominant ->
      DirectReversalEpochRelativeHandoff oldDominant.other h r ->
      EpochRelativeLocalCase previousDominant h r

/--
Every appended round has one of the three local epoch-relative cases.  This is
the total case splitter used by the global induction over graph histories.
-/
def epochRelativeLocalCase
    {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
    (previousDominant : Option Proc)
    (h : History In₁ In₂ Graph Out₁ Out₂)
    (r : RoundRecord In₁ In₂ Graph Out₁ Out₂) :
    EpochRelativeLocalCase previousDominant h r := by
  cases previousDominant with
  | none =>
      cases hGraph : r.graph with
      | left =>
          exact .interior Proc.one (Or.inl rfl)
            (sameSide_epochInteriorStep Proc.one h r hGraph)
      | right =>
          exact .interior Proc.two (Or.inl rfl)
            (sameSide_epochInteriorStep Proc.two h r hGraph)
      | both =>
          exact .boundary (bidirectionalBoundary_epochReset h r hGraph)
  | some oldDominant =>
      cases oldDominant with
      | one =>
          cases hGraph : r.graph with
          | left =>
              exact .interior Proc.one (Or.inr rfl)
                (sameSide_epochInteriorStep Proc.one h r hGraph)
          | right =>
              exact .directReversal Proc.one rfl
                (directReversal_leftToRight_epochRelativeHandoff h r hGraph)
          | both =>
              exact .boundary (bidirectionalBoundary_epochReset h r hGraph)
      | two =>
          cases hGraph : r.graph with
          | left =>
              exact .directReversal Proc.two rfl
                (directReversal_rightToLeft_epochRelativeHandoff h r hGraph)
          | right =>
              exact .interior Proc.two (Or.inr rfl)
                (sameSide_epochInteriorStep Proc.two h r hGraph)
          | both =>
              exact .boundary (bidirectionalBoundary_epochReset h r hGraph)

/--
Proof-relevant decomposition of a finite history into epoch-relative local
cases.  The previous dominant side at each append step is computed from the
graph prefix, so the trace follows the actual play history rather than an
externally supplied mode.
-/
inductive EpochRelativeHistoryTrace
    {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y} :
    History In₁ In₂ Graph Out₁ Out₂ -> Type (max u v x y) where
  | empty : EpochRelativeHistoryTrace []
  | append :
      {h : History In₁ In₂ Graph Out₁ Out₂} ->
      (r : RoundRecord In₁ In₂ Graph Out₁ Out₂) ->
      EpochRelativeHistoryTrace h ->
      EpochRelativeLocalCase (dominantProcessOfWord (History.graphSequence h)) h r ->
      EpochRelativeHistoryTrace (History.append h r)

/--
Every finite history admits the canonical epoch-relative local-case trace.
This is the global induction spine for `prop:epochhierarchical`.
-/
def epochRelativeHistoryTrace
    {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
    (h : History In₁ In₂ Graph Out₁ Out₂) :
    EpochRelativeHistoryTrace h := by
  induction h using List.reverseRecOn with
  | nil =>
      exact .empty
  | append_singleton h r ih =>
      exact
        .append r ih
          (epochRelativeLocalCase
            (dominantProcessOfWord (History.graphSequence h)) h r)

/--
Generic induction principle for epoch-relative history invariants.  A concrete
summary proof only has to handle the three local cases exposed by
`EpochRelativeLocalCase`; this theorem threads those handlers over the canonical
history trace.
-/
def epochRelativeHistoryTrace_fold
    {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
    (Invariant : History In₁ In₂ Graph Out₁ Out₂ -> Prop)
    (base : Invariant [])
    (step :
      ∀ h : History In₁ In₂ Graph Out₁ Out₂,
        ∀ r : RoundRecord In₁ In₂ Graph Out₁ Out₂,
          Invariant h ->
          EpochRelativeLocalCase
            (dominantProcessOfWord (History.graphSequence h)) h r ->
          Invariant (History.append h r))
    (h : History In₁ In₂ Graph Out₁ Out₂) :
    Invariant h := by
  induction h using List.reverseRecOn with
  | nil =>
      exact base
  | append_singleton h r ih =>
      exact step h r ih
        (epochRelativeLocalCase
          (dominantProcessOfWord (History.graphSequence h)) h r)

/--
The local proof obligations needed to lift the epoch-relative trace into a
global summary invariant.
-/
structure EpochSummaryTraceHandlers
    {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
    (Invariant : History In₁ In₂ Graph Out₁ Out₂ -> Prop) where
  base : Invariant []
  boundary :
    ∀ h : History In₁ In₂ Graph Out₁ Out₂,
      ∀ r : RoundRecord In₁ In₂ Graph Out₁ Out₂,
        Invariant h ->
        BidirectionalBoundaryEpochReset h r ->
        Invariant (History.append h r)
  interior :
    ∀ h : History In₁ In₂ Graph Out₁ Out₂,
      ∀ r : RoundRecord In₁ In₂ Graph Out₁ Out₂,
        Invariant h ->
        ∀ dominant : Proc,
          (dominantProcessOfWord (History.graphSequence h) = none ∨
            dominantProcessOfWord (History.graphSequence h) = some dominant) ->
          SameSideEpochInteriorStep dominant h r ->
          Invariant (History.append h r)
  directReversal :
    ∀ h : History In₁ In₂ Graph Out₁ Out₂,
      ∀ r : RoundRecord In₁ In₂ Graph Out₁ Out₂,
        Invariant h ->
        ∀ oldDominant : Proc,
          dominantProcessOfWord (History.graphSequence h) = some oldDominant ->
          DirectReversalEpochRelativeHandoff oldDominant.other h r ->
          Invariant (History.append h r)

/-- Apply local trace handlers to prove the summary invariant for every history. -/
theorem epochSummaryInvariant_of_traceHandlers
    {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
    {Invariant : History In₁ In₂ Graph Out₁ Out₂ -> Prop}
    (handlers : EpochSummaryTraceHandlers Invariant) :
    ∀ h : History In₁ In₂ Graph Out₁ Out₂, Invariant h :=
  epochRelativeHistoryTrace_fold Invariant handlers.base
    (fun h r ih localCase =>
      match localCase with
      | .boundary reset =>
          handlers.boundary h r ih reset
      | .interior dominant hprevious interior =>
          handlers.interior h r ih dominant hprevious interior
      | .directReversal oldDominant hprevious handoff =>
          handlers.directReversal h r ih oldDominant hprevious handoff)

/--
Concrete invariant saying every nonempty prefix satisfies the non-fringe order
induced by its final graph letter.
-/
def CurrentHistoryNonFringeOrderInvariant
    {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
    (h : History In₁ In₂ Graph Out₁ Out₂) : Prop :=
  ∀ (pref : History In₁ In₂ Graph Out₁ Out₂),
    ∀ (r : RoundRecord In₁ In₂ Graph Out₁ Out₂),
      h = History.append pref r ->
        CurrentNonFringeOrder h (graphContainmentOrder r.graph)

/--
The raw current-order invariant is preserved by the epoch-relative local trace.
This is the first concrete instantiation of `EpochSummaryTraceHandlers`.
-/
def currentHistoryNonFringeOrderTraceHandlers
    {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y} :
    EpochSummaryTraceHandlers
      (CurrentHistoryNonFringeOrderInvariant
        (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)) where
  base := by
    intro pref r hnil
    simp [History.append] at hnil
  boundary := by
    intro h r _ih _reset pref last hEq
    rw [hEq]
    exact currentNonFringeOrder_append pref last
  interior := by
    intro h r _ih _dominant _hprevious _interior pref last hEq
    rw [hEq]
    exact currentNonFringeOrder_append pref last
  directReversal := by
    intro h r _ih _oldDominant _hprevious _handoff pref last hEq
    rw [hEq]
    exact currentNonFringeOrder_append pref last

/-- Every finite history satisfies the raw current non-fringe order invariant. -/
theorem currentHistoryNonFringeOrderInvariant_all
    {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
    (h : History In₁ In₂ Graph Out₁ Out₂) :
    CurrentHistoryNonFringeOrderInvariant h :=
  epochSummaryInvariant_of_traceHandlers
    (currentHistoryNonFringeOrderTraceHandlers
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    h

/--
Concrete invariant saying every nonempty prefix has a canonical finite
`ReceiptOrderData` component that stores the current receipt tags, stores the
graph-induced containment order, and realizes that order semantically.
-/
def CurrentReceiptOrderDataInvariant
    {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
    (h : History In₁ In₂ Graph Out₁ Out₂) : Prop :=
  ∀ (pref : History In₁ In₂ Graph Out₁ Out₂),
    ∀ (r : RoundRecord In₁ In₂ Graph Out₁ Out₂),
      h = History.append pref r ->
        let data := currentReceiptOrderDataForAppend pref r
        data.receiptOne = (currentView Proc.one h).receiptTag ∧
          data.receiptTwo = (currentView Proc.two h).receiptTag ∧
          data.containmentOrder = graphContainmentOrder r.graph ∧
          CurrentNonFringeOrder h data.containmentOrder

/-- The canonical receipt/order invariant is preserved by the trace handlers. -/
def currentReceiptOrderDataTraceHandlers
    {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y} :
    EpochSummaryTraceHandlers
      (CurrentReceiptOrderDataInvariant
        (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)) where
  base := by
    intro pref r hnil
    simp [History.append] at hnil
  boundary := by
    intro h r _ih _reset pref last hEq
    rw [hEq]
    simp [currentReceiptOrderDataForAppend, currentNonFringeOrder_append]
  interior := by
    intro h r _ih _dominant _hprevious _interior pref last hEq
    rw [hEq]
    simp [currentReceiptOrderDataForAppend, currentNonFringeOrder_append]
  directReversal := by
    intro h r _ih _oldDominant _hprevious _handoff pref last hEq
    rw [hEq]
    simp [currentReceiptOrderDataForAppend, currentNonFringeOrder_append]

/-- Every finite history has the canonical current receipt/order data invariant. -/
theorem currentReceiptOrderDataInvariant_all
    {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
    (h : History In₁ In₂ Graph Out₁ Out₂) :
    CurrentReceiptOrderDataInvariant h :=
  epochSummaryInvariant_of_traceHandlers
    (currentReceiptOrderDataTraceHandlers
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    h

/--
Concrete finite summaries preserve the current receipt/order payload when their
decoded receipt/order component agrees with the canonical history component.
-/
def SummaryReceiptOrderDataInvariant
    {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
    {Summary₁ : Type a} {Summary₂ : Type b}
    (summaryOfHistory :
      History In₁ In₂ Graph Out₁ Out₂ -> Summary₁ × Summary₂)
    (decodeReceiptOrder : Summary₁ × Summary₂ -> ReceiptOrderData)
    (h : History In₁ In₂ Graph Out₁ Out₂) : Prop :=
  ∀ (pref : History In₁ In₂ Graph Out₁ Out₂),
    ∀ (r : RoundRecord In₁ In₂ Graph Out₁ Out₂),
      h = History.append pref r ->
        let data := decodeReceiptOrder (summaryOfHistory h)
        data.receiptOne = (currentView Proc.one h).receiptTag ∧
          data.receiptTwo = (currentView Proc.two h).receiptTag ∧
          data.containmentOrder = graphContainmentOrder r.graph ∧
          CurrentNonFringeOrder h data.containmentOrder

/--
If a concrete summary decoder returns the canonical receipt/order data at every
nonempty prefix, then the summary realizes the raw receipt/order invariant.
-/
theorem summaryReceiptOrderDataInvariant_of_decodesCurrent
    {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
    {Summary₁ : Type a} {Summary₂ : Type b}
    (summaryOfHistory :
      History In₁ In₂ Graph Out₁ Out₂ -> Summary₁ × Summary₂)
    (decodeReceiptOrder : Summary₁ × Summary₂ -> ReceiptOrderData)
    (decodesCurrent :
      ∀ (pref : History In₁ In₂ Graph Out₁ Out₂),
        ∀ (r : RoundRecord In₁ In₂ Graph Out₁ Out₂),
          decodeReceiptOrder (summaryOfHistory (History.append pref r)) =
            currentReceiptOrderDataForAppend pref r)
    (h : History In₁ In₂ Graph Out₁ Out₂) :
    SummaryReceiptOrderDataInvariant summaryOfHistory decodeReceiptOrder h := by
  intro pref r hEq
  rw [hEq]
  have hdecode := decodesCurrent pref r
  simp [hdecode, currentReceiptOrderDataForAppend, currentNonFringeOrder_append]

/--
Trace handlers for any concrete finite summary whose receipt/order decoder
matches the canonical history-derived receipt/order data.
-/
def summaryReceiptOrderDataTraceHandlers
    {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
    {Summary₁ : Type a} {Summary₂ : Type b}
    (summaryOfHistory :
      History In₁ In₂ Graph Out₁ Out₂ -> Summary₁ × Summary₂)
    (decodeReceiptOrder : Summary₁ × Summary₂ -> ReceiptOrderData)
    (decodesCurrent :
      ∀ (pref : History In₁ In₂ Graph Out₁ Out₂),
        ∀ (r : RoundRecord In₁ In₂ Graph Out₁ Out₂),
          decodeReceiptOrder (summaryOfHistory (History.append pref r)) =
            currentReceiptOrderDataForAppend pref r) :
    EpochSummaryTraceHandlers
      (SummaryReceiptOrderDataInvariant summaryOfHistory decodeReceiptOrder) where
  base := by
    intro pref r hnil
    simp [History.append] at hnil
  boundary := by
    intro h r _ih _reset
    exact
      summaryReceiptOrderDataInvariant_of_decodesCurrent
        summaryOfHistory decodeReceiptOrder decodesCurrent (History.append h r)
  interior := by
    intro h r _ih _dominant _hprevious _interior
    exact
      summaryReceiptOrderDataInvariant_of_decodesCurrent
        summaryOfHistory decodeReceiptOrder decodesCurrent (History.append h r)
  directReversal := by
    intro h r _ih _oldDominant _hprevious _handoff
    exact
      summaryReceiptOrderDataInvariant_of_decodesCurrent
        summaryOfHistory decodeReceiptOrder decodesCurrent (History.append h r)

/--
Every history satisfies the decoded finite-summary receipt/order invariant once
the decoder agrees with the canonical current receipt/order component.
-/
theorem summaryReceiptOrderDataInvariant_all
    {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
    {Summary₁ : Type a} {Summary₂ : Type b}
    (summaryOfHistory :
      History In₁ In₂ Graph Out₁ Out₂ -> Summary₁ × Summary₂)
    (decodeReceiptOrder : Summary₁ × Summary₂ -> ReceiptOrderData)
    (decodesCurrent :
      ∀ (pref : History In₁ In₂ Graph Out₁ Out₂),
        ∀ (r : RoundRecord In₁ In₂ Graph Out₁ Out₂),
          decodeReceiptOrder (summaryOfHistory (History.append pref r)) =
            currentReceiptOrderDataForAppend pref r)
    (h : History In₁ In₂ Graph Out₁ Out₂) :
    SummaryReceiptOrderDataInvariant summaryOfHistory decodeReceiptOrder h :=
  epochSummaryInvariant_of_traceHandlers
    (summaryReceiptOrderDataTraceHandlers
      summaryOfHistory decodeReceiptOrder decodesCurrent)
    h

/--
At any final direct reversal, the pending counterpart bit itself is readable
from the new dominant's current non-fringe view.  This is the bit-level version
of the handoff fact; the graph-copy statement below is just its paired-copy
interpretation.
-/
def LastDirectReversalPendingCounterpartCopyBitReadable
    {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
    (h : History In₁ In₂ Graph Out₁ Out₂) : Prop :=
  ∀ (pref : History In₁ In₂ Graph Out₁ Out₂),
    ∀ (r : RoundRecord In₁ In₂ Graph Out₁ Out₂),
      ∀ oldDominant : Proc,
        h = History.append pref r ->
          dominantProcessOfWord (History.graphSequence pref) = some oldDominant ->
          r.graph = dominantGraph oldDominant.other ->
            pendingCopyOfReceipt
                ((currentNonFringe oldDominant.other h).previousView.receiptTag) =
              pendingCopyOfReceipt ((currentView oldDominant.other pref).receiptTag)

/--
Every finite history satisfies the final direct-reversal pending-bit readability
property.  The proof splits on the reversal direction and rewrites with the
new-dominant old-receipt recovery lemma.
-/
theorem lastDirectReversalPendingCounterpartCopyBitReadable_all
    {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
    (h : History In₁ In₂ Graph Out₁ Out₂) :
    LastDirectReversalPendingCounterpartCopyBitReadable h := by
  intro pref r oldDominant hEq _hprevious hgraph
  rw [hEq]
  cases oldDominant with
  | one =>
      have hright : r.graph = .right := by
        simpa [dominantGraph] using hgraph
      change
        pendingCopyOfReceipt
            ((currentNonFringe Proc.two (History.append pref r)).previousView.receiptTag) =
          pendingCopyOfReceipt ((currentView Proc.two pref).receiptTag)
      exact
        congrArg pendingCopyOfReceipt
          (directReversal_leftToRight_receiver_recovers_oldOwnReceipt pref r hright)
  | two =>
      have hleft : r.graph = .left := by
        simpa [dominantGraph] using hgraph
      change
        pendingCopyOfReceipt
            ((currentNonFringe Proc.one (History.append pref r)).previousView.receiptTag) =
          pendingCopyOfReceipt ((currentView Proc.one pref).receiptTag)
      exact
        congrArg pendingCopyOfReceipt
          (directReversal_rightToLeft_receiver_recovers_oldOwnReceipt pref r hleft)

/--
At any final direct reversal, the pending counterpart-copy graph is readable
from the new dominant's current non-fringe view.  This is the global, reusable
form of the direct-reversal handoff fact: the previous dominant determines
which one-way side just closed, and the new dominant's old own receipt selects
the copied graph that represents the old dominant's pending counterpart bit.
-/
def LastDirectReversalPendingCounterpartCopyReadable
    {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
    (h : History In₁ In₂ Graph Out₁ Out₂) : Prop :=
  ∀ (pref : History In₁ In₂ Graph Out₁ Out₂),
    ∀ (r : RoundRecord In₁ In₂ Graph Out₁ Out₂),
      ∀ oldDominant : Proc,
        h = History.append pref r ->
          dominantProcessOfWord (History.graphSequence pref) = some oldDominant ->
          r.graph = dominantGraph oldDominant.other ->
            match oldDominant.other with
            | .one =>
                graphForProcessTwoCopy
                    (pendingCopyOfReceipt
                      ((currentNonFringe Proc.one h).previousView.receiptTag)) =
                  graphForProcessTwoCopy
                    (pendingCopyOfReceipt
                      ((currentView Proc.one pref).receiptTag))
            | .two =>
                graphForProcessOneCopy
                    (pendingCopyOfReceipt
                      ((currentNonFringe Proc.two h).previousView.receiptTag)) =
                  graphForProcessOneCopy
                    (pendingCopyOfReceipt
                      ((currentView Proc.two pref).receiptTag))

/--
Every finite history satisfies the last-step direct-reversal readability
property.  The proof deliberately avoids the dead `pastreceipt` route for the
counterpart bit: in the left-to-right case the new dominant is process `2` and
reads its own previous receipt; in the right-to-left case the new dominant is
process `1` and reads its own previous receipt.
-/
theorem lastDirectReversalPendingCounterpartCopyReadable_all
    {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
    (h : History In₁ In₂ Graph Out₁ Out₂) :
    LastDirectReversalPendingCounterpartCopyReadable h := by
  intro pref r oldDominant hEq _hprevious hgraph
  rw [hEq]
  cases oldDominant with
  | one =>
      have hright : r.graph = .right := by
        simpa [dominantGraph] using hgraph
      simpa [dominantGraph] using
        leftToRight_pendingCounterpartCopyGraph_readBy_newDominant pref r hright
  | two =>
      have hleft : r.graph = .left := by
        simpa [dominantGraph] using hgraph
      simpa [dominantGraph] using
        rightToLeft_pendingCounterpartCopyGraph_readBy_newDominant pref r hleft

/--
At any final direct reversal, the new dominant's current view determines both
previous full views and the current input pair.  This is the global form of the
delayed-handoff clause used by the epoch-relative hierarchy proof.
-/
def LastDirectReversalPreviousViewsAndInputsDetermined
    {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
    (h : History In₁ In₂ Graph Out₁ Out₂) : Prop :=
  ∀ (pref : History In₁ In₂ Graph Out₁ Out₂),
    ∀ (r : RoundRecord In₁ In₂ Graph Out₁ Out₂),
      ∀ oldDominant : Proc,
        h = History.append pref r ->
          dominantProcessOfWord (History.graphSequence pref) = some oldDominant ->
          r.graph = dominantGraph oldDominant.other ->
            ∀ (pref' : History In₁ In₂ Graph Out₁ Out₂),
              ∀ (r' : RoundRecord In₁ In₂ Graph Out₁ Out₂),
                r'.graph = dominantGraph oldDominant.other ->
                currentView oldDominant.other h =
                  currentView oldDominant.other (History.append pref' r') ->
                    currentView Proc.one pref = currentView Proc.one pref' ∧
                      currentView Proc.two pref = currentView Proc.two pref' ∧
                      r.inputOne = r'.inputOne ∧ r.inputTwo = r'.inputTwo

/--
Every finite history satisfies the final direct-reversal delayed-handoff
property.  The proof splits on the old dominant side and reuses the concrete
left-to-right/right-to-left receiver lemmas.
-/
theorem lastDirectReversalPreviousViewsAndInputsDetermined_all
    {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
    (h : History In₁ In₂ Graph Out₁ Out₂) :
    LastDirectReversalPreviousViewsAndInputsDetermined h := by
  intro pref r oldDominant hEq _hprevious hgraph pref' r' hgraph' hview
  rw [hEq] at hview
  cases oldDominant with
  | one =>
      have hright : r.graph = .right := by
        simpa [dominantGraph] using hgraph
      have hright' : r'.graph = .right := by
        simpa [dominantGraph] using hgraph'
      exact
        directReversal_leftToRight_receiver_determines_previousViewsAndInputs
          pref pref' r r' hright hright' hview
  | two =>
      have hleft : r.graph = .left := by
        simpa [dominantGraph] using hgraph
      have hleft' : r'.graph = .left := by
        simpa [dominantGraph] using hgraph'
      exact
        directReversal_rightToLeft_receiver_determines_previousViewsAndInputs
          pref pref' r r' hleft hleft' hview

/-- Certificate that a finite summary retraction preserves the dynamic hierarchy. -/
structure EpochSummaryHierarchyCertificate
    (Summary₁ : Type u) (Summary₂ : Type v) where
  accumulatedHistoriesHierarchical : Prop
  olderReceiptTagsRecoverable : Prop
  directReversalPreviousViewsAndInputsDetermined : Prop
  directReversalPendingCounterpartCopyBitReadable : Prop
  directReversalPendingCounterpartCopyReadable : Prop
  accumulatedHistoriesHierarchical_proof : accumulatedHistoriesHierarchical
  olderReceiptTagsRecoverable_proof : olderReceiptTagsRecoverable
  directReversalPreviousViewsAndInputsDetermined_proof :
    directReversalPreviousViewsAndInputsDetermined
  directReversalPendingCounterpartCopyBitReadable_proof :
    directReversalPendingCounterpartCopyBitReadable
  directReversalPendingCounterpartCopyReadable_proof :
    directReversalPendingCounterpartCopyReadable

/--
Build the paper-facing hierarchy certificate from concrete local handlers over
the epoch-relative history trace.  The remaining non-automatic input is the
paper's older-receipt recoverability theorem for the chosen summaries.
-/
def epochSummaryHierarchyCertificateOfTraceHandlers
    {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
    {Summary₁ : Type a} {Summary₂ : Type b}
    {Invariant : History In₁ In₂ Graph Out₁ Out₂ -> Prop}
    (handlers : EpochSummaryTraceHandlers Invariant)
    (olderReceiptTagsRecoverable : Prop)
    (olderReceiptTagsRecoverable_proof : olderReceiptTagsRecoverable) :
    EpochSummaryHierarchyCertificate Summary₁ Summary₂ where
  accumulatedHistoriesHierarchical :=
    ∀ h : History In₁ In₂ Graph Out₁ Out₂, Invariant h
  olderReceiptTagsRecoverable := olderReceiptTagsRecoverable
  directReversalPreviousViewsAndInputsDetermined :=
    ∀ h : History In₁ In₂ Graph Out₁ Out₂,
      LastDirectReversalPreviousViewsAndInputsDetermined h
  directReversalPendingCounterpartCopyBitReadable :=
    ∀ h : History In₁ In₂ Graph Out₁ Out₂,
      LastDirectReversalPendingCounterpartCopyBitReadable h
  directReversalPendingCounterpartCopyReadable :=
    ∀ h : History In₁ In₂ Graph Out₁ Out₂,
      LastDirectReversalPendingCounterpartCopyReadable h
  accumulatedHistoriesHierarchical_proof :=
    epochSummaryInvariant_of_traceHandlers handlers
  olderReceiptTagsRecoverable_proof := olderReceiptTagsRecoverable_proof
  directReversalPreviousViewsAndInputsDetermined_proof :=
    lastDirectReversalPreviousViewsAndInputsDetermined_all
  directReversalPendingCounterpartCopyBitReadable_proof :=
    lastDirectReversalPendingCounterpartCopyBitReadable_all
  directReversalPendingCounterpartCopyReadable_proof :=
    lastDirectReversalPendingCounterpartCopyReadable_all

/--
Concrete own-receipt recoverability for the raw current non-fringe summaries.
After one later round and any suffix, the older same-process receipt tag is
obtained by rewinding the final non-fringe view.  This is exactly the scope of
`lem:pastreceipt`; it does not assert recovery of the counterpart reversal bit.
-/
def CurrentReceiptOlderOwnTagsRecoverable
    {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y} : Prop :=
  (∀ h : History In₁ In₂ Graph Out₁ Out₂,
    ∀ r : RoundRecord In₁ In₂ Graph Out₁ Out₂,
      ∀ suffix : History In₁ In₂ Graph Out₁ Out₂,
        (rewindNonFringe suffix.length
            (currentNonFringe Proc.one (History.append h r ++ suffix))).previousView.receiptTag =
          (currentView Proc.one h).receiptTag) ∧
  (∀ h : History In₁ In₂ Graph Out₁ Out₂,
    ∀ r : RoundRecord In₁ In₂ Graph Out₁ Out₂,
      ∀ suffix : History In₁ In₂ Graph Out₁ Out₂,
        (rewindNonFringe suffix.length
            (currentNonFringe Proc.two (History.append h r ++ suffix))).previousView.receiptTag =
          (currentView Proc.two h).receiptTag)

/-- The raw current non-fringe summaries recover older same-process receipts. -/
theorem currentReceiptOlderOwnTagsRecoverable
    {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y} :
    CurrentReceiptOlderOwnTagsRecoverable
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂) := by
  constructor
  · intro h r suffix
    exact previousReceiptTag_computable_from_later_nonFringe Proc.one h r suffix
  · intro h r suffix
    exact previousReceiptTag_computable_from_later_nonFringe Proc.two h r suffix

/--
Concrete hierarchy certificate for the raw current non-fringe/receipt payload.
The hierarchy component is fully proved by `currentReceiptOrderDataTraceHandlers`;
the only remaining input is the older-receipt recoverability theorem for the
chosen summary interpretation.
-/
def currentReceiptOrderDataHierarchyCertificate
    {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
    (olderReceiptTagsRecoverable : Prop)
    (olderReceiptTagsRecoverable_proof : olderReceiptTagsRecoverable) :
    EpochSummaryHierarchyCertificate
      (NonFringeView In₁ In₂ Proc.one × ReceiptTag)
      (NonFringeView In₁ In₂ Proc.two × ReceiptTag) :=
  epochSummaryHierarchyCertificateOfTraceHandlers
    (currentReceiptOrderDataTraceHandlers
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    olderReceiptTagsRecoverable
    olderReceiptTagsRecoverable_proof

/--
Fully proved raw hierarchy certificate for current non-fringe views paired with
the current receipt tag.  The hierarchy/order part is supplied by the
epoch-relative trace; the older same-process receipt part is supplied by
`lem:pastreceipt`.
-/
def currentReceiptOrderDataHierarchyCertificateOfPastReceipt
    {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y} :
    EpochSummaryHierarchyCertificate
      (NonFringeView In₁ In₂ Proc.one × ReceiptTag)
      (NonFringeView In₁ In₂ Proc.two × ReceiptTag) :=
  currentReceiptOrderDataHierarchyCertificate
    (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)
    (CurrentReceiptOlderOwnTagsRecoverable
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    currentReceiptOlderOwnTagsRecoverable

/--
Hierarchy certificate for a concrete finite summary pair whose decoded
receipt/order component agrees with the canonical current receipt/order data.
This is the quotient-preservation bridge used before adding the remaining
finite-summary-specific older-receipt recovery proof.
-/
def summaryReceiptOrderDataHierarchyCertificate
    {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
    {Summary₁ : Type a} {Summary₂ : Type b}
    (summaryOfHistory :
      History In₁ In₂ Graph Out₁ Out₂ -> Summary₁ × Summary₂)
    (decodeReceiptOrder : Summary₁ × Summary₂ -> ReceiptOrderData)
    (decodesCurrent :
      ∀ (pref : History In₁ In₂ Graph Out₁ Out₂),
        ∀ (r : RoundRecord In₁ In₂ Graph Out₁ Out₂),
          decodeReceiptOrder (summaryOfHistory (History.append pref r)) =
            currentReceiptOrderDataForAppend pref r)
    (olderReceiptTagsRecoverable : Prop)
    (olderReceiptTagsRecoverable_proof : olderReceiptTagsRecoverable) :
    EpochSummaryHierarchyCertificate Summary₁ Summary₂ :=
  epochSummaryHierarchyCertificateOfTraceHandlers
    (summaryReceiptOrderDataTraceHandlers
      summaryOfHistory decodeReceiptOrder decodesCurrent)
    olderReceiptTagsRecoverable
    olderReceiptTagsRecoverable_proof

/-- Assemble the current receipt/order payload from side-local summary decoders. -/
def receiptOrderDataDecoderOfSideDecoders
    {Summary₁ : Type a} {Summary₂ : Type b}
    (decodeReceiptOne : Summary₁ -> ReceiptTag)
    (decodeReceiptTwo : Summary₂ -> ReceiptTag)
    (decodeOrder : Summary₁ -> Summary₂ -> NonFringeContainmentOrder) :
    Summary₁ × Summary₂ -> ReceiptOrderData :=
  fun summary =>
    { receiptOne := decodeReceiptOne summary.1
      receiptTwo := decodeReceiptTwo summary.2
      containmentOrder := decodeOrder summary.1 summary.2 }

/--
Side-decoder form of `summaryReceiptOrderDataHierarchyCertificate`.

This is the convenient interface for concrete summaries whose two receipt tags
and current containment order are decoded by separate finite maps.
-/
def summaryReceiptOrderDataHierarchyCertificateOfSideDecoders
    {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
    {Summary₁ : Type a} {Summary₂ : Type b}
    (summaryOfHistory :
      History In₁ In₂ Graph Out₁ Out₂ -> Summary₁ × Summary₂)
    (decodeReceiptOne : Summary₁ -> ReceiptTag)
    (decodeReceiptTwo : Summary₂ -> ReceiptTag)
    (decodeOrder : Summary₁ -> Summary₂ -> NonFringeContainmentOrder)
    (sideDecodesCurrent :
      ∀ (pref : History In₁ In₂ Graph Out₁ Out₂),
        ∀ (r : RoundRecord In₁ In₂ Graph Out₁ Out₂),
          let summary := summaryOfHistory (History.append pref r)
          decodeReceiptOne summary.1 =
              (currentView Proc.one (History.append pref r)).receiptTag ∧
            decodeReceiptTwo summary.2 =
              (currentView Proc.two (History.append pref r)).receiptTag ∧
            decodeOrder summary.1 summary.2 = graphContainmentOrder r.graph)
    (olderReceiptTagsRecoverable : Prop)
    (olderReceiptTagsRecoverable_proof : olderReceiptTagsRecoverable) :
    EpochSummaryHierarchyCertificate Summary₁ Summary₂ :=
  summaryReceiptOrderDataHierarchyCertificate
    summaryOfHistory
    (receiptOrderDataDecoderOfSideDecoders
      decodeReceiptOne decodeReceiptTwo decodeOrder)
    (by
      intro pref r
      rcases hsummary : summaryOfHistory (History.append pref r) with
        ⟨summaryOne, summaryTwo⟩
      rcases sideDecodesCurrent pref r with ⟨hone, htwo, horder⟩
      rw [hsummary] at hone htwo horder
      simp [receiptOrderDataDecoderOfSideDecoders,
        currentReceiptOrderDataForAppend, currentReceiptOrderData,
        hone, htwo, horder])
    olderReceiptTagsRecoverable
    olderReceiptTagsRecoverable_proof

/--
Split-decoder form of `summaryReceiptOrderDataHierarchyCertificateOfSideDecoders`.

This matches the replay/backend boundary where concrete summaries decode both
current non-fringe views and current receipt tags.  The hierarchy certificate
only consumes the two receipt decoders and the current containment-order
decoder; the non-fringe equations are carried in the hypothesis so a caller can
use one split-summary factor package for both hierarchy and replay.
-/
def summaryReceiptOrderDataHierarchyCertificateOfSplitDecoders
    {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
    {Summary₁ : Type a} {Summary₂ : Type b}
    (summaryOfHistory :
      History In₁ In₂ Graph Out₁ Out₂ -> Summary₁ × Summary₂)
    (decodeNonFringeOne : Summary₁ -> NonFringeView In₁ In₂ Proc.one)
    (decodeReceiptOne : Summary₁ -> ReceiptTag)
    (decodeNonFringeTwo : Summary₂ -> NonFringeView In₁ In₂ Proc.two)
    (decodeReceiptTwo : Summary₂ -> ReceiptTag)
    (decodeOrder : Summary₁ -> Summary₂ -> NonFringeContainmentOrder)
    (splitDecodesCurrent :
      ∀ (pref : History In₁ In₂ Graph Out₁ Out₂),
        ∀ (r : RoundRecord In₁ In₂ Graph Out₁ Out₂),
          let summary := summaryOfHistory (History.append pref r)
          decodeNonFringeOne summary.1 =
              currentNonFringe Proc.one (History.append pref r) ∧
            decodeReceiptOne summary.1 =
              (currentView Proc.one (History.append pref r)).receiptTag ∧
            decodeNonFringeTwo summary.2 =
              currentNonFringe Proc.two (History.append pref r) ∧
            decodeReceiptTwo summary.2 =
              (currentView Proc.two (History.append pref r)).receiptTag ∧
            decodeOrder summary.1 summary.2 = graphContainmentOrder r.graph)
    (olderReceiptTagsRecoverable : Prop)
    (olderReceiptTagsRecoverable_proof : olderReceiptTagsRecoverable) :
    EpochSummaryHierarchyCertificate Summary₁ Summary₂ :=
  summaryReceiptOrderDataHierarchyCertificateOfSideDecoders
    summaryOfHistory decodeReceiptOne decodeReceiptTwo decodeOrder
    (by
      intro pref r
      rcases splitDecodesCurrent pref r with
        ⟨_honeNonFringe, honeReceipt, _htwoNonFringe, htwoReceipt, horder⟩
      exact ⟨honeReceipt, htwoReceipt, horder⟩)
    olderReceiptTagsRecoverable
    olderReceiptTagsRecoverable_proof

/--
Paper-facing Proposition `prop:epochhierarchical`: the chosen finite summaries retain
the dynamic hierarchy and receipt-tag recoverability needed downstream.
-/
theorem epoch_summaries_preserve_dynamic_hierarchy
    {Summary₁ : Type u} {Summary₂ : Type v}
    (cert : EpochSummaryHierarchyCertificate Summary₁ Summary₂) :
    cert.accumulatedHistoriesHierarchical ∧
      cert.olderReceiptTagsRecoverable ∧
      cert.directReversalPreviousViewsAndInputsDetermined ∧
      cert.directReversalPendingCounterpartCopyBitReadable ∧
      cert.directReversalPendingCounterpartCopyReadable := by
  exact
    ⟨cert.accumulatedHistoriesHierarchical_proof,
      cert.olderReceiptTagsRecoverable_proof,
      cert.directReversalPreviousViewsAndInputsDetermined_proof,
      cert.directReversalPendingCounterpartCopyBitReadable_proof,
      cert.directReversalPendingCounterpartCopyReadable_proof⟩

end DistributedSynthesis
