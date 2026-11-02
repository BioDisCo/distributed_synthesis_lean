/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemFiniteAcknowledgedExactClosingCanonicalFreshHandlers
import DistributedSynthesis.Formalizations.Lemma.LemFiniteAcknowledgedExactClosingSemanticSelectionTrace

/-!
# Temporal provenance of the acknowledged pending member

The deferred exact-close controller uses two temporally different Boolean
members.  The member already stored in the selected pre-round control belongs
to the current table occurrence.  A receive then creates the member of the
next occurrence: `false` for a strict (open) receive and `true` for a
simultaneous (closed) receive.  A non-receiving endpoint merely retains its
old member.

This file records that time indexing once for the canonical deferred
handlers.  The first theorem is about the deterministic semantic trace; the
second transports it to the actual acknowledged relay trace through
`PairSelects`.  The row theorem is parametrized by an arbitrary finite row
interpretation, so concrete clients can instantiate `false` as their strict
row and `true` as their simultaneous row.

All graph case splits occur only in proofs about a completed environment
round.  No executable endpoint transition is given a graph, orientation,
leader bit, strict-leader bit, history, or view.
-/

namespace DistributedSynthesis

universe u v x y a b c d e f r

namespace FiniteAcknowledgedDelayedCarrier

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable {SharedOne : Type a} {PayloadOne : Type b} {RecurrentOne : Type c}
variable {SharedTwo : Type d} {PayloadTwo : Type e} {RecurrentTwo : Type f}

private abbrev OneControl
    (SharedOne : Type a) (PayloadOne : Type b) (RecurrentOne : Type c) :=
  DeferredOrRecurrent SharedOne PayloadOne RecurrentOne

private abbrev TwoControl
    (SharedTwo : Type d) (PayloadTwo : Type e) (RecurrentTwo : Type f) :=
  DeferredOrRecurrent SharedTwo PayloadTwo RecurrentTwo

/-! ## Member and row observations -/

/-- The pending member of a deferred control.  A recurrent control has no
pending member. -/
def deferredOrRecurrentMember? {Shared : Type a} {Payload : Type b}
    {Recurrent : Type c}
    (control : DeferredOrRecurrent Shared Payload Recurrent) : Option Bool :=
  match control with
  | .inl pending => some pending.1
  | .inr _ => none

/-- Interpret the currently stored pending member as a row. -/
def deferredOrRecurrentRow? {Shared : Type a} {Payload : Type b}
    {Recurrent : Type c} {Row : Type r}
    (rowOfMember : Bool → Row)
    (control : DeferredOrRecurrent Shared Payload Recurrent) : Option Row :=
  (deferredOrRecurrentMember? control).map rowOfMember

@[simp] theorem deferredOrRecurrentMember?_inl
    {Shared : Type a} {Payload : Type b} {Recurrent : Type c}
    (pending : DeferredMemberControl Shared Payload) :
    deferredOrRecurrentMember?
        (.inl pending : DeferredOrRecurrent Shared Payload Recurrent) =
      some pending.1 :=
  rfl

@[simp] theorem deferredOrRecurrentMember?_inr
    {Shared : Type a} {Payload : Type b} {Recurrent : Type c}
    (recurrent : Recurrent) :
    deferredOrRecurrentMember?
        (.inr recurrent : DeferredOrRecurrent Shared Payload Recurrent) =
      none :=
  rfl

@[simp] theorem deferredOrRecurrentRow?_inl
    {Shared : Type a} {Payload : Type b} {Recurrent : Type c}
    {Row : Type r} (rowOfMember : Bool → Row)
    (pending : DeferredMemberControl Shared Payload) :
    deferredOrRecurrentRow? rowOfMember
        (.inl pending : DeferredOrRecurrent Shared Payload Recurrent) =
      some (rowOfMember pending.1) :=
  rfl

@[simp] theorem deferredOrRecurrentRow?_inr
    {Shared : Type a} {Payload : Type b} {Recurrent : Type c}
    {Row : Type r} (rowOfMember : Bool → Row)
    (recurrent : Recurrent) :
    deferredOrRecurrentRow? rowOfMember
        (.inr recurrent : DeferredOrRecurrent Shared Payload Recurrent) =
      none :=
  rfl

@[simp] theorem deferredOrRecurrentMember?_pending
    (member : Bool) (shared : SharedOne) (payload : PayloadOne) :
    deferredOrRecurrentMember?
        (.inl (member, shared, payload) :
          OneControl SharedOne PayloadOne RecurrentOne) = some member :=
  rfl

@[simp] theorem deferredOrRecurrentMember?_recurrent
    (recurrent : RecurrentOne) :
    deferredOrRecurrentMember?
        (.inr recurrent : OneControl SharedOne PayloadOne RecurrentOne) =
      none :=
  rfl

@[simp] theorem deferredOrRecurrentRow?_pending
    {Row : Type r} (rowOfMember : Bool → Row)
    (member : Bool) (shared : SharedOne) (payload : PayloadOne) :
    deferredOrRecurrentRow? rowOfMember
        (.inl (member, shared, payload) :
          OneControl SharedOne PayloadOne RecurrentOne) =
      some (rowOfMember member) :=
  rfl

@[simp] theorem deferredOrRecurrentRow?_recurrent
    {Row : Type r} (rowOfMember : Bool → Row)
    (recurrent : RecurrentOne) :
    deferredOrRecurrentRow? rowOfMember
        (.inr recurrent : OneControl SharedOne PayloadOne RecurrentOne) =
      none :=
  rfl

/-- A graph-blind local step does not create or change a pending member. -/
@[simp] theorem deferredOrRecurrentMember?_noRecv
    (pendingStep : Bool → SharedOne → In₁ → SharedOne × Out₁)
    (recurrentStep : RecurrentOne → In₁ → RecurrentOne × Out₁)
    (control : OneControl SharedOne PayloadOne RecurrentOne) (input : In₁) :
    deferredOrRecurrentMember?
        (deferredOrRecurrentNoRecv pendingStep recurrentStep control input).1 =
      deferredOrRecurrentMember? control := by
  cases control <;> rfl

/-- Row form of member preservation under a graph-blind local step. -/
@[simp] theorem deferredOrRecurrentRow?_noRecv
    {Row : Type r} (rowOfMember : Bool → Row)
    (pendingStep : Bool → SharedOne → In₁ → SharedOne × Out₁)
    (recurrentStep : RecurrentOne → In₁ → RecurrentOne × Out₁)
    (control : OneControl SharedOne PayloadOne RecurrentOne) (input : In₁) :
    deferredOrRecurrentRow? rowOfMember
        (deferredOrRecurrentNoRecv pendingStep recurrentStep control input).1 =
      deferredOrRecurrentRow? rowOfMember control := by
  cases control <;> rfl

/-! ## Semantic trace provenance -/

section Canonical

variable
  (initialOne : OneControl SharedOne PayloadOne RecurrentOne)
  (initialTwo : TwoControl SharedTwo PayloadTwo RecurrentTwo)
  (pendingStepOne : Bool → SharedOne → In₁ → SharedOne × Out₁)
  (recurrentStepOne : RecurrentOne → In₁ → RecurrentOne × Out₁)
  (pendingStepTwo : Bool → SharedTwo → In₂ → SharedTwo × Out₂)
  (recurrentStepTwo : RecurrentTwo → In₂ → RecurrentTwo × Out₂)
  (freshOne : OneControl SharedOne PayloadOne RecurrentOne → In₁ →
    TwoControl SharedTwo PayloadTwo RecurrentTwo → In₂ →
    SharedOne × PayloadOne)
  (freshTwo : TwoControl SharedTwo PayloadTwo RecurrentTwo → In₂ →
    OneControl SharedOne PayloadOne RecurrentOne → In₁ →
    SharedTwo × PayloadTwo)
  (outputOne : OneControl SharedOne PayloadOne RecurrentOne → In₁ →
    TwoControl SharedTwo PayloadTwo RecurrentTwo → In₂ → Out₁)
  (outputTwo : TwoControl SharedTwo PayloadTwo RecurrentTwo → In₂ →
    OneControl SharedOne PayloadOne RecurrentOne → In₁ → Out₂)
  (env : EnvironmentSequence In₁ In₂)

private abbrev canonicalTrace : Nat →
    OneControl SharedOne PayloadOne RecurrentOne ×
      TwoControl SharedTwo PayloadTwo RecurrentTwo :=
  exactClosingSemanticPairTrace initialOne initialTwo
    (deferredOrRecurrentNoRecv pendingStepOne recurrentStepOne)
    (deferredOrRecurrentNoRecv pendingStepTwo recurrentStepTwo)
    (canonicalDeferredOpenRecvOne freshOne outputOne)
    (canonicalDeferredOpenRecvTwo freshTwo outputTwo)
    (canonicalDeferredClose freshOne freshTwo) env

/-- Exact one-round member provenance for all three graph orientations.

On a strict-right round, process one does not receive and retains its old
member, while process two installs a fresh open (`false`) member.  Strict-left
is symmetric.  A simultaneous round installs fresh closed (`true`) members at
both endpoints. -/
theorem canonicalDeferredSemanticPairTrace_succ_members (n : Nat) :
    let current := canonicalTrace initialOne initialTwo pendingStepOne
      recurrentStepOne pendingStepTwo recurrentStepTwo freshOne freshTwo
      outputOne outputTwo env n
    let next := canonicalTrace initialOne initialTwo pendingStepOne
      recurrentStepOne pendingStepTwo recurrentStepTwo freshOne freshTwo
      outputOne outputTwo env (n + 1)
    match (env n).graph with
    | .right =>
        deferredOrRecurrentMember? next.1 =
            deferredOrRecurrentMember? current.1 ∧
          deferredOrRecurrentMember? next.2 = some false
    | .left =>
        deferredOrRecurrentMember? next.1 = some false ∧
          deferredOrRecurrentMember? next.2 =
            deferredOrRecurrentMember? current.2
    | .both =>
        deferredOrRecurrentMember? next.1 = some true ∧
          deferredOrRecurrentMember? next.2 = some true := by
  cases hgraph : (env n).graph <;>
    simp [canonicalTrace, exactClosingSemanticPairTrace, hgraph,
      canonicalDeferredOpenRecvOne, canonicalDeferredOpenRecvTwo,
      canonicalDeferredClose]

/-- Row-valued version.  This is the direct handoff for a concrete current
entry-row selector. -/
theorem canonicalDeferredSemanticPairTrace_succ_rows
    {Row : Type r} (rowOfMember : Bool → Row) (n : Nat) :
    let current := canonicalTrace initialOne initialTwo pendingStepOne
      recurrentStepOne pendingStepTwo recurrentStepTwo freshOne freshTwo
      outputOne outputTwo env n
    let next := canonicalTrace initialOne initialTwo pendingStepOne
      recurrentStepOne pendingStepTwo recurrentStepTwo freshOne freshTwo
      outputOne outputTwo env (n + 1)
    match (env n).graph with
    | .right =>
        deferredOrRecurrentRow? rowOfMember next.1 =
            deferredOrRecurrentRow? rowOfMember current.1 ∧
          deferredOrRecurrentRow? rowOfMember next.2 =
            some (rowOfMember false)
    | .left =>
        deferredOrRecurrentRow? rowOfMember next.1 =
            some (rowOfMember false) ∧
          deferredOrRecurrentRow? rowOfMember next.2 =
            deferredOrRecurrentRow? rowOfMember current.2
    | .both =>
        deferredOrRecurrentRow? rowOfMember next.1 =
            some (rowOfMember true) ∧
          deferredOrRecurrentRow? rowOfMember next.2 =
            some (rowOfMember true) := by
  cases hgraph : (env n).graph <;>
    simp [canonicalTrace, exactClosingSemanticPairTrace, hgraph,
      canonicalDeferredOpenRecvOne,
      canonicalDeferredOpenRecvTwo, canonicalDeferredClose]

end Canonical

/-! ## Transport to the actual acknowledged relay trace -/

/-- Mutual relay selection preserves the observed pending members. -/
theorem pairSelects_deferredOrRecurrentMember?_eq
    (one : FiniteAcknowledgedDelayedCarrier (Fin 5)
      (OneControl SharedOne PayloadOne RecurrentOne))
    (two : FiniteAcknowledgedDelayedCarrier (Fin 5)
      (TwoControl SharedTwo PayloadTwo RecurrentTwo))
    (actualOne : OneControl SharedOne PayloadOne RecurrentOne)
    (actualTwo : TwoControl SharedTwo PayloadTwo RecurrentTwo)
    (hselects : PairSelects one two actualOne actualTwo) :
    deferredOrRecurrentMember? (resolvedControl one two) =
        deferredOrRecurrentMember? actualOne ∧
      deferredOrRecurrentMember? (resolvedControl two one) =
        deferredOrRecurrentMember? actualTwo := by
  exact ⟨congrArg deferredOrRecurrentMember? hselects.1,
    congrArg deferredOrRecurrentMember? hselects.2⟩

/-- Row-valued form of the same selected-control projection. -/
theorem pairSelects_deferredOrRecurrentRow?_eq
    {Row : Type r} (rowOfMember : Bool → Row)
    (one : FiniteAcknowledgedDelayedCarrier (Fin 5)
      (OneControl SharedOne PayloadOne RecurrentOne))
    (two : FiniteAcknowledgedDelayedCarrier (Fin 5)
      (TwoControl SharedTwo PayloadTwo RecurrentTwo))
    (actualOne : OneControl SharedOne PayloadOne RecurrentOne)
    (actualTwo : TwoControl SharedTwo PayloadTwo RecurrentTwo)
    (hselects : PairSelects one two actualOne actualTwo) :
    deferredOrRecurrentRow? rowOfMember (resolvedControl one two) =
        deferredOrRecurrentRow? rowOfMember actualOne ∧
      deferredOrRecurrentRow? rowOfMember (resolvedControl two one) =
        deferredOrRecurrentRow? rowOfMember actualTwo := by
  exact ⟨congrArg (deferredOrRecurrentRow? rowOfMember) hselects.1,
    congrArg (deferredOrRecurrentRow? rowOfMember) hselects.2⟩

section Relay

variable [Fintype SharedOne] [Fintype PayloadOne] [Fintype RecurrentOne]
variable [Fintype SharedTwo] [Fintype PayloadTwo] [Fintype RecurrentTwo]

variable
  (initialOne : OneControl SharedOne PayloadOne RecurrentOne)
  (initialTwo : TwoControl SharedTwo PayloadTwo RecurrentTwo)
  (pendingStepOne : Bool → SharedOne → In₁ → SharedOne × Out₁)
  (recurrentStepOne : RecurrentOne → In₁ → RecurrentOne × Out₁)
  (pendingStepTwo : Bool → SharedTwo → In₂ → SharedTwo × Out₂)
  (recurrentStepTwo : RecurrentTwo → In₂ → RecurrentTwo × Out₂)
  (freshOne : OneControl SharedOne PayloadOne RecurrentOne → In₁ →
    TwoControl SharedTwo PayloadTwo RecurrentTwo → In₂ →
      SharedOne × PayloadOne)
  (freshTwo : TwoControl SharedTwo PayloadTwo RecurrentTwo → In₂ →
    OneControl SharedOne PayloadOne RecurrentOne → In₁ →
      SharedTwo × PayloadTwo)
  (outputOne : OneControl SharedOne PayloadOne RecurrentOne → In₁ →
    TwoControl SharedTwo PayloadTwo RecurrentTwo → In₂ → Out₁)
  (outputTwo : TwoControl SharedTwo PayloadTwo RecurrentTwo → In₂ →
    OneControl SharedOne PayloadOne RecurrentOne → In₁ → Out₂)
  (env : EnvironmentSequence In₁ In₂)

private noncomputable abbrev canonicalRelayController :
    FinitePairedMealyController In₁ In₂ Out₁ Out₂ :=
  exactClosingPairedMealyController initialOne initialTwo
    (deferredOrRecurrentNoRecv pendingStepOne recurrentStepOne)
    (deferredOrRecurrentNoRecv pendingStepTwo recurrentStepTwo)
    (canonicalDeferredOpenRecvOne freshOne outputOne)
    (canonicalDeferredOpenRecvTwo freshTwo outputTwo)
    (canonicalDeferredClose freshOne freshTwo)

/-- Exact member provenance on the *actual acknowledged relay trace*.

The `resolvedControl` calls expose only the member already selected before a
round.  The equations for time `n + 1` then show which fresh member the round
installed.  Thus a concrete entry-row query at time `n` cannot accidentally
use the graph-dependent member created for time `n + 1`. -/
theorem canonicalDeferredRelayTrace_succ_members (n : Nat) :
    let controller := canonicalRelayController initialOne initialTwo
      pendingStepOne recurrentStepOne pendingStepTwo recurrentStepTwo
      freshOne freshTwo outputOne outputTwo
    let current := controller.semanticControlTrace env n
    let next := controller.semanticControlTrace env (n + 1)
    match (env n).graph with
    | .right =>
        deferredOrRecurrentMember? (resolvedControl next.1 next.2) =
            deferredOrRecurrentMember?
              (resolvedControl current.1 current.2) ∧
          deferredOrRecurrentMember? (resolvedControl next.2 next.1) =
            some false
    | .left =>
        deferredOrRecurrentMember? (resolvedControl next.1 next.2) =
            some false ∧
          deferredOrRecurrentMember? (resolvedControl next.2 next.1) =
            deferredOrRecurrentMember?
              (resolvedControl current.2 current.1)
    | .both =>
        deferredOrRecurrentMember? (resolvedControl next.1 next.2) =
            some true ∧
          deferredOrRecurrentMember? (resolvedControl next.2 next.1) =
            some true := by
  let controller := canonicalRelayController initialOne initialTwo
    pendingStepOne recurrentStepOne pendingStepTwo recurrentStepTwo
    freshOne freshTwo outputOne outputTwo
  let semantic := canonicalTrace initialOne initialTwo pendingStepOne
    recurrentStepOne pendingStepTwo recurrentStepTwo freshOne freshTwo
    outputOne outputTwo env
  have hcurrent :=
    exactClosingPairedMealyController_semanticControlTrace_pairSelects
      initialOne initialTwo
      (deferredOrRecurrentNoRecv pendingStepOne recurrentStepOne)
      (deferredOrRecurrentNoRecv pendingStepTwo recurrentStepTwo)
      (canonicalDeferredOpenRecvOne freshOne outputOne)
      (canonicalDeferredOpenRecvTwo freshTwo outputTwo)
      (canonicalDeferredClose freshOne freshTwo) env n
  have hnext :=
    exactClosingPairedMealyController_semanticControlTrace_pairSelects
      initialOne initialTwo
      (deferredOrRecurrentNoRecv pendingStepOne recurrentStepOne)
      (deferredOrRecurrentNoRecv pendingStepTwo recurrentStepTwo)
      (canonicalDeferredOpenRecvOne freshOne outputOne)
      (canonicalDeferredOpenRecvTwo freshTwo outputTwo)
      (canonicalDeferredClose freshOne freshTwo) env (n + 1)
  change PairSelects
    (controller.semanticControlTrace env n).1
    (controller.semanticControlTrace env n).2
    (semantic n).1 (semantic n).2 at hcurrent
  change PairSelects
    (controller.semanticControlTrace env (n + 1)).1
    (controller.semanticControlTrace env (n + 1)).2
    (semantic (n + 1)).1 (semantic (n + 1)).2 at hnext
  have hcurrentMembers :=
    pairSelects_deferredOrRecurrentMember?_eq _ _ _ _ hcurrent
  have hnextMembers :=
    pairSelects_deferredOrRecurrentMember?_eq _ _ _ _ hnext
  dsimp only
  rw [hcurrentMembers.1, hcurrentMembers.2,
    hnextMembers.1, hnextMembers.2]
  exact canonicalDeferredSemanticPairTrace_succ_members initialOne initialTwo
    pendingStepOne recurrentStepOne pendingStepTwo recurrentStepTwo freshOne
    freshTwo outputOne outputTwo env n

/-- Row-valued physical-relay provenance. -/
theorem canonicalDeferredRelayTrace_succ_rows
    {Row : Type r} (rowOfMember : Bool → Row) (n : Nat) :
    let controller := canonicalRelayController initialOne initialTwo
      pendingStepOne recurrentStepOne pendingStepTwo recurrentStepTwo
      freshOne freshTwo outputOne outputTwo
    let current := controller.semanticControlTrace env n
    let next := controller.semanticControlTrace env (n + 1)
    match (env n).graph with
    | .right =>
        deferredOrRecurrentRow? rowOfMember
            (resolvedControl next.1 next.2) =
          deferredOrRecurrentRow? rowOfMember
            (resolvedControl current.1 current.2) ∧
        deferredOrRecurrentRow? rowOfMember
            (resolvedControl next.2 next.1) = some (rowOfMember false)
    | .left =>
        deferredOrRecurrentRow? rowOfMember
            (resolvedControl next.1 next.2) = some (rowOfMember false) ∧
        deferredOrRecurrentRow? rowOfMember
            (resolvedControl next.2 next.1) =
          deferredOrRecurrentRow? rowOfMember
            (resolvedControl current.2 current.1)
    | .both =>
        deferredOrRecurrentRow? rowOfMember
            (resolvedControl next.1 next.2) = some (rowOfMember true) ∧
        deferredOrRecurrentRow? rowOfMember
            (resolvedControl next.2 next.1) = some (rowOfMember true) := by
  let controller := canonicalRelayController initialOne initialTwo
    pendingStepOne recurrentStepOne pendingStepTwo recurrentStepTwo
    freshOne freshTwo outputOne outputTwo
  let semantic := canonicalTrace initialOne initialTwo pendingStepOne
    recurrentStepOne pendingStepTwo recurrentStepTwo freshOne freshTwo
    outputOne outputTwo env
  have hcurrent :=
    exactClosingPairedMealyController_semanticControlTrace_pairSelects
      initialOne initialTwo
      (deferredOrRecurrentNoRecv pendingStepOne recurrentStepOne)
      (deferredOrRecurrentNoRecv pendingStepTwo recurrentStepTwo)
      (canonicalDeferredOpenRecvOne freshOne outputOne)
      (canonicalDeferredOpenRecvTwo freshTwo outputTwo)
      (canonicalDeferredClose freshOne freshTwo) env n
  have hnext :=
    exactClosingPairedMealyController_semanticControlTrace_pairSelects
      initialOne initialTwo
      (deferredOrRecurrentNoRecv pendingStepOne recurrentStepOne)
      (deferredOrRecurrentNoRecv pendingStepTwo recurrentStepTwo)
      (canonicalDeferredOpenRecvOne freshOne outputOne)
      (canonicalDeferredOpenRecvTwo freshTwo outputTwo)
      (canonicalDeferredClose freshOne freshTwo) env (n + 1)
  change PairSelects
    (controller.semanticControlTrace env n).1
    (controller.semanticControlTrace env n).2
    (semantic n).1 (semantic n).2 at hcurrent
  change PairSelects
    (controller.semanticControlTrace env (n + 1)).1
    (controller.semanticControlTrace env (n + 1)).2
    (semantic (n + 1)).1 (semantic (n + 1)).2 at hnext
  have hcurrentRows :=
    pairSelects_deferredOrRecurrentRow?_eq rowOfMember _ _ _ _ hcurrent
  have hnextRows :=
    pairSelects_deferredOrRecurrentRow?_eq rowOfMember _ _ _ _ hnext
  dsimp only
  rw [hcurrentRows.1, hcurrentRows.2, hnextRows.1, hnextRows.2]
  exact canonicalDeferredSemanticPairTrace_succ_rows initialOne initialTwo
    pendingStepOne recurrentStepOne pendingStepTwo recurrentStepTwo freshOne
    freshTwo outputOne outputTwo env rowOfMember n

end Relay

end FiniteAcknowledgedDelayedCarrier

end DistributedSynthesis
