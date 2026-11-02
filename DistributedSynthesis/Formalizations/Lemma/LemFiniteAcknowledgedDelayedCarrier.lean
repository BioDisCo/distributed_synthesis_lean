/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemFiniteDelayedBitResolver

/-!
# Finite acknowledged carrier for delayed local receive bits

An identifier alone cannot resolve two overlapping ambiguities.  After a
simultaneous ambiguity `A`, a strict receive may install a fresh ambiguity
`B` at one endpoint while the other endpoint still carries `A`.  On the next
strict reversal, `A` must resolve closed while `B` resolves open.

The finite repair is an acknowledgement relay.  Every carrier contains:

* a known control or an identified two-candidate fork; and
* an optional `(partner fork ID, resolved bit)` acknowledgement.

To resolve its own fork, an endpoint first checks for an equal current ID,
then for a matching acknowledgement delivered by the partner, and otherwise
selects the open branch.  A receive acknowledges the delivered partner fork
and installs a new fork whose ID avoids the two old current IDs and the two
old acknowledgement targets.  Thus `Fin 5` is sufficient.

All maps are finite and endpoint-local.  None accepts a graph, orientation,
leader bit, history, or view.
-/

namespace DistributedSynthesis

universe i u v w x y

/-! ## A canonical color outside four optional forbidden IDs -/

private def delayedRelayForbidden
    (a b c d : Option (Fin 5)) : Finset (Fin 5) :=
  a.toFinset ∪ b.toFinset ∪ c.toFinset ∪ d.toFinset

private theorem delayedRelayForbidden_card_le
    (a b c d : Option (Fin 5)) :
    (delayedRelayForbidden a b c d).card ≤ 4 := by
  have hab := Finset.card_union_le a.toFinset b.toFinset
  have habc := Finset.card_union_le (a.toFinset ∪ b.toFinset) c.toFinset
  have habcd := Finset.card_union_le
    (a.toFinset ∪ b.toFinset ∪ c.toFinset) d.toFinset
  rw [Option.card_toFinset] at hab habc habcd
  cases a <;> cases b <;> cases c <;> cases d <;>
    simp_all [delayedRelayForbidden] <;> omega

private theorem delayedRelayAvailable_nonempty
    (a b c d : Option (Fin 5)) :
    ((Finset.univ : Finset (Fin 5)) \ delayedRelayForbidden a b c d).Nonempty := by
  apply Finset.sdiff_nonempty_of_card_lt_card
  have hcard := delayedRelayForbidden_card_le a b c d
  simpa using (show (delayedRelayForbidden a b c d).card < 5 by omega)

/-- Choose canonically the least of the five colors absent from the four
optional forbidden IDs.  The definition depends only on the forbidden set,
which makes endpoint swapping transparent. -/
def freshDelayedRelayColor
    (a b c d : Option (Fin 5)) : Fin 5 :=
  ((Finset.univ : Finset (Fin 5)) \ delayedRelayForbidden a b c d).min'
    (delayedRelayAvailable_nonempty a b c d)

private theorem freshDelayedRelayColor_not_mem
    (a b c d : Option (Fin 5)) :
    freshDelayedRelayColor a b c d ∉ delayedRelayForbidden a b c d := by
  exact (Finset.mem_sdiff.mp (Finset.min'_mem _ _)).2

private theorem delayedRelayForbidden_pair_comm
    (a b c d : Option (Fin 5)) :
    delayedRelayForbidden a b c d = delayedRelayForbidden b a d c := by
  ext id
  simp only [delayedRelayForbidden, Finset.mem_union, Option.mem_toFinset,
    Option.mem_def]
  tauto

/-- Swapping the two endpoint pairs does not change the selected color. -/
theorem freshDelayedRelayColor_pair_comm
    (a b c d : Option (Fin 5)) :
    freshDelayedRelayColor a b c d =
      freshDelayedRelayColor b a d c := by
  apply le_antisymm
  · apply Finset.min'_le
    rw [← delayedRelayForbidden_pair_comm]
    exact Finset.min'_mem _ _
  · apply Finset.min'_le
    rw [delayedRelayForbidden_pair_comm]
    exact Finset.min'_mem _ _

@[simp] theorem freshDelayedRelayColor_none :
    freshDelayedRelayColor none none none none = 0 := by
  apply (Finset.min'_eq_iff _ _ _).2
  constructor
  · simp [delayedRelayForbidden]
  · intro color _
    exact Fin.zero_le color

/-- The selected color avoids the first forbidden coordinate. -/
theorem freshDelayedRelayColor_ne_first
    (a b c d : Option (Fin 5)) (id : Fin 5) (ha : a = some id) :
    freshDelayedRelayColor a b c d ≠ id := by
  intro heq
  have hnot := freshDelayedRelayColor_not_mem a b c d
  rw [heq] at hnot
  apply hnot
  simp [delayedRelayForbidden, ha]

/-- Avoidance of the second coordinate. -/
theorem freshDelayedRelayColor_ne_second
    (a b c d : Option (Fin 5)) (id : Fin 5) (hb : b = some id) :
    freshDelayedRelayColor a b c d ≠ id := by
  rw [freshDelayedRelayColor_pair_comm]
  exact freshDelayedRelayColor_ne_first b a d c id hb

/-- Avoidance of the third coordinate. -/
theorem freshDelayedRelayColor_ne_third
    (a b c d : Option (Fin 5)) (id : Fin 5) (hc : c = some id) :
    freshDelayedRelayColor a b c d ≠ id := by
  intro heq
  have hnot := freshDelayedRelayColor_not_mem a b c d
  rw [heq] at hnot
  apply hnot
  simp [delayedRelayForbidden, hc]

/-- Avoidance of the fourth coordinate. -/
theorem freshDelayedRelayColor_ne_fourth
    (a b c d : Option (Fin 5)) (id : Fin 5) (hd : d = some id) :
    freshDelayedRelayColor a b c d ≠ id := by
  intro heq
  have hnot := freshDelayedRelayColor_not_mem a b c d
  rw [heq] at hnot
  apply hnot
  simp [delayedRelayForbidden, hd]

/-! ## Finite relay state -/

/-- A resolved control or one identified unresolved two-candidate control. -/
inductive FiniteAcknowledgedDelayedCurrent
    (ForkId : Type i) (Control : Type u) where
  | known (control : Control)
  | fork (id : ForkId) (candidates : FiniteDelayedFork Control)

/-- Local carrier with one acknowledgement about the partner's old fork. -/
structure FiniteAcknowledgedDelayedCarrier
    (ForkId : Type i) (Control : Type u) where
  current : FiniteAcknowledgedDelayedCurrent ForkId Control
  ack : Option (ForkId × Bool)

variable {ForkId : Type i} {Control : Type u}

noncomputable instance [Fintype ForkId] [Fintype Control] :
    Fintype (FiniteAcknowledgedDelayedCurrent ForkId Control) := by
  let encode : FiniteAcknowledgedDelayedCurrent ForkId Control →
      Control ⊕ (ForkId × FiniteDelayedFork Control)
    | .known control => .inl control
    | .fork id candidates => .inr (id, candidates)
  exact Fintype.ofInjective encode (by
    intro left right heq
    cases left <;> cases right <;> cases heq <;> rfl)

noncomputable instance [Fintype ForkId] [Fintype Control] :
    Fintype (FiniteAcknowledgedDelayedCarrier ForkId Control) := by
  let encode : FiniteAcknowledgedDelayedCarrier ForkId Control →
      FiniteAcknowledgedDelayedCurrent ForkId Control ×
        Option (ForkId × Bool) :=
    fun state ↦ (state.current, state.ack)
  exact Fintype.ofInjective encode (by
    intro left right heq
    cases left
    cases right
    cases heq
    rfl)

namespace FiniteAcknowledgedDelayedCarrier

variable {ForkId : Type i} {Control : Type u} {Delivered : Type v}

/-- Current unresolved identifier, if any. -/
def currentId? (state : FiniteAcknowledgedDelayedCarrier ForkId Control) :
    Option ForkId :=
  match state.current with
  | .known _ => none
  | .fork id _ => some id

/-- Identifier named by the stored acknowledgement, if any. -/
def ackId? (state : FiniteAcknowledgedDelayedCarrier ForkId Control) :
    Option ForkId :=
  state.ack.map Prod.fst

@[simp] theorem currentId?_known
    (control : Control) (ack : Option (ForkId × Bool)) :
    currentId? ⟨.known control, ack⟩ = none :=
  rfl

@[simp] theorem currentId?_fork
    (id : ForkId) (candidates : FiniteDelayedFork Control)
    (ack : Option (ForkId × Bool)) :
    currentId? ⟨.fork id candidates, ack⟩ = some id :=
  rfl

@[simp] theorem ackId?_none
    (current : FiniteAcknowledgedDelayedCurrent ForkId Control) :
    ackId? ⟨current, none⟩ = none :=
  rfl

@[simp] theorem ackId?_some
    (current : FiniteAcknowledgedDelayedCurrent ForkId Control)
    (id : ForkId) (bit : Bool) :
    ackId? ⟨current, some (id, bit)⟩ = some id :=
  rfl

/-! ## Local resolution and acknowledgement -/

/-- Resolve the endpoint's own old fork from the delivered relay.

Equal current IDs mean that both forks were installed by the same
simultaneous event.  Otherwise a matching delivered acknowledgement is used;
in every remaining case the fork is the open strict alternative. -/
def resolutionBit [DecidableEq ForkId]
    (own : FiniteAcknowledgedDelayedCarrier ForkId Control)
    (partner : FiniteAcknowledgedDelayedCarrier ForkId Delivered) : Bool :=
  match own.current with
  | .known _ => false
  | .fork ownId _ =>
      if partner.currentId? = some ownId then true
      else
        match partner.ack with
        | some (target, bit) => if target = ownId then bit else false
        | none => false

/-- Select the concrete control before evaluating the current receive
output. -/
def resolvedControl [DecidableEq ForkId]
    (own : FiniteAcknowledgedDelayedCarrier ForkId Control)
    (partner : FiniteAcknowledgedDelayedCarrier ForkId Delivered) : Control :=
  match own.current with
  | .known control => control
  | .fork _ candidates => candidates.candidate (resolutionBit own partner)

/-- The acknowledgement produced for the delivered partner carrier. -/
def acknowledgementFor [DecidableEq ForkId]
    (own : FiniteAcknowledgedDelayedCarrier ForkId Control)
    (partner : FiniteAcknowledgedDelayedCarrier ForkId Delivered) :
    Option (ForkId × Bool) :=
  match partner.current with
  | .known _ => none
  | .fork id _ => some (id, resolutionBit partner own)

@[simp] theorem resolutionBit_known
    [DecidableEq ForkId] (control : Control)
    (ack : Option (ForkId × Bool))
    (partner : FiniteAcknowledgedDelayedCarrier ForkId Delivered) :
    resolutionBit ⟨.known control, ack⟩ partner = false :=
  rfl

@[simp] theorem resolvedControl_known
    [DecidableEq ForkId] (control : Control)
    (ack : Option (ForkId × Bool))
    (partner : FiniteAcknowledgedDelayedCarrier ForkId Delivered) :
    resolvedControl ⟨.known control, ack⟩ partner = control :=
  rfl

@[simp] theorem resolutionBit_same_fork
    [DecidableEq ForkId] (id : ForkId)
    (ownFork : FiniteDelayedFork Control)
    (partnerFork : FiniteDelayedFork Delivered)
    (ownAck partnerAck : Option (ForkId × Bool)) :
    resolutionBit ⟨.fork id ownFork, ownAck⟩
      ⟨.fork id partnerFork, partnerAck⟩ = true := by
  simp [resolutionBit, currentId?]

theorem resolutionBit_of_partner_ack
    [DecidableEq ForkId] {ownId partnerId : ForkId}
    (hne : partnerId ≠ ownId)
    (ownFork : FiniteDelayedFork Control)
    (partnerFork : FiniteDelayedFork Delivered)
    (ownAck : Option (ForkId × Bool)) (bit : Bool) :
    resolutionBit ⟨.fork ownId ownFork, ownAck⟩
      ⟨.fork partnerId partnerFork, some (ownId, bit)⟩ = bit := by
  simp [resolutionBit, currentId?, hne]

@[simp] theorem acknowledgementFor_known
    [DecidableEq ForkId]
    (own : FiniteAcknowledgedDelayedCarrier ForkId Control)
    (control : Delivered) (ack : Option (ForkId × Bool)) :
    acknowledgementFor own ⟨.known control, ack⟩ = none :=
  rfl

@[simp] theorem acknowledgementFor_fork
    [DecidableEq ForkId]
    (own : FiniteAcknowledgedDelayedCarrier ForkId Control)
    (id : ForkId) (candidates : FiniteDelayedFork Delivered)
    (ack : Option (ForkId × Bool)) :
    acknowledgementFor own ⟨.fork id candidates, ack⟩ =
      some (id, resolutionBit ⟨.fork id candidates, ack⟩ own) :=
  rfl

/-! ## Fresh reforking with five colors -/

/-- The common new ID computed at a receive from the two delivered finite
relays. -/
def freshId
    (own : FiniteAcknowledgedDelayedCarrier (Fin 5) Control)
    (partner : FiniteAcknowledgedDelayedCarrier (Fin 5) Delivered) : Fin 5 :=
  freshDelayedRelayColor own.currentId? partner.currentId? own.ackId?
    partner.ackId?

/-- The two endpoints compute the same new ID in opposite local order. -/
theorem freshId_comm
    (own : FiniteAcknowledgedDelayedCarrier (Fin 5) Control)
    (partner : FiniteAcknowledgedDelayedCarrier (Fin 5) Delivered) :
    freshId own partner = freshId partner own :=
  freshDelayedRelayColor_pair_comm own.currentId? partner.currentId?
    own.ackId? partner.ackId?

/-- Install one local half of the new ambiguity and acknowledge the delivered
partner's old fork. -/
def refork {Next : Type y}
    (own : FiniteAcknowledgedDelayedCarrier (Fin 5) Control)
    (partner : FiniteAcknowledgedDelayedCarrier (Fin 5) Delivered)
    (next : FiniteDelayedFork Next) :
    FiniteAcknowledgedDelayedCarrier (Fin 5) Next where
  current := .fork (freshId own partner) next
  ack := acknowledgementFor own partner

@[simp] theorem currentId?_refork
    {Next : Type y}
    (own : FiniteAcknowledgedDelayedCarrier (Fin 5) Control)
    (partner : FiniteAcknowledgedDelayedCarrier (Fin 5) Delivered)
    (next : FiniteDelayedFork Next) :
    (refork own partner next).currentId? = some (freshId own partner) :=
  rfl

@[simp] theorem ack_refork
    {Next : Type y}
    (own : FiniteAcknowledgedDelayedCarrier (Fin 5) Control)
    (partner : FiniteAcknowledgedDelayedCarrier (Fin 5) Delivered)
    (next : FiniteDelayedFork Next) :
    (refork own partner next).ack = acknowledgementFor own partner :=
  rfl

/-- A fresh fork ID differs from the endpoint's old current ID. -/
theorem freshId_ne_own_current
    (id : Fin 5) (candidates : FiniteDelayedFork Control)
    (ack : Option (Fin 5 × Bool))
    (partner : FiniteAcknowledgedDelayedCarrier (Fin 5) Delivered) :
    freshId ⟨.fork id candidates, ack⟩ partner ≠ id := by
  exact freshDelayedRelayColor_ne_first _ _ _ _ id rfl

/-- It also differs from the delivered partner's old current ID. -/
theorem freshId_ne_partner_current
    (own : FiniteAcknowledgedDelayedCarrier (Fin 5) Control)
    (id : Fin 5) (candidates : FiniteDelayedFork Delivered)
    (ack : Option (Fin 5 × Bool)) :
    freshId own ⟨.fork id candidates, ack⟩ ≠ id := by
  exact freshDelayedRelayColor_ne_second _ _ _ _ id rfl

/-- It differs from the endpoint's old acknowledgement target. -/
theorem freshId_ne_own_ack
    (current : FiniteAcknowledgedDelayedCurrent (Fin 5) Control)
    (id : Fin 5) (bit : Bool)
    (partner : FiniteAcknowledgedDelayedCarrier (Fin 5) Delivered) :
    freshId ⟨current, some (id, bit)⟩ partner ≠ id := by
  exact freshDelayedRelayColor_ne_third _ _ _ _ id rfl

/-- It differs from the delivered acknowledgement target. -/
theorem freshId_ne_partner_ack
    (own : FiniteAcknowledgedDelayedCarrier (Fin 5) Control)
    (current : FiniteAcknowledgedDelayedCurrent (Fin 5) Delivered)
    (id : Fin 5) (bit : Bool) :
    freshId own ⟨current, some (id, bit)⟩ ≠ id := by
  exact freshDelayedRelayColor_ne_fourth _ _ _ _ id rfl

/-! ## No-receive and receive/refork maps -/

/-- A no-receive advances both candidates with the generic delayed-fork
table and preserves the acknowledgement.  Its open output is sound whenever
the reachable-fork coherence invariant holds. -/
def noRecvMealy
    (transition : Control → w → Control × x)
    (state : FiniteAcknowledgedDelayedCarrier ForkId Control) (input : w) :
    FiniteAcknowledgedDelayedCarrier ForkId Control × x :=
  match state.current with
  | .known control =>
      let next := transition control input
      (⟨.known next.1, state.ack⟩, next.2)
  | .fork id candidates =>
      let next := candidates.noRecvMealy transition input
      (⟨.fork id next.1, state.ack⟩, next.2)

@[simp] theorem noRecvMealy_ack
    (transition : Control → w → Control × x)
    (state : FiniteAcknowledgedDelayedCarrier ForkId Control) (input : w) :
    (noRecvMealy transition state input).1.ack = state.ack := by
  cases state with
  | mk current ack => cases current <;> rfl

/-- Exact output condition needed while an unresolved fork survives a blind
no-receive step.  It is semantic proof data, not executable state. -/
def NoRecvOutputCoherent
    (transition : Control → w → Control × x)
    (state : FiniteAcknowledgedDelayedCarrier ForkId Control)
    (input : w) : Prop :=
  match state.current with
  | .known _ => True
  | .fork _ candidates =>
      candidates.NoRecvMealyOutputCoherent transition input

/-- Under fork-output coherence, the executable open-branch output is the
output of whichever concrete branch the delivered finite relay selects. -/
theorem noRecvMealy_output_eq_resolvedControl
    [DecidableEq ForkId]
    (transition : Control → w → Control × x)
    (state : FiniteAcknowledgedDelayedCarrier ForkId Control)
    (witness : FiniteAcknowledgedDelayedCarrier ForkId Delivered)
    (input : w)
    (hcoherent : NoRecvOutputCoherent transition state input) :
    (noRecvMealy transition state input).2 =
      (transition (resolvedControl state witness) input).2 := by
  rcases state with ⟨current, ack⟩
  cases current with
  | known control => rfl
  | fork id candidates =>
      exact FiniteDelayedFork.noRecvMealy_output_eq_candidate transition
        candidates input hcoherent
        (resolutionBit ⟨.fork id candidates, ack⟩ witness)

/-- Resolve both old controls before evaluating the current receive, then
install the newly computed fork and acknowledgement. -/
def recvReforkMealy
    (transition : Control → w → Delivered → x → FiniteDelayedFork y × v)
    (own : FiniteAcknowledgedDelayedCarrier (Fin 5) Control)
    (ownInput : w)
    (partner : FiniteAcknowledgedDelayedCarrier (Fin 5) Delivered)
    (deliveredInput : x) :
    FiniteAcknowledgedDelayedCarrier (Fin 5) y × v :=
  let next := transition (resolvedControl own partner) ownInput
    (resolvedControl partner own) deliveredInput
  (refork own partner next.1, next.2)

@[simp] theorem recvReforkMealy_output
    (transition : Control → w → Delivered → x → FiniteDelayedFork y × v)
    (own : FiniteAcknowledgedDelayedCarrier (Fin 5) Control)
    (ownInput : w)
    (partner : FiniteAcknowledgedDelayedCarrier (Fin 5) Delivered)
    (deliveredInput : x) :
    (recvReforkMealy transition own ownInput partner deliveredInput).2 =
      (transition (resolvedControl own partner) ownInput
        (resolvedControl partner own) deliveredInput).2 :=
  rfl

/-! ## The generic mutual-selection invariant -/

/-- The relay `own`, interpreted using exactly the finite metadata delivered
by `witness`, denotes the actual local control. -/
def Selects [DecidableEq ForkId]
    (own : FiniteAcknowledgedDelayedCarrier ForkId Control)
    (witness : FiniteAcknowledgedDelayedCarrier ForkId Delivered)
    (actual : Control) : Prop :=
  resolvedControl own witness = actual

/-- Both actual controls are selected by the two endpoint-local relays. -/
def PairSelects [DecidableEq ForkId]
    (one : FiniteAcknowledgedDelayedCarrier ForkId Control)
    (two : FiniteAcknowledgedDelayedCarrier ForkId Delivered)
    (actualOne : Control) (actualTwo : Delivered) : Prop :=
  Selects one two actualOne ∧ Selects two one actualTwo

@[simp] theorem selects_known
    [DecidableEq ForkId] (control actual : Control)
    (ack : Option (ForkId × Bool))
    (witness : FiniteAcknowledgedDelayedCarrier ForkId Delivered) :
    Selects ⟨.known control, ack⟩ witness actual ↔ control = actual := by
  simp [Selects]

/-- Two freshly installed forks from the same physical event select their
closed branches. -/
theorem resolvedControl_refork_refork_closed
    (one : FiniteAcknowledgedDelayedCarrier (Fin 5) Control)
    (two : FiniteAcknowledgedDelayedCarrier (Fin 5) Delivered)
    (nextOne : FiniteDelayedFork w) (nextTwo : FiniteDelayedFork x) :
    resolvedControl (refork one two nextOne) (refork two one nextTwo) =
      nextOne.closedControl := by
  have hEq : freshId two one = freshId one two := freshId_comm two one
  simp [resolvedControl, refork, resolutionBit, currentId?, hEq]

/-- A freshly installed fork is the open strict branch when read against the
old partner relay.  Avoiding both the partner's current ID and its old
acknowledgement target is essential here. -/
theorem resolvedControl_refork_old_open
    (own : FiniteAcknowledgedDelayedCarrier (Fin 5) Control)
    (partner : FiniteAcknowledgedDelayedCarrier (Fin 5) Delivered)
    (next : FiniteDelayedFork w) :
    resolvedControl (refork own partner next) partner = next.openControl := by
  rcases partner with ⟨current, ack⟩
  cases current with
  | known partnerControl =>
      cases ack with
      | none =>
          simp [refork, resolvedControl, resolutionBit, currentId?]
      | some pair =>
          rcases pair with ⟨target, bit⟩
          have htarget := freshId_ne_partner_ack own
            (.known partnerControl) target bit
          simp [refork, resolvedControl, resolutionBit, currentId?,
            htarget.symm]
  | fork partnerId partnerFork =>
      cases ack with
      | none =>
          have hcurrent := freshId_ne_partner_current own partnerId
            partnerFork none
          simp [refork, resolvedControl, resolutionBit, currentId?,
            hcurrent.symm]
      | some pair =>
          rcases pair with ⟨target, bit⟩
          have hcurrent := freshId_ne_partner_current own partnerId
            partnerFork (some (target, bit))
          have htarget := freshId_ne_partner_ack own
            (.fork partnerId partnerFork) target bit
          simp [refork, resolvedControl, resolutionBit, currentId?,
            hcurrent.symm, htarget.symm]

/-- The acknowledgement installed by a receiver resolves the non-receiving
endpoint's old fork after its branchwise local update. -/
theorem resolvedControl_noRecv_refork
    (transition : Control → w → Control × x)
    (one : FiniteAcknowledgedDelayedCarrier (Fin 5) Control)
    (two : FiniteAcknowledgedDelayedCarrier (Fin 5) Delivered)
    (input : w) (nextTwo : FiniteDelayedFork y) :
    resolvedControl (noRecvMealy transition one input).1
        (refork two one nextTwo) =
      (transition (resolvedControl one two) input).1 := by
  rcases one with ⟨current, ack⟩
  cases current with
  | known control =>
      simp [noRecvMealy, resolvedControl]
  | fork id candidates =>
      have hfresh := freshId_ne_partner_current two id candidates ack
      simp [noRecvMealy, refork, acknowledgementFor, resolvedControl,
        resolutionBit, currentId?, hfresh,
        FiniteDelayedFork.noRecvMealy_candidate,
        FiniteDelayedFork.noRecvMealyTable]

/-- A no-receive changes neither kind of relay identifier, so a fresh fork
still resolves open when read against that advanced carrier. -/
theorem resolvedControl_refork_noRecv_open
    (transition : Delivered → w → Delivered × x)
    (own : FiniteAcknowledgedDelayedCarrier (Fin 5) Control)
    (partner : FiniteAcknowledgedDelayedCarrier (Fin 5) Delivered)
    (input : w) (next : FiniteDelayedFork y) :
    resolvedControl (refork own partner next)
        (noRecvMealy transition partner input).1 = next.openControl := by
  rcases partner with ⟨current, ack⟩
  cases current with
  | known partnerControl =>
      cases ack with
      | none =>
          simp [noRecvMealy, refork, resolvedControl, resolutionBit,
            currentId?]
      | some pair =>
          rcases pair with ⟨target, bit⟩
          have htarget := freshId_ne_partner_ack own
            (.known partnerControl) target bit
          simp [noRecvMealy, refork, resolvedControl, resolutionBit,
            currentId?, htarget.symm]
  | fork partnerId partnerFork =>
      cases ack with
      | none =>
          have hcurrent := freshId_ne_partner_current own partnerId
            partnerFork none
          simp [noRecvMealy, refork, resolvedControl, resolutionBit,
            currentId?, hcurrent.symm]
      | some pair =>
          rcases pair with ⟨target, bit⟩
          have hcurrent := freshId_ne_partner_current own partnerId
            partnerFork (some (target, bit))
          have htarget := freshId_ne_partner_ack own
            (.fork partnerId partnerFork) target bit
          simp [noRecvMealy, refork, resolvedControl, resolutionBit,
            currentId?, hcurrent.symm, htarget.symm]

/-- The mutual-selection invariant holds initially for two known controls. -/
theorem pairSelects_known_known
    [DecidableEq ForkId]
    (one : Control) (two : Delivered)
    (oneAck twoAck : Option (ForkId × Bool)) :
    PairSelects
      (⟨.known one, oneAck⟩ :
        FiniteAcknowledgedDelayedCarrier ForkId Control)
      (⟨.known two, twoAck⟩ :
        FiniteAcknowledgedDelayedCarrier ForkId Delivered)
      one two := by
  simp [PairSelects, Selects]

/-- Proof-side strict-right case.  Endpoint one executes only its graph-blind
no-receive table.  Endpoint two receives, acknowledges endpoint one's old
fork resolution, and installs the open branch of a fresh fork.

This case split is in the semantic preservation proof; neither local map is
given a right/left/leader flag. -/
theorem pairSelects_strictRight
    (transitionOne : Control → w → Control × x)
    (one : FiniteAcknowledgedDelayedCarrier (Fin 5) Control)
    (two : FiniteAcknowledgedDelayedCarrier (Fin 5) Delivered)
    (actualOne : Control) (actualTwo : Delivered)
    (inputOne : w) (nextTwo : FiniteDelayedFork y)
    (hselects : PairSelects one two actualOne actualTwo) :
    PairSelects
      (noRecvMealy transitionOne one inputOne).1
      (refork two one nextTwo)
      (transitionOne actualOne inputOne).1 nextTwo.openControl := by
  rcases hselects with ⟨hone, _htwo⟩
  change resolvedControl one two = actualOne at hone
  constructor
  · change resolvedControl (noRecvMealy transitionOne one inputOne).1
      (refork two one nextTwo) = (transitionOne actualOne inputOne).1
    rw [resolvedControl_noRecv_refork, hone]
  · change resolvedControl (refork two one nextTwo)
      (noRecvMealy transitionOne one inputOne).1 = nextTwo.openControl
    exact resolvedControl_refork_noRecv_open transitionOne two one inputOne
      nextTwo

/-- Proof-side strict-left mirror of `pairSelects_strictRight`. -/
theorem pairSelects_strictLeft
    (transitionTwo : Delivered → w → Delivered × x)
    (one : FiniteAcknowledgedDelayedCarrier (Fin 5) Control)
    (two : FiniteAcknowledgedDelayedCarrier (Fin 5) Delivered)
    (actualOne : Control) (actualTwo : Delivered)
    (inputTwo : w) (nextOne : FiniteDelayedFork y)
    (hselects : PairSelects one two actualOne actualTwo) :
    PairSelects
      (refork one two nextOne)
      (noRecvMealy transitionTwo two inputTwo).1
      nextOne.openControl (transitionTwo actualTwo inputTwo).1 := by
  rcases hselects with ⟨_hone, htwo⟩
  change resolvedControl two one = actualTwo at htwo
  constructor
  · change resolvedControl (refork one two nextOne)
      (noRecvMealy transitionTwo two inputTwo).1 = nextOne.openControl
    exact resolvedControl_refork_noRecv_open transitionTwo one two inputTwo
      nextOne
  · change resolvedControl (noRecvMealy transitionTwo two inputTwo).1
      (refork one two nextOne) = (transitionTwo actualTwo inputTwo).1
    rw [resolvedControl_noRecv_refork, htwo]

/-- Proof-side simultaneous-receive case.  The locally symmetric fresh-ID
calculation makes the two newly installed forks agree, hence both select their
closed branches. -/
theorem pairSelects_both
    (one : FiniteAcknowledgedDelayedCarrier (Fin 5) Control)
    (two : FiniteAcknowledgedDelayedCarrier (Fin 5) Delivered)
    (nextOne : FiniteDelayedFork w) (nextTwo : FiniteDelayedFork x) :
    PairSelects (refork one two nextOne) (refork two one nextTwo)
      nextOne.closedControl nextTwo.closedControl := by
  constructor
  · exact resolvedControl_refork_refork_closed one two nextOne nextTwo
  · exact resolvedControl_refork_refork_closed two one nextTwo nextOne

/-! ## Immediate-reversal regression -/

/-- Kernel-checked form of the dangerous sequence:

`joint A/A` → strict receive installs `B` with `ack(A, closed)` → the
opposite receive resolves stale `A` closed and fresh `B` open, and relays
`ack(B, open)`.

The old acknowledgements may be arbitrary.  Freshness from all four old IDs
is what makes the second, open resolution unconditional. -/
theorem joint_strict_reversal_resolves_old_closed_new_open
    (id : Fin 5)
    (oneFork : FiniteDelayedFork Control)
    (twoFork : FiniteDelayedFork Delivered)
    (nextFork : FiniteDelayedFork Delivered)
    (oneAck twoAck : Option (Fin 5 × Bool)) :
    let one : FiniteAcknowledgedDelayedCarrier (Fin 5) Control :=
      ⟨.fork id oneFork, oneAck⟩
    let two : FiniteAcknowledgedDelayedCarrier (Fin 5) Delivered :=
      ⟨.fork id twoFork, twoAck⟩
    let fresh := refork two one nextFork
    resolutionBit one fresh = true ∧
      resolutionBit fresh one = false ∧
      acknowledgementFor one fresh =
        some (freshId two one, false) := by
  dsimp only
  cases oneAck with
  | none =>
      have hnewNeOld :
          freshId (⟨.fork id twoFork, twoAck⟩ :
              FiniteAcknowledgedDelayedCarrier (Fin 5) Delivered)
            (⟨.fork id oneFork, none⟩ :
              FiniteAcknowledgedDelayedCarrier (Fin 5) Control) ≠ id :=
        freshId_ne_partner_current
          (⟨.fork id twoFork, twoAck⟩ :
            FiniteAcknowledgedDelayedCarrier (Fin 5) Delivered)
          id oneFork none
      have hOldNeNew := hnewNeOld.symm
      simp [refork, resolutionBit, acknowledgementFor, currentId?,
        hnewNeOld, hOldNeNew]
  | some pair =>
      rcases pair with ⟨target, bit⟩
      have hnewNeOld :
          freshId (⟨.fork id twoFork, twoAck⟩ :
              FiniteAcknowledgedDelayedCarrier (Fin 5) Delivered)
            (⟨.fork id oneFork, some (target, bit)⟩ :
              FiniteAcknowledgedDelayedCarrier (Fin 5) Control) ≠ id :=
        freshId_ne_partner_current
          (⟨.fork id twoFork, twoAck⟩ :
            FiniteAcknowledgedDelayedCarrier (Fin 5) Delivered)
          id oneFork (some (target, bit))
      have hnewNeTarget :
          freshId (⟨.fork id twoFork, twoAck⟩ :
              FiniteAcknowledgedDelayedCarrier (Fin 5) Delivered)
            (⟨.fork id oneFork, some (target, bit)⟩ :
              FiniteAcknowledgedDelayedCarrier (Fin 5) Control) ≠ target :=
        freshId_ne_partner_ack
          (⟨.fork id twoFork, twoAck⟩ :
            FiniteAcknowledgedDelayedCarrier (Fin 5) Delivered)
          (.fork id oneFork) target bit
      have hOldNeNew := hnewNeOld.symm
      have hTargetNeNew := hnewNeTarget.symm
      simp [refork, resolutionBit, acknowledgementFor, currentId?,
        hnewNeOld, hOldNeNew, hTargetNeNew]

end FiniteAcknowledgedDelayedCarrier

end DistributedSynthesis
