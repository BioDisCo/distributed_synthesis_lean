/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemFiniteAcknowledgedDelayedCarrier

/-!
# Duplicate-candidate states of the acknowledged relay

After an exact-closing semantic controller reaches a phase in which its open
and closed receive continuations coincide, every receive installs a fork with
two identical candidates.  Such a relay is operationally just one ordinary
control: resolution metadata and acknowledgements can no longer affect it.

This file isolates that generic finite fact.  It is useful for flushing a
single mixed activation fork before re-rooting into an absorbing recurrent
kernel.
-/

namespace DistributedSynthesis

universe i u v w x y

namespace FiniteAcknowledgedDelayedCarrier

variable {ForkId : Type i} {Control : Type u} {Delivered : Type v}

/-- A carrier denotes one literal control independently of all resolution
metadata: it is either known, or its two unresolved candidates are equal to
that same control.  The acknowledgement is intentionally unrestricted. -/
def CarriesDuplicate
    (state : FiniteAcknowledgedDelayedCarrier ForkId Control)
    (control : Control) : Prop :=
  match state.current with
  | .known current => current = control
  | .fork _ candidates =>
      candidates.openControl = control ∧ candidates.closedControl = control

@[simp] theorem carriesDuplicate_known
    (control current : Control) (ack : Option (ForkId × Bool)) :
    CarriesDuplicate
        (⟨.known current, ack⟩ :
          FiniteAcknowledgedDelayedCarrier ForkId Control)
        control ↔
      current = control := by
  rfl

@[simp] theorem carriesDuplicate_fork
    (control : Control) (id : ForkId) (candidates : FiniteDelayedFork Control)
    (ack : Option (ForkId × Bool)) :
    CarriesDuplicate
        (⟨.fork id candidates, ack⟩ :
          FiniteAcknowledgedDelayedCarrier ForkId Control)
        control ↔
      candidates.openControl = control ∧
        candidates.closedControl = control := by
  rfl

/-- A duplicated fork is a duplicate-carrying relay for any old metadata. -/
theorem carriesDuplicate_refork_same
    {Next : Type y}
    (own : FiniteAcknowledgedDelayedCarrier (Fin 5) Control)
    (partner : FiniteAcknowledgedDelayedCarrier (Fin 5) Delivered)
    (control : Next) :
    CarriesDuplicate (refork own partner ⟨control, control⟩) control := by
  exact ⟨rfl, rfl⟩

/-- Resolution of a duplicate carrier is independent of the delivered
partner relay. -/
theorem resolvedControl_eq_of_carriesDuplicate
    [DecidableEq ForkId]
    (state : FiniteAcknowledgedDelayedCarrier ForkId Control)
    (partner : FiniteAcknowledgedDelayedCarrier ForkId Delivered)
    (control : Control) (hduplicate : CarriesDuplicate state control) :
    resolvedControl state partner = control := by
  rcases state with ⟨current, ack⟩
  cases current with
  | known current =>
      simpa [CarriesDuplicate] using hduplicate
  | fork id candidates =>
      rcases hduplicate with ⟨hopen, hclosed⟩
      cases hbit : resolutionBit
          (⟨.fork id candidates, ack⟩ :
            FiniteAcknowledgedDelayedCarrier ForkId Control) partner
      · simpa [resolvedControl, hbit] using hopen
      · simpa [resolvedControl, hbit] using hclosed

/-- Branchwise no-receive evolution of a duplicate carrier is exactly the
ordinary transition of its unique control, both in state and output. -/
theorem carriesDuplicate_noRecvMealy
    (transition : Control → w → Control × x)
    (state : FiniteAcknowledgedDelayedCarrier ForkId Control)
    (control : Control) (input : w)
    (hduplicate : CarriesDuplicate state control) :
    CarriesDuplicate (noRecvMealy transition state input).1
        (transition control input).1 ∧
      (noRecvMealy transition state input).2 =
        (transition control input).2 := by
  rcases state with ⟨current, ack⟩
  cases current with
  | known current =>
      change current = control at hduplicate
      subst current
      exact ⟨rfl, rfl⟩
  | fork id candidates =>
      rcases hduplicate with ⟨hopen, hclosed⟩
      rcases candidates with ⟨openControl, closedControl⟩
      change openControl = control at hopen
      change closedControl = control at hclosed
      subst openControl
      subst closedControl
      exact ⟨⟨rfl, rfl⟩, rfl⟩

/-- If a receive transition returns equal candidates, the acknowledged
receive/refork result carries their common control, regardless of the old
relays. -/
theorem carriesDuplicate_recvReforkMealy
    (transition : Control → w → Delivered → x →
      FiniteDelayedFork y × v)
    (own : FiniteAcknowledgedDelayedCarrier (Fin 5) Control)
    (ownInput : w)
    (partner : FiniteAcknowledgedDelayedCarrier (Fin 5) Delivered)
    (deliveredInput : x)
    (next : y)
    (hnext :
      (transition (resolvedControl own partner) ownInput
          (resolvedControl partner own) deliveredInput).1 = ⟨next, next⟩) :
    CarriesDuplicate
      (recvReforkMealy transition own ownInput partner deliveredInput).1 next :=
  by
  simp only [recvReforkMealy]
  rw [hnext]
  exact carriesDuplicate_refork_same own partner next

/-- A mutually selected semantic pair is enough to identify a diagonal
receive/refork step.  Unlike the persistent duplicate invariant, this lemma
places no restriction on the old relay representation; it is the flushing
step which creates that invariant. -/
theorem carriesDuplicate_recvReforkMealy_of_pairSelects
    (transition : Control → w → Delivered → x →
      FiniteDelayedFork y × v)
    (own : FiniteAcknowledgedDelayedCarrier (Fin 5) Control)
    (ownInput : w)
    (partner : FiniteAcknowledgedDelayedCarrier (Fin 5) Delivered)
    (deliveredInput : x)
    (actualOwn : Control) (actualPartner : Delivered)
    (next : y) (output : v)
    (hselects : PairSelects own partner actualOwn actualPartner)
    (htransition :
      transition actualOwn ownInput actualPartner deliveredInput =
        (⟨next, next⟩, output)) :
    CarriesDuplicate
        (recvReforkMealy transition own ownInput partner deliveredInput).1
        next ∧
      (recvReforkMealy transition own ownInput partner deliveredInput).2 =
        output := by
  rcases hselects with ⟨hone, hpartner⟩
  change resolvedControl own partner = actualOwn at hone
  change resolvedControl partner own = actualPartner at hpartner
  have hdiagonal :
      (transition (resolvedControl own partner) ownInput
          (resolvedControl partner own) deliveredInput).1 = ⟨next, next⟩ := by
    rw [hone, hpartner, htransition]
  constructor
  · exact carriesDuplicate_recvReforkMealy transition own ownInput partner
      deliveredInput next hdiagonal
  · simp only [recvReforkMealy, hone, hpartner, htransition]

end FiniteAcknowledgedDelayedCarrier

end DistributedSynthesis
