/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointUnitFixedPolicyThreadSpliceAcceptance
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointUnitPolicyRecurrentTrace

/-!
# Finite scheduled closes followed by an infinite scheduled tail

Activation selects one fixed policy at its genuine root.  A physical suffix
used for parity may start only after finitely many already completed literal
closes.  This file turns those completed close queries into the finite
`AlternatingPrefix` expected by the state-relative splice theorem, and then
continues with an arbitrary infinite close schedule at its exact endpoint.

Both schedules and their length are proof-side witnesses.  They add no field
to either local controller and expose no leader, graph direction, row, or
history to a process.
-/

namespace DistributedSynthesis

universe u v x y s

namespace DetParityAutomaton

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable
  (A : DetParityAutomaton.{max u v x y, s}
    (RoundRecord In₁ In₂ Graph Out₁ Out₂))

noncomputable section

variable [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁]
  [Inhabited Out₂]
variable [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
variable [DecidableEq In₁] [DecidableEq In₂]

variable (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
variable (initial : ProfiledRawJointOneSidedSemanticState A strategy (I := Unit))
variable (policy : ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
  (initial.code A))
variable (bank : ProfiledRawJointUnitPolicyControllerBank A strategy initial
  policy)

namespace ProfiledRawJointUnitFixedPolicyRoot.AlternatingPrefix

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- Every exact locally checked close extends the finite activation-rooted
lineage by one edge.  This is the basic update used by finite frontier
invariants while the physical row is still ambiguous. -/
theorem Reachable.closeTarget
    {seed current : ProfiledRawJointUnitFixedPolicyRoot A strategy
      (initial.code A) policy}
    (reachable : Reachable A seed current)
    (query : ProfiledRawJointUnitPolicyCloseQuery A strategy initial policy
      current) :
    Reachable A seed
      (query.target A strategy initial policy bank) :=
  reachable.snoc A
    (query.alternatingStep A strategy initial policy bank)

/-- The first `n` exact queries of a close schedule form a finite alternating
chain from its seed to its `n`-th scheduled root. -/
noncomputable def ofCloseSchedule
    (seed : ProfiledRawJointUnitFixedPolicyRoot A strategy (initial.code A)
      policy)
    (schedule : ProfiledRawJointUnitPolicyCloseSchedule A strategy initial
      policy) : ∀ n : Nat,
    AlternatingPrefix A policy seed
      (profiledRawJointUnitPolicyScheduledRoot A strategy initial policy bank
        seed schedule n)
  | 0 => .refl
  | n + 1 =>
      (ofCloseSchedule seed schedule n).snoc
        ((schedule n
          (profiledRawJointUnitPolicyScheduledRoot A strategy initial policy
            bank seed schedule n)).alternatingStep A strategy initial policy
              bank)

section
omit [Inhabited Out₁] [Inhabited Out₂]

@[simp] theorem ofCloseSchedule_zero
    (seed : ProfiledRawJointUnitFixedPolicyRoot A strategy (initial.code A)
      policy)
    (schedule : ProfiledRawJointUnitPolicyCloseSchedule A strategy initial
      policy) :
    ofCloseSchedule A strategy initial policy bank seed schedule 0 =
      .refl :=
  rfl

@[simp] theorem ofCloseSchedule_succ
    (seed : ProfiledRawJointUnitFixedPolicyRoot A strategy (initial.code A)
      policy)
    (schedule : ProfiledRawJointUnitPolicyCloseSchedule A strategy initial
      policy) (n : Nat) :
    ofCloseSchedule A strategy initial policy bank seed schedule (n + 1) =
      (ofCloseSchedule A strategy initial policy bank seed schedule n).snoc
        ((schedule n
          (profiledRawJointUnitPolicyScheduledRoot A strategy initial policy
            bank seed schedule n)).alternatingStep A strategy initial policy
              bank) :=
  rfl

/-- The scheduled-prefix length is literally the number of completed close
queries. -/
@[simp] theorem ofCloseSchedule_length
    (seed : ProfiledRawJointUnitFixedPolicyRoot A strategy (initial.code A)
      policy)
    (schedule : ProfiledRawJointUnitPolicyCloseSchedule A strategy initial
      policy) (n : Nat) :
    (ofCloseSchedule A strategy initial policy bank seed schedule n).length =
      n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [ofCloseSchedule, ih]

/-- A finite activation-rooted schedule followed by an infinite schedule at
its endpoint closes state-relative physical acceptance in one application.
The actual checker starts at `physicalState`; it is never reset to a macro's
counterfactual row coordinate. -/
theorem physicalTail_acceptsFrom_of_closeSchedules
    (seed : ProfiledRawJointUnitFixedPolicyRoot A strategy (initial.code A)
      policy)
    (hseed : ProfiledRawJointUnitFixedPolicyRoot.state A policy seed =
      policy.run [])
    (pastSchedule : ProfiledRawJointUnitPolicyCloseSchedule A strategy initial
      policy)
    (completed : Nat)
    (futureSchedule : ProfiledRawJointUnitPolicyCloseSchedule A strategy
      initial policy)
    (physicalState : A.State)
    (physicalTail : OmegaWord (RoundRecord In₁ In₂ Graph Out₁ Out₂))
    (cuts : Nat → Nat) (cuts_strictMono : StrictMono cuts)
    (cuts_zero : cuts 0 = 0)
    (blockMin_eq_futureRootPriority : ∀ k : Nat,
      cutBlockMin
          (fun n ↦ A.priority (A.runFrom physicalState physicalTail n))
          cuts k =
        profiledRawJointThreadRootPriority A
          (ProfiledRawJointUnitFixedPolicyRoot.threadRoot A policy
            (profiledRawJointUnitPolicyScheduledRoot A strategy initial policy
              bank
              (profiledRawJointUnitPolicyScheduledRoot A strategy initial
                policy bank seed pastSchedule completed)
              futureSchedule (k + 1)))) :
    A.AcceptsFrom physicalState physicalTail := by
  let current := profiledRawJointUnitPolicyScheduledRoot A strategy initial
    policy bank seed pastSchedule completed
  let chain := ofCloseSchedule A strategy initial policy bank seed pastSchedule
    completed
  let future := profiledRawJointUnitPolicyScheduledRoot A strategy initial
    policy bank current futureSchedule
  have hfutureStep : ∀ n : Nat,
      ProfiledRawJointUnitFixedPolicyRoot.AlternatingStep A policy
        (future n) (future (n + 1)) := by
    intro n
    simpa [future] using
      (futureSchedule n
        (profiledRawJointUnitPolicyScheduledRoot A strategy initial policy bank
          current futureSchedule n)).alternatingStep A strategy initial policy
            bank
  exact chain.physicalTail_acceptsFrom_of_futureRootPriority A hseed future
    rfl hfutureStep physicalState physicalTail cuts cuts_strictMono cuts_zero
      blockMin_eq_futureRootPriority

end

end ProfiledRawJointUnitFixedPolicyRoot.AlternatingPrefix

end

end DetParityAutomaton

end DistributedSynthesis
