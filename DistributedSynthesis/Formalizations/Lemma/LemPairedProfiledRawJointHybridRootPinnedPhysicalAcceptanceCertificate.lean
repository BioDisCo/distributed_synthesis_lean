/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridRootPinnedPhysicalPriorityBridge
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledOpenAutomaticRecutEpochCoupling
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledOpenOverlayEpochSlice
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointPersistentReversalRecut

/-!
# One certificate for root-pinned physical acceptance

The recurrent-`.both` and persistent strict-reversal regimes choose different
proof-side cuts, but their semantic consumer is identical.  At the chosen
cuts the carrier must expose the guarded state reached by the literal first
child, prove adjacent `AllowedTarget` steps, and identify each physical block
minimum with the corresponding hidden code-lineage priority.

This file packages those fields and records both the state-relative and full
physical acceptance consequences.  It is independent of the concrete front
adapter and does not expose cuts, lineage side, or graph regimes to either
local process.
-/

namespace DistributedSynthesis

universe u v w x y s

namespace DetParityAutomaton

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable
  (A : DetParityAutomaton.{max u v x y, s}
    (RoundRecord In₁ In₂ Graph Out₁ Out₂))

noncomputable section

variable [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁]
  [Inhabited Out₂]
variable [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]

variable
  (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
  (hwin : ∀ env : EnvironmentSequence In₁ In₂,
    A.Accepts (execution strategy env))

/-- Complete proof-side close-cut certificate consumed by root-pinned
physical parity.  Its data is sampled from the actual finite global machine;
no field is part of either local controller. -/
structure ProfiledRawJointHybridRootPinnedPhysicalAcceptanceCertificate
    (first : In₁ × In₂)
    (firstChild : ProfiledRawJointHybridCode A)
    (G : FiniteGlobalRoundMachine.{u, v, w} In₁ In₂)
    (outputOne : G.State → Out₁) (outputTwo : G.State → Out₂)
    (env : EnvironmentSequence In₁ In₂)
    (start : Nat) (cuts : Nat → Nat) where
  cuts_strictMono : StrictMono cuts
  cuts_zero : cuts 0 = 0
  closeState : G.State →
    ProfiledRawJointHybridInitialRootPinnedGuardedState A strategy first
  close_zero :
    closeState (G.globalStateTrace env (start + cuts 0)) =
      (profiledRawJointHybridInitialRootPinnedPolicy A strategy hwin first
        ).policy.run [firstChild]
  close_step : ∀ n,
    ProfiledRawJointHybridInitialRootPinnedAllowedTarget A strategy hwin first
      (closeState (G.globalStateTrace env (start + cuts n)))
      (closeState (G.globalStateTrace env (start + cuts (n + 1))))
  first_control :
    ((profiledRawJointHybridInitialRootPinnedPolicy A strategy hwin first
      ).policy.run [firstChild]).2.2 =
      (profiledRawJointHybridCodeParityDPA A
        (ProfiledRawJointHybridInitialRootPinnedCode A strategy first)).step
          (profiledRawJointHybridCodeParityDPA A
            (ProfiledRawJointHybridInitialRootPinnedCode A strategy first)
            ).initial firstChild
  initialSide : IndexedLineageSide
  offset : Nat
  blockMin_eq_threadPriority : ∀ k : Nat,
    cutBlockMin
        (fun n ↦ A.priority
          (A.run (G.globalMachineTraceWord outputOne outputTwo env)
            (start + n)))
        cuts k =
      (codedAlternatingIndexedLineageCodeThreadSystem
          (ProfiledRawJointHybridInitialRootPinnedCode A strategy first)
          (profiledRawJointHybridCurrentSlots A)
          (profiledRawJointThreadRootPriority A)).priority
        (codedAlternatingIndexedLineageCodeRun
          (ProfiledRawJointHybridInitialRootPinnedCode A strategy first)
          (profiledRawJointHybridCurrentSlots A)
          (profiledRawJointHybridFirstChildCodeWord A firstChild
            (fun n ↦
              (closeState
                (G.globalStateTrace env
                  (start + cuts (n + 1)))).2.1))
          initialSide () (offset + k))

/-! ## The two automatic recurrent cut choices -/

variable [DecidableEq In₁] [DecidableEq In₂]

/-- The exact remaining carrier certificate in the recurrent-`.both` regime,
with the already verified automatic shift and cuts substituted.  Its source
field records whether these are singleton all-common cuts or productive
strict-gap cuts. -/
abbrev ProfiledRawJointHybridRootPinnedRecurrentAcceptanceCertificate
    (first : In₁ × In₂)
    (firstChild : ProfiledRawJointHybridCode A)
    (G : FiniteGlobalRoundMachine.{u, v, w} In₁ In₂)
    (outputOne : G.State → Out₁) (outputTwo : G.State → Out₂)
    (env : EnvironmentSequence In₁ In₂)
    (hboth : GraphBothRecurrent (fun n ↦ (env n).graph)) :=
  ProfiledRawJointHybridRootPinnedPhysicalAcceptanceCertificate A strategy
    hwin first firstChild G outputOne outputTwo env
      (recurrentEnvironmentEpochCutExtraction env hboth).start
      (recurrentEnvironmentEpochCutExtraction env hboth).cuts

/-- The same carrier certificate at the automatic strict-reversal cuts. -/
abbrev ProfiledRawJointHybridRootPinnedStrictReversalAcceptanceCertificate
    (first : In₁ × In₂)
    (firstChild : ProfiledRawJointHybridCode A)
    (G : FiniteGlobalRoundMachine.{u, v, w} In₁ In₂)
    (outputOne : G.State → Out₁) (outputTwo : G.State → Out₂)
    (env : EnvironmentSequence In₁ In₂)
    (hstrict : PersistentStrictReversalTail (fun n ↦ (env n).graph)) :=
  ProfiledRawJointHybridRootPinnedPhysicalAcceptanceCertificate A strategy
    hwin first firstChild G outputOne outputTwo env
      (persistentStrictReversalEpochCutExtraction env hstrict).start
      (persistentStrictReversalEpochCutExtraction env hstrict).cuts

namespace ProfiledRawJointHybridRootPinnedPhysicalAcceptanceCertificate

omit [DecidableEq In₁] [DecidableEq In₂] [Inhabited Out₁] [Inhabited Out₂] in
/-- The certificate first gives acceptance from the actual DPA state after
the discarded finite prefix. -/
theorem acceptsFrom
    {first : In₁ × In₂}
    {firstChild : ProfiledRawJointHybridCode A}
    {G : FiniteGlobalRoundMachine.{u, v, w} In₁ In₂}
    {outputOne : G.State → Out₁} {outputTwo : G.State → Out₂}
    {env : EnvironmentSequence In₁ In₂}
    {start : Nat} {cuts : Nat → Nat}
    (certificate :
      ProfiledRawJointHybridRootPinnedPhysicalAcceptanceCertificate A strategy
        hwin first firstChild G outputOne outputTwo env start cuts) :
    A.AcceptsFrom
      (A.run (G.globalMachineTraceWord outputOne outputTwo env) start)
      (OmegaWord.drop
        (G.globalMachineTraceWord outputOne outputTwo env) start) :=
  finiteGlobalMachine_profiledRawJointHybridInitialRootPinnedPhysicalTail_acceptsFrom_of_closePath
    A strategy hwin first firstChild G outputOne outputTwo env start cuts
      certificate.cuts_strictMono certificate.cuts_zero certificate.closeState
      certificate.close_zero certificate.close_step certificate.first_control
      certificate.initialSide certificate.offset
      certificate.blockMin_eq_threadPriority

omit [DecidableEq In₁] [DecidableEq In₂] [Inhabited Out₁] [Inhabited Out₂] in
/-- Finite-prefix invariance upgrades the state-relative conclusion to
acceptance of the complete actual physical trace. -/
theorem accepts
    {first : In₁ × In₂}
    {firstChild : ProfiledRawJointHybridCode A}
    {G : FiniteGlobalRoundMachine.{u, v, w} In₁ In₂}
    {outputOne : G.State → Out₁} {outputTwo : G.State → Out₂}
    {env : EnvironmentSequence In₁ In₂}
    {start : Nat} {cuts : Nat → Nat}
    (certificate :
      ProfiledRawJointHybridRootPinnedPhysicalAcceptanceCertificate A strategy
        hwin first firstChild G outputOne outputTwo env start cuts) :
    A.Accepts (G.globalMachineTraceWord outputOne outputTwo env) := by
  let word := G.globalMachineTraceWord outputOne outputTwo env
  have htail :
      A.AcceptsFrom (A.run word start) (OmegaWord.drop word start) :=
    acceptsFrom A strategy hwin certificate
  exact (A.acceptsFrom_runFrom_drop_iff A.initial word start).mp
    htail

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- Recurrent automatic-cut specialization. -/
theorem accepts_of_recurrentCertificate
    {first : In₁ × In₂}
    {firstChild : ProfiledRawJointHybridCode A}
    {G : FiniteGlobalRoundMachine.{u, v, w} In₁ In₂}
    {outputOne : G.State → Out₁} {outputTwo : G.State → Out₂}
    {env : EnvironmentSequence In₁ In₂}
    {hboth : GraphBothRecurrent (fun n ↦ (env n).graph)}
    (certificate :
      ProfiledRawJointHybridRootPinnedRecurrentAcceptanceCertificate A strategy
        hwin first firstChild G outputOne outputTwo env hboth) :
    A.Accepts (G.globalMachineTraceWord outputOne outputTwo env) :=
  accepts A strategy hwin certificate

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- Persistent strict-reversal automatic-cut specialization. -/
theorem accepts_of_strictReversalCertificate
    {first : In₁ × In₂}
    {firstChild : ProfiledRawJointHybridCode A}
    {G : FiniteGlobalRoundMachine.{u, v, w} In₁ In₂}
    {outputOne : G.State → Out₁} {outputTwo : G.State → Out₂}
    {env : EnvironmentSequence In₁ In₂}
    {hstrict : PersistentStrictReversalTail (fun n ↦ (env n).graph)}
    (certificate :
      ProfiledRawJointHybridRootPinnedStrictReversalAcceptanceCertificate A
        strategy hwin first firstChild G outputOne outputTwo env hstrict) :
    A.Accepts (G.globalMachineTraceWord outputOne outputTwo env) :=
  accepts A strategy hwin certificate

end ProfiledRawJointHybridRootPinnedPhysicalAcceptanceCertificate

/-! ## Eventually fixed strict tails -/

/-- Semantic certificate for an actual eventually fixed strict-right suffix.
The concrete kernel owes only the actual post-prefix DPA state and literal
tail-word equalities; `PairedRightForeverAccepts` supplies parity. -/
structure ProfiledRawJointHybridRootPinnedFixedRightAcceptanceCertificate
    (G : FiniteGlobalRoundMachine.{u, v, w} In₁ In₂)
    (outputOne : G.State → Out₁) (outputTwo : G.State → Out₂)
    (env : EnvironmentSequence In₁ In₂) (start : Nat) where
  code : A.State × A.State
  lambda : ProcOnePairedRightLambda
    (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)
  row : PairedEntryRow
  inputs : Nat → In₂ × In₁
  forever : PairedRightForeverAccepts A code lambda
  state_eq :
    A.run (G.globalMachineTraceWord outputOne outputTwo env) start =
      pairedCodeStateForRow A row code
  tail_eq :
    OmegaWord.drop (G.globalMachineTraceWord outputOne outputTwo env) start =
      match row with
      | .first =>
          pairedRightOmegaWord lambda.blind lambda.informedLeft inputs
      | .both =>
          pairedRightOmegaWord lambda.blind lambda.informedBoth inputs

/-- Left-oriented mirror. -/
structure ProfiledRawJointHybridRootPinnedFixedLeftAcceptanceCertificate
    (G : FiniteGlobalRoundMachine.{u, v, w} In₁ In₂)
    (outputOne : G.State → Out₁) (outputTwo : G.State → Out₂)
    (env : EnvironmentSequence In₁ In₂) (start : Nat) where
  code : A.State × A.State
  lambda : ProcTwoPairedLeftLambda
    (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)
  row : PairedEntryRow
  inputs : Nat → In₁ × In₂
  forever : PairedLeftForeverAccepts A code lambda
  state_eq :
    A.run (G.globalMachineTraceWord outputOne outputTwo env) start =
      pairedCodeStateForRow A row code
  tail_eq :
    OmegaWord.drop (G.globalMachineTraceWord outputOne outputTwo env) start =
      match row with
      | .first =>
          pairedLeftOmegaWord lambda.blind lambda.informedRight inputs
      | .both =>
          pairedLeftOmegaWord lambda.blind lambda.informedBoth inputs

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁]
    [Fintype In₂] [Fintype Out₁] [Fintype Out₂] [DecidableEq In₁] [DecidableEq In₂] in
/-- A fixed-right certificate closes the complete actual trace by finite
prefix invariance. -/
theorem
    ProfiledRawJointHybridRootPinnedFixedRightAcceptanceCertificate.accepts
    {G : FiniteGlobalRoundMachine.{u, v, w} In₁ In₂}
    {outputOne : G.State → Out₁} {outputTwo : G.State → Out₂}
    {env : EnvironmentSequence In₁ In₂} {start : Nat}
    (certificate :
      ProfiledRawJointHybridRootPinnedFixedRightAcceptanceCertificate A G
        outputOne outputTwo env start) :
    A.Accepts (G.globalMachineTraceWord outputOne outputTwo env) := by
  let word := G.globalMachineTraceWord outputOne outputTwo env
  have htail :
      A.AcceptsFrom (A.run word start) (OmegaWord.drop word start) := by
    rcases certificate with
      ⟨code, lambda, row, inputs, hforever, hstate, hword⟩
    cases row with
    | first =>
        rw [hstate, hword]
        exact hforever.1 inputs
    | both =>
        rw [hstate, hword]
        exact hforever.2 inputs
  exact (A.acceptsFrom_runFrom_drop_iff A.initial word start).mp htail

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁]
    [Fintype In₂] [Fintype Out₁] [Fintype Out₂] [DecidableEq In₁] [DecidableEq In₂] in
/-- Fixed-left mirror. -/
theorem
    ProfiledRawJointHybridRootPinnedFixedLeftAcceptanceCertificate.accepts
    {G : FiniteGlobalRoundMachine.{u, v, w} In₁ In₂}
    {outputOne : G.State → Out₁} {outputTwo : G.State → Out₂}
    {env : EnvironmentSequence In₁ In₂} {start : Nat}
    (certificate :
      ProfiledRawJointHybridRootPinnedFixedLeftAcceptanceCertificate A G
        outputOne outputTwo env start) :
    A.Accepts (G.globalMachineTraceWord outputOne outputTwo env) := by
  let word := G.globalMachineTraceWord outputOne outputTwo env
  have htail :
      A.AcceptsFrom (A.run word start) (OmegaWord.drop word start) := by
    rcases certificate with
      ⟨code, lambda, row, inputs, hforever, hstate, hword⟩
    cases row with
    | first =>
        rw [hstate, hword]
        exact hforever.1 inputs
    | both =>
        rw [hstate, hword]
        exact hforever.2 inputs
  exact (A.acceptsFrom_runFrom_drop_iff A.initial word start).mp htail

end

end DetParityAutomaton

end DistributedSynthesis
