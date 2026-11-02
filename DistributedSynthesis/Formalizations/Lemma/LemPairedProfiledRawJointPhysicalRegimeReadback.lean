/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemFiniteGlobalMachinePhysicalAcceptanceOfAccepts
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledOpenRecurrentEnvironmentRecut
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointPhysicalAcceptanceReadback

/-!
# From graph-regime acceptance to leader-free readback

The concrete carrier proofs naturally establish acceptance separately in the
four exhaustive proof-side graph regimes.  The existing physical package, on
the other hand, asks for an epoch coupling in the recurrent case and explicit
tail parity in the three trapped cases.  This file records the generic bridge
once: conditional acceptance in each regime first gives unconditional
acceptance by the verified graph split, and direct acceptance then fills the
physical package.

At a leader-free kernel this yields
`AllEnvironmentPhysicalAcceptance`, and therefore `ReadbackUpgrade`, in one
arrow.  None of the definitions below is a runtime graph case distinction:
the regimes occur only as hypotheses of the acceptance proof.
-/

namespace DistributedSynthesis

universe u v w x y s i₁ i₂ e₁ e₂ k ro lr rr lo

namespace DetParityAutomaton

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable
  (A : DetParityAutomaton.{max u v x y, s}
    (RoundRecord In₁ In₂ Graph Out₁ Out₂))

/-- An eventually all-common tail is, in particular, recurrently common.
This lets the eventual-common branch reuse the automatic recurrent cut
certificate without changing any local controller. -/
theorem graphBothRecurrent_of_eventuallyAllBoth
    {graphs : Nat → Graph} (hall : EventuallyAllBoth graphs) :
    GraphBothRecurrent graphs := by
  rcases hall with ⟨after, hafter⟩
  intro start
  refine ⟨max start after, Nat.le_max_left start after, ?_⟩
  exact hafter _ (Nat.le_max_right start after)

/-- Acceptance of one finite-global-machine trace, stated separately under
each member of the exhaustive graph-regime split.  This is a proof package;
it contains no graph-dependent controller data. -/
structure FiniteGlobalMachineRegimeAcceptance
    (G : FiniteGlobalRoundMachine.{u, v, w} In₁ In₂)
    (outputOne : G.State → Out₁) (outputTwo : G.State → Out₂)
    (env : EnvironmentSequence In₁ In₂) : Prop where
  recurrent :
    GraphBothRecurrent (fun n ↦ (env n).graph) →
      A.Accepts (G.globalMachineTraceWord outputOne outputTwo env)
  alternating :
    PersistentStrictReversalTail (fun n ↦ (env n).graph) →
      A.Accepts (G.globalMachineTraceWord outputOne outputTwo env)
  strictRight :
    EventuallyStrictRight (fun n ↦ (env n).graph) →
      A.Accepts (G.globalMachineTraceWord outputOne outputTwo env)
  strictLeft :
    EventuallyStrictLeft (fun n ↦ (env n).graph) →
      A.Accepts (G.globalMachineTraceWord outputOne outputTwo env)

/-- Finer carrier-facing form of the recurrent branch.  Recurrent `.both`
behavior is split into an eventually-all-common tail and the case where both
common and strict rounds occur unboundedly often.  These are exactly the two
alternatives produced by `graphBothRecurrent_split`; the remaining three
fields are the trapped strict-reversal and fixed-side regimes.

This split is proof-side only.  In particular, no local process is given an
`EventuallyAllBoth` or `GraphStrictRecurrent` tag. -/
structure FiniteGlobalMachineDetailedRegimeAcceptance
    (G : FiniteGlobalRoundMachine.{u, v, w} In₁ In₂)
    (outputOne : G.State → Out₁) (outputTwo : G.State → Out₂)
    (env : EnvironmentSequence In₁ In₂) : Prop where
  eventuallyCommon :
    EventuallyAllBoth (fun n ↦ (env n).graph) →
      A.Accepts (G.globalMachineTraceWord outputOne outputTwo env)
  recurrentBothWithStrict :
    GraphBothRecurrent (fun n ↦ (env n).graph) →
      GraphStrictRecurrent (fun n ↦ (env n).graph) →
        A.Accepts (G.globalMachineTraceWord outputOne outputTwo env)
  alternating :
    PersistentStrictReversalTail (fun n ↦ (env n).graph) →
      A.Accepts (G.globalMachineTraceWord outputOne outputTwo env)
  strictRight :
    EventuallyStrictRight (fun n ↦ (env n).graph) →
      A.Accepts (G.globalMachineTraceWord outputOne outputTwo env)
  strictLeft :
    EventuallyStrictLeft (fun n ↦ (env n).graph) →
      A.Accepts (G.globalMachineTraceWord outputOne outputTwo env)

/-- The refined common/recurrent split fills the ordinary four-regime
package. -/
def finiteGlobalMachineRegimeAcceptance_of_detailed
    (G : FiniteGlobalRoundMachine.{u, v, w} In₁ In₂)
    (outputOne : G.State → Out₁) (outputTwo : G.State → Out₂)
    (env : EnvironmentSequence In₁ In₂)
    (detailed :
      A.FiniteGlobalMachineDetailedRegimeAcceptance G outputOne outputTwo
        env) :
    A.FiniteGlobalMachineRegimeAcceptance G outputOne outputTwo env where
  recurrent hboth := by
    rcases graphBothRecurrent_split (fun n ↦ (env n).graph) hboth with
      hall | ⟨hstrict, _⟩
    · exact detailed.eventuallyCommon hall
    · exact detailed.recurrentBothWithStrict hboth hstrict
  alternating := detailed.alternating
  strictRight := detailed.strictRight
  strictLeft := detailed.strictLeft

/-- The proof-side graph split turns the four conditional branch proofs into
acceptance of the actual trace. -/
theorem finiteGlobalMachineTraceWord_accepts_of_regimeAcceptance
    (G : FiniteGlobalRoundMachine.{u, v, w} In₁ In₂)
    (outputOne : G.State → Out₁) (outputTwo : G.State → Out₂)
    (env : EnvironmentSequence In₁ In₂)
    (regime :
      A.FiniteGlobalMachineRegimeAcceptance G outputOne outputTwo env) :
    A.Accepts (G.globalMachineTraceWord outputOne outputTwo env) := by
  rcases environment_physical_acceptance_regime env with
    hboth | halternating | hright | hleft
  · exact regime.recurrent hboth
  · exact regime.alternating halternating
  · exact regime.strictRight hright
  · exact regime.strictLeft hleft

/-- Conditional acceptance in the four regimes fills the standard physical
package.  The conversion deliberately goes through actual DPA acceptance, so
the resulting tail fields use the original run and do not restart a checker. -/
noncomputable def finiteGlobalMachinePhysicalAcceptance_of_regimeAcceptance
    (G : FiniteGlobalRoundMachine.{u, v, w} In₁ In₂)
    (outputOne : G.State → Out₁) (outputTwo : G.State → Out₂)
    (env : EnvironmentSequence In₁ In₂)
    (regime :
      A.FiniteGlobalMachineRegimeAcceptance G outputOne outputTwo env) :
    A.FiniteGlobalMachinePhysicalAcceptance G outputOne outputTwo env :=
  A.finiteGlobalMachinePhysicalAcceptance_of_accepts G outputOne outputTwo env
    (A.finiteGlobalMachineTraceWord_accepts_of_regimeAcceptance G outputOne
      outputTwo env regime)

/-- Direct detailed-to-physical wrapper. -/
noncomputable def
    finiteGlobalMachinePhysicalAcceptance_of_detailedRegimeAcceptance
    (G : FiniteGlobalRoundMachine.{u, v, w} In₁ In₂)
    (outputOne : G.State → Out₁) (outputTwo : G.State → Out₂)
    (env : EnvironmentSequence In₁ In₂)
    (detailed :
      A.FiniteGlobalMachineDetailedRegimeAcceptance G outputOne outputTwo
        env) :
    A.FiniteGlobalMachinePhysicalAcceptance G outputOne outputTwo env :=
  A.finiteGlobalMachinePhysicalAcceptance_of_regimeAcceptance G outputOne
    outputTwo env
      (A.finiteGlobalMachineRegimeAcceptance_of_detailed G outputOne outputTwo
        env detailed)

end DetParityAutomaton

namespace ProfiledRawJointLeaderFreeKernel

variable
  {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
  {InitialOne : Type i₁} {InitialTwo : Type i₂}
  {ExceptionalOne : Type e₁} {ExceptionalTwo : Type e₂}
  {ChildCode : Type k}
  {RightOwner : ChildCode → Type ro}
  {LeftReceiver : ChildCode → Type lr}
  {RightReceiver : ChildCode → Type rr}
  {LeftOwner : ChildCode → Type lo}

variable (kernel : ProfiledRawJointLeaderFreeKernel In₁ In₂ Out₁ Out₂
  InitialOne InitialTwo ExceptionalOne ExceptionalTwo ChildCode RightOwner
  LeftReceiver RightReceiver LeftOwner)

variable [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
variable [Fintype InitialOne] [Fintype InitialTwo]
variable [Fintype ExceptionalOne] [Fintype ExceptionalTwo]
variable [Fintype ChildCode]
variable [∀ key, Fintype (RightOwner key)]
variable [∀ key, Fintype (LeftReceiver key)]
variable [∀ key, Fintype (RightReceiver key)]
variable [∀ key, Fintype (LeftOwner key)]

variable
  (A : DetParityAutomaton.{max u v x y, s}
    (RoundRecord In₁ In₂ Graph Out₁ Out₂))

/-- Exact acceptance obligation after the concrete kernel has been built:
prove its actual trace accepting under each of the four proof-side graph
regimes, for every environment. -/
def AllEnvironmentRegimeAcceptance : Prop :=
  ∀ env : EnvironmentSequence In₁ In₂,
    A.FiniteGlobalMachineRegimeAcceptance kernel.globalMachine
      kernel.globalOutputOne kernel.globalOutputTwo env

/-- Carrier-facing all-environment obligation with the recurrent branch
already split into eventual common behavior and genuinely recurring strict
groups. -/
def AllEnvironmentDetailedRegimeAcceptance : Prop :=
  ∀ env : EnvironmentSequence In₁ In₂,
    A.FiniteGlobalMachineDetailedRegimeAcceptance kernel.globalMachine
      kernel.globalOutputOne kernel.globalOutputTwo env

section
omit [Fintype In₁] [Fintype In₂]

/-- The detailed branch package implies the ordinary branch package. -/
theorem allEnvironmentRegimeAcceptance_of_detailed
    (hdetailed : kernel.AllEnvironmentDetailedRegimeAcceptance A) :
    kernel.AllEnvironmentRegimeAcceptance A := by
  intro env
  exact A.finiteGlobalMachineRegimeAcceptance_of_detailed kernel.globalMachine
    kernel.globalOutputOne kernel.globalOutputTwo env (hdetailed env)

/-- Four branchwise acceptance proofs give the existing all-environment
physical package. -/
theorem allEnvironmentPhysicalAcceptance_of_regimeAcceptance
    (hregime : kernel.AllEnvironmentRegimeAcceptance A) :
    kernel.AllEnvironmentPhysicalAcceptance A := by
  intro env
  exact ⟨A.finiteGlobalMachinePhysicalAcceptance_of_regimeAcceptance
    kernel.globalMachine kernel.globalOutputOne kernel.globalOutputTwo env
      (hregime env)⟩

/-- Direct acceptance of every explicit global-machine trace. -/
theorem globalMachine_accepts_of_regimeAcceptance
    (hregime : kernel.AllEnvironmentRegimeAcceptance A) :
    ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts
        (kernel.globalMachine.globalMachineTraceWord kernel.globalOutputOne
          kernel.globalOutputTwo env) := by
  intro env
  exact A.finiteGlobalMachineTraceWord_accepts_of_regimeAcceptance
    kernel.globalMachine kernel.globalOutputOne kernel.globalOutputTwo env
      (hregime env)

/-- Final reusable endpoint: once the four actual-trace branches are proved,
the carrier's fixed finite summary automaton satisfies `ReadbackUpgrade`. -/
theorem summaryAutomaton_readbackUpgrade_of_regimeAcceptance
    (hregime : kernel.AllEnvironmentRegimeAcceptance A) :
    kernel.summaryAutomaton.ReadbackUpgrade A :=
  kernel.summaryAutomaton_readbackUpgrade_of_physicalAcceptance A
    (kernel.allEnvironmentPhysicalAcceptance_of_regimeAcceptance A hregime)

/-- Final endpoint in the five carrier-facing branches: eventual common,
recurrent common with strict groups, persistent strict reversal, and the two
eventually fixed strict sides. -/
theorem summaryAutomaton_readbackUpgrade_of_detailedRegimeAcceptance
    (hdetailed : kernel.AllEnvironmentDetailedRegimeAcceptance A) :
    kernel.summaryAutomaton.ReadbackUpgrade A :=
  kernel.summaryAutomaton_readbackUpgrade_of_regimeAcceptance A
    (kernel.allEnvironmentRegimeAcceptance_of_detailed A hdetailed)

end

end ProfiledRawJointLeaderFreeKernel

end DistributedSynthesis
