/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleSuccessorRootHandoff
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleSuccessorWholeTraceBookkeeping
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleSuccessorLiteralPrefixResolvedCut

/-!
# From the checked root handoff to a whole-trace witness

The concrete controller proof has two parts: the exceptional common-root
handoff and the recurrent packet invariant after that handoff.  This file
checks that those are exactly the fields of the existing whole-trace
interface.  In particular the finite machine, output tables, start, and cuts
are shared literally; no suffix controller or physical word is substituted.

Sides and selected targets below are proof-side witnesses at actual cuts.
They are not controller inputs and disclose no graph orientation or leader
bit to either endpoint.
-/

namespace DistributedSynthesis

universe u v x y s w

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

variable
  (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
  (hwin : ∀ env : EnvironmentSequence In₁ In₂,
    A.Accepts (execution strategy env))

private abbrev CompatiblePolicy
    (initial : ProfiledRawJointCommonBaseWorld A strategy) :=
  ProfiledRawJointHybridPhysicalCompatibleRationalPolicy A strategy hwin
    initial

private abbrev CompatibleState
    (initial : ProfiledRawJointCommonBaseWorld A strategy) :=
  ProfiledRawJointHybridPhysicalCompatiblePolicyState A strategy hwin initial

variable {initial : ProfiledRawJointCommonBaseWorld A strategy}
variable {policy : CompatiblePolicy A strategy hwin initial}
variable {G : FiniteGlobalRoundMachine.{u, v, w} In₁ In₂}
variable {outputOne : G.State → Out₁} {outputTwo : G.State → Out₂}
variable {env : EnvironmentSequence In₁ In₂}

/-- A common-root handoff and one resolved packet at every later cut are a
whole-trace witness for the very same finite machine and physical word. -/
noncomputable def
    ProfiledRawJointHybridPhysicalCompatibleSuccessorRootHandoffAt.toWholeTraceCutWitness
    (handoff :
      ProfiledRawJointHybridPhysicalCompatibleSuccessorRootHandoffAt A
        strategy hwin policy G outputOne outputTwo env)
    (cuts_strictMono : StrictMono handoff.cuts)
    (cuts_zero : handoff.cuts 0 = 0)
    (later : Nat → CompatibleState A strategy hwin initial)
    (transition : ∀ n : Nat,
      ProfiledRawJointHybridPhysicalCompatibleResolvedTransitionPacketAt A
        strategy hwin policy G outputOne outputTwo env
          (handoff.toInitialExit A strategy hwin).initialSide
          ((handoff.toInitialExit A strategy hwin).state A strategy hwin later)
          handoff.start handoff.cuts n) :
    ProfiledRawJointHybridPhysicalCompatibleWholeTraceCutWitness A strategy
      hwin policy G outputOne outputTwo env where
  start := handoff.start
  cuts := handoff.cuts
  cuts_strictMono := cuts_strictMono
  cuts_zero := cuts_zero
  later := later
  exit := handoff.toInitialExit A strategy hwin
  transition := transition

/-- The recurrent induction may start strictly after the exceptional root
cut.  A checked packet at index `0`, together with packets at every successor
index, is therefore enough to construct the same whole-trace witness.

This is the exact consumption shape of `...RootPhaseCutOne`: the root/first-
phase seam supplies `zero`, while the phase-live invariant supplies
`successor`. -/
noncomputable def
    ProfiledRawJointHybridPhysicalCompatibleSuccessorRootHandoffAt.toWholeTraceCutWitness_of_zero_and_successors
    (handoff :
      ProfiledRawJointHybridPhysicalCompatibleSuccessorRootHandoffAt A
        strategy hwin policy G outputOne outputTwo env)
    (cuts_strictMono : StrictMono handoff.cuts)
    (cuts_zero : handoff.cuts 0 = 0)
    (later : Nat → CompatibleState A strategy hwin initial)
    (zero : Nonempty
      (ProfiledRawJointHybridPhysicalCompatibleResolvedTransitionPacketAt A
        strategy hwin policy G outputOne outputTwo env
          (handoff.toInitialExit A strategy hwin).initialSide
          ((handoff.toInitialExit A strategy hwin).state A strategy hwin later)
          handoff.start handoff.cuts 0))
    (successor : ∀ n : Nat,
      ProfiledRawJointHybridPhysicalCompatibleResolvedTransitionPacketAt A
        strategy hwin policy G outputOne outputTwo env
          (handoff.toInitialExit A strategy hwin).initialSide
          ((handoff.toInitialExit A strategy hwin).state A strategy hwin later)
          handoff.start handoff.cuts (n + 1)) :
    ProfiledRawJointHybridPhysicalCompatibleWholeTraceCutWitness A strategy
      hwin policy G outputOne outputTwo env :=
  handoff.toWholeTraceCutWitness A strategy hwin cuts_strictMono cuts_zero later
    (fun n ↦ match n with
      | 0 => Classical.choice zero
      | k + 1 => successor k)

/-- Consequently the same data already produce the resolved member stream
consumed by the acceptance and main-theorem layers. -/
noncomputable def
    ProfiledRawJointHybridPhysicalCompatibleSuccessorRootHandoffAt.toResolvedMemberStream
    (handoff :
      ProfiledRawJointHybridPhysicalCompatibleSuccessorRootHandoffAt A
        strategy hwin policy G outputOne outputTwo env)
    (cuts_strictMono : StrictMono handoff.cuts)
    (cuts_zero : handoff.cuts 0 = 0)
    (later : Nat → CompatibleState A strategy hwin initial)
    (transition : ∀ n : Nat,
      ProfiledRawJointHybridPhysicalCompatibleResolvedTransitionPacketAt A
        strategy hwin policy G outputOne outputTwo env
          (handoff.toInitialExit A strategy hwin).initialSide
          ((handoff.toInitialExit A strategy hwin).state A strategy hwin later)
          handoff.start handoff.cuts n) :
    ProfiledRawJointHybridPhysicalCompatibleResolvedMemberStream A strategy
      hwin policy G outputOne outputTwo env :=
  (handoff.toWholeTraceCutWitness A strategy hwin cuts_strictMono cuts_zero
    later transition).toResolvedMemberStream A strategy hwin

/-- Resolved-stream form of the base/successor split above. -/
noncomputable def
    ProfiledRawJointHybridPhysicalCompatibleSuccessorRootHandoffAt.toResolvedMemberStream_of_zero_and_successors
    (handoff :
      ProfiledRawJointHybridPhysicalCompatibleSuccessorRootHandoffAt A
        strategy hwin policy G outputOne outputTwo env)
    (cuts_strictMono : StrictMono handoff.cuts)
    (cuts_zero : handoff.cuts 0 = 0)
    (later : Nat → CompatibleState A strategy hwin initial)
    (zero : Nonempty
      (ProfiledRawJointHybridPhysicalCompatibleResolvedTransitionPacketAt A
        strategy hwin policy G outputOne outputTwo env
          (handoff.toInitialExit A strategy hwin).initialSide
          ((handoff.toInitialExit A strategy hwin).state A strategy hwin later)
          handoff.start handoff.cuts 0))
    (successor : ∀ n : Nat,
      ProfiledRawJointHybridPhysicalCompatibleResolvedTransitionPacketAt A
        strategy hwin policy G outputOne outputTwo env
          (handoff.toInitialExit A strategy hwin).initialSide
          ((handoff.toInitialExit A strategy hwin).state A strategy hwin later)
          handoff.start handoff.cuts (n + 1)) :
    ProfiledRawJointHybridPhysicalCompatibleResolvedMemberStream A strategy
      hwin policy G outputOne outputTwo env :=
  (handoff.toWholeTraceCutWitness_of_zero_and_successors A strategy hwin
    cuts_strictMono cuts_zero later zero successor).toResolvedMemberStream A
      strategy hwin

/-- Orientation-free literal successor cuts discharge the successor half of
the whole-trace interface directly.  The exceptional packet at index `0` is
kept separate because it is supplied by the checked root/phase seam; every
packet at index `n + 1` is an ordinary right-or-left literal successor cut. -/
noncomputable def
    ProfiledRawJointHybridPhysicalCompatibleSuccessorRootHandoffAt.toWholeTraceCutWitness_of_zero_and_literalSuccessors
    (handoff :
      ProfiledRawJointHybridPhysicalCompatibleSuccessorRootHandoffAt A
        strategy hwin policy G outputOne outputTwo env)
    (cuts_strictMono : StrictMono handoff.cuts)
    (cuts_zero : handoff.cuts 0 = 0)
    (later : Nat → CompatibleState A strategy hwin initial)
    (schedule : OperationalCloseMemberSchedule
      (fun j ↦
        ((OmegaWord.drop
          (G.globalMachineTraceWord outputOne outputTwo env) handoff.start) j
          ).graph))
    (zero : Nonempty
      (ProfiledRawJointHybridPhysicalCompatibleResolvedTransitionPacketAt A
        strategy hwin policy G outputOne outputTwo env
          (handoff.toInitialExit A strategy hwin).initialSide
          ((handoff.toInitialExit A strategy hwin).state A strategy hwin later)
          handoff.start handoff.cuts 0))
    (successor : ∀ n : Nat,
      ProfiledRawJointHybridPhysicalCompatibleLiteralSuccessorCutAt A strategy
        hwin policy G outputOne outputTwo env
          (handoff.toInitialExit A strategy hwin).initialSide
          ((handoff.toInitialExit A strategy hwin).state A strategy hwin later)
          handoff.start handoff.cuts schedule (n + 1)) :
    ProfiledRawJointHybridPhysicalCompatibleWholeTraceCutWitness A strategy
      hwin policy G outputOne outputTwo env :=
  handoff.toWholeTraceCutWitness_of_zero_and_successors A strategy hwin
    cuts_strictMono cuts_zero later zero
      (fun n ↦ (successor n).toResolvedTransitionPacketAt A strategy hwin)

/-- Resolved-stream form of
`toWholeTraceCutWitness_of_zero_and_literalSuccessors`. -/
noncomputable def
    ProfiledRawJointHybridPhysicalCompatibleSuccessorRootHandoffAt.toResolvedMemberStream_of_zero_and_literalSuccessors
    (handoff :
      ProfiledRawJointHybridPhysicalCompatibleSuccessorRootHandoffAt A
        strategy hwin policy G outputOne outputTwo env)
    (cuts_strictMono : StrictMono handoff.cuts)
    (cuts_zero : handoff.cuts 0 = 0)
    (later : Nat → CompatibleState A strategy hwin initial)
    (schedule : OperationalCloseMemberSchedule
      (fun j ↦
        ((OmegaWord.drop
          (G.globalMachineTraceWord outputOne outputTwo env) handoff.start) j
          ).graph))
    (zero : Nonempty
      (ProfiledRawJointHybridPhysicalCompatibleResolvedTransitionPacketAt A
        strategy hwin policy G outputOne outputTwo env
          (handoff.toInitialExit A strategy hwin).initialSide
          ((handoff.toInitialExit A strategy hwin).state A strategy hwin later)
          handoff.start handoff.cuts 0))
    (successor : ∀ n : Nat,
      ProfiledRawJointHybridPhysicalCompatibleLiteralSuccessorCutAt A strategy
        hwin policy G outputOne outputTwo env
          (handoff.toInitialExit A strategy hwin).initialSide
          ((handoff.toInitialExit A strategy hwin).state A strategy hwin later)
          handoff.start handoff.cuts schedule (n + 1)) :
    ProfiledRawJointHybridPhysicalCompatibleResolvedMemberStream A strategy
      hwin policy G outputOne outputTwo env :=
  (handoff.toWholeTraceCutWitness_of_zero_and_literalSuccessors A strategy hwin
    cuts_strictMono cuts_zero later schedule zero successor
    ).toResolvedMemberStream A strategy hwin

end

end DetParityAutomaton

end DistributedSynthesis
