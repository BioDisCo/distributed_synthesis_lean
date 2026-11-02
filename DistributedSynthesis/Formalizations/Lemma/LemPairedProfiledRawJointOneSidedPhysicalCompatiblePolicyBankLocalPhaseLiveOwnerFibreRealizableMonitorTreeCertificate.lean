/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointOneSidedPhysicalCompatiblePolicyBankLocalPhaseLiveOwnerFibreRealizableMonitor
import DistributedSynthesis.Formalizations.Theorem.ThmInputFreeRationalRun

/-!
# Regular-tree certificate for the exact owner-fibre monitor

The realizable monitor has already removed the spurious-walk problem: each of
its paths is an actual environment execution.  This file records the exact
interface required from the enriched parity-tree regularization.  A finite
monitor edge is mapped to one direction of one accepting rational tree, and
the map preserves priorities.  Consequently every monitor path is an
accepting branch of that tree.

The encoding and its edge witnesses are proof-side data.  They do not add the
graph, the other process's input, an orientation, or a semantic history to an
endpoint controller.
-/

namespace DistributedSynthesis

universe u v x y s t

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

private abbrev OneControl :=
  ProfiledRawJointRecurrentOwnerFibreBoundaryOneControl A strategy hwin

private abbrev TwoControl :=
  ProfiledRawJointRecurrentOwnerFibreBoundaryTwoControl A strategy hwin

/-- A regular-tree direction records the physical graph of the current edge
and the unrestricted input pair stored at its target vertex. -/
abbrev ProfiledRawJointRecurrentOwnerFibreRealizableMonitorDirection :=
  Graph × (In₁ × In₂)

/-- Proof-side embedding of one exact finite monitor into an accepting
rational tree.  Edge preservation is required for every literal monitor
edge, including rollback edges. -/
structure
    ProfiledRawJointRecurrentOwnerFibreRealizableMonitorTreeCertificate
    (initialOne : OneControl A strategy hwin)
    (initialTwo : TwoControl A strategy hwin)
    (hinitial :
      ProfiledRawJointRecurrentOwnerFibreBoundaryOperational A strategy hwin
        initialOne initialTwo)
    (initialInput : In₁ × In₂)
    (T : InputFreeRunParityTreeAutomaton.{max u v, t}
      (ProfiledRawJointRecurrentOwnerFibreRealizableMonitorDirection
        (In₁ := In₁) (In₂ := In₂)))
    (policy : T.RationalTransitionPolicy) where
  encode :
    ProfiledRawJointRecurrentOwnerFibreRealizableMonitorState A strategy hwin
        initialOne initialTwo hinitial initialInput →
      T.State
  initial :
    encode
        (profiledRawJointRecurrentOwnerFibreRealizableMonitorInitial A strategy
          hwin initialOne initialTwo hinitial initialInput) =
      policy.run []
  edge :
    ∀ (source target :
        ProfiledRawJointRecurrentOwnerFibreRealizableMonitorState A strategy
          hwin initialOne initialTwo hinitial initialInput)
      (hedge :
        (source, target) ∈
          profiledRawJointRecurrentOwnerFibreRealizableMonitorEdges A strategy
            hwin initialOne initialTwo hinitial initialInput),
      encode target =
        policy.successor (encode source)
          (profiledRawJointRecurrentOwnerFibreRealizableMonitorEdgeGraph A
              strategy hwin initialOne initialTwo hinitial initialInput source
                target hedge,
            target.2.1)
  priority :
    let D :=
      sourceFreeBeliefParentLinkedCodeParityDPA
        (Annotation := ProfiledRawJointHybridPhysicalEdgeAnnotation A)
        (profiledRawJointOneSidedCodeParityDPA A
          (profiledRawJointRecurrentOwnerFibreBoundaryActiveParent A strategy
            hwin initialOne initialTwo hinitial initialInput).1.1.1)
    ∀ state,
      T.priority (encode state) = D.priority state.2.2

namespace ProfiledRawJointRecurrentOwnerFibreRealizableMonitorTreeCertificate

variable
  {initialOne : OneControl A strategy hwin}
  {initialTwo : TwoControl A strategy hwin}
  {hinitial :
    ProfiledRawJointRecurrentOwnerFibreBoundaryOperational A strategy hwin
      initialOne initialTwo}
  {initialInput : In₁ × In₂}
  {T : InputFreeRunParityTreeAutomaton.{max u v, t}
    (ProfiledRawJointRecurrentOwnerFibreRealizableMonitorDirection
      (In₁ := In₁) (In₂ := In₂))}
  {policy : T.RationalTransitionPolicy}

/-- The encoded states of a monitor walk are the states of the rational run
along the branch formed by its edge directions. -/
theorem path_eq_run
    (certificate :
      ProfiledRawJointRecurrentOwnerFibreRealizableMonitorTreeCertificate A
        strategy hwin initialOne initialTwo hinitial initialInput T policy)
    (walk : Nat →
      ProfiledRawJointRecurrentOwnerFibreRealizableMonitorState A strategy hwin
        initialOne initialTwo hinitial initialInput)
    (hzero :
      walk 0 =
        profiledRawJointRecurrentOwnerFibreRealizableMonitorInitial A strategy
          hwin initialOne initialTwo hinitial initialInput)
    (hedges : ∀ n : Nat,
      (walk n, walk (n + 1)) ∈
        profiledRawJointRecurrentOwnerFibreRealizableMonitorEdges A strategy
          hwin initialOne initialTwo hinitial initialInput) :
    let branch : Nat →
        ProfiledRawJointRecurrentOwnerFibreRealizableMonitorDirection
          (In₁ := In₁) (In₂ := In₂) :=
      fun n ↦
        (profiledRawJointRecurrentOwnerFibreRealizableMonitorEdgeGraph A
            strategy hwin initialOne initialTwo hinitial initialInput (walk n)
              (walk (n + 1)) (hedges n),
          (walk (n + 1)).2.1)
    ∀ n : Nat,
      certificate.encode (walk n) = policy.run (branchNode branch n) := by
  dsimp only
  let branch : Nat →
      ProfiledRawJointRecurrentOwnerFibreRealizableMonitorDirection
        (In₁ := In₁) (In₂ := In₂) :=
    fun n ↦
      (profiledRawJointRecurrentOwnerFibreRealizableMonitorEdgeGraph A strategy
          hwin initialOne initialTwo hinitial initialInput (walk n)
            (walk (n + 1)) (hedges n),
        (walk (n + 1)).2.1)
  intro n
  induction n with
  | zero =>
      rw [hzero]
      exact certificate.initial
  | succ n ih =>
      rw [certificate.edge (walk n) (walk (n + 1)) (hedges n), ih]
      exact policy.successor_at (branchNode branch n) (branch n)

/-- An accepting rational-tree embedding proves parity acceptance of the
entire exact realizable monitor. -/
theorem monitorAccepting
    (certificate :
      ProfiledRawJointRecurrentOwnerFibreRealizableMonitorTreeCertificate A
        strategy hwin initialOne initialTwo hinitial initialInput T policy) :
    ProfiledRawJointRecurrentOwnerFibreRealizableMonitorAccepting A strategy
      hwin initialOne initialTwo hinitial initialInput := by
  intro walk hzero hedges
  let branch : Nat →
      ProfiledRawJointRecurrentOwnerFibreRealizableMonitorDirection
        (In₁ := In₁) (In₂ := In₂) :=
    fun n ↦
      (profiledRawJointRecurrentOwnerFibreRealizableMonitorEdgeGraph A strategy
          hwin initialOne initialTwo hinitial initialInput (walk n)
            (walk (n + 1)) (hedges n),
        (walk (n + 1)).2.1)
  have hpath : ∀ n : Nat,
      certificate.encode (walk n) = policy.run (branchNode branch n) :=
    certificate.path_eq_run A strategy hwin walk hzero hedges
  obtain ⟨p, hpEven, hpInf, hpMin⟩ := policy.accepts.2 branch
  refine ⟨p, hpEven, ?_, ?_⟩
  · intro n
    obtain ⟨k, hnk, hk⟩ := hpInf n
    refine ⟨k, hnk, ?_⟩
    rw [← certificate.priority (walk k), hpath k]
    exact hk
  · intro q hq
    apply hpMin q
    intro n
    obtain ⟨k, hnk, hk⟩ := hq n
    refine ⟨k, hnk, ?_⟩
    change T.priority (policy.run (branchNode branch k)) = q
    rw [← hpath k, certificate.priority (walk k)]
    exact hk

end ProfiledRawJointRecurrentOwnerFibreRealizableMonitorTreeCertificate

/-- Exact remaining regularization target for an entry: every first input has
some accepting rational-tree embedding of its realizable monitor. -/
def ProfiledRawJointRecurrentOwnerFibreRealizableMonitorTreeCertifiedAllInputs
    (initialOne : OneControl A strategy hwin)
    (initialTwo : TwoControl A strategy hwin)
    (hinitial :
      ProfiledRawJointRecurrentOwnerFibreBoundaryOperational A strategy hwin
        initialOne initialTwo) : Prop :=
  ∀ initialInput : In₁ × In₂,
    ∃ T : InputFreeRunParityTreeAutomaton.{max u v, max u v x y s}
        (ProfiledRawJointRecurrentOwnerFibreRealizableMonitorDirection
          (In₁ := In₁) (In₂ := In₂)),
      ∃ policy : T.RationalTransitionPolicy,
        Nonempty
          (ProfiledRawJointRecurrentOwnerFibreRealizableMonitorTreeCertificate
            A strategy hwin initialOne initialTwo hinitial initialInput T
              policy)

/-- The enriched regular-tree certificate has exactly the strength required
by the previously compiled all-input monitor adapter. -/
theorem
    profiledRawJointRecurrentOwnerFibreRealizableMonitorAcceptingAllInputs_of_treeCertified
    (initialOne : OneControl A strategy hwin)
    (initialTwo : TwoControl A strategy hwin)
    (hinitial :
      ProfiledRawJointRecurrentOwnerFibreBoundaryOperational A strategy hwin
        initialOne initialTwo)
    (hcertified :
      ProfiledRawJointRecurrentOwnerFibreRealizableMonitorTreeCertifiedAllInputs
        A strategy hwin initialOne initialTwo hinitial) :
    ProfiledRawJointRecurrentOwnerFibreRealizableMonitorAcceptingAllInputs A
      strategy hwin initialOne initialTwo hinitial := by
  intro initialInput
  rcases hcertified initialInput with ⟨T, policy, certificate⟩
  exact certificate.some.monitorAccepting A strategy hwin

end

end DetParityAutomaton

end DistributedSynthesis
