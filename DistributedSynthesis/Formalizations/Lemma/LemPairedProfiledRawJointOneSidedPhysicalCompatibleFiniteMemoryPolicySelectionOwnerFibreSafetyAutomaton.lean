/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicySelectionOwnerFibreKernel
import DistributedSynthesis.Formalizations.Theorem.ThmInputFreeRationalRun

/-!
# Exact safety automaton for the augmented owner-fibre kernel

For a fixed finite-memory policy selection, the live product stores both
endpoint controls and the actual state of the objective DPA.  Its universal
directions are exactly the current input pair and physical graph.  The product
uses the literal round record emitted by the augmented kernel.

The extra `none` state is an absorbing rejecting sink.  A live state enters
that sink when its endpoint pair does not satisfy the structural decoding
invariant.  Thus acceptance cannot hide a malformed reachable state behind
the total no-receive fallback of the executable kernel.
-/

namespace DistributedSynthesis

universe u v x y s m

namespace DetParityAutomaton

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable {Memory : Type m}
variable
  (A : DetParityAutomaton.{max u v x y, s}
    (RoundRecord In₁ In₂ Graph Out₁ Out₂))

noncomputable section

variable [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁]
  [Inhabited Out₂]
variable [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
variable [DecidableEq In₁] [DecidableEq In₂]
variable [Fintype Memory]

variable
  (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
  (hwin : ∀ env : EnvironmentSequence In₁ In₂,
    A.Accepts (execution strategy env))

private abbrev RootKey :=
  ProfiledRawJointOneSidedPhysicalCompatibleRootKey A strategy

private abbrev OneControl :=
  ProfiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryOneControl
    (Memory := Memory) A strategy

private abbrev TwoControl :=
  ProfiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryTwoControl
    (Memory := Memory) A strategy

private abbrev PolicySelection
    (initialMemory : RootKey A strategy → Memory) :=
  ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicySelection
    (Memory := Memory) A strategy hwin initialMemory

/-- One universally quantified move of the physical environment. -/
abbrev ProfiledRawJointRecurrentFiniteMemoryOwnerFibreSafetyDirection :=
  (In₁ × In₂) × Graph

/-- Live part of the verifier: both controls and the actual objective state. -/
abbrev ProfiledRawJointRecurrentFiniteMemoryOwnerFibreSafetyLiveState :=
  (OneControl (Memory := Memory) A strategy ×
      TwoControl (Memory := Memory) A strategy) ×
    A.State

/-- `none` is the absorbing rejecting decoder-failure state. -/
abbrev ProfiledRawJointRecurrentFiniteMemoryOwnerFibreSafetyState :=
  Option
    (ProfiledRawJointRecurrentFiniteMemoryOwnerFibreSafetyLiveState
      (Memory := Memory) A strategy)

namespace
    ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicySelection

variable
  (initialMemory : RootKey A strategy → Memory)
  (selection : PolicySelection (Memory := Memory) A strategy hwin
    initialMemory)

private abbrev Direction :=
  ProfiledRawJointRecurrentFiniteMemoryOwnerFibreSafetyDirection
    (In₁ := In₁) (In₂ := In₂)

private abbrev LiveState :=
  ProfiledRawJointRecurrentFiniteMemoryOwnerFibreSafetyLiveState
    (Memory := Memory) A strategy

private abbrev SafetyState :=
  ProfiledRawJointRecurrentFiniteMemoryOwnerFibreSafetyState
    (Memory := Memory) A strategy

/-! ## Literal live product -/

/-- Exact live successor before the decoder-failure monitor is added. -/
noncomputable def ownerFibreSafetyLiveStep
    (state : LiveState (Memory := Memory) A strategy)
    (direction : Direction (In₁ := In₁) (In₂ := In₂)) :
    LiveState (Memory := Memory) A strategy :=
  let result := selection.ownerFibreRound A strategy hwin initialMemory
    state.1 direction.1 direction.2
  (result.1,
    A.step state.2
      (selection.ownerFibreRoundRecord A strategy hwin initialMemory state.1
        direction.1 direction.2))

/-- Literal live state at a finite environment node. -/
noncomputable def ownerFibreSafetyLiveStateAt
    (initial : LiveState (Memory := Memory) A strategy)
    (node : TreeNode (Direction (In₁ := In₁) (In₂ := In₂))) :
    LiveState (Memory := Memory) A strategy :=
  node.foldl (selection.ownerFibreSafetyLiveStep A strategy hwin
    initialMemory) initial

@[simp] theorem ownerFibreSafetyLiveStateAt_nil
    (initial : LiveState (Memory := Memory) A strategy) :
    selection.ownerFibreSafetyLiveStateAt A strategy hwin initialMemory
      initial [] = initial :=
  rfl

theorem ownerFibreSafetyLiveStateAt_append
    (initial : LiveState (Memory := Memory) A strategy)
    (node : TreeNode (Direction (In₁ := In₁) (In₂ := In₂)))
    (direction : Direction (In₁ := In₁) (In₂ := In₂)) :
    selection.ownerFibreSafetyLiveStateAt A strategy hwin initialMemory
        initial (node ++ [direction]) =
      selection.ownerFibreSafetyLiveStep A strategy hwin initialMemory
        (selection.ownerFibreSafetyLiveStateAt A strategy hwin initialMemory
          initial node) direction := by
  simp [ownerFibreSafetyLiveStateAt, List.foldl_append]

/-- Exact word emitted by the live kernel along one environment branch. -/
noncomputable def ownerFibreSafetyWord
    (initial : LiveState (Memory := Memory) A strategy)
    (branch : Nat → Direction (In₁ := In₁) (In₂ := In₂)) :
    OmegaWord (RoundRecord In₁ In₂ Graph Out₁ Out₂) :=
  fun n ↦
    let state := selection.ownerFibreSafetyLiveStateAt A strategy hwin
      initialMemory initial (branchNode branch n)
    selection.ownerFibreRoundRecord A strategy hwin initialMemory state.1
      (branch n).1 (branch n).2

/-- The live DPA coordinate is the literal run on the emitted records. -/
theorem ownerFibreSafetyLiveStateAt_dpa
    (initial : LiveState (Memory := Memory) A strategy)
    (branch : Nat → Direction (In₁ := In₁) (In₂ := In₂)) :
    ∀ n,
      (selection.ownerFibreSafetyLiveStateAt A strategy hwin initialMemory
        initial (branchNode branch n)).2 =
      A.runFrom initial.2
        (selection.ownerFibreSafetyWord A strategy hwin initialMemory initial
          branch) n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [show branchNode branch (n + 1) =
          branchNode branch n ++ [branch n] from rfl,
        selection.ownerFibreSafetyLiveStateAt_append A strategy hwin
          initialMemory initial (branchNode branch n) (branch n)]
      simp only [ownerFibreSafetyLiveStep, runFrom, ownerFibreSafetyWord]
      rw [ih]

/-! ## Rejecting decoder monitor -/

/-- Guard the literal transition by the current structural decoder. -/
noncomputable def ownerFibreSafetyStep
    (state : SafetyState (Memory := Memory) A strategy)
    (direction : Direction (In₁ := In₁) (In₂ := In₂)) :
    SafetyState (Memory := Memory) A strategy := by
  classical
  exact
    match state with
    | none => none
    | some live =>
        if ProfiledRawJointRecurrentFiniteMemoryOwnerFibreDecodes
            (Memory := Memory) A strategy live.1.1 live.1.2 then
          some (selection.ownerFibreSafetyLiveStep A strategy hwin
            initialMemory live direction)
        else none

/-- Monitored state at a finite environment node. -/
noncomputable def ownerFibreSafetyStateAt
    (initial : LiveState (Memory := Memory) A strategy)
    (node : TreeNode (Direction (In₁ := In₁) (In₂ := In₂))) :
    SafetyState (Memory := Memory) A strategy :=
  node.foldl (selection.ownerFibreSafetyStep A strategy hwin initialMemory)
    (some initial)

@[simp] theorem ownerFibreSafetyStateAt_nil
    (initial : LiveState (Memory := Memory) A strategy) :
    selection.ownerFibreSafetyStateAt A strategy hwin initialMemory initial
      [] = some initial :=
  rfl

theorem ownerFibreSafetyStateAt_append
    (initial : LiveState (Memory := Memory) A strategy)
    (node : TreeNode (Direction (In₁ := In₁) (In₂ := In₂)))
    (direction : Direction (In₁ := In₁) (In₂ := In₂)) :
    selection.ownerFibreSafetyStateAt A strategy hwin initialMemory initial
        (node ++ [direction]) =
      selection.ownerFibreSafetyStep A strategy hwin initialMemory
        (selection.ownerFibreSafetyStateAt A strategy hwin initialMemory
          initial node) direction := by
  simp [ownerFibreSafetyStateAt, List.foldl_append]

@[simp] theorem ownerFibreSafetyStep_none
    (direction : Direction (In₁ := In₁) (In₂ := In₂)) :
    selection.ownerFibreSafetyStep A strategy hwin initialMemory none
      direction = none :=
  rfl

/-- Priority `1` makes the absorbing failure state rejecting. -/
noncomputable def ownerFibreSafetyPriority
    (state : SafetyState (Memory := Memory) A strategy) : Nat :=
  match state with
  | none => 1
  | some live => A.priority live.2

/-- Exact universal safety condition for one augmented recurrent entry. -/
def OwnerFibreSafe
    (initial : LiveState (Memory := Memory) A strategy) : Prop :=
  ∀ branch : Nat → Direction (In₁ := In₁) (In₂ := In₂),
    NatSeqMinEvenParity (fun n ↦
      ownerFibreSafetyPriority (Memory := Memory) A strategy
        (selection.ownerFibreSafetyStateAt A strategy hwin initialMemory
          initial (branchNode branch n)))

/-- Once reached, the failure state persists along every remaining suffix. -/
theorem ownerFibreSafetyStateAt_none_persists
    (initial : LiveState (Memory := Memory) A strategy)
    (branch : Nat → Direction (In₁ := In₁) (In₂ := In₂))
    (N : Nat)
    (hN : selection.ownerFibreSafetyStateAt A strategy hwin initialMemory
      initial (branchNode branch N) = none) :
    ∀ k,
      selection.ownerFibreSafetyStateAt A strategy hwin initialMemory initial
        (branchNode branch (N + k)) = none := by
  intro k
  induction k with
  | zero => simpa using hN
  | succ k ih =>
      rw [show branchNode branch (N + (k + 1)) =
          branchNode branch (N + k) ++ [branch (N + k)] by
            congr 1,
        selection.ownerFibreSafetyStateAt_append A strategy hwin
          initialMemory initial (branchNode branch (N + k))
          (branch (N + k)), ih]
      rfl

/-- An accepting monitored unfolding never reaches decoder failure. -/
theorem OwnerFibreSafe.stateAt_ne_none
    (initial : LiveState (Memory := Memory) A strategy)
    (hsafe : selection.OwnerFibreSafe A strategy hwin initialMemory initial)
    (branch : Nat → Direction (In₁ := In₁) (In₂ := In₂))
    (N : Nat) :
    selection.ownerFibreSafetyStateAt A strategy hwin initialMemory initial
      (branchNode branch N) ≠ none := by
  intro hN
  have hpersist :=
    selection.ownerFibreSafetyStateAt_none_persists A strategy hwin
      initialMemory initial branch N hN
  have heventual :
      ∃ cutoff,
        ∀ n, cutoff ≤ n →
          ownerFibreSafetyPriority (Memory := Memory) A strategy
              (selection.ownerFibreSafetyStateAt A strategy hwin
                initialMemory initial (branchNode branch n)) = 1 := by
    refine ⟨N, ?_⟩
    intro n hn
    have heq : N + (n - N) = n := by omega
    rw [← heq, hpersist]
    rfl
  rcases hsafe branch with ⟨p, hpEven, hpSeen, _hpMin⟩
  rcases heventual with ⟨cutoff, heventual⟩
  rcases hpSeen cutoff with ⟨k, hk, hpriority⟩
  have hp : p = 1 := by
    exact hpriority.symm.trans (heventual k hk)
  subst p
  rcases hpEven with ⟨q, hq⟩
  omega

/-- Under safety, the monitored run is exactly the live literal run. -/
theorem OwnerFibreSafe.stateAt_eq_some_liveStateAt
    (initial : LiveState (Memory := Memory) A strategy)
    (hsafe : selection.OwnerFibreSafe A strategy hwin initialMemory initial)
    (branch : Nat → Direction (In₁ := In₁) (In₂ := In₂)) :
    ∀ n,
      selection.ownerFibreSafetyStateAt A strategy hwin initialMemory initial
          (branchNode branch n) =
        some
          (selection.ownerFibreSafetyLiveStateAt A strategy hwin
            initialMemory initial (branchNode branch n)) := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [show branchNode branch (n + 1) =
          branchNode branch n ++ [branch n] from rfl,
        selection.ownerFibreSafetyStateAt_append A strategy hwin
          initialMemory initial (branchNode branch n) (branch n),
        selection.ownerFibreSafetyLiveStateAt_append A strategy hwin
          initialMemory initial (branchNode branch n) (branch n), ih]
      by_cases hdecodes :
        ProfiledRawJointRecurrentFiniteMemoryOwnerFibreDecodes
          (Memory := Memory) A strategy
          (selection.ownerFibreSafetyLiveStateAt A strategy hwin
            initialMemory initial (branchNode branch n)).1.1
          (selection.ownerFibreSafetyLiveStateAt A strategy hwin
            initialMemory initial (branchNode branch n)).1.2
      · simp [ownerFibreSafetyStep, hdecodes]
      · exfalso
        apply OwnerFibreSafe.stateAt_ne_none (Memory := Memory) A strategy
          hwin initialMemory selection initial hsafe branch (n + 1)
        rw [show branchNode branch (n + 1) =
            branchNode branch n ++ [branch n] from rfl,
          selection.ownerFibreSafetyStateAt_append A strategy hwin
            initialMemory initial (branchNode branch n) (branch n), ih]
        simp [ownerFibreSafetyStep, hdecodes]

/-- Safety forces the decoder invariant at every branch prefix. -/
theorem OwnerFibreSafe.decodes
    (initial : LiveState (Memory := Memory) A strategy)
    (hsafe : selection.OwnerFibreSafe A strategy hwin initialMemory initial)
    (branch : Nat → Direction (In₁ := In₁) (In₂ := In₂))
    (n : Nat) :
    ProfiledRawJointRecurrentFiniteMemoryOwnerFibreDecodes
      (Memory := Memory) A strategy
      (selection.ownerFibreSafetyLiveStateAt A strategy hwin initialMemory
        initial (branchNode branch n)).1.1
      (selection.ownerFibreSafetyLiveStateAt A strategy hwin initialMemory
        initial (branchNode branch n)).1.2 := by
  by_contra hdecodes
  apply OwnerFibreSafe.stateAt_ne_none (Memory := Memory) A strategy hwin
    initialMemory selection initial hsafe branch (n + 1)
  rw [show branchNode branch (n + 1) =
      branchNode branch n ++ [branch n] from rfl,
    selection.ownerFibreSafetyStateAt_append A strategy hwin initialMemory
      initial (branchNode branch n) (branch n),
    OwnerFibreSafe.stateAt_eq_some_liveStateAt (Memory := Memory) A strategy
      hwin initialMemory selection initial hsafe branch n]
  simp [ownerFibreSafetyStep, hdecodes]

/-- Safety implies acceptance of the kernel's exact literal output word. -/
theorem OwnerFibreSafe.acceptsFrom
    (initial : LiveState (Memory := Memory) A strategy)
    (hsafe : selection.OwnerFibreSafe A strategy hwin initialMemory initial)
    (branch : Nat → Direction (In₁ := In₁) (In₂ := In₂)) :
    A.AcceptsFrom initial.2
      (selection.ownerFibreSafetyWord A strategy hwin initialMemory initial
        branch) := by
  change NatSeqMinEvenParity (fun n ↦
    A.priority
      (A.runFrom initial.2
        (selection.ownerFibreSafetyWord A strategy hwin initialMemory initial
          branch) n))
  simpa only [OwnerFibreSafe.stateAt_eq_some_liveStateAt (Memory := Memory)
      A strategy hwin initialMemory selection initial hsafe branch,
    ownerFibreSafetyPriority,
    selection.ownerFibreSafetyLiveStateAt_dpa A strategy hwin initialMemory
      initial branch] using hsafe branch

/-! ## Converse characterization -/

/-- Branchwise decoding keeps the monitored run out of the sink. -/
theorem ownerFibreSafetyStateAt_eq_some_of_decodes
    (initial : LiveState (Memory := Memory) A strategy)
    (branch : Nat → Direction (In₁ := In₁) (In₂ := In₂))
    (hdecodes : ∀ n,
      ProfiledRawJointRecurrentFiniteMemoryOwnerFibreDecodes
        (Memory := Memory) A strategy
        (selection.ownerFibreSafetyLiveStateAt A strategy hwin initialMemory
          initial (branchNode branch n)).1.1
        (selection.ownerFibreSafetyLiveStateAt A strategy hwin initialMemory
          initial (branchNode branch n)).1.2) :
    ∀ n,
      selection.ownerFibreSafetyStateAt A strategy hwin initialMemory initial
          (branchNode branch n) =
        some
          (selection.ownerFibreSafetyLiveStateAt A strategy hwin
            initialMemory initial (branchNode branch n)) := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [show branchNode branch (n + 1) =
          branchNode branch n ++ [branch n] from rfl,
        selection.ownerFibreSafetyStateAt_append A strategy hwin
          initialMemory initial (branchNode branch n) (branch n),
        selection.ownerFibreSafetyLiveStateAt_append A strategy hwin
          initialMemory initial (branchNode branch n) (branch n), ih]
      simp [ownerFibreSafetyStep, hdecodes n]

/-- Exact paper-facing characterization of the guarded safety product. -/
theorem ownerFibreSafe_iff_decodes_and_forall_acceptsFrom
    (initial : LiveState (Memory := Memory) A strategy) :
    selection.OwnerFibreSafe A strategy hwin initialMemory initial ↔
      (∀ branch : Nat → Direction (In₁ := In₁) (In₂ := In₂),
        ∀ n,
          ProfiledRawJointRecurrentFiniteMemoryOwnerFibreDecodes
            (Memory := Memory) A strategy
            (selection.ownerFibreSafetyLiveStateAt A strategy hwin
              initialMemory initial (branchNode branch n)).1.1
            (selection.ownerFibreSafetyLiveStateAt A strategy hwin
              initialMemory initial (branchNode branch n)).1.2) ∧
      (∀ branch : Nat → Direction (In₁ := In₁) (In₂ := In₂),
        A.AcceptsFrom initial.2
          (selection.ownerFibreSafetyWord A strategy hwin initialMemory
            initial branch)) := by
  constructor
  · intro hsafe
    exact
      ⟨OwnerFibreSafe.decodes (Memory := Memory) A strategy hwin initialMemory
        selection initial hsafe,
        OwnerFibreSafe.acceptsFrom (Memory := Memory) A strategy hwin
          initialMemory selection initial hsafe⟩
  · rintro ⟨hdecodes, haccepts⟩ branch
    have hacceptsBranch := haccepts branch
    change NatSeqMinEvenParity (fun n ↦
      A.priority
        (A.runFrom initial.2
          (selection.ownerFibreSafetyWord A strategy hwin initialMemory
            initial branch) n)) at hacceptsBranch
    simpa only [selection.ownerFibreSafetyStateAt_eq_some_of_decodes
        A strategy hwin initialMemory initial branch (hdecodes branch),
      ownerFibreSafetyPriority,
      selection.ownerFibreSafetyLiveStateAt_dpa A strategy hwin initialMemory
        initial branch] using hacceptsBranch

/-! ## Finite deterministic tree verifier -/

/-- One selection must be safe from every entry in the supplied family. -/
def OwnerFibreSafeOn
    (entries : Finset (LiveState (Memory := Memory) A strategy)) : Prop :=
  ∀ initial ∈ entries,
    selection.OwnerFibreSafe A strategy hwin initialMemory initial

/-- Deterministic input-free automaton unfolding the guarded exact product. -/
noncomputable def ownerFibreSafetyAutomaton
    (initial : LiveState (Memory := Memory) A strategy) :
    InputFreeRunParityTreeAutomaton.{max u v, max u v x y s m}
      (Direction (In₁ := In₁) (In₂ := In₂)) where
  State := SafetyState (Memory := Memory) A strategy
  stateFinite := inferInstance
  initial := some initial
  delta := fun state _ children ↦
    ∀ direction,
      children direction =
        selection.ownerFibreSafetyStep A strategy hwin initialMemory state
          direction
  priority := ownerFibreSafetyPriority (Memory := Memory) A strategy

/-- The literal guarded unfolding is already transition-rational. -/
noncomputable def ownerFibreSafetyPolicy
    (initial : LiveState (Memory := Memory) A strategy)
    (hsafe : selection.OwnerFibreSafe A strategy hwin initialMemory initial) :
    (selection.ownerFibreSafetyAutomaton A strategy hwin initialMemory initial)
      |>.RationalTransitionPolicy where
  run := selection.ownerFibreSafetyStateAt A strategy hwin initialMemory
    initial
  accepts := by
    constructor
    · constructor
      · rfl
      · intro node direction
        exact selection.ownerFibreSafetyStateAt_append A strategy hwin
          initialMemory initial node direction
    · exact hsafe
  successor := selection.ownerFibreSafetyStep A strategy hwin initialMemory
  successor_at := by
    intro node direction
    exact (selection.ownerFibreSafetyStateAt_append A strategy hwin
      initialMemory initial node direction).symm
  legal_at := by
    intro node direction
    rfl

/-- Determinism forces every rational verifier policy to be the literal run. -/
theorem ownerFibreSafetyPolicy_run_eq
    (initial : LiveState (Memory := Memory) A strategy)
    (policy :
      (selection.ownerFibreSafetyAutomaton A strategy hwin initialMemory
        initial).RationalTransitionPolicy) :
    ∀ node,
      policy.run node =
        selection.ownerFibreSafetyStateAt A strategy hwin initialMemory
          initial node := by
  intro node
  induction node using List.reverseRecOn with
  | nil => exact policy.accepts.1.1
  | append_singleton node direction ih =>
      rw [← policy.successor_at node direction,
        selection.ownerFibreSafetyStateAt_append A strategy hwin
          initialMemory initial node direction, ← ih]
      exact policy.legal_at node direction

/-- Exact equivalence after the augmented selection has been fixed. -/
theorem ownerFibreSafe_iff_nonempty_rationalPolicy
    (initial : LiveState (Memory := Memory) A strategy) :
    selection.OwnerFibreSafe A strategy hwin initialMemory initial ↔
      Nonempty
        ((selection.ownerFibreSafetyAutomaton A strategy hwin initialMemory
          initial).RationalTransitionPolicy) := by
  constructor
  · intro hsafe
    exact
      ⟨selection.ownerFibreSafetyPolicy A strategy hwin initialMemory initial
        hsafe⟩
  · rintro ⟨policy⟩
    intro branch
    have haccepts := policy.accepts.2 branch
    simpa only [selection.ownerFibreSafetyPolicy_run_eq A strategy hwin
      initialMemory initial policy] using haccepts

/-- Family form: the same augmented selection occurs at every entry. -/
theorem ownerFibreSafeOn_iff_forall_nonempty_rationalPolicy
    (entries : Finset (LiveState (Memory := Memory) A strategy)) :
    selection.OwnerFibreSafeOn A strategy hwin initialMemory entries ↔
      ∀ initial ∈ entries,
        Nonempty
          ((selection.ownerFibreSafetyAutomaton A strategy hwin initialMemory
            initial).RationalTransitionPolicy) := by
  constructor
  · intro hsafe initial hinitial
    exact
      (selection.ownerFibreSafe_iff_nonempty_rationalPolicy A strategy hwin
        initialMemory initial).mp (hsafe initial hinitial)
  · intro hpolicies initial hinitial
    exact
      (selection.ownerFibreSafe_iff_nonempty_rationalPolicy A strategy hwin
        initialMemory initial).mpr (hpolicies initial hinitial)

end
    ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicySelection

end

end DetParityAutomaton

end DistributedSynthesis
