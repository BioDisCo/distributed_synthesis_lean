/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointOneSidedPhysicalCompatiblePolicySelectionOwnerFibreKernel
import DistributedSynthesis.Formalizations.Theorem.ThmInputFreeRationalRun

/-!
# Exact parity automaton for a selected owner-fibre kernel

For a fixed policy selection and recurrent entry, the controller, its two
outputs, and the objective-DPA update form a finite deterministic transition
system.  Its directions are precisely the environment's current input pair
and physical graph.  The input-free parity tree automaton below unfolds all
of these directions.

The equivalence at the end is important strategically: after a selection has
been fixed, an accepting rational tree exists exactly when its closed-loop
kernel is safe.  Hence the remaining regularization theorem must construct a
single observation-uniform selection whose kernel is safe; choosing a tree
certificate after fixing an arbitrary forward-accepting policy cannot repair
an unsafe selection.
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

variable
  (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
  (hwin : ∀ env : EnvironmentSequence In₁ In₂,
    A.Accepts (execution strategy env))

private abbrev OneControl :=
  ProfiledRawJointRecurrentOwnerFibreBoundaryOneControl A strategy hwin

private abbrev TwoControl :=
  ProfiledRawJointRecurrentOwnerFibreBoundaryTwoControl A strategy hwin

private abbrev PolicySelection :=
  ProfiledRawJointOneSidedPhysicalCompatiblePolicySelection A strategy hwin

/-- One universally quantified move of the physical environment. -/
abbrev ProfiledRawJointRecurrentOwnerFibreSafetyDirection :=
  (In₁ × In₂) × Graph

/-- Product of both finite endpoint controls and the actual objective-DPA
state. -/
abbrev ProfiledRawJointRecurrentOwnerFibreSafetyState :=
  (OneControl A strategy hwin × TwoControl A strategy hwin) × A.State

namespace ProfiledRawJointOneSidedPhysicalCompatiblePolicySelection

variable (selection : PolicySelection A strategy hwin)

/-- Exact closed-loop successor for one environment direction. -/
noncomputable def ownerFibreSafetyStep
    (state :
      ProfiledRawJointRecurrentOwnerFibreSafetyState A strategy hwin)
    (direction :
      ProfiledRawJointRecurrentOwnerFibreSafetyDirection
        (In₁ := In₁) (In₂ := In₂)) :
    ProfiledRawJointRecurrentOwnerFibreSafetyState A strategy hwin :=
  let result := selection.ownerFibreRound A strategy hwin state.1
    direction.1 direction.2
  (result.1,
    A.step state.2
      (selection.ownerFibreRoundRecord A strategy hwin state.1 direction.1
        direction.2))

/-- Closed-loop state at a finite environment node. -/
noncomputable def ownerFibreSafetyStateAt
    (initial :
      ProfiledRawJointRecurrentOwnerFibreSafetyState A strategy hwin)
    (node : TreeNode
      (ProfiledRawJointRecurrentOwnerFibreSafetyDirection
        (In₁ := In₁) (In₂ := In₂))) :
    ProfiledRawJointRecurrentOwnerFibreSafetyState A strategy hwin :=
  node.foldl (selection.ownerFibreSafetyStep A strategy hwin) initial

@[simp] theorem ownerFibreSafetyStateAt_nil
    (initial :
      ProfiledRawJointRecurrentOwnerFibreSafetyState A strategy hwin) :
    selection.ownerFibreSafetyStateAt A strategy hwin initial [] = initial :=
  rfl

theorem ownerFibreSafetyStateAt_append
    (initial :
      ProfiledRawJointRecurrentOwnerFibreSafetyState A strategy hwin)
    (node : TreeNode
      (ProfiledRawJointRecurrentOwnerFibreSafetyDirection
        (In₁ := In₁) (In₂ := In₂)))
    (direction :
      ProfiledRawJointRecurrentOwnerFibreSafetyDirection
        (In₁ := In₁) (In₂ := In₂)) :
    selection.ownerFibreSafetyStateAt A strategy hwin initial
        (node ++ [direction]) =
      selection.ownerFibreSafetyStep A strategy hwin
        (selection.ownerFibreSafetyStateAt A strategy hwin initial node)
        direction := by
  simp [ownerFibreSafetyStateAt, List.foldl_append]

/-- Universal parity safety of one selection-relative recurrent entry.  The
quantifier ranges over every input and graph schedule, and the priority is
that of the actual DPA state reached from `initial.2` on the exact emitted
round records. -/
def OwnerFibreSafe
    (initial :
      ProfiledRawJointRecurrentOwnerFibreSafetyState A strategy hwin) : Prop :=
  ∀ branch : Nat →
      ProfiledRawJointRecurrentOwnerFibreSafetyDirection
        (In₁ := In₁) (In₂ := In₂),
    NatSeqMinEvenParity (fun n ↦
      A.priority
        (selection.ownerFibreSafetyStateAt A strategy hwin initial
          (branchNode branch n)).2)

/-- The literal objective word emitted along one environment branch. -/
noncomputable def ownerFibreSafetyWord
    (initial :
      ProfiledRawJointRecurrentOwnerFibreSafetyState A strategy hwin)
    (branch : Nat →
      ProfiledRawJointRecurrentOwnerFibreSafetyDirection
        (In₁ := In₁) (In₂ := In₂)) :
    OmegaWord (RoundRecord In₁ In₂ Graph Out₁ Out₂) :=
  fun n ↦
    let state := selection.ownerFibreSafetyStateAt A strategy hwin initial
      (branchNode branch n)
    selection.ownerFibreRoundRecord A strategy hwin state.1
      (branch n).1 (branch n).2

/-- The DPA coordinate of the safety product is its literal run on the
emitted word. -/
theorem ownerFibreSafetyStateAt_dpa
    (initial :
      ProfiledRawJointRecurrentOwnerFibreSafetyState A strategy hwin)
    (branch : Nat →
      ProfiledRawJointRecurrentOwnerFibreSafetyDirection
        (In₁ := In₁) (In₂ := In₂)) :
    ∀ n,
      (selection.ownerFibreSafetyStateAt A strategy hwin initial
        (branchNode branch n)).2 =
      A.runFrom initial.2
        (selection.ownerFibreSafetyWord A strategy hwin initial branch) n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [show branchNode branch (n + 1) =
          branchNode branch n ++ [branch n] from rfl,
        selection.ownerFibreSafetyStateAt_append A strategy hwin initial
          (branchNode branch n) (branch n)]
      simp only [ownerFibreSafetyStep, runFrom, ownerFibreSafetyWord]
      rw [ih]

/-- Paper-facing form: safety means that the objective DPA accepts the exact
word emitted for every input/graph schedule. -/
theorem ownerFibreSafe_iff_forall_acceptsFrom
    (initial :
      ProfiledRawJointRecurrentOwnerFibreSafetyState A strategy hwin) :
    selection.OwnerFibreSafe A strategy hwin initial ↔
      ∀ branch : Nat →
          ProfiledRawJointRecurrentOwnerFibreSafetyDirection
            (In₁ := In₁) (In₂ := In₂),
        A.AcceptsFrom initial.2
          (selection.ownerFibreSafetyWord A strategy hwin initial branch) := by
  unfold OwnerFibreSafe NatSeqMinEvenParity NatSeqSeenInfinitelyOften
    AcceptsFrom PrioritySeenInfinitelyOftenFrom
  constructor <;> intro h branch
  · simpa only [selection.ownerFibreSafetyStateAt_dpa A strategy hwin
      initial branch] using h branch
  · simpa only [selection.ownerFibreSafetyStateAt_dpa A strategy hwin
      initial branch] using h branch

/-- One selected bank must be safe from every canonical entry in the fixed
fibre, not merely from one chosen entry.  The finite entry set will be supplied
by the model-specific entry compilation. -/
def OwnerFibreSafeOn
    (entries : Finset
      (ProfiledRawJointRecurrentOwnerFibreSafetyState A strategy hwin)) :
    Prop :=
  ∀ initial ∈ entries,
    selection.OwnerFibreSafe A strategy hwin initial

/-- Deterministic input-free tree automaton that unfolds the exact kernel. -/
noncomputable def ownerFibreSafetyAutomaton
    (initial :
      ProfiledRawJointRecurrentOwnerFibreSafetyState A strategy hwin) :
    InputFreeRunParityTreeAutomaton.{max u v, max u v x y s}
      (ProfiledRawJointRecurrentOwnerFibreSafetyDirection
        (In₁ := In₁) (In₂ := In₂)) where
  State := ProfiledRawJointRecurrentOwnerFibreSafetyState A strategy hwin
  stateFinite := inferInstance
  initial := initial
  delta := fun state _ children ↦
    ∀ direction,
      children direction =
        selection.ownerFibreSafetyStep A strategy hwin state direction
  priority := fun state ↦ A.priority state.2

/-- The literal finite unfolding is already transition-rational: its
successor table is `ownerFibreSafetyStep`. -/
noncomputable def ownerFibreSafetyPolicy
    (initial :
      ProfiledRawJointRecurrentOwnerFibreSafetyState A strategy hwin)
    (hsafe : selection.OwnerFibreSafe A strategy hwin initial) :
    (selection.ownerFibreSafetyAutomaton A strategy hwin initial)
      |>.RationalTransitionPolicy where
  run := selection.ownerFibreSafetyStateAt A strategy hwin initial
  accepts := by
    constructor
    · constructor
      · rfl
      · intro node direction
        exact selection.ownerFibreSafetyStateAt_append A strategy hwin initial
          node direction
    · exact hsafe
  successor := selection.ownerFibreSafetyStep A strategy hwin
  successor_at := by
    intro node direction
    exact (selection.ownerFibreSafetyStateAt_append A strategy hwin initial
      node direction).symm
  legal_at := by
    intro node direction
    rfl

/-- Every rational policy of the deterministic safety automaton has the
literal kernel unfolding as its run. -/
theorem ownerFibreSafetyPolicy_run_eq
    (initial :
      ProfiledRawJointRecurrentOwnerFibreSafetyState A strategy hwin)
    (policy :
      (selection.ownerFibreSafetyAutomaton A strategy hwin initial)
        |>.RationalTransitionPolicy) :
    ∀ node,
      policy.run node =
        selection.ownerFibreSafetyStateAt A strategy hwin initial node := by
  intro node
  induction node using List.reverseRecOn with
  | nil => exact policy.accepts.1.1
  | append_singleton node direction ih =>
      rw [← policy.successor_at node direction,
        selection.ownerFibreSafetyStateAt_append A strategy hwin initial node
          direction, ← ih]
      exact policy.legal_at node direction

/-- Exact equivalence between closed-loop safety and an accepting rational
tree after the selection has been fixed. -/
theorem ownerFibreSafe_iff_nonempty_rationalPolicy
    (initial :
      ProfiledRawJointRecurrentOwnerFibreSafetyState A strategy hwin) :
    selection.OwnerFibreSafe A strategy hwin initial ↔
      Nonempty
        ((selection.ownerFibreSafetyAutomaton A strategy hwin initial)
          |>.RationalTransitionPolicy) := by
  constructor
  · intro hsafe
    exact ⟨selection.ownerFibreSafetyPolicy A strategy hwin initial hsafe⟩
  · rintro ⟨policy⟩
    intro branch
    have haccepts := policy.accepts.2 branch
    simpa only [selection.ownerFibreSafetyPolicy_run_eq A strategy hwin
      initial policy] using haccepts

/-- Family form of the exact equivalence.  The same `selection` occurs in
every member; only the proof-side verifier policy is entry-specific. -/
theorem ownerFibreSafeOn_iff_forall_nonempty_rationalPolicy
    (entries : Finset
      (ProfiledRawJointRecurrentOwnerFibreSafetyState A strategy hwin)) :
    selection.OwnerFibreSafeOn A strategy hwin entries ↔
      ∀ initial ∈ entries,
        Nonempty
          ((selection.ownerFibreSafetyAutomaton A strategy hwin initial)
            |>.RationalTransitionPolicy) := by
  constructor
  · intro hsafe initial hinitial
    exact (selection.ownerFibreSafe_iff_nonempty_rationalPolicy A strategy hwin
      initial).mp (hsafe initial hinitial)
  · intro hpolicies initial hinitial
    exact (selection.ownerFibreSafe_iff_nonempty_rationalPolicy A strategy hwin
      initial).mpr (hpolicies initial hinitial)

end ProfiledRawJointOneSidedPhysicalCompatiblePolicySelection

end

end DetParityAutomaton

end DistributedSynthesis
