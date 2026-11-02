/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemActualFullViewFamilyRecovery
import DistributedSynthesis.Formalizations.Lemma.LemEpochArenaCuts
import DistributedSynthesis.Formalizations.Lemma.LemFiniteGlobalBeliefEpochAcceptance

/-!
# The complete physical acceptance regime split

This file closes the omega-combinatorial assembly needed by the finite global
belief-machine route.  It deliberately assumes no physical coverage or
trace-identification theorem.

There are exactly four proof-side regimes:

* `.both` occurs unboundedly often, so the ordinary epoch coupling applies;
* after the last `.both`, both strict letters still occur unboundedly often,
  which is the persistent reversal-chain case;
* the graph is eventually always strict right;
* the graph is eventually always strict left.

The second case is derived from the full-view recovery trichotomy, not exposed
to either process as a leader or orientation test.  For each trapped-tail
case, acceptance is assembled with the identity cut sequence.  Thus the final
infinite block is not incorrectly treated as one last finite `.both` epoch.

The only model-specific fields left by the endpoint are consequently the
expected trace/state identifications: recurrent epoch block minima, normal
right/left tail parity, and persistent-chain tail parity.
-/

namespace DistributedSynthesis

universe u v w x y s

/-- Synchronizing `.both` rounds occur at arbitrarily late positions. -/
def GraphBothRecurrent (graphs : Nat → Graph) : Prop :=
  ∀ start : Nat, ∃ n : Nat, start ≤ n ∧ graphs n = .both

/-- Synchronizing rounds disappear after a finite prefix. -/
def EventuallyNoBoth (graphs : Nat → Graph) : Prop :=
  ∃ start : Nat, ∀ n : Nat, start ≤ n → graphs n ≠ .both

/-- Both strict directions occur at arbitrarily late positions.  Once `.both`
has disappeared, this is precisely the graph-theoretic shape of the
persistent reversal-chain regime. -/
def BothStrictDirectionsRecurrent (graphs : Nat → Graph) : Prop :=
  (∀ start : Nat, ∃ n : Nat, start ≤ n ∧ graphs n = .left) ∧
    (∀ start : Nat, ∃ n : Nat, start ≤ n ∧ graphs n = .right)

/-- The final epoch is infinite and keeps reversing forever.  Keeping the
`EventuallyNoBoth` conjunct is important: strict-direction recurrence alone
would also hold on some executions with recurrent synchronization rounds. -/
def PersistentStrictReversalTail (graphs : Nat → Graph) : Prop :=
  EventuallyNoBoth graphs ∧ BothStrictDirectionsRecurrent graphs

/-- A persistent strict-reversal tail contains arbitrarily late ordered
left-to-right reversals (possibly with a longer constant block in between). -/
theorem PersistentStrictReversalTail.left_then_right
    {graphs : Nat → Graph} (h : PersistentStrictReversalTail graphs)
    (start : Nat) :
    ∃ leftAt rightAt : Nat,
      start ≤ leftAt ∧ leftAt < rightAt ∧
        graphs leftAt = .left ∧ graphs rightAt = .right := by
  rcases h.2.1 start with ⟨leftAt, hstart, hleft⟩
  rcases h.2.2 (leftAt + 1) with ⟨rightAt, hrightAt, hright⟩
  exact ⟨leftAt, rightAt, hstart, by omega, hleft, hright⟩

/-- Mirror ordered reversal witness. -/
theorem PersistentStrictReversalTail.right_then_left
    {graphs : Nat → Graph} (h : PersistentStrictReversalTail graphs)
    (start : Nat) :
    ∃ rightAt leftAt : Nat,
      start ≤ rightAt ∧ rightAt < leftAt ∧
        graphs rightAt = .right ∧ graphs leftAt = .left := by
  rcases h.2.2 start with ⟨rightAt, hstart, hright⟩
  rcases h.2.1 (rightAt + 1) with ⟨leftAt, hleftAt, hleft⟩
  exact ⟨rightAt, leftAt, hstart, by omega, hright, hleft⟩

/-- The hierarchy is eventually fixed with process two receiving forever. -/
def EventuallyStrictRight (graphs : Nat → Graph) : Prop :=
  ∃ start : Nat, ∀ n : Nat, start ≤ n → graphs n = .right

/-- The hierarchy is eventually fixed with process one receiving forever. -/
def EventuallyStrictLeft (graphs : Nat → Graph) : Prop :=
  ∃ start : Nat, ∀ n : Nat, start ≤ n → graphs n = .left

/-- In the no-more-`.both` regime, recurring full-view transfer to both
processes forces both strict directions to occur unboundedly often. -/
theorem bothStrictDirectionsRecurrent_of_noBoth_of_bothFrequentlyReceive
    (graphs : Nat → Graph)
    (hnoBoth : EventuallyNoBoth graphs)
    (hrecovery :
      (∀ start, ∃ n, start ≤ n ∧
          (graphs n = .left ∨ graphs n = .both)) ∧
        (∀ start, ∃ n, start ≤ n ∧
          (graphs n = .right ∨ graphs n = .both))) :
    BothStrictDirectionsRecurrent graphs := by
  rcases hnoBoth with ⟨N, hN⟩
  constructor
  · intro start
    rcases hrecovery.1 (max start N) with ⟨n, hn, hreceive⟩
    refine ⟨n, Nat.le_trans (Nat.le_max_left start N) hn, ?_⟩
    rcases hreceive with hleft | hboth
    · exact hleft
    · exact False.elim
        (hN n (Nat.le_trans (Nat.le_max_right start N) hn) hboth)
  · intro start
    rcases hrecovery.2 (max start N) with ⟨n, hn, hreceive⟩
    refine ⟨n, Nat.le_trans (Nat.le_max_left start N) hn, ?_⟩
    rcases hreceive with hright | hboth
    · exact hright
    · exact False.elim
        (hN n (Nat.le_trans (Nat.le_max_right start N) hn) hboth)

/-- Exhaustive graph regime split used by physical acceptance.  It is wholly
proof-side: no process learns which disjunct holds. -/
theorem environment_physical_acceptance_regime
    {In₁ : Type u} {In₂ : Type v}
    (env : EnvironmentSequence In₁ In₂) :
    GraphBothRecurrent (fun n ↦ (env n).graph) ∨
      PersistentStrictReversalTail (fun n ↦ (env n).graph) ∨
      EventuallyStrictRight (fun n ↦ (env n).graph) ∨
      EventuallyStrictLeft (fun n ↦ (env n).graph) := by
  rcases env_both_recurrent_or_trapped env with hboth | hnoBoth
  · exact Or.inl hboth
  · refine Or.inr ?_
    apply
      of_both_frequently_receive_of_eventually_strict_right_of_eventually_strict_left
        (fun n ↦ (env n).graph)
    · intro hrecovery
      exact Or.inl ⟨hnoBoth,
        bothStrictDirectionsRecurrent_of_noBoth_of_bothFrequentlyReceive
          (fun n ↦ (env n).graph) hnoBoth hrecovery⟩
    · intro hright
      exact Or.inr (Or.inl hright)
    · intro hleft
      exact Or.inr (Or.inr hleft)

/-- Identity cuts split a sequence into singleton blocks. -/
@[simp] theorem cutBlockMin_identity (priorities : Nat → Nat) (k : Nat) :
    cutBlockMin priorities (fun n ↦ n) k = priorities k := by
  simp [cutBlockMin, rangeMin]

namespace DetParityAutomaton

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable
  (A : DetParityAutomaton.{max u v x y, s}
    (RoundRecord In₁ In₂ Graph Out₁ Out₂))

/-- Any accepting physical tail gives a legitimate epoch coupling by using
the identity cuts.  This is the safe coupling for a final infinite epoch. -/
def finiteGlobalMachineEpochCoupling_of_tailParity
    (G : FiniteGlobalRoundMachine.{u, v, w} In₁ In₂)
    (outputOne : G.State → Out₁) (outputTwo : G.State → Out₂)
    (env : EnvironmentSequence In₁ In₂) (start : Nat)
    (htail : NatSeqMinEvenParity
      (fun n ↦ A.priority
        (A.run (G.globalMachineTraceWord outputOne outputTwo env)
          (start + n)))) :
    A.FiniteGlobalMachineEpochCoupling G outputOne outputTwo env where
  start := start
  cuts := fun n ↦ n
  cuts_strictMono := strictMono_id
  cuts_zero := rfl
  epochPriority := fun n ↦ A.priority
    (A.run (G.globalMachineTraceWord outputOne outputTwo env) (start + n))
  epochParity := htail
  blockMin_eq_epochPriority := by
    intro k
    exact cutBlockMin_identity _ k

/-- Tail parity therefore implies acceptance of the complete physical word,
with its arbitrary finite prefix. -/
theorem finiteGlobalMachineTraceWord_accepts_of_tailParity
    (G : FiniteGlobalRoundMachine.{u, v, w} In₁ In₂)
    (outputOne : G.State → Out₁) (outputTwo : G.State → Out₂)
    (env : EnvironmentSequence In₁ In₂) (start : Nat)
    (htail : NatSeqMinEvenParity
      (fun n ↦ A.priority
        (A.run (G.globalMachineTraceWord outputOne outputTwo env)
          (start + n)))) :
    A.Accepts (G.globalMachineTraceWord outputOne outputTwo env) :=
  A.finiteGlobalMachineTraceWord_accepts_of_epochCoupling G outputOne
    outputTwo env
      (A.finiteGlobalMachineEpochCoupling_of_tailParity G outputOne outputTwo
        env start htail)

/-- A checker tail transfers to the physical trace through pointwise priority
equality.  This names the sole equality still owed when applying the existing
fixed-side block monitors or the persistent chain checker. -/
theorem finiteGlobalMachineTraceWord_accepts_of_checkerTail
    (G : FiniteGlobalRoundMachine.{u, v, w} In₁ In₂)
    (outputOne : G.State → Out₁) (outputTwo : G.State → Out₂)
    (env : EnvironmentSequence In₁ In₂) (start : Nat)
    (checkerPriority : Nat → Nat)
    (hchecker : NatSeqMinEvenParity checkerPriority)
    (priority_eq_checker : ∀ n : Nat,
      A.priority
          (A.run (G.globalMachineTraceWord outputOne outputTwo env)
            (start + n)) =
        checkerPriority n) :
    A.Accepts (G.globalMachineTraceWord outputOne outputTwo env) := by
  apply A.finiteGlobalMachineTraceWord_accepts_of_tailParity G outputOne
    outputTwo env start
  simpa only [priority_eq_checker] using hchecker

/-- Exact model-facing acceptance package.  The recurrent branch retains the
existing block-minimum coupling.  Each trapped branch may choose its own
finite tail start and then supplies original-DPA parity on that physical tail.

The three tail fields correspond respectively to the persistent
`ChainAllThreadsWin` checker and the two fixed-side `ForeverAccepts`
obligations. -/
structure FiniteGlobalMachinePhysicalAcceptance
    (G : FiniteGlobalRoundMachine.{u, v, w} In₁ In₂)
    (outputOne : G.State → Out₁) (outputTwo : G.State → Out₂)
    (env : EnvironmentSequence In₁ In₂) where
  recurrent :
    GraphBothRecurrent (fun n ↦ (env n).graph) →
      A.FiniteGlobalMachineEpochCoupling G outputOne outputTwo env
  alternatingTail :
    PersistentStrictReversalTail (fun n ↦ (env n).graph) →
      ∃ start : Nat, NatSeqMinEvenParity
        (fun n ↦ A.priority
          (A.run (G.globalMachineTraceWord outputOne outputTwo env)
            (start + n)))
  strictRightTail :
    EventuallyStrictRight (fun n ↦ (env n).graph) →
      ∃ start : Nat, NatSeqMinEvenParity
        (fun n ↦ A.priority
          (A.run (G.globalMachineTraceWord outputOne outputTwo env)
            (start + n)))
  strictLeftTail :
    EventuallyStrictLeft (fun n ↦ (env n).graph) →
      ∃ start : Nat, NatSeqMinEvenParity
        (fun n ↦ A.priority
          (A.run (G.globalMachineTraceWord outputOne outputTwo env)
            (start + n)))

/-- The four physical regimes exhaust all environments, so the model-facing
package implies acceptance.  No additional omega-combinatorial obligation
remains after this theorem. -/
theorem finiteGlobalMachineTraceWord_accepts_of_physicalAcceptance
    (G : FiniteGlobalRoundMachine.{u, v, w} In₁ In₂)
    (outputOne : G.State → Out₁) (outputTwo : G.State → Out₂)
    (env : EnvironmentSequence In₁ In₂)
    (physical :
      A.FiniteGlobalMachinePhysicalAcceptance G outputOne outputTwo env) :
    A.Accepts (G.globalMachineTraceWord outputOne outputTwo env) := by
  rcases environment_physical_acceptance_regime env with
    hboth | halternating | hright | hleft
  · exact A.finiteGlobalMachineTraceWord_accepts_of_epochCoupling G outputOne
      outputTwo env (physical.recurrent hboth)
  · rcases physical.alternatingTail halternating with ⟨start, htail⟩
    exact A.finiteGlobalMachineTraceWord_accepts_of_tailParity G outputOne
      outputTwo env start htail
  · rcases physical.strictRightTail hright with ⟨start, htail⟩
    exact A.finiteGlobalMachineTraceWord_accepts_of_tailParity G outputOne
      outputTwo env start htail
  · rcases physical.strictLeftTail hleft with ⟨start, htail⟩
    exact A.finiteGlobalMachineTraceWord_accepts_of_tailParity G outputOne
      outputTwo env start htail

/-! ## Strategy-indexed endpoint -/

variable [Fintype In₁] [Fintype In₂]
variable [Inhabited Out₁] [Inhabited Out₂]

/-- The exact model-facing strategy-indexed endpoint after the physical
acceptance split.  The construction may depend on the supplied winning
strategy.  Its finite global machine must have locally uniform reachable
beliefs, while the four-regime acceptance package is supplied separately for
each environment.

The winning premise is intentionally available to the construction but does
not occur as an opaque acceptance field: all acceptance of the constructed
physical word passes through `FiniteGlobalMachinePhysicalAcceptance`. -/
def PerStrategyWinningFiniteGlobalPhysicalAcceptance : Prop :=
  ∀ strategy : StrategyPair In₁ In₂ Out₁ Out₂,
    (∀ environment : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy environment)) →
      ∃ (G : FiniteGlobalRoundMachine.{u, v, w} In₁ In₂)
        (outputOne : G.State → Out₁)
        (outputTwo : G.State → Out₂),
        G.ReachableBeliefsUniform outputOne outputTwo ∧
          ∀ environment : EnvironmentSequence In₁ In₂,
            Nonempty
              (A.FiniteGlobalMachinePhysicalAcceptance G outputOne outputTwo
                environment)

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- Reachable-belief locality and the four physical acceptance regimes give
the generic finite-global belief-machine package in one arrow. -/
theorem perStrategyWinningFiniteGlobalBeliefMachine_of_physicalAcceptance
    (fallback : LocalSummaryAutomaton.{u, v, w} In₁ In₂)
    (hextract :
      PerStrategyWinningFiniteGlobalPhysicalAcceptance.{u, v, w, x, y, s}
        A) :
    PerStrategyWinningFiniteGlobalBeliefMachine A fallback := by
  intro strategy hwin
  obtain ⟨G, outputOne, outputTwo, huniform, hphysical⟩ :=
    hextract strategy hwin
  refine ⟨G, outputOne, outputTwo, huniform, ?_⟩
  intro environment
  obtain ⟨physical⟩ := hphysical environment
  exact A.finiteGlobalMachineTraceWord_accepts_of_physicalAcceptance G
    outputOne outputTwo environment physical

end DetParityAutomaton

end DistributedSynthesis
