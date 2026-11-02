/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonTailEventualStrictCut

/-!
# Proof-side execution shapes for the guarded common tail

A graph word has only three relevant asymptotic shapes for the common-tail
construction: it is eventually strict right, it is eventually strict left,
or synchronization/change events occur arbitrarily late.  Here a renewal is
either a simultaneous round or a change immediately after the current round.

This classification is wholly proof-side.  In particular, none of the local
transition maps is given the eventual side, a renewal flag, a leader bit, or
the physical graph.  The final integration theorem consumes actual reached
common-cut certificates in the two fixed cases and leaves exactly the
recurrent-renewal case to the switching invariant.
-/

namespace DistributedSynthesis

universe u v x y s

/-! ## The graph-word trichotomy -/

/-- A proof-side renewal point: the current round synchronizes both
processes, or the next round changes the physical graph. -/
def GraphRenewalAt (graphs : Nat → Graph) (n : Nat) : Prop :=
  graphs n = .both ∨ graphs (n + 1) ≠ graphs n

/-- Synchronization/change points occur at arbitrarily late positions. -/
def GraphRenewalRecurrent (graphs : Nat → Graph) : Prop :=
  ∀ start : Nat, ∃ n : Nat, start ≤ n ∧ GraphRenewalAt graphs n

/-- If renewals stop, the graph is eventually one fixed strict direction.
The proof only analyzes the graph word; it constructs no executable side
test. -/
theorem eventuallyStrict_of_not_graphRenewalRecurrent
    (graphs : Nat → Graph) (hrenew : ¬ GraphRenewalRecurrent graphs) :
    EventuallyStrictRight graphs ∨ EventuallyStrictLeft graphs := by
  classical
  simp only [GraphRenewalRecurrent] at hrenew
  push Not at hrenew
  rcases hrenew with ⟨start, hstart⟩
  have hnotBoth : graphs start ≠ .both := by
    intro hboth
    exact hstart start le_rfl (Or.inl hboth)
  have hconst : ∀ n : Nat, start ≤ n → graphs n = graphs start := by
    intro n hn
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
    induction k with
    | zero => rfl
    | succ k ih =>
        have hsame : graphs (start + k + 1) = graphs (start + k) := by
          by_contra hne
          exact hstart (start + k) (by omega) (Or.inr hne)
        rw [Nat.add_succ]
        exact hsame.trans (ih (by omega))
  cases hgraph : graphs start with
  | left =>
      exact Or.inr ⟨start, fun n hn ↦ (hconst n hn).trans hgraph⟩
  | right =>
      exact Or.inl ⟨start, fun n hn ↦ (hconst n hn).trans hgraph⟩
  | both => exact False.elim (hnotBoth hgraph)

/-- An eventually fixed right tail has no arbitrarily late renewals. -/
theorem not_graphRenewalRecurrent_of_eventuallyStrictRight
    {graphs : Nat → Graph} (hstrict : EventuallyStrictRight graphs) :
    ¬ GraphRenewalRecurrent graphs := by
  rcases hstrict with ⟨start, hstart⟩
  intro hrenew
  rcases hrenew start with ⟨n, hn, hpoint⟩
  have hnRight := hstart n hn
  have hnNextRight := hstart (n + 1) (by omega)
  rcases hpoint with hboth | hchange
  · rw [hnRight] at hboth
    cases hboth
  · exact hchange (hnNextRight.trans hnRight.symm)

/-- Left mirror. -/
theorem not_graphRenewalRecurrent_of_eventuallyStrictLeft
    {graphs : Nat → Graph} (hstrict : EventuallyStrictLeft graphs) :
    ¬ GraphRenewalRecurrent graphs := by
  rcases hstrict with ⟨start, hstart⟩
  intro hrenew
  rcases hrenew start with ⟨n, hn, hpoint⟩
  have hnLeft := hstart n hn
  have hnNextLeft := hstart (n + 1) (by omega)
  rcases hpoint with hboth | hchange
  · rw [hnLeft] at hboth
    cases hboth
  · exact hchange (hnNextLeft.trans hnLeft.symm)

/-- Exact complement form of the execution-shape split. -/
theorem graphRenewalRecurrent_iff_not_eventuallyStrict
    (graphs : Nat → Graph) :
    GraphRenewalRecurrent graphs ↔
      ¬ EventuallyStrictRight graphs ∧ ¬ EventuallyStrictLeft graphs := by
  constructor
  · intro hrenew
    exact ⟨fun hright ↦
      not_graphRenewalRecurrent_of_eventuallyStrictRight hright hrenew,
      fun hleft ↦
        not_graphRenewalRecurrent_of_eventuallyStrictLeft hleft hrenew⟩
  · rintro ⟨hnotRight, hnotLeft⟩
    by_contra hnotRenew
    rcases eventuallyStrict_of_not_graphRenewalRecurrent graphs hnotRenew with
      hright | hleft
    · exact hnotRight hright
    · exact hnotLeft hleft

/-- Every graph word is eventually fixed strict right, eventually fixed
strict left, or has arbitrarily late synchronization/change points. -/
theorem graph_eventuallyStrictRight_or_eventuallyStrictLeft_or_renewalRecurrent
    (graphs : Nat → Graph) :
    EventuallyStrictRight graphs ∨ EventuallyStrictLeft graphs ∨
      GraphRenewalRecurrent graphs := by
  classical
  by_cases hrenew : GraphRenewalRecurrent graphs
  · exact Or.inr (Or.inr hrenew)
  · rcases eventuallyStrict_of_not_graphRenewalRecurrent graphs hrenew with
      hright | hleft
    · exact Or.inl hright
    · exact Or.inr (Or.inl hleft)

/-! ## Compatibility with the established four physical regimes -/

/-- Recurrent simultaneous rounds are recurrent renewal points. -/
theorem graphRenewalRecurrent_of_graphBothRecurrent
    {graphs : Nat → Graph} (hboth : GraphBothRecurrent graphs) :
    GraphRenewalRecurrent graphs := by
  intro start
  rcases hboth start with ⟨n, hn, hgraph⟩
  exact ⟨n, hn, Or.inl hgraph⟩

/-- A persistent strict-reversal tail also has recurrent renewals. -/
theorem graphRenewalRecurrent_of_persistentStrictReversalTail
    {graphs : Nat → Graph} (hreversal : PersistentStrictReversalTail graphs) :
    GraphRenewalRecurrent graphs := by
  rw [graphRenewalRecurrent_iff_not_eventuallyStrict]
  constructor
  · rintro ⟨start, hright⟩
    rcases hreversal.2.1 start with ⟨n, hn, hleft⟩
    rw [hright n hn] at hleft
    cases hleft
  · rintro ⟨start, hleft⟩
    rcases hreversal.2.2 start with ⟨n, hn, hright⟩
    rw [hleft n hn] at hright
    cases hright

/-- On a physical environment, the renewal branch is exactly the union of
the two non-fixed regimes from the established four-way split. -/
theorem environment_hard_regime_of_graphRenewalRecurrent
    {In₁ : Type u} {In₂ : Type v}
    (env : EnvironmentSequence In₁ In₂)
    (hrenew : GraphRenewalRecurrent (fun n ↦ (env n).graph)) :
    GraphBothRecurrent (fun n ↦ (env n).graph) ∨
      PersistentStrictReversalTail (fun n ↦ (env n).graph) := by
  rcases environment_physical_acceptance_regime env with
    hboth | hreversal | hright | hleft
  · exact Or.inl hboth
  · exact Or.inr hreversal
  · exact False.elim
      (not_graphRenewalRecurrent_of_eventuallyStrictRight hright hrenew)
  · exact False.elim
      (not_graphRenewalRecurrent_of_eventuallyStrictLeft hleft hrenew)

/-! ## Cut-backed fixed branches -/

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
  (initialBank : ProfiledRawJointInitialControllerBank A strategy)

private abbrev CommonControl :=
  ProfiledRawJointGuardedInitialCommonControl A strategy hwin

private abbrev TailKernel (kernelRoot : CommonControl A strategy hwin) :=
  profiledRawJointGuardedCommonTailCoreKernel A strategy hwin initialBank
    kernelRoot

private abbrev TailWord
    (kernelRoot : CommonControl A strategy hwin)
    (physicalEnv : EnvironmentSequence In₁ In₂) :=
  (TailKernel A strategy hwin initialBank kernelRoot).globalMachine.globalMachineTraceWord
    (TailKernel A strategy hwin initialBank kernelRoot).globalOutputOne
    (TailKernel A strategy hwin initialBank kernelRoot).globalOutputTwo
    physicalEnv

/-- The outer reachable invariant only has to provide a represented common
cut when the proof-side graph word is eventually fixed.  The local machine
does not receive either implication or the side selected by it. -/
structure ProfiledRawJointGuardedCommonTailFixedCutCoverage
    (kernelRoot : CommonControl A strategy hwin)
    (physicalEnv : EnvironmentSequence In₁ In₂) where
  right :
    EventuallyStrictRight (fun n ↦ (physicalEnv n).graph) →
      ProfiledRawJointGuardedCommonTailEventuallyStrictRightCut A strategy
        hwin initialBank kernelRoot physicalEnv
  left :
    EventuallyStrictLeft (fun n ↦ (physicalEnv n).graph) →
      ProfiledRawJointGuardedCommonTailEventuallyStrictLeftCut A strategy
        hwin initialBank kernelRoot physicalEnv

/-- Cut coverage closes the eventual-right branch by the already verified
physical-word splice. -/
theorem ProfiledRawJointGuardedCommonTailFixedCutCoverage.accepts_right
    {kernelRoot : CommonControl A strategy hwin}
    {physicalEnv : EnvironmentSequence In₁ In₂}
    (coverage : ProfiledRawJointGuardedCommonTailFixedCutCoverage A strategy
      hwin initialBank kernelRoot physicalEnv)
    (hstrict : EventuallyStrictRight (fun n ↦ (physicalEnv n).graph)) :
    A.Accepts (TailWord A strategy hwin initialBank kernelRoot physicalEnv) :=
  (coverage.right hstrict).accepts A strategy hwin initialBank

/-- Cut-backed eventual-left mirror. -/
theorem ProfiledRawJointGuardedCommonTailFixedCutCoverage.accepts_left
    {kernelRoot : CommonControl A strategy hwin}
    {physicalEnv : EnvironmentSequence In₁ In₂}
    (coverage : ProfiledRawJointGuardedCommonTailFixedCutCoverage A strategy
      hwin initialBank kernelRoot physicalEnv)
    (hstrict : EventuallyStrictLeft (fun n ↦ (physicalEnv n).graph)) :
    A.Accepts (TailWord A strategy hwin initialBank kernelRoot physicalEnv) :=
  (coverage.left hstrict).accepts A strategy hwin initialBank

/-- Once fixed-tail cut coverage is available, either the complete physical
word is already accepted or renewals occur arbitrarily late.  This is the
three-shape handoff used by the global switching proof. -/
theorem
    profiledRawJointGuardedCommonTail_accepts_or_graphRenewalRecurrent
    (kernelRoot : CommonControl A strategy hwin)
    (physicalEnv : EnvironmentSequence In₁ In₂)
    (coverage : ProfiledRawJointGuardedCommonTailFixedCutCoverage A strategy
      hwin initialBank kernelRoot physicalEnv) :
    A.Accepts (TailWord A strategy hwin initialBank kernelRoot physicalEnv) ∨
      GraphRenewalRecurrent (fun n ↦ (physicalEnv n).graph) := by
  rcases
      graph_eventuallyStrictRight_or_eventuallyStrictLeft_or_renewalRecurrent
        (fun n ↦ (physicalEnv n).graph) with hright | hleft | hrenew
  · exact Or.inl (coverage.accepts_right A strategy hwin initialBank hright)
  · exact Or.inl (coverage.accepts_left A strategy hwin initialBank hleft)
  · exact Or.inr hrenew

/-- Final one-arrow assembly: the two fixed branches are discharged by their
actual common cuts, so the caller supplies acceptance only for recurrent
renewals. -/
theorem profiledRawJointGuardedCommonTail_accepts_of_fixedCuts_of_renewals
    (kernelRoot : CommonControl A strategy hwin)
    (physicalEnv : EnvironmentSequence In₁ In₂)
    (coverage : ProfiledRawJointGuardedCommonTailFixedCutCoverage A strategy
      hwin initialBank kernelRoot physicalEnv)
    (renewalAcceptance :
      GraphRenewalRecurrent (fun n ↦ (physicalEnv n).graph) →
        A.Accepts
          (TailWord A strategy hwin initialBank kernelRoot physicalEnv)) :
    A.Accepts (TailWord A strategy hwin initialBank kernelRoot physicalEnv) := by
  rcases profiledRawJointGuardedCommonTail_accepts_or_graphRenewalRecurrent A
    strategy hwin initialBank kernelRoot physicalEnv coverage with
    haccepts | hrenew
  · exact haccepts
  · exact renewalAcceptance hrenew

/-- Variant aligned with the repository's established physical split.  The
only non-fixed obligations are recurrent `.both` and the persistent strict
reversal tail; the eventual fixed sides are closed from cut coverage. -/
theorem
    profiledRawJointGuardedCommonTail_accepts_of_fixedCuts_of_hardRegimes
    (kernelRoot : CommonControl A strategy hwin)
    (physicalEnv : EnvironmentSequence In₁ In₂)
    (coverage : ProfiledRawJointGuardedCommonTailFixedCutCoverage A strategy
      hwin initialBank kernelRoot physicalEnv)
    (bothAcceptance :
      GraphBothRecurrent (fun n ↦ (physicalEnv n).graph) →
        A.Accepts
          (TailWord A strategy hwin initialBank kernelRoot physicalEnv))
    (reversalAcceptance :
      PersistentStrictReversalTail (fun n ↦ (physicalEnv n).graph) →
        A.Accepts
          (TailWord A strategy hwin initialBank kernelRoot physicalEnv)) :
    A.Accepts (TailWord A strategy hwin initialBank kernelRoot physicalEnv) := by
  apply profiledRawJointGuardedCommonTail_accepts_of_fixedCuts_of_renewals A
    strategy hwin initialBank kernelRoot physicalEnv coverage
  intro hrenew
  rcases environment_hard_regime_of_graphRenewalRecurrent physicalEnv hrenew
    with hboth | hreversal
  · exact bothAcceptance hboth
  · exact reversalAcceptance hreversal

end

end DetParityAutomaton

end DistributedSynthesis
