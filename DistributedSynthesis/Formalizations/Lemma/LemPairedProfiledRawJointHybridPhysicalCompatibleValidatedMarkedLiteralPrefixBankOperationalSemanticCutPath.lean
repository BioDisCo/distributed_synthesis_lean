/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleValidatedMarkedLiteralPrefixBankOperationalCutPath

/-!
# Semantic payload directions at operational cuts

The finite linked table is a rational narrowing of an infinite semantic
table.  At an arbitrary retained depth its target is therefore known to be a
genuine target at *some* semantic prefix, but that prefix need not be the
literal physical prefix which led to the finite table state.  Consequently
the canonical physical-input direction of `...BankOperationalCutPath` is a
useful graph clock, but is deliberately not claimed to be the direction of
the bank child.

This file gives the exact interface which the linked controller supplies.
The operational cuts still determine

* the real maximal physical graph block,
* its right/left side, and
* the acknowledged closing row (`.first` for a singleton block and `.both`
  otherwise).

Only the semantic `past` and closing `input` are chosen from the target
payload witness.  The resulting noncanonical schedule is an ordinary
`OperationalCutSchedule`, so all generic cut-to-bank-path and strict-side
alternation theorems apply unchanged.
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

private abbrev BankControl :=
  ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankControl A strategy hwin

private abbrev HybridDirection :=
  ProfiledRawJointHybridDirection (In₁ := In₁) (In₂ := In₂)

private abbrev OperationalSchedule
    (env : EnvironmentSequence In₁ In₂) :=
  ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankOperationalCutSchedule
    (In₁ := In₁) (In₂ := In₂) env

/-! ## The close-payload interface -/

/-- At every completed operational block, the controller's closing payload
is a child of the block-entry bank state.  The graph clock fixes the side and
the canonical acknowledgement row.  The semantic prefix and input are the
existential witnesses exposed by the finite linked table.

Unlike the former physical-input formulation, this statement is stable under
rational table narrowing: it asks for exactly the data proved by
`RightPairAtPrefix.payload_exists` and its left mirror. -/
def
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankOperationalSemanticCloseWitness
    (env : EnvironmentSequence In₁ In₂)
    (cuts : OperationalCloseCutPackage (fun n ↦ (env n).graph))
    (trace : Nat → BankControl A strategy hwin) : Prop :=
  ∀ k : Nat,
    match (env (cuts.cuts k)).graph with
    | .right =>
        ∃ semanticPast : List (In₂ × In₁), ∃ semanticInput : In₂ × In₁,
          trace (cuts.cuts (k + 1)) =
            profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildren A
              strategy hwin (trace (cuts.cuts k))
                (.strict
                  (profiledRawJointUnitRightActualDirection
                    (In₁ := In₁) (In₂ := In₂)
                    (OperationalCloseCutPackage.bankOperationalRowAt cuts k)
                    semanticPast semanticInput))
    | .left =>
        ∃ semanticPast : List (In₁ × In₂), ∃ semanticInput : In₁ × In₂,
          trace (cuts.cuts (k + 1)) =
            profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildren A
              strategy hwin (trace (cuts.cuts k))
                (.strict
                  (profiledRawJointUnitLeftActualDirection
                    (In₁ := In₁) (In₂ := In₂)
                    (OperationalCloseCutPackage.bankOperationalRowAt cuts k)
                    semanticPast semanticInput))
    | .both =>
        trace (cuts.cuts (k + 1)) =
          profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildren A
            strategy hwin (trace (cuts.cuts k))
              (.simultaneous
                ((env (cuts.cuts k)).inputOne,
                  (env (cuts.cuts k)).inputTwo))

/-! ## Choosing the proof-side direction -/

theorem
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankOperationalSemanticCloseWitness.right
    {env : EnvironmentSequence In₁ In₂}
    {cuts : OperationalCloseCutPackage (fun n ↦ (env n).graph)}
    {trace : Nat → BankControl A strategy hwin}
    (hclose :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankOperationalSemanticCloseWitness
        A strategy hwin env cuts trace)
    (k : Nat) (hgraph : (env (cuts.cuts k)).graph = .right) :
    ∃ semanticPast : List (In₂ × In₁), ∃ semanticInput : In₂ × In₁,
      trace (cuts.cuts (k + 1)) =
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildren A
          strategy hwin (trace (cuts.cuts k))
            (.strict
              (profiledRawJointUnitRightActualDirection
                (In₁ := In₁) (In₂ := In₂)
                (OperationalCloseCutPackage.bankOperationalRowAt cuts k)
                semanticPast semanticInput)) := by
  simpa [
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankOperationalSemanticCloseWitness,
    hgraph] using hclose k

theorem
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankOperationalSemanticCloseWitness.left
    {env : EnvironmentSequence In₁ In₂}
    {cuts : OperationalCloseCutPackage (fun n ↦ (env n).graph)}
    {trace : Nat → BankControl A strategy hwin}
    (hclose :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankOperationalSemanticCloseWitness
        A strategy hwin env cuts trace)
    (k : Nat) (hgraph : (env (cuts.cuts k)).graph = .left) :
    ∃ semanticPast : List (In₁ × In₂), ∃ semanticInput : In₁ × In₂,
      trace (cuts.cuts (k + 1)) =
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildren A
          strategy hwin (trace (cuts.cuts k))
            (.strict
              (profiledRawJointUnitLeftActualDirection
                (In₁ := In₁) (In₂ := In₂)
                (OperationalCloseCutPackage.bankOperationalRowAt cuts k)
                semanticPast semanticInput)) := by
  simpa [
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankOperationalSemanticCloseWitness,
    hgraph] using hclose k

theorem
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankOperationalSemanticCloseWitness.both
    {env : EnvironmentSequence In₁ In₂}
    {cuts : OperationalCloseCutPackage (fun n ↦ (env n).graph)}
    {trace : Nat → BankControl A strategy hwin}
    (hclose :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankOperationalSemanticCloseWitness
        A strategy hwin env cuts trace)
    (k : Nat) (hgraph : (env (cuts.cuts k)).graph = .both) :
    trace (cuts.cuts (k + 1)) =
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildren A
        strategy hwin (trace (cuts.cuts k))
          (.simultaneous
            ((env (cuts.cuts k)).inputOne,
              (env (cuts.cuts k)).inputTwo)) := by
  simpa [
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankOperationalSemanticCloseWitness,
    hgraph] using hclose k

/-- The semantic bank direction selected from the closing payload witness.
This is proof-side finite-choice data; it is not supplied to either process. -/
noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankOperationalSemanticDirection
    (env : EnvironmentSequence In₁ In₂)
    (cuts : OperationalCloseCutPackage (fun n ↦ (env n).graph))
    (trace : Nat → BankControl A strategy hwin)
    (hclose :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankOperationalSemanticCloseWitness
        A strategy hwin env cuts trace)
    (k : Nat) : HybridDirection (In₁ := In₁) (In₂ := In₂) :=
  if hright : (env (cuts.cuts k)).graph = .right then
    let hex := hclose.right A strategy hwin k hright
    .strict
      (profiledRawJointUnitRightActualDirection
        (In₁ := In₁) (In₂ := In₂)
        (OperationalCloseCutPackage.bankOperationalRowAt cuts k)
        (Classical.choose hex) (Classical.choose (Classical.choose_spec hex)))
  else if hleft : (env (cuts.cuts k)).graph = .left then
    let hex := hclose.left A strategy hwin k hleft
    .strict
      (profiledRawJointUnitLeftActualDirection
        (In₁ := In₁) (In₂ := In₂)
        (OperationalCloseCutPackage.bankOperationalRowAt cuts k)
        (Classical.choose hex) (Classical.choose (Classical.choose_spec hex)))
  else
    .simultaneous
      ((env (cuts.cuts k)).inputOne, (env (cuts.cuts k)).inputTwo)

/-- Replace only the canonical schedule's over-specific physical direction
by the semantic direction selected from the actual closing payload. -/
noncomputable def
    OperationalCloseCutPackage.toSemanticBankOperationalCutSchedule
    (env : EnvironmentSequence In₁ In₂)
    (cuts : OperationalCloseCutPackage (fun n ↦ (env n).graph))
    (trace : Nat → BankControl A strategy hwin)
    (hclose :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankOperationalSemanticCloseWitness
        A strategy hwin env cuts trace) :
    OperationalSchedule (In₁ := In₁) (In₂ := In₂) env where
  cut := cuts.cuts
  direction :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankOperationalSemanticDirection
      A strategy hwin env cuts trace hclose
  initial := cuts.cuts_zero
  step := by
    intro k
    have hcanonical :=
      (OperationalCloseCutPackage.toCanonicalBankOperationalCutSchedule env
        cuts).step k
    change
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankOperationalCutStep
        env (cuts.cuts k) (cuts.cuts (k + 1)) _ at hcanonical
    cases hgraph : (env (cuts.cuts k)).graph with
    | right =>
        rw [
          ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankOperationalCutStep,
          hgraph] at hcanonical ⊢
        simp only at hcanonical
        refine ⟨hcanonical.1, ?_⟩
        let hex := hclose.right A strategy hwin k hgraph
        let actual :=
          profiledRawJointUnitRightActualDirection
            (In₁ := In₁) (In₂ := In₂)
            (OperationalCloseCutPackage.bankOperationalRowAt cuts k)
            (Classical.choose hex)
            (Classical.choose (Classical.choose_spec hex))
        refine ⟨actual, rfl, ?_⟩
        simp [
          profiledRawJointHybridValidatedMarkedLiteralPrefixBankOperationalSemanticDirection,
          hgraph, actual]
    | left =>
        rw [
          ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankOperationalCutStep,
          hgraph] at hcanonical ⊢
        simp only at hcanonical
        refine ⟨hcanonical.1, ?_⟩
        let hex := hclose.left A strategy hwin k hgraph
        let actual :=
          profiledRawJointUnitLeftActualDirection
            (In₁ := In₁) (In₂ := In₂)
            (OperationalCloseCutPackage.bankOperationalRowAt cuts k)
            (Classical.choose hex)
            (Classical.choose (Classical.choose_spec hex))
        refine ⟨actual, rfl, ?_⟩
        simp [
          profiledRawJointHybridValidatedMarkedLiteralPrefixBankOperationalSemanticDirection,
          hgraph, actual]
    | both =>
        rw [
          ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankOperationalCutStep,
          hgraph] at hcanonical ⊢
        simp only at hcanonical
        refine ⟨hcanonical.1, ?_⟩
        simp [
          profiledRawJointHybridValidatedMarkedLiteralPrefixBankOperationalSemanticDirection,
          hgraph]

/-! ## Exactness and the generic bank path -/

/-- By construction, the semantic-payload schedule satisfies the exact bank
child equation at every completed cut. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankSemanticOperationalCutExact
    (env : EnvironmentSequence In₁ In₂)
    (cuts : OperationalCloseCutPackage (fun n ↦ (env n).graph))
    (trace : Nat → BankControl A strategy hwin)
    (hclose :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankOperationalSemanticCloseWitness
        A strategy hwin env cuts trace) :
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankOperationalCutExact A
      strategy hwin
        (OperationalCloseCutPackage.toSemanticBankOperationalCutSchedule A
          strategy hwin env cuts trace hclose)
        trace := by
  intro k
  cases hgraph : (env (cuts.cuts k)).graph with
  | right =>
      let hex :
          ∃ semanticPast : List (In₂ × In₁), ∃ semanticInput : In₂ × In₁,
            trace (cuts.cuts (k + 1)) =
              profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildren A
                strategy hwin (trace (cuts.cuts k))
                  (.strict
                    (profiledRawJointUnitRightActualDirection
                      (In₁ := In₁) (In₂ := In₂)
                      (OperationalCloseCutPackage.bankOperationalRowAt cuts k)
                      semanticPast semanticInput)) := by
        simpa [
          ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankOperationalSemanticCloseWitness,
          hgraph] using hclose k
      have hexact := Classical.choose_spec (Classical.choose_spec hex)
      simpa [
        OperationalCloseCutPackage.toSemanticBankOperationalCutSchedule,
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankOperationalSemanticDirection,
        hgraph] using hexact
  | left =>
      let hex :
          ∃ semanticPast : List (In₁ × In₂), ∃ semanticInput : In₁ × In₂,
            trace (cuts.cuts (k + 1)) =
              profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildren A
                strategy hwin (trace (cuts.cuts k))
                  (.strict
                    (profiledRawJointUnitLeftActualDirection
                      (In₁ := In₁) (In₂ := In₂)
                      (OperationalCloseCutPackage.bankOperationalRowAt cuts k)
                      semanticPast semanticInput)) := by
        simpa [
          ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankOperationalSemanticCloseWitness,
          hgraph] using hclose k
      have hexact := Classical.choose_spec (Classical.choose_spec hex)
      simpa [
        OperationalCloseCutPackage.toSemanticBankOperationalCutSchedule,
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankOperationalSemanticDirection,
        hgraph] using hexact
  | both =>
      have hk :
          trace (cuts.cuts (k + 1)) =
            profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildren A
              strategy hwin (trace (cuts.cuts k))
                (.simultaneous
                  ((env (cuts.cuts k)).inputOne,
                    (env (cuts.cuts k)).inputTwo)) := by
        simpa [
          ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankOperationalSemanticCloseWitness,
          hgraph] using hclose k
      simpa [
        OperationalCloseCutPackage.toSemanticBankOperationalCutSchedule,
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankOperationalSemanticDirection,
        hgraph] using hk

/-- The corrected close witness can be handed directly to the generic
cut-to-child-run theorem. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankTraceAtSemanticOperationalCuts_eq_childRun
    (env : EnvironmentSequence In₁ In₂)
    (cuts : OperationalCloseCutPackage (fun n ↦ (env n).graph))
    (control : ProfiledRawJointHybridCommonControl A strategy hwin)
    (trace : Nat → BankControl A strategy hwin)
    (hroot : trace 0 =
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankRoot A strategy hwin
        control)
    (hclose :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankOperationalSemanticCloseWitness
        A strategy hwin env cuts trace) :
    ∀ k : Nat,
      trace (cuts.cuts k) =
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildRunControlAt
          A strategy hwin control
            (OperationalCloseCutPackage.toSemanticBankOperationalCutSchedule A
              strategy hwin env cuts trace hclose).direction k := by
  apply
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankTraceAtOperationalCuts_eq_childRun
      A strategy hwin env
        (OperationalCloseCutPackage.toSemanticBankOperationalCutSchedule A
          strategy hwin env cuts trace hclose)
        control trace
  · change trace (cuts.cuts 0) =
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankRoot A strategy hwin
        control
    rw [cuts.cuts_zero]
    exact hroot
  · exact
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankSemanticOperationalCutExact
        A strategy hwin env cuts trace hclose

end

end DetParityAutomaton

end DistributedSynthesis
