/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmStarSynthesis
import DistributedSynthesis.Formalizations.Lemma.LemReadbackUpgradeReduction

/-!
# Hosting finite local-summary strategies in the star game

An arbitrary distributed strategy cannot in general be replayed inside the
star game: after a receive, its unbounded private view is not part of the star
state.  A finite local-summary strategy has exactly the missing property.  Its
private summary is the star private control; a blind round applies
`stepNoRecv`, and a receiving round applies `stepRecv` to the two pre-round
summaries delivered to the star plan.

The resulting constant star plans reproduce the local-summary readback word
on every environment.  Consequently a `LocalSummaryAutomaton.ReadbackUpgrade`
supplies a `StarFoldPackage` directly.  This bypasses the stronger
`MeasurableJournalExtraction`: journal measurability remains a useful
standalone statement, but it is not required by the star decision route.
-/

namespace DistributedSynthesis

universe u

variable {In₁ In₂ Out₁ Out₂ : Type u}

namespace DetParityAutomaton

variable
  (A : DetParityAutomaton.{u, u}
    (RoundRecord In₁ In₂ Graph Out₁ Out₂))
  (M : LocalSummaryAutomaton.{u, u, u} In₁ In₂)

/-- Process one's local-summary program as one constant star plan. -/
def summaryStarPlanOne
    (outputOne : M.Summary Proc.one -> Out₁) :
    StarPlanOne (In₁ := In₁) (In₂ := In₂) A
      (M.Summary Proc.one) (M.Summary Proc.two) where
  init := M.initial Proc.one
  enter := fun own other _core move =>
    M.stepRecv Proc.one own (.inl move.1) other (.inr move.2)
  step := fun own inputOne =>
    M.stepNoRecv Proc.one own (.inl inputOne)
  recv := fun own other _core move =>
    outputOne (M.stepRecv Proc.one own (.inl move.1) other (.inr move.2))
  blind := fun own inputOne =>
    outputOne (M.stepNoRecv Proc.one own (.inl inputOne))

/-- Process two's local-summary program as one constant star plan. -/
def summaryStarPlanTwo
    (outputTwo : M.Summary Proc.two -> Out₂) :
    StarPlanTwo (In₁ := In₁) (In₂ := In₂) A
      (M.Summary Proc.one) (M.Summary Proc.two) where
  init := M.initial Proc.two
  enter := fun own other _core move =>
    M.stepRecv Proc.two own (.inr move.1) other (.inl move.2)
  step := fun own inputTwo =>
    M.stepNoRecv Proc.two own (.inr inputTwo)
  recv := fun own other _core move =>
    outputTwo (M.stepRecv Proc.two own (.inr move.1) other (.inl move.2))
  blind := fun own inputTwo =>
    outputTwo (M.stepNoRecv Proc.two own (.inr inputTwo))

section Correspondence

variable [Inhabited Out₁] [Inhabited Out₂]
variable (outputOne : M.Summary Proc.one -> Out₁)
variable (outputTwo : M.Summary Proc.two -> Out₂)

private abbrev p₁ :
    Nat -> StarPlanOne (In₁ := In₁) (In₂ := In₂) A
      (M.Summary Proc.one) (M.Summary Proc.two) :=
  fun _ => summaryStarPlanOne A M outputOne

private abbrev p₂ :
    Nat -> StarPlanTwo (In₁ := In₁) (In₂ := In₂) A
      (M.Summary Proc.one) (M.Summary Proc.two) :=
  fun _ => summaryStarPlanTwo A M outputTwo

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- Along every concrete history, the two star private controls are exactly
the summaries read from the two current views.  `getD` handles the empty
history, where the star stores `none` and the summary fold is at `initial`. -/
theorem summaryStarControl_currentView
    (h : History In₁ In₂ Graph Out₁ Out₂) :
    ((wAfterOne A (p₁ A M outputOne) (p₂ A M outputTwo)
        (currentView Proc.one h)).getD (M.initial Proc.one) =
      M.read (currentView Proc.one h)) ∧
    ((wAfterTwo A (p₁ A M outputOne) (p₂ A M outputTwo)
        (currentView Proc.two h)).getD (M.initial Proc.two) =
      M.read (currentView Proc.two h)) := by
  induction h using List.reverseRecOn with
  | nil =>
      simp [currentView, viewPair, wAfterOne, wAfterTwo, starControlAfter]
      exact ⟨Option.getD_none, Option.getD_none⟩
  | append_singleton h round ih =>
      have ihOne :
          ((starControlAfter A (p₁ A M outputOne) (p₂ A M outputTwo)
              (currentView Proc.one h)).getD (M.initial Proc.one)) =
            M.read (currentView Proc.one h) := by
        simpa only [wAfterOne] using ih.1
      have ihTwo :
          ((starControlAfter A (p₁ A M outputOne) (p₂ A M outputTwo)
              (currentView Proc.two h)).getD (M.initial Proc.two)) =
            M.read (currentView Proc.two h) := by
        simpa only [wAfterTwo] using ih.2
      rw [show h ++ [round] = History.append h round from rfl,
        currentView_one_append, currentView_two_append]
      cases hg : round.graph
      · constructor
        · simp [wAfterOne, starControlAfter,
            p₁, p₂, summaryStarPlanOne, summaryStarPlanTwo]
          exact Option.getD_some.trans (congrArg₂
            (fun own other => M.stepRecv Proc.one own (.inl round.inputOne)
              other (.inr round.inputTwo)) ihOne ihTwo)
        · simp [wAfterTwo, starControlAfter,
            p₂, summaryStarPlanTwo]
          exact Option.getD_some.trans (congrArg
            (fun own => M.stepNoRecv Proc.two own (.inr round.inputTwo)) ihTwo)
      · constructor
        · simp [wAfterOne, starControlAfter,
            p₁, summaryStarPlanOne]
          exact Option.getD_some.trans (congrArg
            (fun own => M.stepNoRecv Proc.one own (.inl round.inputOne)) ihOne)
        · simp [wAfterTwo, starControlAfter,
            p₁, p₂, summaryStarPlanOne, summaryStarPlanTwo]
          exact Option.getD_some.trans (congrArg₂
            (fun own other => M.stepRecv Proc.two own (.inr round.inputTwo)
              other (.inl round.inputOne)) ihTwo ihOne)
      · constructor
        · simp [wAfterOne, starControlAfter,
            p₁, p₂, summaryStarPlanOne, summaryStarPlanTwo]
          exact Option.getD_some.trans (congrArg₂
            (fun own other => M.stepRecv Proc.one own (.inl round.inputOne)
              other (.inr round.inputTwo)) ihOne ihTwo)
        · simp [wAfterTwo, starControlAfter,
            p₁, p₂, summaryStarPlanOne, summaryStarPlanTwo]
          exact Option.getD_some.trans (congrArg₂
            (fun own other => M.stepRecv Proc.two own (.inr round.inputTwo)
              other (.inl round.inputOne)) ihTwo ihOne)

/-- On the next concrete view of process one, the hosted star plan emits the
same output as the local-summary readback table. -/
theorem summaryStarReadback_nextView_one
    (h : History In₁ In₂ Graph Out₁ Out₂)
    (round : EnvironmentRound In₁ In₂) :
    (starReadback A (p₁ A M outputOne) (p₂ A M outputTwo)).one
        (nextView Proc.one h round) =
      (M.readbackStrategy outputOne outputTwo).one
        (nextView Proc.one h round) := by
  have hc := summaryStarControl_currentView (A := A) M outputOne outputTwo h
  have hcOne :
      ((wAfterOne A (p₁ A M outputOne) (p₂ A M outputTwo)
          (viewPair h).1).getD (M.initial Proc.one)) =
        M.read (viewPair h).1 := by
    simpa only [currentView] using hc.1
  have hcTwo :
      ((wAfterTwo A (p₁ A M outputOne) (p₂ A M outputTwo)
          (viewPair h).2).getD (M.initial Proc.two)) =
        M.read (viewPair h).2 := by
    simpa only [currentView] using hc.2
  cases hg : round.graph <;>
    simp [starReadback, nextView, advanceViewsWithEnvironment, hg,
      p₁, p₂, summaryStarPlanOne, summaryStarPlanTwo,
      LocalSummaryAutomaton.readbackStrategy] <;>
    simp only [hcOne, hcTwo] <;> rfl

/-- Process-two mirror of `summaryStarReadback_nextView_one`. -/
theorem summaryStarReadback_nextView_two
    (h : History In₁ In₂ Graph Out₁ Out₂)
    (round : EnvironmentRound In₁ In₂) :
    (starReadback A (p₁ A M outputOne) (p₂ A M outputTwo)).two
        (nextView Proc.two h round) =
      (M.readbackStrategy outputOne outputTwo).two
        (nextView Proc.two h round) := by
  have hc := summaryStarControl_currentView (A := A) M outputOne outputTwo h
  have hcOne :
      ((wAfterOne A (p₁ A M outputOne) (p₂ A M outputTwo)
          (viewPair h).1).getD (M.initial Proc.one)) =
        M.read (viewPair h).1 := by
    simpa only [currentView] using hc.1
  have hcTwo :
      ((wAfterTwo A (p₁ A M outputOne) (p₂ A M outputTwo)
          (viewPair h).2).getD (M.initial Proc.two)) =
        M.read (viewPair h).2 := by
    simpa only [currentView] using hc.2
  cases hg : round.graph <;>
    simp [starReadback, nextView, advanceViewsWithEnvironment, hg,
      p₁, p₂, summaryStarPlanOne, summaryStarPlanTwo,
      LocalSummaryAutomaton.readbackStrategy] <;>
    simp only [hcOne, hcTwo] <;> rfl

/-- The two strategies choose the same complete next-round record after every
concrete history. -/
theorem nextRound_summaryStarReadback
    (h : History In₁ In₂ Graph Out₁ Out₂)
    (round : EnvironmentRound In₁ In₂) :
    nextRound (starReadback A (p₁ A M outputOne) (p₂ A M outputTwo)) h round =
      nextRound (M.readbackStrategy outputOne outputTwo) h round := by
  simp only [nextRound]
  rw [summaryStarReadback_nextView_one (A := A) M outputOne outputTwo h round,
    summaryStarReadback_nextView_two (A := A) M outputOne outputTwo h round]

/-- Exact word equality: constant star plans host every finite local-summary
readback strategy on every environment. -/
theorem execution_summaryStarReadback_eq
    (env : EnvironmentSequence In₁ In₂) :
    execution (starReadback A (p₁ A M outputOne) (p₂ A M outputTwo)) env =
      execution (M.readbackStrategy outputOne outputTwo) env := by
  have hprefix : ∀ n : Nat,
      executionPrefix
          (starReadback A (p₁ A M outputOne) (p₂ A M outputTwo)) env n =
        executionPrefix (M.readbackStrategy outputOne outputTwo) env n := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
        rw [executionPrefix_succ, executionPrefix_succ, ih,
          nextRound_summaryStarReadback A M outputOne outputTwo]
  funext n
  rw [execution_apply, execution_apply, hprefix n,
    nextRound_summaryStarReadback A M outputOne outputTwo]

end Correspondence

section Package

variable [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
variable [DecidableEq In₁] [DecidableEq In₂]
variable [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]

/-- A finite local-summary measurability upgrade supplies the star fold
directly.  This is the precise replacement for the stronger journal-package
extraction in the star route. -/
noncomputable def starFoldPackageOfReadbackUpgrade
    (hupgrade : M.ReadbackUpgrade (Out₁ := Out₁) (Out₂ := Out₂) A) :
    StarFoldPackage A := by
  classical
  refine
    { W₁ := M.Summary Proc.one
      W₂ := M.Summary Proc.two
      fintypeOne := M.finite Proc.one
      decidableEqOne := Classical.decEq _
      inhabitedOne := ⟨M.initial Proc.one⟩
      fintypeTwo := M.finite Proc.two
      decidableEqTwo := Classical.decEq _
      inhabitedTwo := ⟨M.initial Proc.two⟩
      fold := ?_ }
  rintro ⟨σ, hσ⟩
  obtain ⟨outputOne, outputTwo, houtputs⟩ := hupgrade σ hσ
  refine
    ⟨fun _ => summaryStarPlanOne A M outputOne,
      fun _ => summaryStarPlanTwo A M outputTwo, ?_⟩
  intro env
  rw [execution_summaryStarReadback_eq A M outputOne outputTwo env]
  exact houtputs env

/-- Existential finite-summary extraction is sufficient; the summary
automaton may be chosen separately for each objective automaton. -/
noncomputable def starFoldPackageOfExistsReadbackUpgrade
    (hextract :
      ∃ M : LocalSummaryAutomaton.{u, u, u} In₁ In₂,
        M.ReadbackUpgrade (Out₁ := Out₁) (Out₂ := Out₂) A) :
    StarFoldPackage A := by
  classical
  let M' := Classical.choose hextract
  exact starFoldPackageOfReadbackUpgrade A M'
    (Classical.choose_spec hextract)

/-- The star fold now consumes the finite-summary winner obligation
through the already checked extraction to `ReadbackUpgrade`. -/
noncomputable def starFoldPackageOfSummaryObservableWinner
    (hcert : SummaryObservableWinnerCertificate A M) :
    StarFoldPackage A :=
  starFoldPackageOfReadbackUpgrade A M
    (readbackUpgrade_of_summaryObservableWinner A M hcert)

/-- Direct DPA synthesis from a finite local-summary upgrade.  This uses the
constant-observation star solver and does not consume the journal extraction
or the older epoch backend. -/
noncomputable def synthesisDecidable_direct_ofReadbackUpgrade
    (hupgrade : M.ReadbackUpgrade (Out₁ := Out₁) (Out₂ := Out₂) A) :
    Decidable
      (∃ σ : StrategyPair In₁ In₂ Out₁ Out₂,
        ∀ env : EnvironmentSequence In₁ In₂,
          A.Accepts (execution σ env)) := by
  classical
  exact (starFoldPackageOfReadbackUpgrade A M hupgrade).synthesisDecidable_direct

/-- Direct DPA synthesis from the literature-shaped finite-game certificate. -/
noncomputable def synthesisDecidable_direct_ofSummaryObservableWinner
    (hcert : SummaryObservableWinnerCertificate A M) :
    Decidable
      (∃ σ : StrategyPair In₁ In₂ Out₁ Out₂,
        ∀ env : EnvironmentSequence In₁ In₂,
          A.Accepts (execution σ env)) := by
  classical
  exact
    (starFoldPackageOfSummaryObservableWinner A M hcert).synthesisDecidable_direct

end Package

end DetParityAutomaton

end DistributedSynthesis
