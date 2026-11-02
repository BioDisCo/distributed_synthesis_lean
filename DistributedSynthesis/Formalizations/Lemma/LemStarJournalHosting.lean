/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmStarSynthesis
import DistributedSynthesis.Formalizations.Theorem.ThmJournalPlayCorrespondence

/-!
# Hosting measurable journal plans in the star game

The finite controls of the star commitments are the already constructed
candidate-summary cores.  On a receive round both pre-round cores are
available, so the commitment uses `oneRecvStep`/`twoRecvStep`; on a blind
round it uses only the owner's core and `oneNoRecvStep`/`twoNoRecvStep`.

This is the hosting bridge needed before the genuinely paper-specific task of
extracting a measurable accepted plan family from an arbitrary realizer.
-/

namespace DistributedSynthesis

universe u

variable {In₁ In₂ Out₁ Out₂ : Type u}

namespace DetParityAutomaton

variable
  (A : DetParityAutomaton.{u, u}
    (RoundRecord In₁ In₂ Graph Out₁ Out₂))
  (C_L C_R C_V : Type u)

variable
  [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
  [DecidableEq In₁] [DecidableEq In₂] [DecidableEq A.State]
  [Fintype C_L] [DecidableEq C_L] [Fintype C_R] [DecidableEq C_R]
  [Fintype C_V] [DecidableEq C_V]
  [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]
  [Inhabited C_L] [Inhabited C_R] [Inhabited C_V]

variable {A C_L C_R C_V}

/-- Process one's constant star commitment induced by a journal plan family. -/
def journalStarPlanOne
    (plans : PlanFamily (In₁ := In₁) A C_L C_R C_V) :
    StarPlanOne (In₁ := In₁) (In₂ := In₂) A
      (OneCore (In₁ := In₁) A C_L C_R C_V)
      (TwoCore (In₁ := In₁) A C_L C_R C_V) where
  init := Sum.inr (Sum.inl (A.initial, A.initial))
  enter := fun own peer _ move => (oneRecvStep (A := A) plans own move peer).2
  step := fun own input => (oneNoRecvStep (A := A) plans own input).2
  recv := fun own peer _ move => (oneRecvStep (A := A) plans own move peer).1
  blind := fun own input => (oneNoRecvStep (A := A) plans own input).1

/-- Process two's mirror commitment induced by a journal plan family. -/
def journalStarPlanTwo
    (plans : PlanFamily (In₁ := In₁) A C_L C_R C_V) :
    StarPlanTwo (In₁ := In₁) (In₂ := In₂) A
      (OneCore (In₁ := In₁) A C_L C_R C_V)
      (TwoCore (In₁ := In₁) A C_L C_R C_V) where
  init := Sum.inr (Sum.inl (A.initial, A.initial))
  enter := fun own peer _ move =>
    (twoRecvStep (A := A) plans own (move.2, move.1) peer).2
  step := fun own input => (twoNoRecvStep (A := A) plans own input).2
  recv := fun own peer _ move =>
    (twoRecvStep (A := A) plans own (move.2, move.1) peer).1
  blind := fun own input => (twoNoRecvStep (A := A) plans own input).1

/-- The journal commitments do not depend on the round number. -/
def journalStarPlansOne
    (plans : PlanFamily (In₁ := In₁) A C_L C_R C_V) :
    Nat -> StarPlanOne (In₁ := In₁) (In₂ := In₂) A
      (OneCore (In₁ := In₁) A C_L C_R C_V)
      (TwoCore (In₁ := In₁) A C_L C_R C_V) :=
  fun _ => journalStarPlanOne plans

/-- The mirror constant stream. -/
def journalStarPlansTwo
    (plans : PlanFamily (In₁ := In₁) A C_L C_R C_V) :
    Nat -> StarPlanTwo (In₁ := In₁) (In₂ := In₂) A
      (OneCore (In₁ := In₁) A C_L C_R C_V)
      (TwoCore (In₁ := In₁) A C_L C_R C_V) :=
  fun _ => journalStarPlanTwo plans

section
omit [Inhabited C_L] [Inhabited C_R] [Inhabited C_V]

/-- Along every environment, the star arena's private controls are exactly the
core components of the journal summaries. -/
theorem journalStarRun_controls
    (plans : PlanFamily (In₁ := In₁) A C_L C_R C_V)
    (env : EnvironmentSequence In₁ In₂) (n : Nat) :
    (starRun A (journalStarPlansOne plans) (journalStarPlansTwo plans) env n).2.1.getD
        (journalStarPlanOne plans).init = (oneSummaryAt plans env n).2 ∧
      (starRun A (journalStarPlansOne plans) (journalStarPlansTwo plans) env n).2.2.getD
          (journalStarPlanTwo plans).init = (twoSummaryAt plans env n).2 := by
  induction n with
  | zero =>
      constructor <;>
        rfl
  | succ n ih =>
      have ihOne :
          (starRun A (journalStarPlansOne plans) (journalStarPlansTwo plans) env n).2.1.getD
              (Sum.inr (Sum.inl (A.initial, A.initial))) =
            (oneSummaryAt plans env n).2 := by
        simpa only [journalStarPlanOne] using ih.1
      have ihTwo :
          (starRun A (journalStarPlansOne plans) (journalStarPlansTwo plans) env n).2.2.getD
              (Sum.inr (Sum.inl (A.initial, A.initial))) =
            (twoSummaryAt plans env n).2 := by
        simpa only [journalStarPlanTwo] using ih.2
      cases hgraph : (env n).graph
      · constructor
        · rw [oneSummaryAt_succ_left plans env n hgraph]
          simp [starRun, starNext, journalStarPlansOne, journalStarPlansTwo,
            journalStarPlanOne, journalStarPlanTwo, hgraph, ihOne, ihTwo]
        · rw [twoSummaryAt_succ_left plans env n hgraph]
          simp [starRun, starNext, journalStarPlansOne, journalStarPlansTwo,
            journalStarPlanOne, journalStarPlanTwo, hgraph, ihTwo]
      · constructor
        · rw [oneSummaryAt_succ_right plans env n hgraph]
          simp [starRun, starNext, journalStarPlansOne, journalStarPlansTwo,
            journalStarPlanOne, journalStarPlanTwo, hgraph, ihOne]
        · rw [twoSummaryAt_succ_right plans env n hgraph]
          simp [starRun, starNext, journalStarPlansOne, journalStarPlansTwo,
            journalStarPlanOne, journalStarPlanTwo, hgraph, ihOne, ihTwo]
      · constructor
        · rw [oneSummaryAt_succ_both plans env n hgraph]
          simp [starRun, starNext, journalStarPlansOne, journalStarPlansTwo,
            journalStarPlanOne, journalStarPlanTwo, hgraph, ihOne, ihTwo]
        · rw [twoSummaryAt_succ_both plans env n hgraph]
          simp [starRun, starNext, journalStarPlansOne, journalStarPlansTwo,
            journalStarPlanOne, journalStarPlanTwo, hgraph, ihOne, ihTwo]

/-- The record emitted by the hosted star run is the record emitted by the
journal readback strategy in the same round. -/
theorem journalStarRecord_eq_execution
    (plans : PlanFamily (In₁ := In₁) A C_L C_R C_V)
    (env : EnvironmentSequence In₁ In₂) (n : Nat) :
    starRecord A
        (starRun A (journalStarPlansOne plans) (journalStarPlansTwo plans) env n)
        (journalStarPlanOne plans) (journalStarPlanTwo plans) (env n) =
      execution (journalStrategy plans) env n := by
  rw [execution_journal_apply]
  have hcontrols := journalStarRun_controls plans env n
  have hOne :
      (starRun A (journalStarPlansOne plans) (journalStarPlansTwo plans) env n).2.1.getD
          (Sum.inr (Sum.inl (A.initial, A.initial))) =
        (oneSummaryAt plans env n).2 := by
    simpa only [journalStarPlanOne] using hcontrols.1
  have hTwo :
      (starRun A (journalStarPlansOne plans) (journalStarPlansTwo plans) env n).2.2.getD
          (Sum.inr (Sum.inl (A.initial, A.initial))) =
        (twoSummaryAt plans env n).2 := by
    simpa only [journalStarPlanTwo] using hcontrols.2
  cases hgraph : (env n).graph
  · rw [oneSummaryAt_succ_left plans env n hgraph,
      twoSummaryAt_succ_left plans env n hgraph]
    simp [starRecord, starOutputOne, starOutputTwo, journalStarPlanOne,
      journalStarPlanTwo, hgraph, hOne, hTwo]
  · rw [oneSummaryAt_succ_right plans env n hgraph,
      twoSummaryAt_succ_right plans env n hgraph]
    simp [starRecord, starOutputOne, starOutputTwo, journalStarPlanOne,
      journalStarPlanTwo, hgraph, hOne, hTwo]
  · rw [oneSummaryAt_succ_both plans env n hgraph,
      twoSummaryAt_succ_both plans env n hgraph]
    simp [starRecord, starOutputOne, starOutputTwo, journalStarPlanOne,
      journalStarPlanTwo, hgraph, hOne, hTwo]

/-- Hosting does not change the generated execution. -/
theorem execution_starReadback_journal_eq
    (plans : PlanFamily (In₁ := In₁) A C_L C_R C_V)
    (env : EnvironmentSequence In₁ In₂) :
    execution
        (starReadback A (journalStarPlansOne plans) (journalStarPlansTwo plans)) env =
      execution (journalStrategy plans) env := by
  funext n
  rw [execution_apply, nextRound_starReadback]
  exact journalStarRecord_eq_execution plans env n

/-- A measurable journal plan family is therefore hosted exactly as its arena
word, on every environment sequence. -/
theorem execution_starReadback_journal_eq_arenaWord
    (plans : PlanFamily (In₁ := In₁) A C_L C_R C_V)
    (hcert : ReversalMeasurable plans)
    (env : EnvironmentSequence In₁ In₂) :
    execution
        (starReadback A (journalStarPlansOne plans) (journalStarPlansTwo plans)) env =
      arenaWord plans env := by
  rw [execution_starReadback_journal_eq plans env]
  exact execution_journalStrategy_eq_arenaWord_full plans env hcert

/-- Concrete star plans realizing every accepted measurable arena-word family. -/
theorem exists_starPlans_of_reversalMeasurable
    (plans : PlanFamily (In₁ := In₁) A C_L C_R C_V)
    (hcert : ReversalMeasurable plans)
    (haccept : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (arenaWord plans env)) :
    ∃ (p₁ : Nat -> StarPlanOne (In₁ := In₁) (In₂ := In₂) A
          (OneCore (In₁ := In₁) A C_L C_R C_V)
          (TwoCore (In₁ := In₁) A C_L C_R C_V))
      (p₂ : Nat -> StarPlanTwo (In₁ := In₁) (In₂ := In₂) A
          (OneCore (In₁ := In₁) A C_L C_R C_V)
          (TwoCore (In₁ := In₁) A C_L C_R C_V)),
      ∀ env : EnvironmentSequence In₁ In₂,
        A.Accepts (execution (starReadback A p₁ p₂) env) := by
  refine ⟨journalStarPlansOne plans, journalStarPlansTwo plans, ?_⟩
  intro env
  rw [execution_starReadback_journal_eq_arenaWord plans hcert env]
  exact haccept env

end

/-- Finite journal data sufficient for the star fold.  This is deliberately
stronger and more structured than merely asserting a `StarFoldCertificate`:
it exposes the precise object the remaining paper proof must extract. -/
structure MeasurableJournalPackage
    (A : DetParityAutomaton.{u, u}
      (RoundRecord In₁ In₂ Graph Out₁ Out₂)) where
  C_L : Type u
  C_R : Type u
  C_V : Type u
  fintypeLeft : Fintype C_L
  decidableEqLeft : DecidableEq C_L
  inhabitedLeft : Inhabited C_L
  fintypeRight : Fintype C_R
  decidableEqRight : DecidableEq C_R
  inhabitedRight : Inhabited C_R
  fintypeChain : Fintype C_V
  decidableEqChain : DecidableEq C_V
  inhabitedChain : Inhabited C_V
  plans : PlanFamily (In₁ := In₁) A C_L C_R C_V
  measurable : ReversalMeasurable plans
  accepts : ∀ env : EnvironmentSequence In₁ In₂,
    A.Accepts (arenaWord plans env)

/-- A finite measurable accepted journal package supplies the concrete private
controls and fold field of `StarFoldPackage`. -/
noncomputable def starFoldPackageOfMeasurableJournal
    (journal : MeasurableJournalPackage A) : StarFoldPackage A := by
  classical
  letI : Fintype journal.C_L := journal.fintypeLeft
  letI : DecidableEq journal.C_L := journal.decidableEqLeft
  letI : Inhabited journal.C_L := journal.inhabitedLeft
  letI : Fintype journal.C_R := journal.fintypeRight
  letI : DecidableEq journal.C_R := journal.decidableEqRight
  letI : Inhabited journal.C_R := journal.inhabitedRight
  letI : Fintype journal.C_V := journal.fintypeChain
  letI : DecidableEq journal.C_V := journal.decidableEqChain
  letI : Inhabited journal.C_V := journal.inhabitedChain
  let W₁ := OneCore (In₁ := In₁) A journal.C_L journal.C_R journal.C_V
  let W₂ := TwoCore (In₁ := In₁) A journal.C_L journal.C_R journal.C_V
  refine
    { W₁ := W₁
      W₂ := W₂
      fintypeOne := inferInstance
      decidableEqOne := Classical.decEq W₁
      inhabitedOne := ⟨Sum.inr (Sum.inl (A.initial, A.initial))⟩
      fintypeTwo := inferInstance
      decidableEqTwo := Classical.decEq W₂
      inhabitedTwo := ⟨Sum.inr (Sum.inl (A.initial, A.initial))⟩
      fold := ?_ }
  intro _
  exact exists_starPlans_of_reversalMeasurable
    journal.plans journal.measurable journal.accepts

/-- The exact remaining extraction statement: every realizable objective has
some finite measurable accepted journal package. -/
def MeasurableJournalExtraction
    (A : DetParityAutomaton.{u, u}
      (RoundRecord In₁ In₂ Graph Out₁ Out₂)) : Prop :=
  ( ∃ σ : StrategyPair In₁ In₂ Out₁ Out₂,
      ∀ env : EnvironmentSequence In₁ In₂,
        A.Accepts (execution σ env)) ->
    Nonempty (MeasurableJournalPackage A)

/-- Once measurable-journal extraction is proved, the original
`StarFoldPackage` follows.  In the unrealizable case the fold implication is
vacuous; in the realizable case the extracted journal cores are the controls. -/
noncomputable def starFoldPackage_of_measurableJournalExtraction
    (hextract : MeasurableJournalExtraction A) : StarFoldPackage A := by
  classical
  by_cases hreal : ∃ σ : StrategyPair In₁ In₂ Out₁ Out₂,
      ∀ env : EnvironmentSequence In₁ In₂,
        A.Accepts (execution σ env)
  · let journal := Classical.choice (hextract hreal)
    exact starFoldPackageOfMeasurableJournal journal
  · refine
      { W₁ := PUnit
        W₂ := PUnit
        fintypeOne := inferInstance
        decidableEqOne := inferInstance
        inhabitedOne := inferInstance
        fintypeTwo := inferInstance
        decidableEqTwo := inferInstance
        inhabitedTwo := inferInstance
        fold := ?_ }
    intro impossible
    exact (hreal impossible).elim

/--
Measurable journal extraction is sufficient for the full DPA synthesis
decision directly; no dynamic-hierarchy synthesis theorem is consumed.
-/
noncomputable def synthesisDecidable_of_measurableJournalExtraction
    (hextract : MeasurableJournalExtraction A) :
    Decidable
      (∃ σ : StrategyPair In₁ In₂ Out₁ Out₂,
        ∀ env : EnvironmentSequence In₁ In₂,
          A.Accepts (execution σ env)) :=
  (starFoldPackage_of_measurableJournalExtraction hextract).synthesisDecidable_direct

end DetParityAutomaton

end DistributedSynthesis
