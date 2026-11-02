/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmStarReadback
import DistributedSynthesis.Formalizations.Theorem.ThmLTLAPASemanticBridge
import DistributedSynthesis.Formalizations.Theorem.ThmBlindGameAPA

/-!
# Star synthesis: the decidability endpoint of the star route (F6)

The star game's perfect-recall realizability is *equivalent* to
realizability of the objective by star-readback strategies
(`starGame_historyRealizable_iff_readback`): a star strategy is a
round-indexed stream of plan commitments, and the game's parity value is
acceptance of the readback execution.  Consequently, the lower-level
Transport C route decides distributed synthesis from three named inputs:

* `ShadowLeaderArenaComplete` at the star game (R1′, Reif and
  Berwanger--Mathew--van den Bogaard leader-arena completeness);
* `LeaderArenaWinDecidable` at its shadow arena (B, finite parity
  solvability);
* `StarFoldCertificate` (F3, paper `prop:starcomplete`): every realizable
  objective is realizable by a star-readback strategy.  This is a pure
  strategy-folding statement -- no game theory remains in it -- and is the
  sole non-published residual of the route.

The preferred endpoint below solves the constant-observation star game by
alternating-parity word-automaton nonemptiness.  The literature-relative
endpoint through `Literature.Berwanger.Theorem10` remains available as an
independent generalization check.
-/

namespace DistributedSynthesis

universe u

variable {In₁ In₂ Out₁ Out₂ : Type u}

namespace DetParityAutomaton

open StarReadback

variable {A : DetParityAutomaton.{u, u} (RoundRecord In₁ In₂ Graph Out₁ Out₂)}
variable {W₁ W₂ : Type u}

section Endpoint

variable [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
variable [DecidableEq In₁] [DecidableEq In₂]
variable [Fintype A.State] [DecidableEq A.State]
variable [Fintype W₁] [DecidableEq W₁] [Fintype W₂] [DecidableEq W₂]
variable [Inhabited Out₁] [Inhabited Out₂] [Inhabited W₁] [Inhabited W₂]

omit [Inhabited W₁] [Inhabited W₂] in
/-- A star strategy wins the game exactly when its readback realizes the
objective: the game's parity sequence is the objective priority along the
readback execution's run. -/
theorem historyStrategyWins_iff_readback
    (s : (A.starGame (In₁ := In₁) (In₂ := In₂) W₁ W₂).HistoryProductStrategy) :
    (A.starGame (In₁ := In₁) (In₂ := In₂) W₁ W₂).HistoryStrategyWins s ↔
      ∀ env : EnvironmentSequence In₁ In₂,
        A.Accepts
          (execution (starReadback A (gamePlanOne s) (gamePlanTwo s)) env) := by
  have hprio :
      ∀ (env : EnvironmentSequence In₁ In₂) (n : Nat),
        (A.starGame (In₁ := In₁) (In₂ := In₂) W₁ W₂).priority
            (FiniteConcurrentGame.strategyState
              (G := A.starGame (In₁ := In₁) (In₂ := In₂) W₁ W₂) s env n).1 =
          A.priority
            (A.run
              (execution (starReadback A (gamePlanOne s) (gamePlanTwo s)) env)
              n) := by
    intro env n
    rw [strategyState_starGame]
    show A.priority
        (starRun A (gamePlanOne s) (gamePlanTwo s) env n).1.state = _
    rw [starRun_state_eq_run]
  constructor
  · intro hs env
    obtain ⟨p, hp2, hinf, hmin⟩ := hs env
    refine ⟨p, ⟨p / 2, by omega⟩, ?_, ?_⟩
    · intro n
      obtain ⟨k, hk, hkp⟩ := hinf n
      refine ⟨k, hk, ?_⟩
      show A.priority (A.runFrom A.initial _ k) = p
      rw [show A.runFrom A.initial
            (execution (starReadback A (gamePlanOne s) (gamePlanTwo s)) env)
            k =
          A.run (execution (starReadback A (gamePlanOne s) (gamePlanTwo s))
            env) k from rfl, <- hprio env k]
      exact hkp
    · intro q hq
      refine hmin q ?_
      intro n
      obtain ⟨k, hk, hkq⟩ := hq n
      refine ⟨k, hk, ?_⟩
      show (A.starGame (In₁ := In₁) (In₂ := In₂) W₁ W₂).priority
          (FiniteConcurrentGame.strategyState
            (G := A.starGame (In₁ := In₁) (In₂ := In₂) W₁ W₂) s env k).1 = q
      rw [hprio env k]
      exact hkq
  · intro hreal env
    obtain ⟨p, ⟨m, hm⟩, hinf, hmin⟩ := hreal env
    refine ⟨p, by omega, ?_, ?_⟩
    · intro n
      obtain ⟨k, hk, hkp⟩ := hinf n
      refine ⟨k, hk, ?_⟩
      show (A.starGame (In₁ := In₁) (In₂ := In₂) W₁ W₂).priority
          (FiniteConcurrentGame.strategyState
            (G := A.starGame (In₁ := In₁) (In₂ := In₂) W₁ W₂) s env k).1 = p
      rw [hprio env k]
      exact hkp
    · intro q hq
      refine hmin q ?_
      intro n
      obtain ⟨k, hk, hkq⟩ := hq n
      refine ⟨k, hk, ?_⟩
      rw [show A.runFrom A.initial
            (execution (starReadback A (gamePlanOne s) (gamePlanTwo s)) env)
            k =
          A.run (execution (starReadback A (gamePlanOne s) (gamePlanTwo s))
            env) k from rfl, <- hprio env k]
      exact hkq

omit [Inhabited W₁] [Inhabited W₂] in
/-- Star realizability is realizability by star-readback strategies. -/
theorem starGame_historyRealizable_iff_readback :
    (A.starGame (In₁ := In₁) (In₂ := In₂) W₁ W₂).HistoryRealizable ↔
      ∃ (p₁ : Nat -> StarPlanOne (In₁ := In₁) (In₂ := In₂) A W₁ W₂)
        (p₂ : Nat -> StarPlanTwo (In₁ := In₁) (In₂ := In₂) A W₁ W₂),
        ∀ env : EnvironmentSequence In₁ In₂,
          A.Accepts (execution (starReadback A p₁ p₂) env) := by
  constructor
  · rintro ⟨s, hs⟩
    exact ⟨gamePlanOne s, gamePlanTwo s,
      (historyStrategyWins_iff_readback s).mp hs⟩
  · rintro ⟨p₁, p₂, hreal⟩
    refine ⟨(fun l => p₁ (l.length - 1), fun l => p₂ (l.length - 1)), ?_⟩
    have h₁ : gamePlanOne (A := A) (W₁ := W₁) (W₂ := W₂)
        (fun l => p₁ (l.length - 1), fun l => p₂ (l.length - 1)) = p₁ := by
      funext n
      simp [gamePlanOne]
    have h₂ : gamePlanTwo (A := A) (W₁ := W₁) (W₂ := W₂)
        (fun l => p₁ (l.length - 1), fun l => p₂ (l.length - 1)) = p₂ := by
      funext n
      simp [gamePlanTwo]
    refine (historyStrategyWins_iff_readback _).mpr ?_
    rw [h₁, h₂]
    exact hreal

variable (A W₁ W₂) in
/--
**The star fold certificate** (F3, paper `prop:starcomplete`): whenever the
objective is realizable by an arbitrary distributed strategy, it is
realizable by a star-readback strategy over the controls `W₁`, `W₂` -- a
strategy whose receive behavior factors through the star core and its
private control, and whose blind behavior factors through the private
control alone.  This is the θ̄-fold of the paper stated at its smallest
interface: a pure statement about distributed strategies of the model.
-/
def StarFoldCertificate : Prop :=
  (∃ σ : StrategyPair In₁ In₂ Out₁ Out₂,
      ∀ env : EnvironmentSequence In₁ In₂, A.Accepts (execution σ env)) ->
    ∃ (p₁ : Nat -> StarPlanOne (In₁ := In₁) (In₂ := In₂) A W₁ W₂)
      (p₂ : Nat -> StarPlanTwo (In₁ := In₁) (In₂ := In₂) A W₁ W₂),
      ∀ env : EnvironmentSequence In₁ In₂,
        A.Accepts (execution (starReadback A p₁ p₂) env)

/-- The paper-specific fold theorem with the finite private controls it
chooses.  The controls are existential data of the fold; no theorem should
claim `StarFoldCertificate A W₁ W₂` uniformly for arbitrary prescribed
types `W₁`, `W₂`.

Once this generic package is supplied, the direct constant-observation APA
solver completes the decision procedure.  `LemStarSummaryHosting` supplies it
from a finite local-summary `ReadbackUpgrade`, so it is not an independent
open assumption; the general Berwanger--Mathew--van den Bogaard Theorem 10 is
an optional alternative. -/
structure StarFoldPackage
    (A : DetParityAutomaton.{u, u}
      (RoundRecord In₁ In₂ Graph Out₁ Out₂)) where
  W₁ : Type u
  W₂ : Type u
  fintypeOne : Fintype W₁
  decidableEqOne : DecidableEq W₁
  inhabitedOne : Inhabited W₁
  fintypeTwo : Fintype W₂
  decidableEqTwo : DecidableEq W₂
  inhabitedTwo : Inhabited W₂
  fold : StarFoldCertificate (In₁ := In₁) (In₂ := In₂) A W₁ W₂

namespace StarFoldPackage

instance (package : StarFoldPackage A) : Fintype package.W₁ :=
  package.fintypeOne

instance (package : StarFoldPackage A) : DecidableEq package.W₁ :=
  package.decidableEqOne

instance (package : StarFoldPackage A) : Inhabited package.W₁ :=
  package.inhabitedOne

instance (package : StarFoldPackage A) : Fintype package.W₂ :=
  package.fintypeTwo

instance (package : StarFoldPackage A) : DecidableEq package.W₂ :=
  package.decidableEqTwo

instance (package : StarFoldPackage A) : Inhabited package.W₂ :=
  package.inhabitedTwo

end StarFoldPackage

omit [Inhabited W₁] [Inhabited W₂] in
/-- Star realizability is distributed realizability, given the fold
certificate; the readback direction is unconditional. -/
theorem starGame_historyRealizable_iff_realizable
    (hfold : StarFoldCertificate (In₁ := In₁) (In₂ := In₂) A W₁ W₂) :
    (A.starGame (In₁ := In₁) (In₂ := In₂) W₁ W₂).HistoryRealizable ↔
      ∃ σ : StrategyPair In₁ In₂ Out₁ Out₂,
        ∀ env : EnvironmentSequence In₁ In₂, A.Accepts (execution σ env) := by
  constructor
  · exact exists_realizing_of_starGame_historyRealizable
  · intro hreal
    obtain ⟨p₁, p₂, hp⟩ := hfold hreal
    exact starGame_historyRealizable_iff_readback.mpr ⟨p₁, p₂, hp⟩

/--
The star game is decidable directly, without the general dynamic-hierarchy
synthesis theorem: both observation alphabets are `PUnit`, so its strategies
are synchronized joint-plan words and the universal Nature branching is an
alternating parity word automaton.
-/
noncomputable def starGame_historyRealizableDecidable_direct :
    Decidable
      (A.starGame (In₁ := In₁) (In₂ := In₂) W₁ W₂).HistoryRealizable := by
  letI : Subsingleton
      (A.starGame (In₁ := In₁) (In₂ := In₂) W₁ W₂).Observation1 := by
    change Subsingleton PUnit
    infer_instance
  letI : Subsingleton
      (A.starGame (In₁ := In₁) (In₂ := In₂) W₁ W₂).Observation2 := by
    change Subsingleton PUnit
    infer_instance
  exact
    (A.starGame (In₁ := In₁) (In₂ := In₂)
      W₁ W₂).historyRealizableDecidable_of_subsingletonObservations

/--
**Direct star-route synthesis endpoint.**  The paper-specific fold plus the
constant-observation APA solver decides the original deterministic parity
objective; Berwanger--Mathew--van den Bogaard Theorem 10 is not required.
-/
noncomputable def star_full_synthesis_decidable_direct
    (hfold : StarFoldCertificate (In₁ := In₁) (In₂ := In₂) A W₁ W₂) :
    Decidable
      (∃ σ : StrategyPair In₁ In₂ Out₁ Out₂,
        ∀ env : EnvironmentSequence In₁ In₂, A.Accepts (execution σ env)) :=
  letI : Decidable
      (A.starGame (In₁ := In₁) (In₂ := In₂) W₁ W₂).HistoryRealizable :=
    starGame_historyRealizableDecidable_direct
  decidable_of_iff _ (starGame_historyRealizable_iff_realizable hfold)

/-- **Generic star-route synthesis endpoint.**  Any finite-state synthesis
certificate for the star game, together with the paper-specific fold, decides
realizability of the original deterministic parity objective. -/
noncomputable def star_full_synthesis_decidable_of_certificate
    (hcertificate : Nonempty
      (A.starGame (In₁ := In₁) (In₂ := In₂)
        W₁ W₂).FiniteStateSynthesisCertificate)
    (hfold : StarFoldCertificate (In₁ := In₁) (In₂ := In₂) A W₁ W₂) :
    Decidable
      (∃ σ : StrategyPair In₁ In₂ Out₁ Out₂,
        ∀ env : EnvironmentSequence In₁ In₂, A.Accepts (execution σ env)) :=
  letI : Decidable
      (A.starGame (In₁ := In₁) (In₂ := In₂) W₁ W₂).HistoryRealizable :=
    Classical.choice
      (hcertificate.map fun c => c.decision)
  decidable_of_iff _ (starGame_historyRealizable_iff_realizable hfold)

/-- Compatibility endpoint using the development's lower-level decomposition
of the dynamic-hierarchy theorem into shadow completeness and parity-game
solvability.  The direct APA endpoint above supersedes this route for the
constant-observation star game. -/
noncomputable def star_full_synthesis_decidable
    (hc : (A.starGame (In₁ := In₁) (In₂ := In₂) W₁ W₂).ShadowLeaderArenaComplete)
    (hd : (A.starGame (In₁ := In₁) (In₂ := In₂)
        W₁ W₂).commonSignalShadowGame.LeaderArenaWinDecidable)
    (hfold : StarFoldCertificate (In₁ := In₁) (In₂ := In₂) A W₁ W₂) :
    Decidable
      (∃ σ : StrategyPair In₁ In₂ Out₁ Out₂,
        ∀ env : EnvironmentSequence In₁ In₂, A.Accepts (execution σ env)) :=
  star_full_synthesis_decidable_of_certificate
    (starGame_finiteStateSolvable hc hd) hfold

end Endpoint

section PackagedEndpoint

variable [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
variable [DecidableEq In₁] [DecidableEq In₂]
variable [Fintype A.State] [DecidableEq A.State]
variable [Inhabited Out₁] [Inhabited Out₂]

/-- A packaged paper-specific fold directly decides the original DPA objective. -/
noncomputable def StarFoldPackage.synthesisDecidable_direct
    (package : StarFoldPackage A) :
    Decidable
      (∃ σ : StrategyPair In₁ In₂ Out₁ Out₂,
        ∀ env : EnvironmentSequence In₁ In₂,
          A.Accepts (execution σ env)) :=
  star_full_synthesis_decidable_direct
    (W₁ := package.W₁) (W₂ := package.W₂) package.fold

end PackagedEndpoint

end DetParityAutomaton

section LTLFlagship

open DetParityAutomaton

/--
**Direct star-route LTL synthesis endpoint.**  Distributed synthesis of arbitrary full
LTL over the full `{←,→,↔}` model is decidable from the paper-specific star
fold alone.  The star game is solved by constant-observation APA nonemptiness;
neither the shadow-game decomposition nor Berwanger Theorem 10 is used.
-/
noncomputable def main_result_for_ltl_full_synthesis_star_route_direct
    {AP : Type}
    (In₁ In₂ Out₁ Out₂ : Type)
    [DecidableEq AP]
    [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
    [DecidableEq In₁] [DecidableEq In₂]
    [Inhabited Out₁] [Inhabited Out₂]
    (interp : AP -> RoundRecord In₁ In₂ Graph Out₁ Out₂ -> Prop)
    (dec : ∀ ap letter, Decidable (interp ap letter))
    (formula : LTL AP)
    (W₁ W₂ : Type)
    [Fintype W₁] [DecidableEq W₁] [Fintype W₂] [DecidableEq W₂]
    [Inhabited W₁] [Inhabited W₂]
    [DecidableEq
        ((PositiveLTL.canonicalLTLToDPACompiler interp dec).compile
          formula).State]
    (hfold :
      StarFoldCertificate (In₁ := In₁) (In₂ := In₂)
        ((PositiveLTL.canonicalLTLToDPACompiler interp dec).compile formula)
        W₁ W₂) :
    Decidable
      (∃ σ : StrategyPair In₁ In₂ Out₁ Out₂,
        ∀ env : EnvironmentSequence In₁ In₂,
          LTL.Satisfies interp (execution σ env) formula) :=
  letI :
      Decidable
        (∃ σ : StrategyPair In₁ In₂ Out₁ Out₂,
          ∀ env : EnvironmentSequence In₁ In₂,
            ((PositiveLTL.canonicalLTLToDPACompiler interp dec).compile
              formula).Accepts (execution σ env)) :=
    star_full_synthesis_decidable_direct hfold
  decidable_of_iff
    (∃ σ : StrategyPair In₁ In₂ Out₁ Out₂,
      ∀ env : EnvironmentSequence In₁ In₂,
        ((PositiveLTL.canonicalLTLToDPACompiler interp dec).compile
          formula).Accepts (execution σ env))
    (by
      constructor
      · rintro ⟨σ, hσ⟩
        exact ⟨σ, fun env =>
          ((PositiveLTL.canonicalLTLToDPACompiler interp dec).correct formula
            (execution σ env)).mp (hσ env)⟩
      · rintro ⟨σ, hσ⟩
        exact ⟨σ, fun env =>
          ((PositiveLTL.canonicalLTLToDPACompiler interp dec).correct formula
            (execution σ env)).mpr (hσ env)⟩)

/--
**The star-route LTL synthesis endpoint**: distributed synthesis of arbitrary full
LTL over the full `{←,→,↔}` model, for finite input/output alphabets, is
decidable given R1′ and B at the star game of the canonically compiled
objective and the star fold certificate.  The compiler is the canonical
unconditional LTL-to-DPA chain; no other hypotheses remain.
-/
noncomputable def main_result_for_ltl_full_synthesis_star_route
    {AP : Type}
    (In₁ In₂ Out₁ Out₂ : Type)
    [DecidableEq AP]
    [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
    [DecidableEq In₁] [DecidableEq In₂]
    [Inhabited Out₁] [Inhabited Out₂]
    (interp : AP -> RoundRecord In₁ In₂ Graph Out₁ Out₂ -> Prop)
    (dec : ∀ ap letter, Decidable (interp ap letter))
    (formula : LTL AP)
    (W₁ W₂ : Type)
    [Fintype W₁] [DecidableEq W₁] [Fintype W₂] [DecidableEq W₂]
    [Inhabited W₁] [Inhabited W₂]
    [DecidableEq
        ((PositiveLTL.canonicalLTLToDPACompiler interp dec).compile
          formula).State]
    (hc :
      (((PositiveLTL.canonicalLTLToDPACompiler interp dec).compile
            formula).starGame (In₁ := In₁) (In₂ := In₂)
          W₁ W₂).ShadowLeaderArenaComplete)
    (hd :
      (((PositiveLTL.canonicalLTLToDPACompiler interp dec).compile
            formula).starGame (In₁ := In₁) (In₂ := In₂)
          W₁ W₂).commonSignalShadowGame.LeaderArenaWinDecidable)
    (hfold :
      StarFoldCertificate (In₁ := In₁) (In₂ := In₂)
        ((PositiveLTL.canonicalLTLToDPACompiler interp dec).compile formula)
        W₁ W₂) :
    Decidable
      (∃ σ : StrategyPair In₁ In₂ Out₁ Out₂,
        ∀ env : EnvironmentSequence In₁ In₂,
          LTL.Satisfies interp (execution σ env) formula) :=
  letI :
      Decidable
        (∃ σ : StrategyPair In₁ In₂ Out₁ Out₂,
          ∀ env : EnvironmentSequence In₁ In₂,
            ((PositiveLTL.canonicalLTLToDPACompiler interp dec).compile
              formula).Accepts (execution σ env)) :=
    star_full_synthesis_decidable hc hd hfold
  decidable_of_iff
    (∃ σ : StrategyPair In₁ In₂ Out₁ Out₂,
      ∀ env : EnvironmentSequence In₁ In₂,
        ((PositiveLTL.canonicalLTLToDPACompiler interp dec).compile
          formula).Accepts (execution σ env))
    (by
      constructor
      · rintro ⟨σ, hσ⟩
        exact ⟨σ, fun env =>
          ((PositiveLTL.canonicalLTLToDPACompiler interp dec).correct formula
            (execution σ env)).mp (hσ env)⟩
      · rintro ⟨σ, hσ⟩
        exact ⟨σ, fun env =>
          ((PositiveLTL.canonicalLTLToDPACompiler interp dec).correct formula
            (execution σ env)).mpr (hσ env)⟩)

end LTLFlagship

end DistributedSynthesis
