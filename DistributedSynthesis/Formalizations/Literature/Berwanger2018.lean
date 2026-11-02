/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmDynhiersynth
import DistributedSynthesis.Formalizations.Theorem.ThmFringeCompiledGame
import DistributedSynthesis.Formalizations.Theorem.ThmSplitFringeCompiledGame
import DistributedSynthesis.Formalizations.Theorem.ThmStarSynthesis
import DistributedSynthesis.Formalizations.Literature.PetersonReif1979
import DistributedSynthesis.Formalizations.Literature.ParityGameSolvability

/-!
# Berwanger--Mathew--van den Bogaard (2018): dynamic hierarchies

**Source.**  D. Berwanger, A. B. Mathew, M. van den Bogaard, *Hierarchical
Information and the Synthesis of Distributed Strategies*, Acta Informatica
55(8), 2018 (`berwanger2018hierarchical`), Theorem 10.

This file collects the literature-facing interfaces of that theorem used by
the development, and the machine-checked consumption theorems that relieve
the project once they are discharged.

* `Theorem10` -- the cited statement itself: every finite game with dynamic
  hierarchical information has a finite-state synthesis certificate.
* `ShadowCompleteness` -- the completeness half of their Theorem 10 proof
  at the composed reduction (their Lemma 12 applied to the shadow
  construction): a distributed winner yields an Even winner of the shadow
  game's leader knowledge arena.  It decomposes further along the
  literature seams via
  `Literature.PetersonReif.shadow_completeness_of_beliefSufficiency`.
* `ExtractionAtFold` -- a compatibility name for `StarFoldCertificate`.
  It is **not** itself a statement of Theorem 10.  The direct development now
  obtains it from a finite local-summary readback upgrade in
  `LemStarSummaryHosting`, so the stronger measurable-journal construction is
  not required.
* `SplitFringeToStrictGame.baseCertificate_of_theorem10` -- the correct
  finite-fringe route: split observations into non-fringe core and current
  finite fringe, prove strict hierarchy of the accumulated core histories,
  compile only the fringe into contingent actions, and only then invoke
  Theorem 10.
* `ltl_full_synthesis_of_theorem10` -- the general literature-relative endpoint.  Its
  only inputs beyond finite alphabets are the published `Theorem10` and a
  paper-specific `StarFoldPackage`, whose finite private controls are chosen
  by the fold rather than fixed arbitrarily by the caller.

**Status.**  `Theorem10` is a clean classical literature interface, and the
new `SplitFringeToStrictGame` declarations machine-check its use only on the
strict post-fringe game.  The older `WholeObservationDelay` adapter is retained
as a generic theorem but is not the model reduction: delaying both complete
observation streams is stronger than the proved delay-one order and does not
establish its `SummaryGameSettledHierarchy` premise.  The constant-observation star game has a
direct APA decision and no longer needs Theorem 10 for its own solution.
`LemStarSummaryHosting` supplies a `StarFoldPackage` from a finite-summary
winner, but producing such a winner from an arbitrary realizer still requires
the model-specific finite retraction/fold; it is not discharged merely by
naming `Theorem10`.  The lower-level
`ShadowCompleteness`/parity-solver decomposition remains available for a
future internal mechanization of Theorem 10, but is not needed by the direct
star endpoint.
-/

namespace DistributedSynthesis

namespace Literature

namespace Berwanger

universe u

/-- Formal interface for the cited Theorem 10: every finite concurrent game
with dynamic hierarchical information has a finite-state synthesis
certificate. -/
abbrev Theorem10 : Prop := DynamicHierarchyFiniteStateSolvable.{u}

/-- The completeness half of the Theorem 10 proof, at the composed
reduction (Lemma 12 at the shadow construction). -/
abbrev ShadowCompleteness (G : FiniteConcurrentGame.{u})
    [Inhabited G.Action1] [Inhabited G.Action2]
    [Inhabited G.Observation1] [Inhabited G.Observation2] : Prop :=
  G.ShadowLeaderArenaComplete

/-- Compatibility alias for the paper-specific fold certificate
(`prop:starcomplete`).  This is deliberately not claimed as a theorem from
the cited paper: Theorem 10 solves a dynamically hierarchical game once it
is realizable, whereas this certificate transfers realizability of the
original model to the star game. -/
abbrev ExtractionAtFold {In₁ In₂ Out₁ Out₂ : Type u}
    (A : DetParityAutomaton.{u, u} (RoundRecord In₁ In₂ Graph Out₁ Out₂))
    (W₁ W₂ : Type u) [Inhabited Out₁] [Inhabited Out₂] : Prop :=
  DetParityAutomaton.StarFoldCertificate A W₁ W₂

namespace WholeObservationDelay

open FiniteConcurrentGame

variable {In₁ In₂ Out₁ Out₂ : Type u}
  [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
  [Inhabited In₁] [Inhabited In₂]
  [Inhabited Out₁] [Inhabited Out₂]

/-- The published theorem applied to the whole-observation-delay adapter.  Its
model-specific premise is the settled hierarchy of the finite summary game;
the equivalence with strict hierarchy after this generic compilation is proved
in `ThmFringeCompiledGame`.

This is retained as an audit boundary, not as the paper's fringe reduction:
the actual delay-one theorem does not establish `hsettled`. -/
noncomputable def fringeCompiledCertificate_of_theorem10
    (theorem10 : Theorem10.{u})
    (A : DetParityAutomaton.{u, u}
      (RoundRecord In₁ In₂ Graph Out₁ Out₂))
    (M : LocalSummaryAutomaton.{u, u, u} In₁ In₂)
    (hsettled : A.SummaryGameSettledHierarchy M) :
    A.FringeCompiledFiniteStateCertificate M := by
  exact Classical.choice
    (theorem10 (A.summaryFringeCompiledGame M)
      ((A.summaryFringeCompiledGame_dynamicHierarchy_iff M).2 hsettled))

/-- Certificate transport for the whole-observation-delay adapter.  This is
correct under `hsettled`, but `hsettled` is not a consequence of the model's
delay-one hierarchy. -/
noncomputable def summaryGameCertificate_of_theorem10
    (theorem10 : Theorem10.{u})
    (A : DetParityAutomaton.{u, u}
      (RoundRecord In₁ In₂ Graph Out₁ Out₂))
    (M : LocalSummaryAutomaton.{u, u, u} In₁ In₂)
    (hsettled : A.SummaryGameSettledHierarchy M) :
    A.SummaryGameFiniteStateCertificate M :=
  A.summaryGameFiniteStateCertificate_of_fringeCompiled M
    (fringeCompiledCertificate_of_theorem10 theorem10 A M hsettled)

end WholeObservationDelay

namespace SplitFringeToStrictGame

open FiniteConcurrentGame

/-- Apply the published theorem only after the split-fringe compilation has
already been proved strictly dynamically hierarchical.  The premise is the
strict hierarchy of accumulated non-fringe core histories, not a delay
property. -/
noncomputable def compiledCertificate_of_theorem10
    (theorem10 : Theorem10.{u})
    (G : FiniteConcurrentGame.{u})
    (D : G.FringeDecomposition)
    (hcore : D.CoreHierarchy) :
    D.compiled.FiniteStateSynthesisCertificate :=
  Classical.choice
    (theorem10 D.compiled (D.compiled_dynamicHierarchy_iff.mpr hcore))

/-- The complete unconditional finite-fringe reduction around Theorem 10:
the strict compiled certificate reads back to the original game, and the
history-realizability equivalence used by the decision field is proved by the
split/recovery construction. -/
noncomputable def baseCertificate_of_theorem10
    (theorem10 : Theorem10.{u})
    (G : FiniteConcurrentGame.{u})
    (D : G.FringeDecomposition)
    (hcore : D.CoreHierarchy) :
    G.FiniteStateSynthesisCertificate :=
  D.finiteStateSynthesisCertificate_of_compiled
    (compiledCertificate_of_theorem10 theorem10 G D hcore)

end SplitFringeToStrictGame

/-- DPA-level synthesis relative to the published dynamic-hierarchy theorem
and one paper-specific fold package.  This is the direct, non-circular
composition: the fold transfers original realizability to the star game;
Theorem 10 decides that finite dynamically hierarchical game. -/
noncomputable def dpa_full_synthesis_of_theorem10
    {In₁ In₂ Out₁ Out₂ : Type u}
    [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
    [DecidableEq In₁] [DecidableEq In₂]
    [Inhabited Out₁] [Inhabited Out₂]
    (theorem10 : Theorem10.{u})
    (A : DetParityAutomaton.{u, u}
      (RoundRecord In₁ In₂ Graph Out₁ Out₂))
    (package : DetParityAutomaton.StarFoldPackage A) :
    Decidable
      (∃ σ : StrategyPair In₁ In₂ Out₁ Out₂,
        ∀ env : EnvironmentSequence In₁ In₂,
          A.Accepts (execution σ env)) := by
  letI : DecidableEq A.State := Classical.decEq _
  exact DetParityAutomaton.star_full_synthesis_decidable_of_certificate
    (theorem10
      (A.starGame (In₁ := In₁) (In₂ := In₂) package.W₁ package.W₂)
      DetParityAutomaton.starGame_dynamicHierarchy)
    package.fold

/-- **The per-game Theorem 10, machine-checked from the interfaces**: the
Transport C engine derives the certificate of any dynamically hierarchical
game from `ShadowCompleteness` and parity solvability at its shadow arena. -/
theorem theorem10_pointwise_of_certs (G : FiniteConcurrentGame.{u})
    [Inhabited G.Action1] [Inhabited G.Action2]
    [Inhabited G.Observation1] [Inhabited G.Observation2]
    (hhier : G.DynamicHierarchy) (hc : ShadowCompleteness G)
    (hd : G.commonSignalShadowGame.LeaderArenaWinDecidable) :
    Nonempty G.FiniteStateSynthesisCertificate :=
  G.dynamicHierarchy_finiteStateSolvable_of_shadowCerts hhier hc hd

/-- **The per-game Theorem 10 from the lower-level interfaces**: a parity
solver and the composed completeness certificate suffice; the shadow
arena's decidability side is derived, not assumed. -/
theorem theorem10_pointwise_of_solver
    (solver : ParitySolving.Solver.{u}) (G : FiniteConcurrentGame.{u})
    [Inhabited G.Action1] [Inhabited G.Action2]
    [Inhabited G.Observation1] [Inhabited G.Observation2]
    (hhier : G.DynamicHierarchy) (hc : ShadowCompleteness G) :
    Nonempty G.FiniteStateSynthesisCertificate :=
  theorem10_pointwise_of_certs G hhier hc
    (ParitySolving.leaderArenaWinDecidable_of_solver solver
      G.commonSignalShadowGame)

/-- **Preferred literature-relative synthesis endpoint.**  Full LTL synthesis in the
`{←,→,↔}` model is decidable from exactly:

1. Berwanger--Mathew--van den Bogaard Theorem 10, and
2. the paper-specific star-fold package for the compiled objective.

The fold package existentially chooses its finite private memories.  No
shadow-completeness, Peterson--Reif, or parity-solver hypothesis is exposed
at this endpoint because those belong inside the cited Theorem 10. -/
noncomputable def ltl_full_synthesis_of_theorem10
    {AP : Type}
    (In₁ In₂ Out₁ Out₂ : Type)
    [DecidableEq AP]
    [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
    [DecidableEq In₁] [DecidableEq In₂]
    [Inhabited Out₁] [Inhabited Out₂]
    (interp : AP -> RoundRecord In₁ In₂ Graph Out₁ Out₂ -> Prop)
    (dec : ∀ ap letter, Decidable (interp ap letter))
    (formula : LTL AP)
    (theorem10 : Theorem10.{0})
    (package :
      DetParityAutomaton.StarFoldPackage
        ((PositiveLTL.canonicalLTLToDPACompiler interp dec).compile formula)) :
    Decidable
      (∃ σ : StrategyPair In₁ In₂ Out₁ Out₂,
        ∀ env : EnvironmentSequence In₁ In₂,
          LTL.Satisfies interp (execution σ env) formula) :=
  letI : Decidable
      (∃ σ : StrategyPair In₁ In₂ Out₁ Out₂,
        ∀ env : EnvironmentSequence In₁ In₂,
          ((PositiveLTL.canonicalLTLToDPACompiler interp dec).compile
            formula).Accepts (execution σ env)) :=
    dpa_full_synthesis_of_theorem10 theorem10
      ((PositiveLTL.canonicalLTLToDPACompiler interp dec).compile formula)
      package
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
**Lower-level decomposition endpoint**:
distributed synthesis of arbitrary full LTL over the full `{←,→,↔}` model,
for finite input/output alphabets, is decidable given `ShadowCompleteness`
and parity solvability at the star game of the canonically compiled
objective, and `ExtractionAtFold`.
-/
noncomputable def ltl_full_synthesis
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
      ShadowCompleteness
        (((PositiveLTL.canonicalLTLToDPACompiler interp dec).compile
            formula).starGame (In₁ := In₁) (In₂ := In₂) W₁ W₂))
    (hd :
      (((PositiveLTL.canonicalLTLToDPACompiler interp dec).compile
            formula).starGame (In₁ := In₁) (In₂ := In₂)
          W₁ W₂).commonSignalShadowGame.LeaderArenaWinDecidable)
    (hfold :
      ExtractionAtFold (In₁ := In₁) (In₂ := In₂)
        ((PositiveLTL.canonicalLTLToDPACompiler interp dec).compile formula)
        W₁ W₂) :
    Decidable
      (∃ σ : StrategyPair In₁ In₂ Out₁ Out₂,
        ∀ env : EnvironmentSequence In₁ In₂,
          LTL.Satisfies interp (execution σ env) formula) :=
  main_result_for_ltl_full_synthesis_star_route
    In₁ In₂ Out₁ Out₂ interp dec formula W₁ W₂ hc hd hfold

/--
**The lower-level synthesis endpoint with a parity solver**: as `ltl_full_synthesis`,
with the shadow arena's decidability derived from a parity solver instead
of assumed.  This compatibility endpoint exposes the internal
decomposition and the paper-specific fold separately; it is not the
preferred literature boundary.
-/
noncomputable def ltl_full_synthesis_of_solver
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
    (solver : ParitySolving.Solver.{0})
    (hc :
      ShadowCompleteness
        (((PositiveLTL.canonicalLTLToDPACompiler interp dec).compile
            formula).starGame (In₁ := In₁) (In₂ := In₂) W₁ W₂))
    (hfold :
      ExtractionAtFold (In₁ := In₁) (In₂ := In₂)
        ((PositiveLTL.canonicalLTLToDPACompiler interp dec).compile formula)
        W₁ W₂) :
    Decidable
      (∃ σ : StrategyPair In₁ In₂ Out₁ Out₂,
        ∀ env : EnvironmentSequence In₁ In₂,
          LTL.Satisfies interp (execution σ env) formula) :=
  ltl_full_synthesis In₁ In₂ Out₁ Out₂ interp dec formula W₁ W₂ hc
    (ParitySolving.leaderArenaWinDecidable_of_solver solver
      (((PositiveLTL.canonicalLTLToDPACompiler interp dec).compile
          formula).starGame (In₁ := In₁) (In₂ := In₂)
        W₁ W₂).commonSignalShadowGame)
    hfold

end Berwanger

end Literature

end DistributedSynthesis
