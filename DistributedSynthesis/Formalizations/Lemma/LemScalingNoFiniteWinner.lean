/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemScalingPhysicalRows
import DistributedSynthesis.Formalizations.Lemma.LemScalingSourceWinner
import DistributedSynthesis.Formalizations.Lemma.LemFiniteBlindLiteralTraceObstruction

/-!
# A realizable finite safety objective without a finite distributed winner

The source realizes the literal objective on every environment. Conversely,
any finite physical winner induces connected rows whose masses grow by a
common factor in {2,4}. A blind endpoint makes these factors eventually
periodic, contradicting the row mass bounds. No conservation certificate or
agreement with the source is a hypothesis of the impossibility theorem.
-/

namespace DistributedSynthesis.ScalingSafety

universe u v

theorem Physical.row_mode_periodic
    (C : FinitePairedPhysicalController.{0,0,0,0,u,v} Unit Unit Label Label) :
    WordEventuallyPeriodic (rowMode C) := by
  simpa only [rowMode, Function.iterate_succ_apply] using
    finite_orbit_output_eventuallyPeriodic (blind C) (mode C)
      (blind C (left C (root C)))

/-- No finite controller wins this objective, even when it may freely
replace every output of the exhibited perfect-recall strategy. -/
theorem no_finite_winner
    (C : FinitePairedPhysicalController.{0,0,0,0,u,v} Unit Unit Label Label) :
    ¬ Physical.Winning C := by
  intro hwin
  exact ScalingAperiodicity.no_eventually_periodic_scaling
    (Physical.rowMass C) (Physical.rowMode C) 1
    (Physical.row_recurrence C hwin) (Physical.row_mode_cases C)
    (Physical.row_mass_bounds C) (Physical.row_mode_periodic C)

/-- End-to-end counterexample to universal finite winning replacement. -/
theorem realizable_not_finite :
    (∃ σ : StrategyPair Unit Unit Label Label,
      ∀ env, objective.Accepts (execution σ env)) ∧
    ¬ (∃ C : FinitePairedPhysicalController.{0,0,0,0,u,v} Unit Unit Label Label,
      ∀ env, objective.Accepts
        (C.globalMachine.globalMachineTraceWord C.globalOutputOne C.globalOutputTwo env)) := by
  refine ⟨Source.realizable, ?_⟩
  rintro ⟨C,hC⟩
  exact no_finite_winner C hC

/-- Finite blind-library synthesis is sound, but cannot cover this
realizable objective. Both blind-control types are finite here. -/
theorem no_accepting_finite_blind_library
    (L : BlindControllerLibrary.{0,0,0,0,u,v} Unit Unit Label Label)
    [Fintype L.OneControl] [Fintype L.TwoControl] :
    ¬ L.HasAcceptingTree objective := by
  letI : Inhabited Label := ⟨Source.label 0 0⟩
  intro h
  obtain ⟨C,hC⟩ := L.exists_winning_physical_controller objective h
  exact no_finite_winner C hC

/-- The exact strategy-indexed finite-extraction gate used by the positive
development is false for this finite objective. -/
theorem not_perStrategyWinningFinitePairedPhysicalController :
    ¬ DetParityAutomaton.PerStrategyWinningFinitePairedPhysicalController.{0,0,0,0,0,u}
      objective := by
  intro h
  obtain ⟨C,hC⟩ := h Source.strategy Source.wins
  exact no_finite_winner C hC

end DistributedSynthesis.ScalingSafety
