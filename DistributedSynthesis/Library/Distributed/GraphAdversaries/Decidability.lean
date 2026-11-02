/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderGame.Encoding.EncodedHolesSolverCorrect
import DistributedSynthesis.Library.Distributed.GraphAdversaries.LeaderGame

/-! The positive graph-hole theorem for LTL synthesis with arbitrary finite
private inputs. Each fixed omega-regular adversary with graph-only holes has
a primitive-recursive Boolean solver on the existing library instance encoding. -/
namespace Characterisation.WithInputs
open DistributedSynthesis
set_option maxHeartbeats 1600000

/-- Empty promises admit every instance, since all four alphabets are nonempty. -/
theorem realizable_of_empty (A : Set (Nat → Graph)) (empty : ¬ A.Nonempty) (i : Instance) :
    Realizable A i := by
  refine ⟨⟨fun _ => 0,fun _ => 0⟩,?_⟩
  intro env admitted
  exact False.elim (empty ⟨_,admitted⟩)

/-- Fixed graph-only holes supply the graph bounds once; the compiler remains
primitive recursive in the formula, truth table, and four finite alphabets. -/
theorem holes_primitive_recursive_solver_nonempty
    (A : Set (Nat → Graph)) (nonempty : A.Nonempty)
    (adversary : DetParityAutomaton.{0,0} Graph)
    (recognizes : ∀ word, word ∈ A ↔ adversary.Accepts word)
    (holes : GeometricHoles A) :
    ∃ solve : Instance → Bool, Primrec solve ∧ ∀ i, solve i = true ↔ Realizable A i := by
  classical
  have regular : OmegaRegular A := ⟨adversary,recognizes⟩
  obtain ⟨delay,recent⟩ := holes_component_recent_receiver A regular holes
  obtain ⟨K,bounded⟩ := (omegaRegular_holes_iff_bounded_components A regular).mp holes
  let graphs := Fintype.equivFin (GraphRootState adversary.State delay K)
  obtain ⟨initialGraph,represented⟩ := graphRootRep_exists (prefixRecognizer adversary)
    (LivePrefix A) delay K bounded []
  obtain ⟨tables,effective,language⟩ := EncodedGuardedObjective.uniform_frontend adversary
  let context := EncodedHeaderCompiler.graphDataEncode (B:=0) (prefixRecognizer adversary) graphs
  let leaders := EncodedPublicLeaderGame.leaderTable graphs
  have live : LivePrefix A [] := by
    obtain ⟨word,admitted⟩ := nonempty
    exact ⟨word,admitted,rfl⟩
  refine ⟨EncodedHolesSolver.solve context leaders K (graphs initialGraph).val tables,
    EncodedHolesSolver.solve_primrec context leaders K (graphs initialGraph).val tables effective,?_⟩
  intro i
  exact EncodedHolesSolver.solve_correct A adversary recognizes graphs initialGraph represented
    tables language recent bounded live i

/-- Existence of an actual primitive-recursive solver, including the empty
adversary. No solver or instance-dependent presentation is assumed. -/
theorem holes_primitive_recursive_solver
    (A : Set (Nat → Graph)) (regular : OmegaRegular A) (holes : GeometricHoles A) :
    ∃ solve : Instance → Bool, Primrec solve ∧ ∀ i, solve i = true ↔ Realizable A i := by
  classical
  by_cases nonempty : A.Nonempty
  · obtain ⟨adversary,recognizes⟩ := regular
    exact holes_primitive_recursive_solver_nonempty A nonempty adversary recognizes holes
  · refine ⟨fun _ => true,Primrec.const true,fun i => ?_⟩
    exact iff_of_true rfl (realizable_of_empty A nonempty i)

/-- Graph-only holes imply computable finite-private-input LTL synthesis. -/
theorem holes_realizable_computable
    (A : Set (Nat → Graph)) (regular : OmegaRegular A) (holes : GeometricHoles A) :
    ComputablePred (Realizable A) := by
  obtain ⟨solve,effective,correct⟩ := holes_primitive_recursive_solver A regular holes
  exact (Primrec.eq.comp effective (Primrec.const true)).computablePred.of_eq correct

/-- The full positive characterization requested for the finite-input model. -/
theorem positiveHolesCharacterization : PositiveHolesCharacterization :=
  holes_realizable_computable

end Characterisation.WithInputs
