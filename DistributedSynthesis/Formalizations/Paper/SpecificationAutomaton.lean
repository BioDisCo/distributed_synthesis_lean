/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Formalizations.ComponentGames.Objective

/-!
# The specification automaton

Manuscript source label: `lem:A_phi`.

## Paper statement

From $\mathcal A_\text{adv}$ and an \ac{LTL} formula~$\phi$, one can construct a deterministic parity
  automaton $\mathcal A_\phi = (Q_\phi, q_\phi, \delta_\phi, \chi_\phi)$, with states $Q_\phi$, initial state $q_\phi$,
  transition function $\delta_\phi: Q_\phi \times (\Sigma \times \Omega) \to Q_\phi$, and priorities $\chi_\phi: Q_\phi \to \NN$,
  that accepts the executions $e \in (\Sigma \times \Omega)^\omega$ with $\Graph(e) \notin A$ or $e \models \phi$.

## Reading the proof

See the [proof locations](PROOFS.md#the-specification-automaton) for direct links to the
underlying declarations. The full Lean statements and proofs follow below.
-/

open DistributedSynthesis Characterisation

namespace DistributedSynthesis.Paper.SpecificationAutomaton

/-- Reuses `Characterisation.ComponentGames.A_phi_language`. -/
theorem A_phi_language :
    ∀ (adversary : DetParityAutomaton Graph) (i : WithInputs.Instance)
      (word : ℕ → WithInputs.TupleLetter i),
      (WithInputs.guardedInstanceObjective adversary i).Accepts word ↔
        (¬adversary.Accepts fun (n : ℕ) => (word n).1.2.2) ∨
          LTL.Satisfies (EncodedNoDirect.interp i) (OmegaWord.map continuationRecord word)
            (EncodedFiniteLTL.decode i.formula) :=
  @_root_.Characterisation.ComponentGames.A_phi_language

/-- Reuses `Characterisation.ComponentGames.A_phi_uniform_compiler`. -/
theorem A_phi_uniform_compiler :
    Primrec EncodedGuardedObjective.compile ∧
      ∀ (d : EncodedGuardedObjective.Data) (alphabet : (EncodedParityTables.rows d.1).length = 3)
        (word : ℕ → WithInputs.TupleLetter d.2),
        (EncodedLeaderObjective.automaton (d.2, EncodedGuardedObjective.compile d)).Accepts word ↔
          (¬(EncodedGuardedObjective.graphAutomaton d.1 alphabet).Accepts fun (n : ℕ) => (word n).1.2.2) ∨
            LTL.Satisfies (EncodedNoDirect.interp d.2) (OmegaWord.map continuationRecord word)
              (EncodedFiniteLTL.decode d.2.formula) :=
  @_root_.Characterisation.ComponentGames.A_phi_uniform_compiler

end DistributedSynthesis.Paper.SpecificationAutomaton
