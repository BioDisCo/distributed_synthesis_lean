/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Formalizations.ComponentTrees.ConsensusBroadcaster

/-!
# Agreeing on a broadcaster

Manuscript source label: `lem:cons:means:broadcaster`.

## Paper statement

Let~$A$ be a message adversary under which consensus is solvable within~$R$ rounds.
    Then there is a distributed algorithm that makes both processes decide at round~$R$ on a common process~$p$, which is a broadcaster for the first~$R$ rounds.

## Reading the proof

See the [proof locations](PROOFS.md#agreeing-on-a-broadcaster) for direct links to the
underlying declarations. The full Lean statements and proofs follow below.
-/

open DistributedSynthesis Characterisation

namespace DistributedSynthesis.Paper.Broadcaster

/-- Reuses `Characterisation.ComponentTrees.consensus_broadcaster`. -/
theorem consensus_broadcaster :
    ∀ {V I₁ I₂ : Type} [Nontrivial V] (A : Set (ℕ → Graph)) (R : ℕ)
      (σ : StrategyPair V V (Option V) (Option V)),
      ComponentGames.Consensus.SolvesBy σ A R →
        ∃ (select : StrategyPair I₁ I₂ Proc Proc),
          ∀ (h : EnvHistory I₁ I₂),
            History.length h = R →
              LivePrefix A (History.graphSequence h) →
                ∃ (p : Proc),
                  select.one (currentView Proc.one h) = p ∧
                    select.two (currentView Proc.two h) = p ∧
                      ∃ (a : List Graph) (g : Graph) (b : List Graph),
                        History.graphSequence h = a ++ [g] ++ b ∧ DeliversFrom p g :=
  @_root_.Characterisation.ComponentTrees.consensus_broadcaster

end DistributedSynthesis.Paper.Broadcaster
