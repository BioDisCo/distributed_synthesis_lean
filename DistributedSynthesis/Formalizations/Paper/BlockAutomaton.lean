/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Formalizations.ComponentTrees.SynthesisAutomaton

/-!
# The block automaton and live states

Manuscript source label: `lem:tree-combined-automaton`.

## Paper statement

One can construct a deterministic parity automaton
  $\mathcal B=(Q,q_\text{init},\delta,\chi)$ over
  $\Sigma^D\times\Omega^D$ that accepts exactly the executions,
  grouped into blocks, that satisfy~$\phi$ or whose graph sequence
  is outside~$A$.
Moreover, one can compute a subset $Q_\text{live}\subseteq Q$ such that,
  after any finite sequence of blocks, the automaton is in
  $Q_\text{live}$ if and only if the corresponding graph sequence
  extends to a word in~$A$.

## Reading the proof

See the [proof locations](PROOFS.md#the-block-automaton-and-live-states) for direct links to the
underlying declarations. The full Lean statements and proofs follow below.
-/

open DistributedSynthesis Characterisation

namespace DistributedSynthesis.Paper.BlockAutomaton

/-- Reuses `Characterisation.ComponentTrees.synthesisBlockAutomaton_language`. -/
theorem synthesisBlockAutomaton_language :
    ∀ (A : Set (ℕ → Graph)) (adversary : DetParityAutomaton Graph),
      (∀ (word : ℕ → Graph), word ∈ A ↔ adversary.Accepts word) →
        ∀ (i : WithInputs.Instance) {D : ℕ},
          0 < D →
            ∀ (word : ℕ → WithInputs.TupleLetter i),
              (ComponentTrees.synthesisBlockAutomaton adversary i D).Accepts (ComponentTrees.groupedWord word D) ↔
                (fun (n : ℕ) => (word n).1.2.2) ∉ A ∨
                  LTL.Satisfies (EncodedNoDirect.interp i) (OmegaWord.map continuationRecord word)
                    (EncodedFiniteLTL.decode i.formula) :=
  @_root_.Characterisation.ComponentTrees.synthesisBlockAutomaton_language

/-- Reuses `Characterisation.ComponentTrees.synthesisBlockAutomaton_live`. -/
theorem synthesisBlockAutomaton_live :
    ∀ (A : Set (ℕ → Graph)) (adversary : DetParityAutomaton Graph),
      (∀ (word : ℕ → Graph), word ∈ A ↔ adversary.Accepts word) →
        ∀ (i : WithInputs.Instance) (D : ℕ) (words : List (PeriodicBlocks.BlockWord (WithInputs.TupleLetter i) D)),
          List.foldl (ComponentTrees.synthesisBlockAutomaton adversary i D).step
                (ComponentTrees.synthesisBlockAutomaton adversary i D).initial words ∈
              ComponentTrees.blockLive (ComponentTrees.jointRecognizer (prefixRecognizer adversary))
                (WithInputs.guardedInstanceObjective adversary i) D ↔
            LivePrefix A (List.map (fun (a : WithInputs.TupleLetter i) => a.1.2.2) (List.map Subtype.val words).flatten) :=
  @_root_.Characterisation.ComponentTrees.synthesisBlockAutomaton_live

end DistributedSynthesis.Paper.BlockAutomaton
