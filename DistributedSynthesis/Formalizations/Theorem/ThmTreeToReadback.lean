/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmGlobalTreeWinning
import DistributedSynthesis.Formalizations.Theorem.ThmJournalPlayCorrespondence

/-!
# From an accepted journal tree to accepted readback executions

The composition of the HG-C winning chain with the H4 readback chain:
acceptance of a transition-rational journal tree places the initial
boundary in Even's winning region of the boundary game
(`bnd_initial_mem_winningRegion_of_accepts`), countable positional
determinacy turns the history winner into a positional one, and the
play correspondence (`accepts_execution_journalStrategy_of_winning`)
makes every no-direct execution of the committed plans' journal
readback accepted.
-/

namespace DistributedSynthesis

universe u v x y s

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}

namespace DetParityAutomaton

variable
  {A :
    DetParityAutomaton.{max u v x y, s}
      (RoundRecord In₁ In₂ Graph Out₁ Out₂)}

variable
  (t :
    TransitionRationalTree.{max u v s, max u v x y s, s}
      (GlobalJournalBranch (In₁ := In₁) A)
      (GlobalJournalLabel (In₁ := In₁) A))

variable [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
variable [DecidableEq In₁] [DecidableEq In₂] [DecidableEq A.State]
variable [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]
variable [DecidableEq t.Control] [Inhabited t.Control]
variable (CL : LeftThreadChecker (In₁ := In₁) A)
variable (CR : RightThreadChecker (In₁ := In₁) A)
variable (CC : ChainThreadChecker (In₁ := In₁) (A := A))

/-- Acceptance yields a positional Even winner of the boundary game. -/
theorem exists_positional_boundary_winner_of_accepts
    (hacc : (globalJournalAutomaton A CL CR CC).acceptsTree t.labeledTree) :
    ∃ τ :
        (DetParityAutomaton.boundaryGame A
            (ULift.{max u v x y, s} t.Control)
            (ULift.{max u v x y, s} t.Control)
            (ULift.{max u v x y, s} t.Control)).PositionalStrategy
          ParityPlayer.even,
      CountableParityGame.PositionalStrategy.WinningFrom
        (G :=
          DetParityAutomaton.boundaryGame A
            (ULift.{max u v x y, s} t.Control)
            (ULift.{max u v x y, s} t.Control)
            (ULift.{max u v x y, s} t.Control))
        τ (Sum.inl (A.initial, A.initial)) :=
  (DetParityAutomaton.boundaryGame A
      (ULift.{max u v x y, s} t.Control)
      (ULift.{max u v x y, s} t.Control)
      (ULift.{max u v x y, s} t.Control)).positionalDeterminacy
    ParityPlayer.even (Sum.inl (A.initial, A.initial))
    (bnd_initial_mem_winningRegion_of_accepts t CL CR CC hacc)

/--
Acceptance of the journal tree yields a committed plan family whose
journal readback strategy has every no-direct execution accepted:
the readback endpoint of the fragment upgrade, conditional only on
tree acceptance.
-/
theorem journal_readback_accepts_of_accepts
    (hacc : (globalJournalAutomaton A CL CR CC).acceptsTree t.labeledTree) :
    ∃ plans :
        PlanFamily (In₁ := In₁) A (ULift.{max u v x y, s} t.Control)
          (ULift.{max u v x y, s} t.Control)
          (ULift.{max u v x y, s} t.Control),
      ∀ env : EnvironmentSequence In₁ In₂,
        NoDirectReversalSequence env ->
          A.Accepts (execution (journalStrategy plans) env) := by
  obtain ⟨τ, hτ⟩ :=
    exists_positional_boundary_winner_of_accepts t CL CR CC hacc
  exact
    ⟨plansOf τ, fun env hnodirect =>
      accepts_execution_journalStrategy_of_winning τ hτ env hnodirect⟩

/--
Full-model readback: acceptance of the journal tree yields a committed plan
family whose readback strategy has *every* execution accepted — on all
environments, including direct reversals — given the entry-indexed
measurability certificate `hcert`.

The certificate is the honest existential of paper `prop:starcomplete`: whenever
the boundary game is won, it has a **θ̄-measurable** positional winner (one whose
committed blind tables are `b_old`-invariant, `ReversalMeasurable`).  This is the
folding of a realizing strategy onto its θ̄-representative (`lem:blindonetransducer`,
finite index `prop:reversedblockmonitor`, hierarchy `prop:dynhier`) followed by
re-positionalization.  Unlike the blanket `∀ τ, ReversalMeasurable (plansOf τ)`
-- which the paper's state-tailoring `τ` refutes -- this existential is true at
paper rigor and non-vacuous: we consume a measurable winner, not an arbitrary one.
-/
theorem journal_readback_accepts_of_accepts_full
    (hacc : (globalJournalAutomaton A CL CR CC).acceptsTree t.labeledTree)
    (hcert :
      ∀ τ :
          (DetParityAutomaton.boundaryGame A
              (ULift.{max u v x y, s} t.Control)
              (ULift.{max u v x y, s} t.Control)
              (ULift.{max u v x y, s} t.Control)).PositionalStrategy
            ParityPlayer.even,
        CountableParityGame.PositionalStrategy.WinningFrom
            (G :=
              DetParityAutomaton.boundaryGame A
                (ULift.{max u v x y, s} t.Control)
                (ULift.{max u v x y, s} t.Control)
                (ULift.{max u v x y, s} t.Control))
            τ (Sum.inl (A.initial, A.initial)) ->
          ∃ τ' :
              (DetParityAutomaton.boundaryGame A
                  (ULift.{max u v x y, s} t.Control)
                  (ULift.{max u v x y, s} t.Control)
                  (ULift.{max u v x y, s} t.Control)).PositionalStrategy
                ParityPlayer.even,
            CountableParityGame.PositionalStrategy.WinningFrom
                (G :=
                  DetParityAutomaton.boundaryGame A
                    (ULift.{max u v x y, s} t.Control)
                    (ULift.{max u v x y, s} t.Control)
                    (ULift.{max u v x y, s} t.Control))
                τ' (Sum.inl (A.initial, A.initial)) ∧
              ReversalMeasurable (plansOf τ')) :
    ∃ plans :
        PlanFamily (In₁ := In₁) A (ULift.{max u v x y, s} t.Control)
          (ULift.{max u v x y, s} t.Control)
          (ULift.{max u v x y, s} t.Control),
      ∀ env : EnvironmentSequence In₁ In₂,
        A.Accepts (execution (journalStrategy plans) env) := by
  obtain ⟨τ, hτ⟩ :=
    exists_positional_boundary_winner_of_accepts t CL CR CC hacc
  obtain ⟨τ', hτ', hmeas⟩ := hcert τ hτ
  exact
    ⟨plansOf τ', fun env =>
      accepts_execution_journalStrategy_of_winning_full τ' hτ' env hmeas⟩

end DetParityAutomaton

end DistributedSynthesis
