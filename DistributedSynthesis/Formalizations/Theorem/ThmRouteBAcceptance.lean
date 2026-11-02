/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmTreeToReadback

/-!
# Readback acceptance from summary-level transfer

The constructions below take `SummaryAcceptanceTransfer` as an explicit
hypothesis. It transfers acceptance of summary readback strategies from the
no-direct-reversal fragment to all environments. The resulting readback
acceptance theorem uses this transfer in place of `ReversalMeasurable`.
This module proves the conditional implication; it does not supply the
transfer hypothesis for arbitrary summary automata.
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

/--
The summary-soundness certificate (paper `prop:starcomplete`+`prop:starsound`,
summary level), honest existential form: from any *winning* boundary strategy `τ`,
there is a *folded* winning strategy `τ'` whose journal readback -- a
view-measurable, `b_old`-robust strategy -- is accepted on **every** environment,
direct reversals included.

This replaces `EntryIndexedCertificate`, and unlike it, is true: the fold onto the
`θ̄`-representative (`prop:starcomplete`, finite index `prop:reversedblockmonitor`,
delay-one hierarchy `lem:delayonehierarchy`) yields a readback whose acceptance
transfers across every reversal by fringe elimination (`lem:fringe`,
`read_crossReading`).  It states the all-environment acceptance *directly*, so it
never routes through the arena correspondence / `ReversalMeasurable` that was stuck
at the atom-indexing wall.  A `∀ plans` "transfer" would be false (a readback can be
accepted on the fragment yet wrong at a reversal); this existential over folded
winners is the correct, satisfiable statement.
-/
abbrev SummarySoundnessCertificate : Prop :=
  ∀ (C : Type s) [Fintype C] [DecidableEq C] [Inhabited C]
    (τ :
      (DetParityAutomaton.boundaryGame A
          (ULift.{max u v x y, s} C) (ULift.{max u v x y, s} C)
          (ULift.{max u v x y, s} C)).PositionalStrategy ParityPlayer.even),
    CountableParityGame.PositionalStrategy.WinningFrom
        (G :=
          DetParityAutomaton.boundaryGame A
            (ULift.{max u v x y, s} C) (ULift.{max u v x y, s} C)
            (ULift.{max u v x y, s} C))
        τ (Sum.inl (A.initial, A.initial)) ->
      ∃ τ' :
          (DetParityAutomaton.boundaryGame A
              (ULift.{max u v x y, s} C) (ULift.{max u v x y, s} C)
              (ULift.{max u v x y, s} C)).PositionalStrategy ParityPlayer.even,
        CountableParityGame.PositionalStrategy.WinningFrom
            (G :=
              DetParityAutomaton.boundaryGame A
                (ULift.{max u v x y, s} C) (ULift.{max u v x y, s} C)
                (ULift.{max u v x y, s} C))
            τ' (Sum.inl (A.initial, A.initial)) ∧
          ∀ env : EnvironmentSequence In₁ In₂,
            A.Accepts (execution (journalStrategy (plansOf τ')) env)

/--
Route-B readback upgrade: acceptance of the journal tree yields a committed plan
family whose readback is accepted on *every* environment, given the
summary-soundness certificate.  Identical to `journal_readback_accepts_of_accepts`
except the conclusion drops `NoDirectReversalSequence`, discharged through the
folded-winner all-environment acceptance in place of the entry-indexed certificate.
-/
theorem journal_readback_accepts_of_accepts_route_b
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
              ∀ env : EnvironmentSequence In₁ In₂,
                A.Accepts (execution (journalStrategy (plansOf τ')) env)) :
    ∃ plans :
        PlanFamily (In₁ := In₁) A (ULift.{max u v x y, s} t.Control)
          (ULift.{max u v x y, s} t.Control)
          (ULift.{max u v x y, s} t.Control),
      ∀ env : EnvironmentSequence In₁ In₂,
        A.Accepts (execution (journalStrategy plans) env) := by
  obtain ⟨τ, hτ⟩ :=
    exists_positional_boundary_winner_of_accepts t CL CR CC hacc
  obtain ⟨τ', _, hacc'⟩ := hcert τ hτ
  exact ⟨plansOf τ', hacc'⟩

end DetParityAutomaton

end DistributedSynthesis
