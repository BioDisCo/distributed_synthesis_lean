/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmPairedEntryRationalTree
import DistributedSynthesis.Formalizations.Lemma.LemArenaSuffixTransport

/-!
# A winning strategy supplies the paired-entry acceptance obligations

This file proves the first semantic half of the Bérard reduction.  From every
generated paired entry of a globally winning distributed strategy, an
environment that stays forever in the current one-way block produces exactly
the omega word stored in the paired lambda.  Consequently Bérard's local T2
condition is automatic; it is not an additional hypothesis on the strategy.

The infinitely-switching case is kept separate because its proof is the block
minimum pasting argument.  This separation makes the remaining mathematical
boundary visible and prevents the rational-run theorem from silently assuming
the desired global reduction.
-/

namespace DistributedSynthesis

universe u v x y s

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}

namespace DetParityAutomaton

variable
  (A :
    DetParityAutomaton.{max u v x y, s}
      (RoundRecord In₁ In₂ Graph Out₁ Out₂))

@[simp]
theorem omegaPrefix_succ {Move : Type*} (env : Nat -> Move) (n : Nat) :
    omegaPrefix env (n + 1) = omegaPrefix env n ++ [env n] := by
  unfold omegaPrefix
  rw [List.ofFn_succ_last]
  simp only [Fin.val_castSucc, Fin.val_last]

/-- A continuation through an all-right environment is the corresponding
finite `extendPrefix`. -/
theorem continueExec_right_eq_extendPrefix
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (base : History In₁ In₂ Graph Out₁ Out₂)
    (env : Nat -> In₂ × In₁) :
    ∀ n : Nat,
      continueExec strategy base (fun k => rightEnvironment (env k)) n =
        extendPrefix strategy base
          ((omegaPrefix env n).map rightEnvironment) := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [continueExec, omegaPrefix_succ, List.map_append,
        List.map_singleton, extendPrefix_snoc]
      rw [ih]

/-- Mirror continuation identity for an all-left environment. -/
theorem continueExec_left_eq_extendPrefix
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (base : History In₁ In₂ Graph Out₁ Out₂)
    (env : Nat -> In₁ × In₂) :
    ∀ n : Nat,
      continueExec strategy base (fun k => leftEnvironment (env k)) n =
        extendPrefix strategy base
          ((omegaPrefix env n).map leftEnvironment) := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [continueExec, omegaPrefix_succ, List.map_append,
        List.map_singleton, extendPrefix_snoc]
      rw [ih]

/-- A globally winning strategy accepts every continuation from a generated
history, from the DPA state reached by that history. -/
theorem acceptsFrom_contWord_of_winning
    [Inhabited In₁] [Inhabited In₂]
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    {base : History In₁ In₂ Graph Out₁ Out₂}
    (hgenerated : StrategyGeneratedPrefix strategy base)
    (env : EnvironmentSequence In₁ In₂) :
    A.AcceptsFrom (entryState (A := A) base)
      (contWord strategy base env) := by
  exact (accepts_prependList_iff_acceptsFrom A base _).mp
    (accepts_prependList_contWord strategy hwin hgenerated env)

/-- The left-row paired lambda omega word is the real all-right continuation
of its representative. -/
theorem pairedRightOmegaWord_lambda_left
    [Inhabited In₂]
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (entry : ProcOnePairedEntryRep strategy)
    (env : Nat -> In₂ × In₁) :
    pairedRightOmegaWord entry.lambdaOfStrategy.blind
        entry.lambdaOfStrategy.informedLeft env =
      contWord strategy entry.leftHistory
        (fun n => rightEnvironment (env n)) := by
  funext n
  rw [contWord, continueExec_right_eq_extendPrefix]
  simp only [pairedRightOmegaWord, ProcOnePairedEntryRep.lambdaOfStrategy]
  rw [blockSenderOne_eq strategy entry.leftHistory (omegaPrefix env n) (env n)]
  rfl

/-- The `both`-row paired lambda omega word is the real all-right
continuation of its representative. -/
theorem pairedRightOmegaWord_lambda_both
    [Inhabited In₂]
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (entry : ProcOnePairedEntryRep strategy)
    (env : Nat -> In₂ × In₁) :
    pairedRightOmegaWord entry.lambdaOfStrategy.blind
        entry.lambdaOfStrategy.informedBoth env =
      contWord strategy entry.bothHistory
        (fun n => rightEnvironment (env n)) := by
  funext n
  rw [contWord, continueExec_right_eq_extendPrefix]
  simp only [pairedRightOmegaWord, ProcOnePairedEntryRep.lambdaOfStrategy]
  have hblind := congrArg
    (fun sender : SenderBlockStrategy In₁ Out₁ =>
      sender (senderWord (omegaPrefix env n)) (env n).2)
    entry.lambdaOfStrategy_blind_eq_both
  change blockSenderOne strategy entry.leftHistory
      (senderWord (omegaPrefix env n)) (env n).2 =
    blockSenderOne strategy entry.bothHistory
      (senderWord (omegaPrefix env n)) (env n).2 at hblind
  rw [hblind,
    blockSenderOne_eq strategy entry.bothHistory (omegaPrefix env n) (env n)]
  rfl

/-- Mirror right-row equality. -/
theorem pairedLeftOmegaWord_lambda_right
    [Inhabited In₁]
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (entry : ProcTwoPairedEntryRep strategy)
    (env : Nat -> In₁ × In₂) :
    pairedLeftOmegaWord entry.lambdaOfStrategy.blind
        entry.lambdaOfStrategy.informedRight env =
      contWord strategy entry.rightHistory
        (fun n => leftEnvironment (env n)) := by
  funext n
  rw [contWord, continueExec_left_eq_extendPrefix]
  simp only [pairedLeftOmegaWord, ProcTwoPairedEntryRep.lambdaOfStrategy]
  rw [blockSenderTwo_eq strategy entry.rightHistory (omegaPrefix env n) (env n)]
  rfl

/-- Mirror `both`-row equality. -/
theorem pairedLeftOmegaWord_lambda_both
    [Inhabited In₁]
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (entry : ProcTwoPairedEntryRep strategy)
    (env : Nat -> In₁ × In₂) :
    pairedLeftOmegaWord entry.lambdaOfStrategy.blind
        entry.lambdaOfStrategy.informedBoth env =
      contWord strategy entry.bothHistory
        (fun n => leftEnvironment (env n)) := by
  funext n
  rw [contWord, continueExec_left_eq_extendPrefix]
  simp only [pairedLeftOmegaWord, ProcTwoPairedEntryRep.lambdaOfStrategy]
  have hblind := congrArg
    (fun sender : SenderBlockStrategy In₂ Out₂ =>
      sender (senderWord (omegaPrefix env n)) (env n).2)
    entry.lambdaOfStrategy_blind_eq_both
  change blockSenderTwo strategy entry.rightHistory
      (senderWord (omegaPrefix env n)) (env n).2 =
    blockSenderTwo strategy entry.bothHistory
      (senderWord (omegaPrefix env n)) (env n).2 at hblind
  rw [hblind,
    blockSenderTwo_eq strategy entry.bothHistory (omegaPrefix env n) (env n)]
  rfl

/-- A winning strategy satisfies local T2 at every process-one paired entry. -/
theorem pairedRightForeverAccepts_of_winning
    [Inhabited In₁] [Inhabited In₂]
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (entry : ProcOnePairedEntryRep strategy) :
    PairedRightForeverAccepts A entry.code entry.lambdaOfStrategy := by
  constructor
  · intro env
    rw [pairedRightOmegaWord_lambda_left strategy entry env]
    exact acceptsFrom_contWord_of_winning A strategy hwin entry.leftGenerated _
  · intro env
    rw [pairedRightOmegaWord_lambda_both strategy entry env]
    exact acceptsFrom_contWord_of_winning A strategy hwin entry.bothGenerated _

/-- Mirror local T2 theorem. -/
theorem pairedLeftForeverAccepts_of_winning
    [Inhabited In₁] [Inhabited In₂]
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (entry : ProcTwoPairedEntryRep strategy) :
    PairedLeftForeverAccepts A entry.code entry.lambdaOfStrategy := by
  constructor
  · intro env
    rw [pairedLeftOmegaWord_lambda_right strategy entry env]
    exact acceptsFrom_contWord_of_winning A strategy hwin entry.rightGenerated _
  · intro env
    rw [pairedLeftOmegaWord_lambda_both strategy entry env]
    exact acceptsFrom_contWord_of_winning A strategy hwin entry.bothGenerated _

/-- Therefore the local T2 field of every reachable operational node follows
directly from global realizability. -/
theorem PairedStrategyMemory.foreverAccepts_of_winning
    [Inhabited In₁] [Inhabited In₂]
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (initial : PairedStrategyMemory A strategy) :
    initial.ForeverAccepts (A := A) := by
  intro node
  cases initial.atNode (A := A) node with
  | sink => trivial
  | processOne entry minimum =>
      exact pairedRightForeverAccepts_of_winning A strategy hwin entry
  | processTwo entry minimum =>
      exact pairedLeftForeverAccepts_of_winning A strategy hwin entry

/-- Once the infinitely-switching block-pasting lemma is supplied, a global
winning strategy yields the nonempty paired-entry language.  Local T2 has
already been discharged above and is absent from the hypotheses. -/
theorem PairedStrategyMemory.nonemptyLanguage_of_winning
    [Inhabited In₁] [Inhabited In₂]
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (initial : PairedStrategyMemory A strategy)
    (hswitching : initial.SwitchingAccepts (A := A)) :
    (pairedEntryRunAutomaton A initial.toTreeState).NonemptyLanguage :=
  initial.nonemptyLanguage (A := A)
    (initial.foreverAccepts_of_winning (A := A) hwin) hswitching

/-- End-to-end rational-run handoff from a winning strategy, conditional only
on the classical input-free rational-run basis and the checked block-pasting
statement for infinitely many reversals. -/
theorem PairedStrategyMemory.hasRationalRun_of_winning
    [Inhabited In₁] [Inhabited In₂]
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (initial : PairedStrategyMemory A strategy)
    (basis :
      (pairedEntryRunAutomaton A initial.toTreeState).RationalRunBasis)
    (hswitching : initial.SwitchingAccepts (A := A)) :
    (pairedEntryRunAutomaton A initial.toTreeState).HasRationalRun :=
  basis (initial.nonemptyLanguage_of_winning (A := A) hwin hswitching)

end DetParityAutomaton

end DistributedSynthesis
