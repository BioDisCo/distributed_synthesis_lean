/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledEndToEndOperationalAutomaton

/-!
# Concrete semantics of the end-to-end operational automaton

The Moore output is the second component of each local summary.  This file
removes the recursive local views from the remaining correctness proof: the
summary pair read from the two concrete execution views is exactly the finite
joint state obtained by iterating `LocalSummaryAutomaton.advance` along the
environment.  Consequently every round of the distributed readback has the
outputs stored by the next joint finite state.
-/

namespace DistributedSynthesis

universe u v x y s

namespace DetParityAutomaton

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable
  (A : DetParityAutomaton.{max u v x y, s}
    (RoundRecord In₁ In₂ Graph Out₁ Out₂))

noncomputable section

variable [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]
variable [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
variable [DecidableEq In₁] [DecidableEq In₂]

variable (bundle : EndToEndOperationalControllerPackage A)

abbrev endToEndOperationalM :=
  endToEndOperationalSummaryAutomaton A bundle

/-- The Moore tables exposed by the operational summaries. -/
def endToEndOperationalOutputOne :
    (endToEndOperationalM A bundle).Summary Proc.one -> Out₁ :=
  fun summary => summary.2

def endToEndOperationalOutputTwo :
    (endToEndOperationalM A bundle).Summary Proc.two -> Out₂ :=
  fun summary => summary.2

/-- The actual distributed strategy implemented by the finite local tables. -/
def endToEndOperationalStrategy : StrategyPair In₁ In₂ Out₁ Out₂ :=
  (endToEndOperationalM A bundle).readbackStrategy
    (endToEndOperationalOutputOne A bundle)
    (endToEndOperationalOutputTwo A bundle)

/-- Joint finite state before round `n`. -/
def endToEndOperationalTrace
    (env : EnvironmentSequence In₁ In₂) : Nat ->
      (endToEndOperationalM A bundle).Pair
  | 0 =>
      ((endToEndOperationalM A bundle).initial Proc.one,
        (endToEndOperationalM A bundle).initial Proc.two)
  | n + 1 =>
      (endToEndOperationalM A bundle).advance
        (endToEndOperationalTrace env n) (env n).graph
        (env n).inputOne (env n).inputTwo

@[simp]
theorem endToEndOperationalTrace_zero
    (env : EnvironmentSequence In₁ In₂) :
    endToEndOperationalTrace A bundle env 0 =
      ((endToEndOperationalM A bundle).initial Proc.one,
        (endToEndOperationalM A bundle).initial Proc.two) :=
  rfl

@[simp]
theorem endToEndOperationalTrace_succ
    (env : EnvironmentSequence In₁ In₂) (n : Nat) :
    endToEndOperationalTrace A bundle env (n + 1) =
      (endToEndOperationalM A bundle).advance
        (endToEndOperationalTrace A bundle env n) (env n).graph
        (env n).inputOne (env n).inputTwo :=
  rfl

/-- Reading the two execution views is the direct finite-state trace. -/
theorem endToEndOperational_readPair_executionPrefix
    (env : EnvironmentSequence In₁ In₂) (n : Nat) :
    (endToEndOperationalM A bundle).readPair
        (viewPair (executionPrefix
          (endToEndOperationalStrategy A bundle) env n)) =
      endToEndOperationalTrace A bundle env n := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      rw [executionPrefix_succ, viewPair_append]
      rw [(endToEndOperationalM A bundle).readPair_advanceViews]
      rw [ih]
      rfl

/-- The two outputs of round `n` are the Moore outputs stored in the next
finite state. -/
theorem endToEndOperational_execution_outputs
    (env : EnvironmentSequence In₁ In₂) (n : Nat) :
    ((execution (endToEndOperationalStrategy A bundle) env n).outputOne,
      (execution (endToEndOperationalStrategy A bundle) env n).outputTwo) =
      ((endToEndOperationalTrace A bundle env (n + 1)).1.2,
        (endToEndOperationalTrace A bundle env (n + 1)).2.2) := by
  rw [execution_apply]
  change
    (((endToEndOperationalM A bundle).read
        (nextView Proc.one
          (executionPrefix (endToEndOperationalStrategy A bundle) env n)
          (env n))).2,
      ((endToEndOperationalM A bundle).read
        (nextView Proc.two
          (executionPrefix (endToEndOperationalStrategy A bundle) env n)
          (env n))).2) = _
  have hpair := (endToEndOperationalM A bundle).readPair_advanceViewsWithEnvironment
    (viewPair (executionPrefix (endToEndOperationalStrategy A bundle) env n))
    (env n)
  rw [endToEndOperational_readPair_executionPrefix A bundle env n] at hpair
  have htrace :
      endToEndOperationalTrace A bundle env (n + 1) =
        (endToEndOperationalM A bundle).advance
          (endToEndOperationalTrace A bundle env n) (env n).graph
          (env n).inputOne (env n).inputTwo := rfl
  rw [← htrace] at hpair
  exact congrArg (fun pair => (pair.1.2, pair.2.2)) hpair

end

end DetParityAutomaton

end DistributedSynthesis
