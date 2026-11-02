/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Definition.DefSynthesisProblem

/-!
# Blind cross-reading at the execution level

This file proves `cor:blindcrossreading` (`real_model/paper.tex`) for real
strategy executions: flip the acknowledgement bit `b_old` of an environment
sequence -- the graph of one receive round of the blind process, `left`
versus `both` for process `1` -- and, as long as the blind process does not
receive again, its view and hence its strategy outputs are *unchanged*, round
by round, at the reversal round itself included.

This is the "one response on both `b_old` variants" half of the
sufficient-statistic fold of `prop:starcomplete`(b): a legal blind strategy
cannot branch on `b_old`, so along the reversed block it already plays the
single table value the fold commits.  The record-level view invariance is
`LemViewinv`; here the suffix records are not given but *generated* by the
strategy, so the invariance of the blind view and of the blind outputs must
be established simultaneously.  The proof rests on views reading only inputs
and graphs, never outputs: the informed side's outputs do diverge after the
flip, but they never enter the blind view while the block lasts.
-/

namespace DistributedSynthesis

universe u v x y

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}

/-- **Blind-view invariance under a `b_old` flip (process `1`).**  If two
environment sequences agree everywhere except at round `s`, where they carry
the same inputs and each lets process `1` receive (`left` or `both`), and
every round strictly between `s` and `n` is `right`, then process `1` has the
same view after `n` rounds of the two generated executions. -/
theorem executionPrefix_one_view_bOldFlip
    (σ : StrategyPair In₁ In₂ Out₁ Out₂)
    (env env' : EnvironmentSequence In₁ In₂) (s : Nat)
    (hagree : ∀ k : Nat, k ≠ s → env k = env' k)
    (hin₁ : (env s).inputOne = (env' s).inputOne)
    (hin₂ : (env s).inputTwo = (env' s).inputTwo)
    (hg : (env s).graph = Graph.left ∨ (env s).graph = Graph.both)
    (hg' : (env' s).graph = Graph.left ∨ (env' s).graph = Graph.both)
    (n : Nat)
    (hafter : ∀ k : Nat, s < k → k < n → (env k).graph = Graph.right) :
    currentView Proc.one (executionPrefix σ env n) =
      currentView Proc.one (executionPrefix σ env' n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rcases Nat.lt_trichotomy n s with hns | rfl | hsn
      · have hpre : executionPrefix σ env (n + 1) = executionPrefix σ env' (n + 1) :=
          executionPrefix_congr_of_env_eq_lt σ
            (fun k hk => hagree k (by omega))
        rw [hpre]
      · have hpre : executionPrefix σ env n = executionPrefix σ env' n :=
          executionPrefix_congr_of_env_eq_lt σ
            (fun k hk => hagree k (by omega))
        rw [currentView_executionPrefix_succ, currentView_executionPrefix_succ,
          hpre]
        rcases hg with hgl | hgl <;> rcases hg' with hgl' | hgl' <;>
          simp [nextView, advanceViewsWithEnvironment, hgl, hgl', hin₁, hin₂]
      · have hgn : (env n).graph = Graph.right :=
          hafter n hsn (Nat.lt_succ_self n)
        have henvn : env n = env' n := hagree n (by omega)
        have ihv := ih (fun k hk hkn => hafter k hk (by omega))
        rw [currentView_executionPrefix_succ, currentView_executionPrefix_succ,
          ← henvn]
        simp only [nextView, advanceViewsWithEnvironment, hgn]
        simpa [currentView] using ihv

/-- **Blind-output invariance under a `b_old` flip (process `1`).**  Under the
hypotheses of `executionPrefix_one_view_bOldFlip`, process `1` emits the same
output at every round `k` with no receive strictly after `s` up to `k` -- the
reversal round `k = s` and every earlier round included.  The informed side's
outputs may diverge from round `s` on; they never reach process `1`'s view
inside the block. -/
theorem execution_outputOne_bOldFlip
    (σ : StrategyPair In₁ In₂ Out₁ Out₂)
    (env env' : EnvironmentSequence In₁ In₂) (s : Nat)
    (hagree : ∀ k : Nat, k ≠ s → env k = env' k)
    (hin₁ : (env s).inputOne = (env' s).inputOne)
    (hin₂ : (env s).inputTwo = (env' s).inputTwo)
    (hg : (env s).graph = Graph.left ∨ (env s).graph = Graph.both)
    (hg' : (env' s).graph = Graph.left ∨ (env' s).graph = Graph.both)
    (k : Nat)
    (hafter : ∀ j : Nat, s < j → j ≤ k → (env j).graph = Graph.right) :
    (execution σ env k).outputOne = (execution σ env' k).outputOne := by
  rcases Nat.lt_trichotomy k s with hks | rfl | hsk
  · have hpre : executionPrefix σ env k = executionPrefix σ env' k :=
      executionPrefix_congr_of_env_eq_lt σ (fun j hj => hagree j (by omega))
    have henvk : env k = env' k := hagree k (by omega)
    simp [execution_apply, hpre, henvk]
  · have hpre : executionPrefix σ env k = executionPrefix σ env' k :=
      executionPrefix_congr_of_env_eq_lt σ (fun j hj => hagree j (by omega))
    simp only [execution_apply, nextRound_outputOne]
    rcases hg with hgl | hgl <;> rcases hg' with hgl' | hgl' <;>
      simp [nextView, advanceViewsWithEnvironment, hgl, hgl', hin₁, hin₂, hpre]
  · have hgk : (env k).graph = Graph.right := hafter k hsk (Nat.le_refl k)
    have henvk : env k = env' k := hagree k (by omega)
    have hview :
        currentView Proc.one (executionPrefix σ env k) =
          currentView Proc.one (executionPrefix σ env' k) :=
      executionPrefix_one_view_bOldFlip σ env env' s hagree hin₁ hin₂ hg hg' k
        (fun j hj hjk => hafter j hj (by omega))
    simp only [execution_apply, nextRound_outputOne, ← henvk]
    simp only [nextView, advanceViewsWithEnvironment, hgk]
    simp only [currentView] at hview
    rw [hview]

/-- **Blind-view invariance under a `b_new` flip (process `2`).**  The
orientation mirror: the flipped round lets process `2` receive (`right` or
`both`), and every round strictly between `s` and `n` is `left`. -/
theorem executionPrefix_two_view_bOldFlip
    (σ : StrategyPair In₁ In₂ Out₁ Out₂)
    (env env' : EnvironmentSequence In₁ In₂) (s : Nat)
    (hagree : ∀ k : Nat, k ≠ s → env k = env' k)
    (hin₁ : (env s).inputOne = (env' s).inputOne)
    (hin₂ : (env s).inputTwo = (env' s).inputTwo)
    (hg : (env s).graph = Graph.right ∨ (env s).graph = Graph.both)
    (hg' : (env' s).graph = Graph.right ∨ (env' s).graph = Graph.both)
    (n : Nat)
    (hafter : ∀ k : Nat, s < k → k < n → (env k).graph = Graph.left) :
    currentView Proc.two (executionPrefix σ env n) =
      currentView Proc.two (executionPrefix σ env' n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rcases Nat.lt_trichotomy n s with hns | rfl | hsn
      · have hpre : executionPrefix σ env (n + 1) = executionPrefix σ env' (n + 1) :=
          executionPrefix_congr_of_env_eq_lt σ
            (fun k hk => hagree k (by omega))
        rw [hpre]
      · have hpre : executionPrefix σ env n = executionPrefix σ env' n :=
          executionPrefix_congr_of_env_eq_lt σ
            (fun k hk => hagree k (by omega))
        rw [currentView_executionPrefix_succ, currentView_executionPrefix_succ,
          hpre]
        rcases hg with hgl | hgl <;> rcases hg' with hgl' | hgl' <;>
          simp [nextView, advanceViewsWithEnvironment, hgl, hgl', hin₁, hin₂]
      · have hgn : (env n).graph = Graph.left :=
          hafter n hsn (Nat.lt_succ_self n)
        have henvn : env n = env' n := hagree n (by omega)
        have ihv := ih (fun k hk hkn => hafter k hk (by omega))
        rw [currentView_executionPrefix_succ, currentView_executionPrefix_succ,
          ← henvn]
        simp only [nextView, advanceViewsWithEnvironment, hgn]
        simpa [currentView] using ihv

/-- **Blind-output invariance under a `b_new` flip (process `2`).**  The
orientation mirror of `execution_outputOne_bOldFlip`. -/
theorem execution_outputTwo_bOldFlip
    (σ : StrategyPair In₁ In₂ Out₁ Out₂)
    (env env' : EnvironmentSequence In₁ In₂) (s : Nat)
    (hagree : ∀ k : Nat, k ≠ s → env k = env' k)
    (hin₁ : (env s).inputOne = (env' s).inputOne)
    (hin₂ : (env s).inputTwo = (env' s).inputTwo)
    (hg : (env s).graph = Graph.right ∨ (env s).graph = Graph.both)
    (hg' : (env' s).graph = Graph.right ∨ (env' s).graph = Graph.both)
    (k : Nat)
    (hafter : ∀ j : Nat, s < j → j ≤ k → (env j).graph = Graph.left) :
    (execution σ env k).outputTwo = (execution σ env' k).outputTwo := by
  rcases Nat.lt_trichotomy k s with hks | rfl | hsk
  · have hpre : executionPrefix σ env k = executionPrefix σ env' k :=
      executionPrefix_congr_of_env_eq_lt σ (fun j hj => hagree j (by omega))
    have henvk : env k = env' k := hagree k (by omega)
    simp [execution_apply, hpre, henvk]
  · have hpre : executionPrefix σ env k = executionPrefix σ env' k :=
      executionPrefix_congr_of_env_eq_lt σ (fun j hj => hagree j (by omega))
    simp only [execution_apply, nextRound_outputTwo]
    rcases hg with hgl | hgl <;> rcases hg' with hgl' | hgl' <;>
      simp [nextView, advanceViewsWithEnvironment, hgl, hgl', hin₁, hin₂, hpre]
  · have hgk : (env k).graph = Graph.left := hafter k hsk (Nat.le_refl k)
    have henvk : env k = env' k := hagree k (by omega)
    have hview :
        currentView Proc.two (executionPrefix σ env k) =
          currentView Proc.two (executionPrefix σ env' k) :=
      executionPrefix_two_view_bOldFlip σ env env' s hagree hin₁ hin₂ hg hg' k
        (fun j hj hjk => hafter j hj (by omega))
    simp only [execution_apply, nextRound_outputTwo, ← henvk]
    simp only [nextView, advanceViewsWithEnvironment, hgk]
    simp only [currentView] at hview
    rw [hview]

end DistributedSynthesis
