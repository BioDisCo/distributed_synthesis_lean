/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmArenaFold
import DistributedSynthesis.Formalizations.Lemma.LemSameThetaInterchange

/-!
# Arena suffix words and the acceptance-transport frame

The arena-level frame for `hsound` (`prop:starsound` for the summary fold).
The execution-level replay transport (`LemThetaBarReplayTable`) rests on two
world-agnostic moves: decompose an ω-word at a cut into prefix and suffix,
and transport acceptance through the prefix by the automaton state it
reaches.  This file supplies the same frame for **arena** words:

* `arenaFoldSeqFrom`/`arenaWordFrom` -- the arena run and its emitted word
  started from an arbitrary position;
* `arenaWord_decompose` -- every arena word is its first `k` records
  prepended to the suffix word from the position reached at `k`;
* `accepts_prependList_iff_acceptsFrom` -- prefix transport in `AcceptsFrom`
  form (the general lemma behind `accepts_prependList_congr`);
* `accepts_arenaWord_of_suffix_match` -- the `hsound` skeleton: if the
  summary fold's suffix word from its reached position *equals* a reference
  family's suffix word (the finite per-tier simulation, to be supplied), and
  the two prefixes drive `A` to the same state, then acceptance transfers.

What remains beyond this frame is exactly the finite simulation between the
summary family's block run and the representative committed plan's block run
(the per-tier record matching of the extracted tables), plus the
boundary-round contingency already represented in the arena's staged
closing.
-/

namespace DistributedSynthesis

universe u v x y s w t

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}

namespace DetParityAutomaton

variable {A : DetParityAutomaton.{max u v x y, s} (RoundRecord In₁ In₂ Graph Out₁ Out₂)}
variable {C_L C_R C_V : Type max u v x y s}

/-- The arena position stream started from an arbitrary position. -/
def arenaFoldSeqFrom (plans : PlanFamily (In₁ := In₁) A C_L C_R C_V)
    (start : BoundaryGamePosition (In₁ := In₁) A C_L C_R C_V)
    (env : EnvironmentSequence In₁ In₂) :
    Nat → BoundaryGamePosition (In₁ := In₁) A C_L C_R C_V
  | 0 => start
  | n + 1 => arenaStep plans (arenaFoldSeqFrom plans start env n) (env n)

/-- The word emitted from an arbitrary position. -/
def arenaWordFrom (plans : PlanFamily (In₁ := In₁) A C_L C_R C_V)
    (start : BoundaryGamePosition (In₁ := In₁) A C_L C_R C_V)
    (env : EnvironmentSequence In₁ In₂) :
    OmegaWord (RoundRecord In₁ In₂ Graph Out₁ Out₂) :=
  fun n => arenaRecord plans (arenaFoldSeqFrom plans start env n) (env n)

/-- Restarting the fold at the position reached after `k` rounds, against the
shifted environment, reproduces the original stream. -/
theorem arenaFoldSeqFrom_arenaFoldSeq
    (plans : PlanFamily (In₁ := In₁) A C_L C_R C_V)
    (env : EnvironmentSequence In₁ In₂) (k : Nat) :
    ∀ n : Nat,
      arenaFoldSeqFrom plans (arenaFoldSeq plans env k) (OmegaWord.drop env k) n =
        arenaFoldSeq plans env (k + n) := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      calc
        arenaFoldSeqFrom plans (arenaFoldSeq plans env k)
            (OmegaWord.drop env k) (n + 1)
            = arenaStep plans
                (arenaFoldSeqFrom plans (arenaFoldSeq plans env k)
                  (OmegaWord.drop env k) n)
                (env (k + n)) := rfl
        _ = arenaStep plans (arenaFoldSeq plans env (k + n)) (env (k + n)) := by
              rw [ih]
        _ = arenaFoldSeq plans env (k + (n + 1)) := rfl

/-- The first `k` records of an arena word, as a list. -/
def arenaWordPrefix (plans : PlanFamily (In₁ := In₁) A C_L C_R C_V)
    (env : EnvironmentSequence In₁ In₂) (k : Nat) :
    List (RoundRecord In₁ In₂ Graph Out₁ Out₂) :=
  (List.range k).map (arenaWord plans env)

@[simp]
theorem arenaWordPrefix_length (plans : PlanFamily (In₁ := In₁) A C_L C_R C_V)
    (env : EnvironmentSequence In₁ In₂) (k : Nat) :
    (arenaWordPrefix plans env k).length = k := by
  simp [arenaWordPrefix]

/-- **Cut decomposition of an arena word**: the whole word is its first `k`
records prepended to the suffix word from the position reached at `k`. -/
theorem arenaWord_decompose (plans : PlanFamily (In₁ := In₁) A C_L C_R C_V)
    (env : EnvironmentSequence In₁ In₂) (k : Nat) :
    arenaWord plans env =
      OmegaWord.prependList (arenaWordPrefix plans env k)
        (arenaWordFrom plans (arenaFoldSeq plans env k) (OmegaWord.drop env k)) := by
  funext j
  rcases Nat.lt_or_ge j k with hj | hj
  · have hlen : j < (arenaWordPrefix plans env k).length := by simp [hj]
    rw [OmegaWord.prependList_getElem_lt _ _ hlen]
    simp [arenaWordPrefix, hj]
  · obtain ⟨m, rfl⟩ : ∃ m, j = k + m := ⟨j - k, by omega⟩
    calc
      arenaWord plans env (k + m)
          = arenaRecord plans (arenaFoldSeq plans env (k + m)) (env (k + m)) :=
            rfl
      _ = arenaRecord plans
            (arenaFoldSeqFrom plans (arenaFoldSeq plans env k)
              (OmegaWord.drop env k) m)
            (OmegaWord.drop env k m) := by
            rw [arenaFoldSeqFrom_arenaFoldSeq]
            rfl
      _ = arenaWordFrom plans (arenaFoldSeq plans env k)
            (OmegaWord.drop env k) m := rfl
      _ = OmegaWord.prependList (arenaWordPrefix plans env k)
            (arenaWordFrom plans (arenaFoldSeq plans env k)
              (OmegaWord.drop env k)) (k + m) := by
            rw [show k + m = (arenaWordPrefix plans env k).length + m by simp]
            exact (OmegaWord.prependList_length_add _ _ m).symm

/-- Prefix transport in `AcceptsFrom` form: acceptance of a prepended word is
acceptance of the tail from the state the prefix reaches. -/
theorem accepts_prependList_iff_acceptsFrom
    {Alphabet : Type w}
    (B : DetParityAutomaton.{w, t} Alphabet)
    (l : List Alphabet) (word : OmegaWord Alphabet) :
    B.Accepts (OmegaWord.prependList l word) ↔
      B.AcceptsFrom (l.foldl B.step B.initial) word := by
  have h :=
    B.acceptsFrom_runFrom_drop_iff B.initial (OmegaWord.prependList l word)
      l.length
  rw [runFrom_prependList_length, OmegaWord.drop_length_prependList] at h
  exact h.symm

/-- **The `hsound` transport skeleton.**  Let `F` be the (summary) family
under `env`, and `G` a reference family under `env'`.  If after `k` and `m`
rounds the two prefixes drive `A` to the same state, and the suffix words
from the reached positions coincide (the finite simulation obligation), then
acceptance of the reference arena word gives acceptance of `F`'s. -/
theorem accepts_arenaWord_of_suffix_match
    {C_L' C_R' C_V' : Type max u v x y s}
    (F : PlanFamily (In₁ := In₁) A C_L C_R C_V)
    (G : PlanFamily (In₁ := In₁) A C_L' C_R' C_V')
    (env env' : EnvironmentSequence In₁ In₂) (k m : Nat)
    (hstate :
      entryState (A := A) (arenaWordPrefix F env k) =
        entryState (A := A) (arenaWordPrefix G env' m))
    (hsuffix :
      arenaWordFrom F (arenaFoldSeq F env k) (OmegaWord.drop env k) =
        arenaWordFrom G (arenaFoldSeq G env' m) (OmegaWord.drop env' m))
    (haccepts : A.Accepts (arenaWord G env')) :
    A.Accepts (arenaWord F env) := by
  rw [arenaWord_decompose G env' m,
    accepts_prependList_iff_acceptsFrom A _ _] at haccepts
  rw [arenaWord_decompose F env k, accepts_prependList_iff_acceptsFrom A _ _,
    hsuffix]
  have hstate' :
      (arenaWordPrefix F env k).foldl A.step A.initial =
        (arenaWordPrefix G env' m).foldl A.step A.initial := hstate
  rw [hstate']
  exact haccepts

end DetParityAutomaton

end DistributedSynthesis
