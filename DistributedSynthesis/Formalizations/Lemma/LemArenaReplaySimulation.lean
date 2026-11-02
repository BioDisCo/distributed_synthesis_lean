/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemArenaSuffixTransport
import DistributedSynthesis.Formalizations.Lemma.LemSummaryblockplan

/-!
# The replay simulation: block-tier record agreement, by construction

The first simulation brick towards `hsound` (`prop:starsound` for the summary
fold).  The transport skeleton `accepts_arenaWord_of_suffix_match`
(`LemArenaSuffixTransport`) reduces `hsound` to a suffix-word equality between
the summary family and a reference family.  This file supplies that equality
for **both orientations**, against the *constant* reference family that
commits one fixed representative plan `P` at every boundary atom.  The right
orientation is treated first (`RightReplaySim`), the left orientation is its
exact mirror (`LeftReplaySim`).

The extraction is chosen so that the simulation holds by construction: the
summary family's tables literally read `P`'s right block plan (`replayFamily`,
an instance of `summaryPlanFamily` with summary types `S₁ := C_R`,
`S₂ := C_L`, stepped exactly as `P`'s block plans step).  The correspondence
`RightReplaySim` relates two summary tiers to the reference's plain in-block
right tier:

* the summary family's own in-block right positions, control for control; and
* the summary family's **reversed-right** positions with chain control
  `Sum.inr c`, which by the fold's replay semantics run `P`'s right block plan
  at control `c` -- the eternal-replay reading of a directly reversed block.

Main results, all definitional in content:

* `RightReplaySim.record_eq` -- related positions emit **equal round records**
  on every non-`left` round (interior `right` continuation and `both`
  closing);
* `RightReplaySim.step_right` -- the relation is **preserved by `arenaStep`**
  on interior `right` rounds;
* `RightReplaySim.close_target` -- on a closing `both` round the two folds
  reach the **same boundary atom**;
* `RightReplaySim.arenaWordFrom_agree`/`arenaWordFrom_eq` -- the induction:
  the suffix arena words **coincide** for as long as the environment stays
  `right`, and coincide as ω-words on an all-`right` environment -- the exact
  `hsuffix` shape consumed by `accepts_arenaWord_of_suffix_match`.

The left orientation mirrors all of this verbatim: `LeftReplaySim` relates
the summary family's in-block left and reversed-left (chain control
`Sum.inl c`) positions to the reference's plain in-block left position, and
`LeftReplaySim.record_eq`/`step_left`/`close_target`/`arenaFoldSeqFrom_sim`/
`arenaWordFrom_agree`/`arenaWordFrom_eq` are the orientation mirrors of the
six right-tier results, with `right` the excluded reversal round.

What this brick does **not** cover: the reversal round itself (the round of
the opposite orientation at an in-block position reads the reference plan's
committed `rev` slot, which the extraction replaces by the derived
fresh-opening output -- the `b_new` close-resolve contingency), and crossing
a block boundary back through the committed tier (the reference family and
the summary family commit different plans at the reached atom).
-/

namespace DistributedSynthesis

universe u v x y s

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}

namespace DetParityAutomaton

variable {A : DetParityAutomaton.{max u v x y, s} (RoundRecord In₁ In₂ Graph Out₁ Out₂)}
variable {C_L C_R C_V : Type max u v x y s}

/-- The constant reference family: commit the fixed representative plan `P` at
every boundary atom.  For a boundary-game winner `τ` the intended instance is
`P := plansOf τ atom⋆`; constancy sidesteps `τ`'s atom-dependence in this
brick. -/
def constantFamily (P : BoundaryPlan (In₁ := In₁) A C_L C_R C_V) :
    PlanFamily (In₁ := In₁) A C_L C_R C_V :=
  fun _ => P

/-- The **extraction** of the right block plan from the representative `P`: a
summary-controlled right block plan whose summary type is `P`'s own control
`C_R`, stepped exactly as `P`'s right block plan steps, with blind, informed,
and close tables reading `P`'s corresponding labels.  Only the reversal slot
differs from `P.2.1`: it is the derived fresh-opening output of `P`'s left
block plan, as `summaryPlanFamily` prescribes. -/
def replayRightPlan (P : BoundaryPlan (In₁ := In₁) A C_L C_R C_V) :
    RightBlockPlan (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂) A C_R :=
  summaryRightBlockPlan (A := A) C_R P.2.1.init P.2.1.step
    (fun c => (P.2.1.label c).1) (fun c => (P.2.1.label c).2) P.2.1.close
    (fun _ _ i => (P.1.label P.1.init).1 i)

/-- The extraction of the left block plan from `P`: the orientation mirror of
`replayRightPlan`. -/
def replayLeftPlan (P : BoundaryPlan (In₁ := In₁) A C_L C_R C_V) :
    LeftBlockPlan (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂) A C_L :=
  summaryLeftBlockPlan (A := A) C_L P.1.init P.1.step
    (fun c => (P.1.label c).1) (fun c => (P.1.label c).2) P.1.close
    (fun _ _ i => (P.2.1.label P.2.1.init).1 i)

/-- The extracted chain: the summary chain of the two extracted block plans.
Its reversed-right branch at control `Sum.inr c` replays `P`'s right block
plan at control `c` -- the replay semantics the simulation exploits. -/
def replayChain (P : BoundaryPlan (In₁ := In₁) A C_L C_R C_V) :
    ChainPlan (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)
      A C_L C_R (C_L ⊕ C_R) :=
  summaryChain (replayLeftPlan P) (replayRightPlan P)

/-- The **replay family**: the summary plan family whose tables are extracted
from the representative `P`.  It is a `summaryPlanFamily` on the summary types
`S₁ := C_R`, `S₂ := C_L`, so the fold's unconditional measurability
(`summaryPlanFamily_reversalMeasurable`) applies to it verbatim. -/
def replayFamily (P : BoundaryPlan (In₁ := In₁) A C_L C_R C_V) :
    PlanFamily (In₁ := In₁) A C_L C_R (C_L ⊕ C_R) :=
  summaryPlanFamily (A := A) C_R C_L
    P.2.1.init P.2.1.step
    (fun c => (P.2.1.label c).1) (fun c => (P.2.1.label c).2) P.2.1.close
    P.1.init P.1.step
    (fun c => (P.1.label c).1) (fun c => (P.1.label c).2) P.1.close

@[simp]
theorem replayFamily_apply (P : BoundaryPlan (In₁ := In₁) A C_L C_R C_V)
    (atom : A.State × A.State) :
    replayFamily P atom = (replayLeftPlan P, replayRightPlan P, replayChain P) :=
  rfl

/-- The right-orientation **control correspondence** between the replay family
and the constant reference family.  A summary in-block right position at
control `c` corresponds to the reference's in-block right position at the same
control; a summary reversed-right position at chain control `Sum.inr c`
corresponds to the *same* reference in-block position -- the reversed block is
the replayed block.  Automaton state, minimum-priority state, and (in the
reversed case) the carried entry are free. -/
inductive RightReplaySim (P : BoundaryPlan (In₁ := In₁) A C_L C_R C_V) :
    BoundaryGamePosition (In₁ := In₁) A C_L C_R (C_L ⊕ C_R) ->
      BoundaryGamePosition (In₁ := In₁) A C_L C_R C_V -> Prop
  | inBlock (control : C_R) (state minState : A.State) :
      RightReplaySim P
        (Sum.inr (Sum.inr (Sum.inr (Sum.inl
          (replayRightPlan P, replayChain P, control, state, minState)))))
        (Sum.inr (Sum.inr (Sum.inr (Sum.inl
          (P.2.1, P.2.2, control, state, minState)))))
  | reversed (control : C_R) (entry : A.State × A.State)
      (state minState : A.State) :
      RightReplaySim P
        (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr
          (replayChain P, Sum.inr control, entry, state, minState))))))
        (Sum.inr (Sum.inr (Sum.inr (Sum.inl
          (P.2.1, P.2.2, control, state, minState)))))

namespace RightReplaySim

variable {P : BoundaryPlan (In₁ := In₁) A C_L C_R C_V}
variable {p : BoundaryGamePosition (In₁ := In₁) A C_L C_R (C_L ⊕ C_R)}
variable {q : BoundaryGamePosition (In₁ := In₁) A C_L C_R C_V}

/-- **Record agreement.**  Related positions emit equal round records on every
non-`left` round: the interior `right` continuation and the `both` closing.
Both cases are definitional, because the extracted tables *are* `P`'s labels;
only the reversal round (`left`), which reads the committed `rev` slot, is
excluded -- that is the `b_new` contingency of the staged closing. -/
theorem record_eq (h : RightReplaySim P p q)
    (round : EnvironmentRound In₁ In₂) (hg : round.graph ≠ Graph.left) :
    arenaRecord (replayFamily P) p round =
      arenaRecord (constantFamily P) q round := by
  obtain ⟨i₁, i₂, g⟩ := round
  cases h <;> cases g
  · exact absurd rfl hg
  · rfl
  · rfl
  · exact absurd rfl hg
  · rfl
  · rfl

/-- **Step preservation.**  On an interior `right` round, `arenaStep` carries
related positions to related positions: both tiers continue with the control
stepped by `P.2.1.step` on process one's input, and the equal round records
drive `A` to the same state. -/
theorem step_right (h : RightReplaySim P p q)
    (round : EnvironmentRound In₁ In₂) (hg : round.graph = Graph.right) :
    RightReplaySim P (arenaStep (replayFamily P) p round)
      (arenaStep (constantFamily P) q round) := by
  obtain ⟨i₁, i₂, g⟩ := round
  have hg' : g = Graph.right := hg
  subst hg'
  cases h with
  | inBlock control state minState => exact inBlock _ _ _
  | reversed control entry state minState => exact reversed _ _ _ _

/-- **Closing agreement.**  On a `both` round, both folds leave the block to
the *same* boundary atom: the equal closing records drive `A` to the same
state, and the emitted minimum is the shared `minState`. -/
theorem close_target (h : RightReplaySim P p q)
    (round : EnvironmentRound In₁ In₂) (hg : round.graph = Graph.both) :
    ∃ atom : A.State × A.State,
      arenaStep (replayFamily P) p round = Sum.inl atom ∧
        arenaStep (constantFamily P) q round = Sum.inl atom := by
  obtain ⟨i₁, i₂, g⟩ := round
  have hg' : g = Graph.both := hg
  subst hg'
  cases h with
  | inBlock control state minState => exact ⟨_, rfl, rfl⟩
  | reversed control entry state minState => exact ⟨_, rfl, rfl⟩

/-- The correspondence propagates along the fold: as long as the environment
plays `right`, the two position streams stay related round by round. -/
theorem arenaFoldSeqFrom_sim (h : RightReplaySim P p q)
    (env : EnvironmentSequence In₁ In₂) :
    ∀ n : Nat, (∀ j : Nat, j < n -> (env j).graph = Graph.right) ->
      RightReplaySim P (arenaFoldSeqFrom (replayFamily P) p env n)
        (arenaFoldSeqFrom (constantFamily P) q env n) := by
  intro n
  induction n with
  | zero => exact fun _ => h
  | succ n ih =>
      intro hright
      exact
        (ih fun j hj => hright j (Nat.lt_succ_of_lt hj)).step_right (env n)
          (hright n (Nat.lt_succ_self n))

/-- **Per-round word agreement.**  While the environment stays `right` through
round `n`, the two suffix arena words agree at `n`. -/
theorem arenaWordFrom_agree (h : RightReplaySim P p q)
    (env : EnvironmentSequence In₁ In₂) (n : Nat)
    (hright : ∀ j : Nat, j ≤ n -> (env j).graph = Graph.right) :
    arenaWordFrom (replayFamily P) p env n =
      arenaWordFrom (constantFamily P) q env n :=
  (h.arenaFoldSeqFrom_sim env n fun j hj => hright j (Nat.le_of_lt hj)).record_eq
    (env n)
    (fun hleft => by
      rw [hright n (Nat.le_refl n)] at hleft
      exact Graph.noConfusion hleft)

/-- **Suffix-word equality on an all-`right` environment**: the exact
`hsuffix` shape consumed by the transport skeleton
`accepts_arenaWord_of_suffix_match`, with `F := replayFamily P` and
`G := constantFamily P`. -/
theorem arenaWordFrom_eq (h : RightReplaySim P p q)
    (env : EnvironmentSequence In₁ In₂)
    (hright : ∀ j : Nat, (env j).graph = Graph.right) :
    arenaWordFrom (replayFamily P) p env =
      arenaWordFrom (constantFamily P) q env :=
  funext fun n => h.arenaWordFrom_agree env n fun j _ => hright j

end RightReplaySim

/-- The left-orientation **control correspondence**: the exact orientation
mirror of `RightReplaySim`.  A summary in-block left position at control `c`
corresponds to the reference's in-block left position at the same control; a
summary reversed-left position at chain control `Sum.inl c` (the left branch
of `summaryChain`'s control sum carries the left summary `C_L`) corresponds to
the *same* reference in-block position -- the reversed block is the replayed
block.  Automaton state, minimum-priority state, and (in the reversed case)
the carried entry are free. -/
inductive LeftReplaySim (P : BoundaryPlan (In₁ := In₁) A C_L C_R C_V) :
    BoundaryGamePosition (In₁ := In₁) A C_L C_R (C_L ⊕ C_R) ->
      BoundaryGamePosition (In₁ := In₁) A C_L C_R C_V -> Prop
  | inBlock (control : C_L) (state minState : A.State) :
      LeftReplaySim P
        (Sum.inr (Sum.inr (Sum.inl
          (replayLeftPlan P, replayChain P, control, state, minState))))
        (Sum.inr (Sum.inr (Sum.inl
          (P.1, P.2.2, control, state, minState))))
  | reversed (control : C_L) (entry : A.State × A.State)
      (state minState : A.State) :
      LeftReplaySim P
        (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl
          (replayChain P, Sum.inl control, entry, state, minState))))))
        (Sum.inr (Sum.inr (Sum.inl
          (P.1, P.2.2, control, state, minState))))

namespace LeftReplaySim

variable {P : BoundaryPlan (In₁ := In₁) A C_L C_R C_V}
variable {p : BoundaryGamePosition (In₁ := In₁) A C_L C_R (C_L ⊕ C_R)}
variable {q : BoundaryGamePosition (In₁ := In₁) A C_L C_R C_V}

/-- **Record agreement**, left orientation.  Related positions emit equal
round records on every non-`right` round: the interior `left` continuation
and the `both` closing.  Both cases are definitional, because the extracted
tables *are* `P`'s labels; only the reversal round (`right`), which reads the
committed `rev` slot, is excluded. -/
theorem record_eq (h : LeftReplaySim P p q)
    (round : EnvironmentRound In₁ In₂) (hg : round.graph ≠ Graph.right) :
    arenaRecord (replayFamily P) p round =
      arenaRecord (constantFamily P) q round := by
  obtain ⟨i₁, i₂, g⟩ := round
  cases h <;> cases g
  · rfl
  · exact absurd rfl hg
  · rfl
  · rfl
  · exact absurd rfl hg
  · rfl

/-- **Step preservation**, left orientation.  On an interior `left` round,
`arenaStep` carries related positions to related positions: both tiers
continue with the control stepped by `P.1.step` on process two's input, and
the equal round records drive `A` to the same state. -/
theorem step_left (h : LeftReplaySim P p q)
    (round : EnvironmentRound In₁ In₂) (hg : round.graph = Graph.left) :
    LeftReplaySim P (arenaStep (replayFamily P) p round)
      (arenaStep (constantFamily P) q round) := by
  obtain ⟨i₁, i₂, g⟩ := round
  have hg' : g = Graph.left := hg
  subst hg'
  cases h with
  | inBlock control state minState => exact inBlock _ _ _
  | reversed control entry state minState => exact reversed _ _ _ _

/-- **Closing agreement**, left orientation.  On a `both` round, both folds
leave the block to the *same* boundary atom: the equal closing records drive
`A` to the same state, and the emitted minimum is the shared `minState`. -/
theorem close_target (h : LeftReplaySim P p q)
    (round : EnvironmentRound In₁ In₂) (hg : round.graph = Graph.both) :
    ∃ atom : A.State × A.State,
      arenaStep (replayFamily P) p round = Sum.inl atom ∧
        arenaStep (constantFamily P) q round = Sum.inl atom := by
  obtain ⟨i₁, i₂, g⟩ := round
  have hg' : g = Graph.both := hg
  subst hg'
  cases h with
  | inBlock control state minState => exact ⟨_, rfl, rfl⟩
  | reversed control entry state minState => exact ⟨_, rfl, rfl⟩

/-- The correspondence propagates along the fold: as long as the environment
plays `left`, the two position streams stay related round by round. -/
theorem arenaFoldSeqFrom_sim (h : LeftReplaySim P p q)
    (env : EnvironmentSequence In₁ In₂) :
    ∀ n : Nat, (∀ j : Nat, j < n -> (env j).graph = Graph.left) ->
      LeftReplaySim P (arenaFoldSeqFrom (replayFamily P) p env n)
        (arenaFoldSeqFrom (constantFamily P) q env n) := by
  intro n
  induction n with
  | zero => exact fun _ => h
  | succ n ih =>
      intro hleft
      exact
        (ih fun j hj => hleft j (Nat.lt_succ_of_lt hj)).step_left (env n)
          (hleft n (Nat.lt_succ_self n))

/-- **Per-round word agreement**, left orientation.  While the environment
stays `left` through round `n`, the two suffix arena words agree at `n`. -/
theorem arenaWordFrom_agree (h : LeftReplaySim P p q)
    (env : EnvironmentSequence In₁ In₂) (n : Nat)
    (hleft : ∀ j : Nat, j ≤ n -> (env j).graph = Graph.left) :
    arenaWordFrom (replayFamily P) p env n =
      arenaWordFrom (constantFamily P) q env n :=
  (h.arenaFoldSeqFrom_sim env n fun j hj => hleft j (Nat.le_of_lt hj)).record_eq
    (env n)
    (fun hright => by
      rw [hleft n (Nat.le_refl n)] at hright
      exact Graph.noConfusion hright)

/-- **Suffix-word equality on an all-`left` environment**: the exact
`hsuffix` shape consumed by the transport skeleton
`accepts_arenaWord_of_suffix_match`, with `F := replayFamily P` and
`G := constantFamily P`. -/
theorem arenaWordFrom_eq (h : LeftReplaySim P p q)
    (env : EnvironmentSequence In₁ In₂)
    (hleft : ∀ j : Nat, (env j).graph = Graph.left) :
    arenaWordFrom (replayFamily P) p env =
      arenaWordFrom (constantFamily P) q env :=
  funext fun n => h.arenaWordFrom_agree env n fun j _ => hleft j

end LeftReplaySim

end DetParityAutomaton

end DistributedSynthesis
