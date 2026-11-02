/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemEpochArenaCuts
import DistributedSynthesis.Formalizations.Lemma.LemPlanTableFamily

/-!
# The per-epoch re-cut of the table family

aligning the entry coordinate of the atom-indexed
tables with the epoch's entry atom.  Brick β2's pinned family
(`tableFamily`) commits one fixed pair of table-controlled block plans
whose summary inits carry the *initial* boundary atom; since the arena
fold resets the block control to the committed init at every block
opening, the pinned fold carries the coordinate `(A.initial, A.initial)`
forever and replays the reference plans committed *there* in every
epoch.  It therefore cannot re-enter the atom-dependent correspondence
at any later boundary atom -- the alignment gap β2 deliberately left
open.  The re-cut dissolves it: `recutFamily G` commits, at each
boundary atom `a`, the same summary tables with their inits re-based at
`a` (`tableInitOneAt`/`tableInitTwoAt`), so the control-reset at each
block opening installs exactly the current epoch's entry atom.

Contents:

* `recutFamily` -- the re-cut table family; at the initial atom it
  commits exactly the pinned plans (`recutFamily_initial`);
* `ReversingRound` -- the one round shape on which record equality is
  *not* claimed: an in-block or reversed position meeting the opposite
  one-sided orientation, i.e. a direct reversal or re-reversal (owned
  by `LemReversingRoundBridge`);
* `RecutSim` -- the epoch-composable correspondence: equal boundary
  atoms, and in-block positions whose table summary `(a, c)` mirrors
  the reference `G`'s position at control `c` in the block committed at
  `a`.  `record_eq` gives equal records on every non-reversing round;
  `step` gives preservation, including the boundary re-entry: from an
  equal boundary atom both folds commit their plans and re-enter the
  relation; `close_target` closes every epoch to the same boundary
  atom; `boundary_iff` states that the two folds rest at the same
  boundary atoms at the same rounds;
* `recutSim_arenaFoldSeqFrom` -- the epoch-by-epoch composition: from a
  common boundary atom the correspondence propagates through every
  round whose adjacent pairs are direct-reversal free
  (`NoDirectReversalAt`; a `both` round satisfies it vacuously, so the
  condition is exactly that every epoch interior stays in one
  orientation);
* `arenaWordFrom_recutFamily_agree`/`arenaWordFrom_recutFamily_eq` --
  per-round and full suffix-word equality from a shared entry atom;
* `arenaWord_recutFamily_eq` -- **the assembled endpoint**: full
  omega-word equality `arenaWord (recutFamily G) env = arenaWord G env`
  on every environment without direct reversals
  (`NoDirectReversalSequence`, covering both regimes of
  `arenaFoldSeq_regime_dichotomy`); acceptance transfer
  (`accepts_arenaWord_recutFamily_iff`), the interface of
  pointwise-equal per-epoch min-priority summaries
  (`cutBlockMin_arenaWord_recutFamily_eq`), and the epoch cut
  correspondence re-read against the *reference* fold
  (`arenaWord_recutFamily_epoch_cut`, the per-epoch shape `LemRouteBetaAssembly`
  splices into `accepts_iff_of_epoch_segments`) follow.

What is deliberately left to `LemReversingRoundBridge`: the direct-reversal round
itself.  At a `ReversingRound` from related in-block positions the two
closing outputs agree, but the blind side's output is the re-cut
family's *derived* reversal slot -- the fresh opening output of the
opposite orientation at the same atom, e.g. on a reversing left block
`((G a).2.1.label (G a).2.1.init).1` -- whereas the reference emits the
committed slot `(G a).1.rev c (state, minState)`.  `LemReversingRoundBridge` proves this
one record per reversal round (the `b_new` legality), or the β1
fallback of equal epoch minima and exit atoms, together with the
reversed-tier continuation.

The re-cut family trades β2's unconditional measurability for the
alignment: it is atom-dependent, hence not a `summaryPlanFamily`, and
`ReversalMeasurable` for it would require the fresh-opening blind
tables of `G` to be one global table (`rem:globalblindtable`).
Reconciling alignment with measurability is the concern of the
`hsound` discharge, not of this brick.
-/

namespace DistributedSynthesis

universe u v x y s

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}

/-- Rounds `j` and `j + 1` do not form a direct reversal.  A `both`
round at `j` satisfies this vacuously, so requiring it along a prefix
states exactly that every epoch interior met so far stays in one
orientation. -/
def NoDirectReversalAt (env : EnvironmentSequence In₁ In₂) (j : Nat) :
    Prop :=
  ((env j).graph = Graph.left -> (env (j + 1)).graph ≠ Graph.right) ∧
    ((env j).graph = Graph.right -> (env (j + 1)).graph ≠ Graph.left)

/-- The no-direct-reversal regime is closed under dropping a prefix. -/
theorem noDirectReversalSequence_drop {env : EnvironmentSequence In₁ In₂}
    (hnd : NoDirectReversalSequence env) (k : Nat) :
    NoDirectReversalSequence (OmegaWord.drop env k) :=
  fun n => hnd (k + n)

namespace DetParityAutomaton

variable
  {A :
    DetParityAutomaton.{max u v x y, s}
      (RoundRecord In₁ In₂ Graph Out₁ Out₂)}
variable {C_L C_R C_V : Type max u v x y s}

/-- The process-one table init re-based at boundary atom `a`: the atom
coordinate together with the right-plan control `G` commits there. -/
def tableInitOneAt (G : PlanFamily (In₁ := In₁) A C_L C_R C_V)
    (a : A.State × A.State) : (A.State × A.State) × C_R :=
  (a, (G a).2.1.init)

/-- The process-two table init re-based at `a`: the orientation
mirror. -/
def tableInitTwoAt (G : PlanFamily (In₁ := In₁) A C_L C_R C_V)
    (a : A.State × A.State) : (A.State × A.State) × C_L :=
  (a, (G a).1.init)

/-- The re-cut right block plan at `a`: β2's summary tables with the
init re-based at `a`. -/
def recutRightPlan (G : PlanFamily (In₁ := In₁) A C_L C_R C_V)
    (a : A.State × A.State) :
    RightBlockPlan (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)
      A ((A.State × A.State) × C_R) :=
  summaryRightBlockPlan (A := A) ((A.State × A.State) × C_R)
    (tableInitOneAt G a) (tableStepOne G) (tableBlindR G) (tableInformedR G)
    (tableCloseR G) (fun _ _ i => tableBlindL G (tableInitTwoAt G a) i)

/-- The re-cut left block plan at `a`: the orientation mirror. -/
def recutLeftPlan (G : PlanFamily (In₁ := In₁) A C_L C_R C_V)
    (a : A.State × A.State) :
    LeftBlockPlan (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)
      A ((A.State × A.State) × C_L) :=
  summaryLeftBlockPlan (A := A) ((A.State × A.State) × C_L)
    (tableInitTwoAt G a) (tableStepTwo G) (tableBlindL G) (tableInformedL G)
    (tableCloseL G) (fun _ _ i => tableBlindR G (tableInitOneAt G a) i)

/-- The re-cut chain at `a`: the summary chain of the two re-cut block
plans. -/
def recutChain (G : PlanFamily (In₁ := In₁) A C_L C_R C_V)
    (a : A.State × A.State) :
    ChainPlan (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂) A
      ((A.State × A.State) × C_L) ((A.State × A.State) × C_R)
      (((A.State × A.State) × C_L) ⊕ ((A.State × A.State) × C_R)) :=
  summaryChain (recutLeftPlan G a) (recutRightPlan G a)

/-- The **re-cut table family**: at every boundary atom, β2's summary
tables with the entry coordinate aligned to that atom.  A block opened
at atom `a` then carries the summary `(a, c)` with `c` running through
the controls of the plan `G` commits at `a` -- the per-epoch re-cut. -/
def recutFamily (G : PlanFamily (In₁ := In₁) A C_L C_R C_V) :
    PlanFamily (In₁ := In₁) A ((A.State × A.State) × C_L)
      ((A.State × A.State) × C_R)
      (((A.State × A.State) × C_L) ⊕ ((A.State × A.State) × C_R)) :=
  fun a => (recutLeftPlan G a, recutRightPlan G a, recutChain G a)

/-- At the initial atom the re-cut family commits exactly β2's pinned
plans: the re-cut is the identity on epoch zero. -/
theorem recutFamily_initial (G : PlanFamily (In₁ := In₁) A C_L C_R C_V) :
    recutFamily G (A.initial, A.initial) =
      tableFamily G (A.initial, A.initial) :=
  rfl

/-- The round shape excluded from the β4 record equality: an in-block
or reversed position meeting the opposite one-sided orientation, i.e. a
direct reversal or re-reversal.  These rounds are owned by `LemReversingRoundBridge`;
boundary positions never reverse. -/
def ReversingRound
    (position : BoundaryGamePosition (In₁ := In₁) A C_L C_R C_V)
    (round : EnvironmentRound In₁ In₂) : Prop :=
  match position with
  | Sum.inr (Sum.inr (Sum.inl _)) => round.graph = Graph.right
  | Sum.inr (Sum.inr (Sum.inr (Sum.inl _))) => round.graph = Graph.left
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl _)))) =>
      round.graph = Graph.right
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr _)))) =>
      round.graph = Graph.left
  | _ => False

/-- The **per-epoch re-cut correspondence**: the re-cut fold and the
reference fold rest at the same boundary atom, or sit in blocks of the
same orientation where the table summary `(a, c)` mirrors the reference
`G`'s position at control `c` in the block committed at `a`.  Unlike
β2's `RightTableSim`/`LeftTableSim`, the boundary constructor closes
the correspondence under epoch re-entry: from an equal boundary atom
both folds commit their plans and the opened blocks are again
related. -/
inductive RecutSim (G : PlanFamily (In₁ := In₁) A C_L C_R C_V) :
    BoundaryGamePosition (In₁ := In₁) A ((A.State × A.State) × C_L)
        ((A.State × A.State) × C_R)
        (((A.State × A.State) × C_L) ⊕ ((A.State × A.State) × C_R)) ->
      BoundaryGamePosition (In₁ := In₁) A C_L C_R C_V -> Prop
  | boundary (state minState : A.State) :
      RecutSim G (Sum.inl (state, minState)) (Sum.inl (state, minState))
  | inBlockL (a : A.State × A.State) (c : C_L) (state minState : A.State) :
      RecutSim G
        (Sum.inr (Sum.inr (Sum.inl
          (recutLeftPlan G a, recutChain G a, (a, c), state, minState))))
        (Sum.inr (Sum.inr (Sum.inl
          ((G a).1, (G a).2.2, c, state, minState))))
  | inBlockR (a : A.State × A.State) (c : C_R) (state minState : A.State) :
      RecutSim G
        (Sum.inr (Sum.inr (Sum.inr (Sum.inl
          (recutRightPlan G a, recutChain G a, (a, c), state, minState)))))
        (Sum.inr (Sum.inr (Sum.inr (Sum.inl
          ((G a).2.1, (G a).2.2, c, state, minState)))))

namespace RecutSim

variable {G : PlanFamily (In₁ := In₁) A C_L C_R C_V}
variable
  {p :
    BoundaryGamePosition (In₁ := In₁) A ((A.State × A.State) × C_L)
      ((A.State × A.State) × C_R)
      (((A.State × A.State) × C_L) ⊕ ((A.State × A.State) × C_R))}
variable {q : BoundaryGamePosition (In₁ := In₁) A C_L C_R C_V}

/-- **Record agreement.**  Related positions emit equal round records
on every non-reversing round: at a boundary atom on all rounds, inside
a block on its own orientation and on the closing `both` round.  The
re-cut tables at coordinate `a` *are* the labels of the plan `G`
commits at `a`. -/
theorem record_eq (h : RecutSim G p q) (round : EnvironmentRound In₁ In₂)
    (hnr : ¬ ReversingRound p round) :
    arenaRecord (recutFamily G) p round = arenaRecord G q round := by
  obtain ⟨i₁, i₂, g⟩ := round
  cases h <;> cases g <;> first | rfl | exact absurd rfl hnr

/-- **Step preservation and epoch re-entry.**  On every non-reversing
round the correspondence is preserved: boundary rounds re-commit and
re-enter the relation at the opened block (the re-cut), in-block rounds
continue it, and closing rounds land both folds on the same boundary
atom. -/
theorem step (h : RecutSim G p q) (round : EnvironmentRound In₁ In₂)
    (hnr : ¬ ReversingRound p round) :
    RecutSim G (arenaStep (recutFamily G) p round) (arenaStep G q round) := by
  obtain ⟨i₁, i₂, g⟩ := round
  cases h <;> cases g
  · exact inBlockL _ _ _ _
  · exact inBlockR _ _ _ _
  · exact boundary _ _
  · exact inBlockL _ _ _ _
  · exact absurd rfl hnr
  · exact boundary _ _
  · exact absurd rfl hnr
  · exact inBlockR _ _ _ _
  · exact boundary _ _

/-- **Closing agreement.**  On a `both` round both folds leave for the
same boundary atom. -/
theorem close_target (h : RecutSim G p q) (round : EnvironmentRound In₁ In₂)
    (hg : round.graph = Graph.both) :
    ∃ atom : A.State × A.State,
      arenaStep (recutFamily G) p round = Sum.inl atom ∧
        arenaStep G q round = Sum.inl atom := by
  obtain ⟨i₁, i₂, g⟩ := round
  have hg' : g = Graph.both := hg
  subst hg'
  cases h
  · exact ⟨_, rfl, rfl⟩
  · exact ⟨_, rfl, rfl⟩
  · exact ⟨_, rfl, rfl⟩

/-- Related positions rest at a boundary atom simultaneously, and at
the same atom. -/
theorem boundary_iff (h : RecutSim G p q) (atom : A.State × A.State) :
    p = Sum.inl atom ↔ q = Sum.inl atom := by
  cases h <;> simp

/-- The step of a related pair never faces a reversing round on the
next round, provided the adjacent environment pair is direct-reversal
free: a block position is entered only by a round of its own
orientation. -/
theorem not_reversing_step (h : RecutSim G p q)
    (round nextRound : EnvironmentRound In₁ In₂)
    (hnr : ¬ ReversingRound p round)
    (hleft : round.graph = Graph.left -> nextRound.graph ≠ Graph.right)
    (hright : round.graph = Graph.right -> nextRound.graph ≠ Graph.left) :
    ¬ ReversingRound (arenaStep (recutFamily G) p round) nextRound := by
  obtain ⟨i₁, i₂, g⟩ := round
  cases h <;> cases g
  · exact fun hrev => hleft rfl hrev
  · exact fun hrev => hright rfl hrev
  · exact fun hrev => hrev
  · exact fun hrev => hleft rfl hrev
  · exact absurd rfl hnr
  · exact fun hrev => hrev
  · exact absurd rfl hnr
  · exact fun hrev => hright rfl hrev
  · exact fun hrev => hrev

end RecutSim

/-- **The epoch-by-epoch composition.**  From a common boundary atom
the re-cut correspondence propagates through every round whose
traversed adjacent pairs are direct-reversal free: the two folds stay
related, and the pending round is never a reversing round of the
current position.  Requiring only the pairs below `n` makes the lemma
per-epoch: an epoch whose interior stays in one orientation satisfies
the hypothesis on its own segment. -/
theorem recutSim_arenaFoldSeqFrom
    (G : PlanFamily (In₁ := In₁) A C_L C_R C_V)
    (env : EnvironmentSequence In₁ In₂) (p : A.State × A.State) :
    ∀ n : Nat, (∀ j : Nat, j < n -> NoDirectReversalAt env j) ->
      RecutSim G
          (arenaFoldSeqFrom (recutFamily G) (Sum.inl p) env n)
          (arenaFoldSeqFrom G (Sum.inl p) env n) ∧
        ¬ ReversingRound
          (arenaFoldSeqFrom (recutFamily G) (Sum.inl p) env n) (env n)
  | 0, _ => ⟨RecutSim.boundary p.1 p.2, fun hrev => hrev⟩
  | n + 1, hnd => by
      obtain ⟨hsim, hnr⟩ :=
        recutSim_arenaFoldSeqFrom G env p n
          (fun j hj => hnd j (Nat.lt_succ_of_lt hj))
      exact
        ⟨hsim.step (env n) hnr,
          hsim.not_reversing_step (env n) (env (n + 1)) hnr
            (hnd n (Nat.lt_succ_self n)).1 (hnd n (Nat.lt_succ_self n)).2⟩

/-- **Per-round word agreement from a shared entry atom**: the re-cut
fold and the reference fold started at the same boundary atom emit the
same record at round `n` whenever the adjacent pairs below `n` are
direct-reversal free. -/
theorem arenaWordFrom_recutFamily_agree
    (G : PlanFamily (In₁ := In₁) A C_L C_R C_V)
    (env : EnvironmentSequence In₁ In₂) (p : A.State × A.State) (n : Nat)
    (hnd : ∀ j : Nat, j < n -> NoDirectReversalAt env j) :
    arenaWordFrom (recutFamily G) (Sum.inl p) env n =
      arenaWordFrom G (Sum.inl p) env n := by
  obtain ⟨hsim, hnr⟩ := recutSim_arenaFoldSeqFrom G env p n hnd
  exact hsim.record_eq (env n) hnr

/-- **Suffix-word equality from a shared entry atom** on a
direct-reversal-free environment: the epoch tail of the re-cut fold is
the reference's own replay. -/
theorem arenaWordFrom_recutFamily_eq
    (G : PlanFamily (In₁ := In₁) A C_L C_R C_V)
    (env : EnvironmentSequence In₁ In₂) (p : A.State × A.State)
    (hnd : NoDirectReversalSequence env) :
    arenaWordFrom (recutFamily G) (Sum.inl p) env =
      arenaWordFrom G (Sum.inl p) env :=
  funext fun n =>
    arenaWordFrom_recutFamily_agree G env p n (fun j _ => hnd j)

/-- The fold from the initial boundary is the arena fold. -/
theorem arenaFoldSeqFrom_initial
    (plans : PlanFamily (In₁ := In₁) A C_L C_R C_V)
    (env : EnvironmentSequence In₁ In₂) :
    ∀ n : Nat,
      arenaFoldSeqFrom plans (Sum.inl (A.initial, A.initial)) env n =
        arenaFoldSeq plans env n
  | 0 => rfl
  | n + 1 => by
      show
        arenaStep plans
            (arenaFoldSeqFrom plans (Sum.inl (A.initial, A.initial)) env n)
            (env n) =
          arenaStep plans (arenaFoldSeq plans env n) (env n)
      rw [arenaFoldSeqFrom_initial plans env n]

/-- The re-cut correspondence holds along the whole arena fold on a
direct-reversal-free environment. -/
theorem recutSim_arenaFoldSeq
    (G : PlanFamily (In₁ := In₁) A C_L C_R C_V)
    (env : EnvironmentSequence In₁ In₂)
    (hnd : NoDirectReversalSequence env) (n : Nat) :
    RecutSim G (arenaFoldSeq (recutFamily G) env n)
      (arenaFoldSeq G env n) := by
  have h :=
    (recutSim_arenaFoldSeqFrom G env (A.initial, A.initial) n
      (fun j _ => hnd j)).1
  rwa [arenaFoldSeqFrom_initial (recutFamily G) env n,
    arenaFoldSeqFrom_initial G env n] at h

/-- The two folds rest at the same boundary atoms at the same rounds:
the epoch decompositions of the re-cut play and of the reference play
coincide, cut for cut and atom for atom. -/
theorem recutFamily_boundary_atom_iff
    (G : PlanFamily (In₁ := In₁) A C_L C_R C_V)
    (env : EnvironmentSequence In₁ In₂)
    (hnd : NoDirectReversalSequence env) (n : Nat)
    (p : A.State × A.State) :
    arenaFoldSeq (recutFamily G) env n = Sum.inl p ↔
      arenaFoldSeq G env n = Sum.inl p :=
  (recutSim_arenaFoldSeq G env hnd n).boundary_iff p

/-- **The assembled β4 endpoint: full omega-word equality.**  On every
environment without direct reversals -- every epoch interior in one
orientation, in either regime of `arenaFoldSeq_regime_dichotomy` -- the
word emitted by the re-cut table family is the word emitted by the
reference family itself. -/
theorem arenaWord_recutFamily_eq
    (G : PlanFamily (In₁ := In₁) A C_L C_R C_V)
    (env : EnvironmentSequence In₁ In₂)
    (hnd : NoDirectReversalSequence env) :
    arenaWord (recutFamily G) env = arenaWord G env := by
  funext n
  obtain ⟨hsim, hnr⟩ :=
    recutSim_arenaFoldSeqFrom G env (A.initial, A.initial) n
      (fun j _ => hnd j)
  rw [arenaFoldSeqFrom_initial (recutFamily G) env n,
    arenaFoldSeqFrom_initial G env n] at hsim
  rw [arenaFoldSeqFrom_initial (recutFamily G) env n] at hnr
  exact hsim.record_eq (env n) hnr

/-- Acceptance transfers between the re-cut fold and the reference fold
on the direct-reversal-free regime. -/
theorem accepts_arenaWord_recutFamily_iff
    (G : PlanFamily (In₁ := In₁) A C_L C_R C_V)
    (env : EnvironmentSequence In₁ In₂)
    (hnd : NoDirectReversalSequence env) :
    A.Accepts (arenaWord (recutFamily G) env) ↔
      A.Accepts (arenaWord G env) := by
  rw [arenaWord_recutFamily_eq G env hnd]

/-- **The β1 interface**: along the sync cuts, the per-epoch
min-priority summaries of the re-cut word and of the reference word are
pointwise equal -- the exact hypothesis `accepts_iff_of_cutBlockMin_eq`
consumes. -/
theorem cutBlockMin_arenaWord_recutFamily_eq
    (G : PlanFamily (In₁ := In₁) A C_L C_R C_V)
    (env : EnvironmentSequence In₁ In₂)
    (hnd : NoDirectReversalSequence env)
    (hinf : ∀ n : Nat, ∃ m : Nat, n ≤ m ∧
      (arenaWord (recutFamily G) env m).graph = Graph.both)
    (hinf' : ∀ n : Nat, ∃ m : Nat, n ≤ m ∧
      (arenaWord G env m).graph = Graph.both)
    (k : Nat) :
    cutBlockMin
        (fun n => A.priority (A.run (arenaWord (recutFamily G) env) n))
        (syncCuts (arenaWord (recutFamily G) env) hinf) k =
      cutBlockMin (fun n => A.priority (A.run (arenaWord G env) n))
        (syncCuts (arenaWord G env) hinf') k := by
  have h := arenaWord_recutFamily_eq G env hnd
  revert hinf
  rw [h]
  intro hinf
  rfl

/-- **The re-cut epoch endpoint against the reference.**  With
recurring sync rounds, every cut of the re-cut word carries a boundary
atom shared by both folds, its state component is the run at the cut,
and the epoch tail of the re-cut word is the *reference* family's arena
word restarted from that atom -- the per-epoch shape `LemRouteBetaAssembly` splices
into `accepts_iff_of_epoch_segments`. -/
theorem arenaWord_recutFamily_epoch_cut
    (G : PlanFamily (In₁ := In₁) A C_L C_R C_V)
    (env : EnvironmentSequence In₁ In₂)
    (hnd : NoDirectReversalSequence env)
    (hinf : ∀ n : Nat, ∃ m : Nat, n ≤ m ∧
      (arenaWord (recutFamily G) env m).graph = Graph.both)
    (k : Nat) :
    ∃ p : A.State × A.State,
      arenaFoldSeq (recutFamily G) env
          (syncCuts (arenaWord (recutFamily G) env) hinf k) = Sum.inl p ∧
        arenaFoldSeq G env
          (syncCuts (arenaWord (recutFamily G) env) hinf k) = Sum.inl p ∧
        p.1 =
          A.run (arenaWord (recutFamily G) env)
            (syncCuts (arenaWord (recutFamily G) env) hinf k) ∧
        ∀ j : Nat,
          arenaWord (recutFamily G) env
              (syncCuts (arenaWord (recutFamily G) env) hinf k + j) =
            arenaWordFrom G (Sum.inl p)
              (OmegaWord.drop env
                (syncCuts (arenaWord (recutFamily G) env) hinf k)) j := by
  obtain ⟨p, hp, hrun, htail⟩ :=
    arenaWord_epoch_cut (recutFamily G) env hinf k
  refine
    ⟨p, hp, (recutFamily_boundary_atom_iff G env hnd _ p).1 hp, hrun,
      fun j => ?_⟩
  rw [htail j]
  exact
    congrFun
      (arenaWordFrom_recutFamily_eq G _ p
        (noDirectReversalSequence_drop hnd _)) j

end DetParityAutomaton

end DistributedSynthesis
