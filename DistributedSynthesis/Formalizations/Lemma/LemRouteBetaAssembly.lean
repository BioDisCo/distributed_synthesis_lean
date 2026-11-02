/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemReversingRoundBridge
import DistributedSynthesis.Formalizations.Lemma.LemBoundarysteparena

/-!
# the reversal normalization and the `hsound` assembly

Brick β5 closed the re-cut correspondence on arbitrary environments under the
one named hypothesis `GlobalFreshOpening G`.  This brick discharges that
hypothesis *constructively* and assembles the endpoint chain.

**The four table equations at an arbitrary winner (β6(a)(i)).**  They do
**not** hold for `plansOf τ` of an arbitrary positional boundary-game winner
`τ`, and we do not force them: the game's legality constrains only the shape
of the committed move, never the `rev` slots or the chain labels, and
`plansOf` is surjective onto plan families (`plansOf_committingStrategy`), so
whenever some family violating the equations wins, a winner refuting
`GlobalFreshOpening (plansOf τ)` exists.  The paper's state-tailoring winner
is exactly such a refutation (it keys its reversal slot on `b_old`).

**The normalization (β6(a)(ii)).**  `normalizeRev G` overwrites, at every
atom, the two reversal slots with the derived fresh openings of the opposite
orientation and the chain with the replay chain (`summaryChain`) of the two
block plans; the block plans' `init`/`step`/`label`/`close` are untouched.
Then:

* `GlobalFreshOpening (normalizeRev G)` holds **by construction**
  (`normalizeRev_globalFreshOpening`, all fields `rfl` after
  `chainTracks_summaryChain_eq` identifies tracked chain controls with their
  replay states);
* `recutFamily (normalizeRev G) = recutFamily G` by `rfl`
  (`recutFamily_normalizeRev`): the re-cut tables never read the reversal
  slots or the chain, which is exactly the data the normalization rewrites;
* hence the **unconditional splice**
  `arenaWord (recutFamily G) env = arenaWord (normalizeRev G) env` on
  *arbitrary* environments (`arenaWord_recutFamily_eq_normalizeRev`), and
  `GlobalFreshOpening (recutFamily G)` itself
  (`recutFamily_globalFreshOpening`): the re-cut family is its own
  normalization.

**The remaining comparison and the β1 check.**  What is left is
`arenaWord (normalizeRev G) env` against `arenaWord G env`, confined to the
reversal-round records and the reversed-tier chains.  On the no-direct
fragment it is an equality, unconditionally
(`arenaWord_normalizeRev_eq_of_noDirect`, two applications of the β4 word
equality through `recutFamily_normalizeRev`).  Across a direct reversal the
β1 per-epoch-minima interface (`accepts_iff_of_cutBlockMin_eq`) does **not**
close it: the reversing round's record replaces the emitted output, that
output feeds `A.step` for the remainder of the epoch, so the two runs diverge
*inside* the epoch and the per-epoch min-priority summaries are not pointwise
equal.  The comparison is therefore the final named residual,
`NormalizedReversalSound` -- one `Prop`, the `b_new` legality of paper
`rem:globalblindtable` read at the winner's committed tables: acceptance must
survive replacing the committed `b_old`-indexed reversal data by the derived
fresh-opening (`b_new`) data.

**The assembly (β6(b)).**  Under the residual, the `hsound`-shaped transfer
holds for the strongest reachable `F`, namely `F := recutFamily G`
(`recutFamily_arenaSound_of_normalizedReversalSound`), and a winning `τ`
yields a winning `committingStrategy (recutFamily (plansOf τ))` through
`accepts_arenaWord_of_winning` and
`winningFrom_committingStrategy_of_accepts`
(`exists_normalized_recut_winner_of_normalizedReversalSound`): a winner whose
committed family is aligned per epoch *and* normalized
(`GlobalFreshOpening`).  What the endpoint deliberately does **not** claim is
`ReversalMeasurable (plansOf τ')`: instantiating `ReversalMeasurable` at
`recutFamily G` (e.g. its `leftTrace` field) forces the fresh-opening blind
traces of `(G cand).2.1` and `(G open).2.1` to coincide from `init` along
every own-input word for *all* atom pairs -- the cross-atom face of
`rem:globalblindtable`, false for a generic winner and unconditional only for
atom-independent summary families (`tableFamily_reversalMeasurable`).
Reconciling the per-epoch alignment installed here with that atom-uniformity
is the `M`-instantiation step that remains on the paper side.
-/

namespace DistributedSynthesis

universe u v x y s

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}

namespace DetParityAutomaton

variable
  {A :
    DetParityAutomaton.{max u v x y, s}
      (RoundRecord In₁ In₂ Graph Out₁ Out₂)}
variable {C_L C_R C_V : Type max u v x y s}

/-! ### The reversal normalization -/

/-- The left block plan with its reversal slot overwritten by the derived
fresh opening: the blind of the right plan committed at the same atom, read
at its initial control.  `init`, `step`, `label`, and `close` are kept. -/
def normalizeRevLeft
    (P :
      BoundaryPlan (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)
        A C_L C_R C_V) :
    LeftBlockPlan (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)
      A C_L :=
  { P.1 with rev := fun _ _ i => (P.2.1.label P.2.1.init).1 i }

/-- The right block plan with its reversal slot overwritten by the derived
fresh opening of the left plan committed at the same atom: the orientation
mirror of `normalizeRevLeft`. -/
def normalizeRevRight
    (P :
      BoundaryPlan (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)
        A C_L C_R C_V) :
    RightBlockPlan (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)
      A C_R :=
  { P.2.1 with rev := fun _ _ i => (P.1.label P.1.init).1 i }

/-- The **reversal normalization** of a plan family: at every atom, keep the
committed block plans' `init`/`step`/`label`/`close`, overwrite the two
reversal slots with the derived fresh openings of the opposite orientation at
the same atom, and replace the chain by the replay chain (`summaryChain`) of
the two normalized block plans.  The chain control becomes `C_L ⊕ C_R`.
Every non-reversal record of the arena fold is unchanged; exactly the
`ReversingRound` records and the reversed-tier records are rewritten. -/
def normalizeRev (G : PlanFamily (In₁ := In₁) A C_L C_R C_V) :
    PlanFamily (In₁ := In₁) A C_L C_R (C_L ⊕ C_R) :=
  fun a =>
    (normalizeRevLeft (G a), normalizeRevRight (G a),
      summaryChain (normalizeRevLeft (G a)) (normalizeRevRight (G a)))

/-- Tracked chain controls of a replay chain are their replay states: for any
committed triple `(L, R, summaryChain L R)` the chain control *is* the sum of
the two block controls.  This generalizes `chainTracks_globalFold_eq` from
the global fold to every family whose chain is the replay of its own block
plans, in particular `normalizeRev` and `recutFamily`. -/
theorem chainTracks_summaryChain_eq
    (L :
      LeftBlockPlan (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)
        A C_L)
    (R :
      RightBlockPlan (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)
        A C_R)
    {cv t : C_L ⊕ C_R}
    (h : ChainTracks (A := A) (L, R, summaryChain L R) cv t) : cv = t := by
  induction h with
  | enterOne c i => rfl
  | enterTwo c i => rfl
  | @stepOne cv' t' h i ih =>
      subst ih
      cases cv' <;> rfl
  | @stepTwo cv' t' h i ih =>
      subst ih
      cases cv' <;> rfl

/-- **The normalization satisfies the β5 hypothesis by construction.**  The
reversal slots are the derived fresh openings (`revLeft`/`revRight` are
`rfl`), and along every reversal-reachable chain control the replay chain's
staged labels are the re-cut chain's staged labels at the tracked replay
state (`chainLeft`/`chainRight`, `rfl` after `chainTracks_summaryChain_eq`). -/
theorem normalizeRev_globalFreshOpening
    (G : PlanFamily (In₁ := In₁) A C_L C_R C_V) :
    GlobalFreshOpening (normalizeRev G) where
  revLeft _ _ _ _ := rfl
  revRight _ _ _ _ := rfl
  chainLeft a cv c h := by
    have hcv :=
      chainTracks_summaryChain_eq (normalizeRevLeft (G a))
        (normalizeRevRight (G a)) h
    subst hcv
    rfl
  chainRight a cv c h := by
    have hcv :=
      chainTracks_summaryChain_eq (normalizeRevLeft (G a))
        (normalizeRevRight (G a)) h
    subst hcv
    rfl

/-- **The re-cut family is its own normalization.**  Its reversal slots are
derived fresh openings and its chain is the replay chain of its own block
plans, so the β5 hypothesis holds for `recutFamily G` unconditionally, for
every `G`. -/
theorem recutFamily_globalFreshOpening
    (G : PlanFamily (In₁ := In₁) A C_L C_R C_V) :
    GlobalFreshOpening (recutFamily G) where
  revLeft _ _ _ _ := rfl
  revRight _ _ _ _ := rfl
  chainLeft a cv c h := by
    have hcv :=
      chainTracks_summaryChain_eq (recutLeftPlan G a) (recutRightPlan G a) h
    subst hcv
    rfl
  chainRight a cv c h := by
    have hcv :=
      chainTracks_summaryChain_eq (recutLeftPlan G a) (recutRightPlan G a) h
    subst hcv
    rfl

/-- **The re-cut does not see the normalized data.**  The re-cut tables read
only the block plans' `init`/`step`/`label`/`close` -- never the reversal
slots or the chain, which is exactly what `normalizeRev` rewrites -- so
re-cutting the normalization is re-cutting the original family. -/
theorem recutFamily_normalizeRev
    (G : PlanFamily (In₁ := In₁) A C_L C_R C_V) :
    recutFamily (normalizeRev G) = recutFamily G := rfl

/-! ### The unconditional splice -/

/-- **The β6 unconditional splice**: on *arbitrary* environments, the word
emitted by the re-cut table family is the word emitted by the reversal
normalization of the reference family.  This is β5's omega-word equality
applied to `normalizeRev G` (whose `GlobalFreshOpening` holds by
construction), read back through `recutFamily_normalizeRev`.  No hypothesis
on `G`, no restriction on direct reversals. -/
theorem arenaWord_recutFamily_eq_normalizeRev
    (G : PlanFamily (In₁ := In₁) A C_L C_R C_V)
    (env : EnvironmentSequence In₁ In₂) :
    arenaWord (recutFamily G) env = arenaWord (normalizeRev G) env := by
  rw [← recutFamily_normalizeRev G]
  exact
    arenaWord_recutFamily_eq_of_globalFreshOpening
      (normalizeRev_globalFreshOpening G) env

/-- On the no-direct fragment the normalization is invisible: the normalized
word is the reference word.  Two applications of the β4 word equality through
`recutFamily_normalizeRev`; the residual below is therefore confined to
environments with direct reversals. -/
theorem arenaWord_normalizeRev_eq_of_noDirect
    (G : PlanFamily (In₁ := In₁) A C_L C_R C_V)
    (env : EnvironmentSequence In₁ In₂)
    (hnd : NoDirectReversalSequence env) :
    arenaWord (normalizeRev G) env = arenaWord G env :=
  calc
    arenaWord (normalizeRev G) env =
        arenaWord (recutFamily G) env :=
      (arenaWord_recutFamily_eq_normalizeRev G env).symm
    _ = arenaWord (recutFamily (normalizeRev G)) env := by
      rw [recutFamily_normalizeRev]
    _ = arenaWord (normalizeRev G) env :=
      arenaWord_recutFamily_eq (normalizeRev G) env hnd
    _ = arenaWord (recutFamily G) env :=
      (arenaWord_recutFamily_eq_normalizeRev G env).symm
    _ = arenaWord G env := arenaWord_recutFamily_eq G env hnd

/-! ### The final named residual -/

/-- **The blind-table compatibility hypothesis** (paper `rem:globalblindtable`,
the `b_new` legality face): acceptance of a plan family's arena word on every
environment survives the reversal normalization.  Equivalently, by the
unconditional splice, this is exactly `hsound` for the fold
`fold := recutFamily`.

Location of the residual.  Everything else is proved: the normalized word
differs from the reference word only at `ReversingRound` records and inside
the reversed tiers they open (`arenaWord_normalizeRev_eq_of_noDirect`: on the
fragment the two words are equal), and there it replaces the winner's
committed `b_old`-indexed reversal output and chain labels by the derived
fresh-opening (`b_new`) outputs and the replay labels.  The β1
per-epoch-minima interface cannot absorb this replacement: the replaced
output feeds `A.step` for the remainder of the epoch, the two runs diverge
inside the epoch, and the per-epoch min-priority summaries cease to be
pointwise equal, so `accepts_iff_of_cutBlockMin_eq` does not apply.  The
statement is *true* for every family already satisfying the β5 hypothesis
(`normalizedReversalSound_of_globalFreshOpening`), in particular for every
global fold and every re-cut family; for the paper's θ̄-tailored winner it is
the reset-parity collapse `bRl · = bRr init`, `bLr · = bLl init` at
reversal-reachable controls together with the chain-replay equalities. -/
def NormalizedReversalSound (G : PlanFamily (In₁ := In₁) A C_L C_R C_V) :
    Prop :=
  (∀ env : EnvironmentSequence In₁ In₂, A.Accepts (arenaWord G env)) ->
    ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (arenaWord (normalizeRev G) env)

/-- Non-vacuity and the discharge shape: a family satisfying the β5
hypothesis satisfies the residual outright, because for it the normalized
word *is* the reference word on every environment. -/
theorem normalizedReversalSound_of_globalFreshOpening
    {G : PlanFamily (In₁ := In₁) A C_L C_R C_V}
    (hG : GlobalFreshOpening G) : NormalizedReversalSound G := by
  intro hacc env
  rw [← arenaWord_recutFamily_eq_normalizeRev G env,
    arenaWord_recutFamily_eq_of_globalFreshOpening hG env]
  exact hacc env

/-- **The `hsound`-shaped transfer for the strongest reachable fold,
`fold := recutFamily`.**  Under the residual, all-environment acceptance of
the reference word transfers to the re-cut word -- the exact hypothesis shape
of `reversalMeasurable_winner_of_fold_of_arenaSound` and
`summaryFold_realizes_of_arenaSound`, with the fold's *alignment* now proved
rather than assumed.  (The fold's `hmeas` is the part that does not hold:
`ReversalMeasurable (recutFamily G)` demands the cross-atom uniformity of
`G`'s fresh-opening blind traces, see the module docstring.) -/
theorem recutFamily_arenaSound_of_normalizedReversalSound
    {G : PlanFamily (In₁ := In₁) A C_L C_R C_V}
    (hres : NormalizedReversalSound G)
    (hacc : ∀ env : EnvironmentSequence In₁ In₂, A.Accepts (arenaWord G env)) :
    ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (arenaWord (recutFamily G) env) := by
  intro env
  rw [arenaWord_recutFamily_eq_normalizeRev G env]
  exact hres hacc env

/-! ### The winner endpoint -/

section Winner

variable [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
  [DecidableEq In₁] [DecidableEq In₂] [DecidableEq A.State]
  [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]
  [Fintype C_L] [DecidableEq C_L] [Inhabited C_L]
  [Fintype C_R] [DecidableEq C_R] [Inhabited C_R]
  [Fintype C_V] [DecidableEq C_V] [Inhabited C_V]

/-- The objective automaton's state space is inhabited by its initial state,
so the re-cut controls inherit `Inhabited`. -/
local instance : Inhabited A.State := ⟨A.initial⟩

/-- Under the residual, a winning boundary strategy's re-cut word is accepted
on **every** environment: `accepts_arenaWord_of_winning` supplies the
reference acceptance, and the `hsound` transfer carries it across the
normalization and the re-cut.  Direct reversals included. -/
theorem accepts_arenaWord_recutFamily_of_winning
    (τ :
      (DetParityAutomaton.boundaryGame A C_L C_R C_V).PositionalStrategy
        ParityPlayer.even)
    (hτ :
      CountableParityGame.PositionalStrategy.WinningFrom
        (G := DetParityAutomaton.boundaryGame A C_L C_R C_V) τ
        (Sum.inl (A.initial, A.initial)))
    (hres : NormalizedReversalSound (plansOf τ))
    (env : EnvironmentSequence In₁ In₂) :
    A.Accepts (arenaWord (recutFamily (plansOf τ)) env) :=
  recutFamily_arenaSound_of_normalizedReversalSound hres
    (fun env' => accepts_arenaWord_of_winning τ hτ env') env

/-- **The β6 endpoint: the aligned, normalized winner, gated solely on the
named residual.**  From a winning positional strategy `τ` and
`NormalizedReversalSound (plansOf τ)`, the boundary game over the re-cut
controls has a winning positional strategy `τ'` committing exactly the
re-cut family of `τ`'s plans -- a winner that is aligned per epoch (β4),
reversal-closed (β5), and normalized: `GlobalFreshOpening (plansOf τ')` holds
by construction.

This is as far toward `EntryIndexedCertificate`'s conclusion
(`WinningFrom τ' ∧ ReversalMeasurable (plansOf τ')`) as truth allows at an
arbitrary winner: the missing conjunct `ReversalMeasurable (plansOf τ')`
reduces, at `plansOf τ' = recutFamily (plansOf τ)`, to the cross-atom
equality of `τ`'s fresh-opening blind traces (`rem:globalblindtable`'s
atom-uniformity face), which fails for a generic winner and is unconditional
only for atom-independent summary families
(`tableFamily_reversalMeasurable`, `summaryFold_reversalMeasurable`). -/
theorem exists_normalized_recut_winner_of_normalizedReversalSound
    (τ :
      (DetParityAutomaton.boundaryGame A C_L C_R C_V).PositionalStrategy
        ParityPlayer.even)
    (hτ :
      CountableParityGame.PositionalStrategy.WinningFrom
        (G := DetParityAutomaton.boundaryGame A C_L C_R C_V) τ
        (Sum.inl (A.initial, A.initial)))
    (hres : NormalizedReversalSound (plansOf τ)) :
    ∃ τ' :
        (DetParityAutomaton.boundaryGame A ((A.State × A.State) × C_L)
            ((A.State × A.State) × C_R)
            (((A.State × A.State) × C_L) ⊕
              ((A.State × A.State) × C_R))).PositionalStrategy
          ParityPlayer.even,
      CountableParityGame.PositionalStrategy.WinningFrom
          (G :=
            DetParityAutomaton.boundaryGame A ((A.State × A.State) × C_L)
              ((A.State × A.State) × C_R)
              (((A.State × A.State) × C_L) ⊕ ((A.State × A.State) × C_R)))
          τ' (Sum.inl (A.initial, A.initial)) ∧
        plansOf τ' = recutFamily (plansOf τ) ∧
        GlobalFreshOpening (plansOf τ') := by
  refine ⟨committingStrategy (recutFamily (plansOf τ)), ?_, ?_, ?_⟩
  · exact
      winningFrom_committingStrategy_of_accepts (recutFamily (plansOf τ))
        (accepts_arenaWord_recutFamily_of_winning τ hτ hres)
  · exact plansOf_committingStrategy _
  · rw [plansOf_committingStrategy]
    exact recutFamily_globalFreshOpening (plansOf τ)

end Winner

end DetParityAutomaton

end DistributedSynthesis
