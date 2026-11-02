/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemEpochRecut

/-!
# The reversing-round bridge: the re-cut correspondence on arbitrary environments

the direct-reversal round and the reversed tier.  `LemEpochRecut`
established full omega-word equality between the re-cut table family
`recutFamily G` and the reference family `G` on every environment without
direct reversals; the single point of disagreement it left to this brick is
the `ReversingRound` record, where `recutFamily G` emits the *derived*
fresh-opening blind of the opposite orientation at the current atom while `G`
emits its committed `rev` slot, together with the reversed-tier continuation.

This file closes that gap under one named hypothesis and lifts the β4
endpoints to **arbitrary environments**:

* `ChainTracks` -- the reversal-reachable chain controls of a committed
  boundary plan, tracked against the replay state they must realize: entered
  from an in-block control by the reversing sender's first input
  (`enterOne`/`enterTwo`), stepped by the mixed sender directions
  (`stepOne`/`stepTwo`, restarting the opposite plan from its `init` across a
  re-reversal, via the β2 projections `summaryChainProjOne/Two`);
* `GlobalFreshOpening` -- the named hypothesis (paper `rem:globalblindtable`
  read at the plan family): the committed reversal slots are the derived
  fresh-opening blinds of the opposite orientation at the same atom
  (`revLeft`/`revRight`, exactly the two outputs a `ReversingRound` record
  compares), and along every reversal-reachable chain control the committed
  chain's staged tables are the replay tables of the block plans committed at
  the same atom (`chainLeft`/`chainRight`, stated as equality with the re-cut
  chain's own staged labels);
* `GlobalRecutSim` -- β4's `RecutSim` extended by the two reversed-tier
  constructors (`revL`/`revR`, the `reversed` shape with the reference
  side at its own chain position, the control tracked by `ChainTracks`);
  `record_eq` now holds on **every** round with no exclusion, and `step` is
  full preservation: the reversing round enters the reversed tier related,
  interior and re-reversal rounds continue it, closing rounds land both folds
  on the same boundary atom;
* the assembled endpoints on arbitrary environments:
  `arenaWord_recutFamily_eq_of_globalFreshOpening` (**full omega-word
  equality**, no `NoDirectReversalSequence`), acceptance transfer, the β1
  minima interface, the cut/atom correspondence, and the β3 epoch-cut shape
  re-read against the reference fold
  (`arenaWord_recutFamily_epoch_cut_of_globalFreshOpening`);
* `globalFold_globalFreshOpening` -- non-vacuity and the intended discharge
  shape: the global fold of any plan family satisfies the hypothesis
  definitionally (`chainTracks_globalFold_eq` identifies its tracked chain
  controls with their replay states).

No retreat to the β1 fallback (equal per-epoch minima and exit atoms in place
of equal records) was needed: under `GlobalFreshOpening` every reversed-tier
case gives record equality.  The hypothesis itself is the honest residue: for
the realizing control-dependent fold (`foldθ`) it demands that the
reversal-slot outputs collapse to the fresh-opening outputs of the committed
inits, the θ̄ reset-parity fact owed by the `hsound`/β6 assembly.
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

/-- The **reversal-reachable chain controls** of a committed boundary plan,
tracked against the replay state they must realize.  `enterOne`/`enterTwo`
enter the reversed tier from an in-block control by the reversing sender's
first input; `stepOne`/`stepTwo` advance by the mixed sender directions,
continuing the tracked block plan on its own orientation and restarting the
opposite plan from its `init` across a re-reversal -- the β2 projections
`summaryChainProjOne`/`summaryChainProjTwo` express both uniformly. -/
inductive ChainTracks
    (P :
      BoundaryPlan (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)
        A C_L C_R C_V) :
    C_V -> (C_L ⊕ C_R) -> Prop
  | enterOne (c : C_L) (i : In₁) :
      ChainTracks P (P.2.2.step (P.2.2.enterL c) (Sum.inr i))
        (Sum.inr (P.2.1.step P.2.1.init i))
  | enterTwo (c : C_R) (i : In₂) :
      ChainTracks P (P.2.2.step (P.2.2.enterR c) (Sum.inl i))
        (Sum.inl (P.1.step P.1.init i))
  | stepOne {cv : C_V} {t : C_L ⊕ C_R} (h : ChainTracks P cv t) (i : In₁) :
      ChainTracks P (P.2.2.step cv (Sum.inr i))
        (Sum.inr
          (P.2.1.step (summaryChainProjOne.{u, v, x, y, s} P.2.1.init t) i))
  | stepTwo {cv : C_V} {t : C_L ⊕ C_R} (h : ChainTracks P cv t) (i : In₂) :
      ChainTracks P (P.2.2.step cv (Sum.inl i))
        (Sum.inl
          (P.1.step (summaryChainProjTwo.{u, v, x, y, s} P.1.init t) i))

/-- **The global-blind-table hypothesis** (paper `rem:globalblindtable` read
at the plan family): the reference family's reversal data is derived, not
free.  `revLeft`/`revRight` state that the committed `rev` slot at any atom,
control, and state pair is the fresh-opening blind of the opposite
orientation committed at the *same* atom -- exactly the two outputs compared
by a `ReversingRound` record of `recutFamily G` against `G`.
`chainLeft`/`chainRight` state that at every reversal-reachable chain control
(`ChainTracks`) the committed chain's staged tables are the replay tables of
the block plans committed at the same atom, i.e. the re-cut chain's own
staged labels at the tracked replay state. -/
structure GlobalFreshOpening
    (G :
      PlanFamily (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)
        A C_L C_R C_V) : Prop where
  revLeft :
    ∀ (a : A.State × A.State) (c : C_L) (q : A.State × A.State) (i : In₁),
      (G a).1.rev c q i = ((G a).2.1.label (G a).2.1.init).1 i
  revRight :
    ∀ (a : A.State × A.State) (c : C_R) (q : A.State × A.State) (i : In₂),
      (G a).2.1.rev c q i = ((G a).1.label (G a).1.init).1 i
  chainLeft :
    ∀ (a : A.State × A.State) (cv : C_V) (c : C_L),
      ChainTracks (G a) cv (Sum.inl c) ->
        (G a).2.2.labelL cv = (recutChain G a).labelL (Sum.inl (a, c))
  chainRight :
    ∀ (a : A.State × A.State) (cv : C_V) (c : C_R),
      ChainTracks (G a) cv (Sum.inr c) ->
        (G a).2.2.labelR cv = (recutChain G a).labelR (Sum.inr (a, c))

/-- The **reversal-closed re-cut correspondence**: β4's `RecutSim` extended
by the two reversed-tier constructors.  A re-cut reversed position at chain
control `Sum.inl (a, c)` (resp. `Sum.inr (a, c)`) corresponds to the
reference's reversed position at a chain control tracking `Sum.inl c` (resp.
`Sum.inr c`) in the block committed at `a` -- the `reversed` shape, with
the reference side at its own chain tier rather than an in-block replay. -/
inductive GlobalRecutSim (G : PlanFamily (In₁ := In₁) A C_L C_R C_V) :
    BoundaryGamePosition (In₁ := In₁) A ((A.State × A.State) × C_L)
        ((A.State × A.State) × C_R)
        (((A.State × A.State) × C_L) ⊕ ((A.State × A.State) × C_R)) ->
      BoundaryGamePosition (In₁ := In₁) A C_L C_R C_V -> Prop
  | boundary (state minState : A.State) :
      GlobalRecutSim G (Sum.inl (state, minState))
        (Sum.inl (state, minState))
  | inBlockL (a : A.State × A.State) (c : C_L) (state minState : A.State) :
      GlobalRecutSim G
        (Sum.inr (Sum.inr (Sum.inl
          (recutLeftPlan G a, recutChain G a, (a, c), state, minState))))
        (Sum.inr (Sum.inr (Sum.inl
          ((G a).1, (G a).2.2, c, state, minState))))
  | inBlockR (a : A.State × A.State) (c : C_R) (state minState : A.State) :
      GlobalRecutSim G
        (Sum.inr (Sum.inr (Sum.inr (Sum.inl
          (recutRightPlan G a, recutChain G a, (a, c), state, minState)))))
        (Sum.inr (Sum.inr (Sum.inr (Sum.inl
          ((G a).2.1, (G a).2.2, c, state, minState)))))
  | revL (a : A.State × A.State) (c : C_L) (cv : C_V)
      (h : ChainTracks (G a) cv (Sum.inl c)) (entry : A.State × A.State)
      (state minState : A.State) :
      GlobalRecutSim G
        (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl
          (recutChain G a, Sum.inl (a, c), entry, state, minState))))))
        (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl
          ((G a).2.2, cv, entry, state, minState))))))
  | revR (a : A.State × A.State) (c : C_R) (cv : C_V)
      (h : ChainTracks (G a) cv (Sum.inr c)) (entry : A.State × A.State)
      (state minState : A.State) :
      GlobalRecutSim G
        (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr
          (recutChain G a, Sum.inr (a, c), entry, state, minState))))))
        (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr
          ((G a).2.2, cv, entry, state, minState))))))

namespace GlobalRecutSim

variable {G : PlanFamily (In₁ := In₁) A C_L C_R C_V}
variable
  {p :
    BoundaryGamePosition (In₁ := In₁) A ((A.State × A.State) × C_L)
      ((A.State × A.State) × C_R)
      (((A.State × A.State) × C_L) ⊕ ((A.State × A.State) × C_R))}
variable {q : BoundaryGamePosition (In₁ := In₁) A C_L C_R C_V}

/-- **Record agreement on every round.**  Related positions emit equal round
records with no exclusion: boundary, in-block, and closing rounds are
definitional as in β4; the reversing round compares the derived fresh-opening
blind with the committed `rev` slot (`revLeft`/`revRight`), and the
reversed-tier rounds read the tracked chain labels (`chainLeft`/`chainRight`). -/
theorem record_eq (hG : GlobalFreshOpening G) (h : GlobalRecutSim G p q)
    (round : EnvironmentRound In₁ In₂) :
    arenaRecord (recutFamily G) p round = arenaRecord G q round := by
  obtain ⟨i₁, i₂, g⟩ := round
  cases h with
  | boundary state minState => cases g <;> rfl
  | inBlockL a c state minState =>
      cases g with
      | left => rfl
      | both => rfl
      | right =>
          show
            rightRoundRecord (i₂, i₁)
                (((G a).2.1.label (G a).2.1.init).1 i₁)
                ((G a).1.close c (state, minState) (i₁, i₂)) =
              rightRoundRecord (i₂, i₁)
                ((G a).1.rev c (state, minState) i₁)
                ((G a).1.close c (state, minState) (i₁, i₂))
          rw [hG.revLeft a c (state, minState) i₁]
  | inBlockR a c state minState =>
      cases g with
      | right => rfl
      | both => rfl
      | left =>
          show
            leftRoundRecord (i₁, i₂)
                ((G a).2.1.close c (state, minState) (i₂, i₁))
                (((G a).1.label (G a).1.init).1 i₂) =
              leftRoundRecord (i₁, i₂)
                ((G a).2.1.close c (state, minState) (i₂, i₁))
                ((G a).2.1.rev c (state, minState) i₂)
          rw [hG.revRight a c (state, minState) i₂]
  | revL a c cv htrack entry state minState =>
      have hl := (hG.chainLeft a cv c htrack).symm
      cases g with
      | left =>
          exact
            congrArg
              (fun st =>
                leftRoundRecord (i₁, i₂)
                  (st.1 (entry, state, minState) (i₁, i₂))
                  (st.2.2.1 entry i₂))
              hl
      | both =>
          exact
            congrArg
              (fun st =>
                bothRoundRecord (i₁, i₂)
                  (st.1 (entry, state, minState) (i₁, i₂))
                  (st.2.2.2 (entry, state, minState) (i₁, i₂)))
              hl
      | right =>
          exact
            congrArg
              (fun st =>
                rightRoundRecord (i₂, i₁)
                  (st.2.1 (entry, state, minState) i₁)
                  (st.2.2.2 (entry, state, minState) (i₁, i₂)))
              hl
  | revR a c cv htrack entry state minState =>
      have hr := (hG.chainRight a cv c htrack).symm
      cases g with
      | right =>
          exact
            congrArg
              (fun st =>
                rightRoundRecord (i₂, i₁) (st.2.1 entry i₁)
                  (st.2.2.2 (entry, state, minState) (i₁, i₂)))
              hr
      | both =>
          exact
            congrArg
              (fun st =>
                bothRoundRecord (i₁, i₂)
                  (st.1 (entry, state, minState) (i₁, i₂))
                  (st.2.2.2 (entry, state, minState) (i₁, i₂)))
              hr
      | left =>
          exact
            congrArg
              (fun st =>
                leftRoundRecord (i₁, i₂)
                  (st.1 (entry, state, minState) (i₁, i₂))
                  (st.2.2.1 (entry, state, minState) i₂))
              hr

/-- **Full step preservation.**  On every round the correspondence is
preserved: boundary rounds re-commit and re-enter (the β4 re-cut), in-block
rounds continue or close as in β4, the reversing round enters the reversed
tier related (`ChainTracks.enterOne`/`enterTwo`), reversed-tier interior
rounds continue it, re-reversals restart the opposite replay
(`ChainTracks.stepOne`/`stepTwo`), and reversed-tier closings land both folds
on the same boundary atom. -/
theorem step (hG : GlobalFreshOpening G) (h : GlobalRecutSim G p q)
    (round : EnvironmentRound In₁ In₂) :
    GlobalRecutSim G (arenaStep (recutFamily G) p round)
      (arenaStep G q round) := by
  obtain ⟨i₁, i₂, g⟩ := round
  cases h with
  | boundary state minState =>
      cases g with
      | left => exact inBlockL _ _ _ _
      | right => exact inBlockR _ _ _ _
      | both => exact boundary _ _
  | inBlockL a c state minState =>
      cases g with
      | left => exact inBlockL _ _ _ _
      | both => exact boundary _ _
      | right =>
          show
            GlobalRecutSim G
              (A.leftReverseTarget (recutLeftPlan G a) (recutChain G a)
                (a, c) state minState (i₁, i₂))
              (A.leftReverseTarget (G a).1 (G a).2.2 c state minState
                (i₁, i₂))
          simp only [leftReverseTarget, hG.revLeft a c (state, minState) i₁]
          exact revR a _ _ (ChainTracks.enterOne c i₁) _ _ _
  | inBlockR a c state minState =>
      cases g with
      | right => exact inBlockR _ _ _ _
      | both => exact boundary _ _
      | left =>
          show
            GlobalRecutSim G
              (A.rightReverseTarget (recutRightPlan G a) (recutChain G a)
                (a, c) state minState (i₂, i₁))
              (A.rightReverseTarget (G a).2.1 (G a).2.2 c state minState
                (i₂, i₁))
          simp only [rightReverseTarget, hG.revRight a c (state, minState) i₂]
          exact revL a _ _ (ChainTracks.enterTwo c i₂) _ _ _
  | revL a c cv htrack entry state minState =>
      have hl := hG.chainLeft a cv c htrack
      cases g with
      | left =>
          show
            GlobalRecutSim G
              (A.revLeftContinueTarget (recutChain G a) (Sum.inl (a, c))
                entry state minState (i₁, i₂))
              (A.revLeftContinueTarget (G a).2.2 cv entry state minState
                (i₁, i₂))
          simp only [revLeftContinueTarget, hl]
          exact revL a _ _ (ChainTracks.stepTwo htrack i₂) _ _ _
      | both =>
          show
            GlobalRecutSim G
              (A.revLeftCloseTarget (recutChain G a) (Sum.inl (a, c)) entry
                state minState (i₁, i₂))
              (A.revLeftCloseTarget (G a).2.2 cv entry state minState
                (i₁, i₂))
          simp only [revLeftCloseTarget, hl]
          exact boundary _ _
      | right =>
          show
            GlobalRecutSim G
              (A.revLeftReverseTarget (recutChain G a) (Sum.inl (a, c))
                entry state minState (i₁, i₂))
              (A.revLeftReverseTarget (G a).2.2 cv entry state minState
                (i₁, i₂))
          simp only [revLeftReverseTarget, hl]
          exact revR a _ _ (ChainTracks.stepOne htrack i₁) _ _ _
  | revR a c cv htrack entry state minState =>
      have hr := hG.chainRight a cv c htrack
      cases g with
      | right =>
          show
            GlobalRecutSim G
              (A.revRightContinueTarget (recutChain G a) (Sum.inr (a, c))
                entry state minState (i₁, i₂))
              (A.revRightContinueTarget (G a).2.2 cv entry state minState
                (i₁, i₂))
          simp only [revRightContinueTarget, hr]
          exact revR a _ _ (ChainTracks.stepOne htrack i₁) _ _ _
      | both =>
          show
            GlobalRecutSim G
              (A.revRightCloseTarget (recutChain G a) (Sum.inr (a, c)) entry
                state minState (i₁, i₂))
              (A.revRightCloseTarget (G a).2.2 cv entry state minState
                (i₁, i₂))
          simp only [revRightCloseTarget, hr]
          exact boundary _ _
      | left =>
          show
            GlobalRecutSim G
              (A.revRightReverseTarget (recutChain G a) (Sum.inr (a, c))
                entry state minState (i₁, i₂))
              (A.revRightReverseTarget (G a).2.2 cv entry state minState
                (i₁, i₂))
          simp only [revRightReverseTarget, hr]
          exact revL a _ _ (ChainTracks.stepTwo htrack i₂) _ _ _

/-- Related positions rest at a boundary atom simultaneously, and at the same
atom. -/
theorem boundary_iff (h : GlobalRecutSim G p q) (atom : A.State × A.State) :
    p = Sum.inl atom ↔ q = Sum.inl atom := by
  cases h <;> simp

end GlobalRecutSim

variable {G : PlanFamily (In₁ := In₁) A C_L C_R C_V}

/-- The correspondence propagates from a common boundary atom through
**every** round of an arbitrary environment. -/
theorem globalRecutSim_arenaFoldSeqFrom (hG : GlobalFreshOpening G)
    (env : EnvironmentSequence In₁ In₂) (p : A.State × A.State) :
    ∀ n : Nat,
      GlobalRecutSim G
        (arenaFoldSeqFrom (recutFamily G) (Sum.inl p) env n)
        (arenaFoldSeqFrom G (Sum.inl p) env n)
  | 0 => GlobalRecutSim.boundary p.1 p.2
  | n + 1 =>
      (globalRecutSim_arenaFoldSeqFrom hG env p n).step hG (env n)

/-- **Suffix-word equality from a shared entry atom on an arbitrary
environment**: the epoch tail of the re-cut fold is the reference's own
replay, direct reversals included. -/
theorem arenaWordFrom_recutFamily_eq_of_globalFreshOpening
    (hG : GlobalFreshOpening G) (env : EnvironmentSequence In₁ In₂)
    (p : A.State × A.State) :
    arenaWordFrom (recutFamily G) (Sum.inl p) env =
      arenaWordFrom G (Sum.inl p) env :=
  funext fun n =>
    (globalRecutSim_arenaFoldSeqFrom hG env p n).record_eq hG (env n)

/-- The correspondence holds along the whole arena fold on an arbitrary
environment. -/
theorem globalRecutSim_arenaFoldSeq (hG : GlobalFreshOpening G)
    (env : EnvironmentSequence In₁ In₂) (n : Nat) :
    GlobalRecutSim G (arenaFoldSeq (recutFamily G) env n)
      (arenaFoldSeq G env n) := by
  have h := globalRecutSim_arenaFoldSeqFrom hG env (A.initial, A.initial) n
  rwa [arenaFoldSeqFrom_initial (recutFamily G) env n,
    arenaFoldSeqFrom_initial G env n] at h

/-- The two folds rest at the same boundary atoms at the same rounds, on an
arbitrary environment: the epoch decompositions coincide, cut for cut and
atom for atom. -/
theorem recutFamily_boundary_atom_iff_of_globalFreshOpening
    (hG : GlobalFreshOpening G) (env : EnvironmentSequence In₁ In₂) (n : Nat)
    (p : A.State × A.State) :
    arenaFoldSeq (recutFamily G) env n = Sum.inl p ↔
      arenaFoldSeq G env n = Sum.inl p :=
  (globalRecutSim_arenaFoldSeq hG env n).boundary_iff p

/-- **The assembled β5 endpoint: full omega-word equality on arbitrary
environments.**  Under the global-blind-table hypothesis the word emitted by
the re-cut table family is the word emitted by the reference family itself,
with no restriction on direct reversals. -/
theorem arenaWord_recutFamily_eq_of_globalFreshOpening
    (hG : GlobalFreshOpening G) (env : EnvironmentSequence In₁ In₂) :
    arenaWord (recutFamily G) env = arenaWord G env :=
  funext fun n =>
    (globalRecutSim_arenaFoldSeq hG env n).record_eq hG (env n)

/-- Acceptance transfers between the re-cut fold and the reference fold on
every environment. -/
theorem accepts_arenaWord_recutFamily_iff_of_globalFreshOpening
    (hG : GlobalFreshOpening G) (env : EnvironmentSequence In₁ In₂) :
    A.Accepts (arenaWord (recutFamily G) env) ↔
      A.Accepts (arenaWord G env) := by
  rw [arenaWord_recutFamily_eq_of_globalFreshOpening hG env]

/-- **The β1 interface on arbitrary environments**: along the sync cuts, the
per-epoch min-priority summaries of the re-cut word and of the reference word
are pointwise equal -- the exact hypothesis `accepts_iff_of_cutBlockMin_eq`
consumes. -/
theorem cutBlockMin_arenaWord_recutFamily_eq_of_globalFreshOpening
    (hG : GlobalFreshOpening G) (env : EnvironmentSequence In₁ In₂)
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
  have h := arenaWord_recutFamily_eq_of_globalFreshOpening hG env
  revert hinf
  rw [h]
  intro hinf
  rfl

/-- **The re-cut epoch endpoint against the reference, on arbitrary
environments.**  With recurring sync rounds, every cut of the re-cut word
carries a boundary atom shared by both folds, its state component is the run
at the cut, and the epoch tail of the re-cut word is the *reference* family's
arena word restarted from that atom -- the per-epoch shape `LemRouteBetaAssembly` splices
into `accepts_iff_of_epoch_segments`, now with direct reversals allowed
inside every epoch. -/
theorem arenaWord_recutFamily_epoch_cut_of_globalFreshOpening
    (hG : GlobalFreshOpening G) (env : EnvironmentSequence In₁ In₂)
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
    ⟨p, hp,
      (recutFamily_boundary_atom_iff_of_globalFreshOpening hG env _ p).1 hp,
      hrun, fun j => ?_⟩
  rw [htail j]
  exact
    congrFun (arenaWordFrom_recutFamily_eq_of_globalFreshOpening hG _ p) j

/-! ### The global fold satisfies the hypothesis by construction

Non-vacuity and the intended discharge shape: for the global fold, whose
blind and reversal slots are two shared constant tables and whose chain is
the fold of its own overwritten block plans, every field of
`GlobalFreshOpening` is definitional.  For the realizing control-dependent
fold (`foldθ`) the hypothesis is exactly the θ̄ reset-parity collapse of the
reversal slots onto the committed inits, owed by the `hsound`/β6 assembly. -/

/-- Tracked chain controls of the global fold are their replay states: the
folded chain's control *is* the sum of the two block controls. -/
theorem chainTracks_globalFold_eq (t_L : In₂ -> Out₂) (t_R : In₁ -> Out₁)
    (P : PlanFamily (In₁ := In₁) A C_L C_R C_V) (a : A.State × A.State)
    {cv t} (h : ChainTracks (globalFold t_L t_R P a) cv t) : cv = t := by
  induction h with
  | enterOne c i => rfl
  | enterTwo c i => rfl
  | @stepOne cv' t' h i ih =>
      subst ih
      cases cv' <;> rfl
  | @stepTwo cv' t' h i ih =>
      subst ih
      cases cv' <;> rfl

/-- **The global fold satisfies `GlobalFreshOpening` by construction**: its
reversal slots and fresh-opening blinds are the same two shared tables, and
its chain replays its own block plans. -/
theorem globalFold_globalFreshOpening (t_L : In₂ -> Out₂) (t_R : In₁ -> Out₁)
    (P : PlanFamily (In₁ := In₁) A C_L C_R C_V) :
    GlobalFreshOpening (globalFold t_L t_R P) where
  revLeft _ _ _ _ := rfl
  revRight _ _ _ _ := rfl
  chainLeft a cv c h := by
    have hcv := chainTracks_globalFold_eq t_L t_R P a h
    subst hcv
    rfl
  chainRight a cv c h := by
    have hcv := chainTracks_globalFold_eq t_L t_R P a h
    subst hcv
    rfl

end DetParityAutomaton

end DistributedSynthesis
