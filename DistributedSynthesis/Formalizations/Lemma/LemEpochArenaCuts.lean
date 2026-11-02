/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemArenaSuffixTransport
import DistributedSynthesis.Formalizations.Theorem.ThmBoundaryDecomposition

/-!
# Epoch cuts of arena words

the epoch decomposition of the word emitted by the
arena fold.  The synchronization cuts of the emitted word coincide with
the rounds at which the fold rests at a boundary atom, and the objective
automaton's run at a cut is the atom's state component.  Concretely:

* `arenaWord_graph` -- the emitted record carries the environment's
  round graph, so the sync structure of the arena word is the sync
  structure of the environment;
* `arenaFoldSeq_succ_boundary_iff` -- the fold rests at a boundary atom
  after round `n` exactly when round `n` synchronizes;
* `syncBoundary_arenaWord_iff` -- **cut/position correspondence**: the
  sync boundaries of the emitted word are exactly the rounds at which
  the fold rests at a boundary atom;
* `run_arenaWord_of_boundary_atom` -- **arena run identity at a cut**:
  at a boundary atom the run of the emitted word is the atom's state
  component (from `positionState_arenaFoldSeq`);
* `arenaWord_epoch_cut` -- the assembled endpoint: with recurring sync
  rounds, every cut of `syncCuts` carries a boundary atom whose state
  component is the run at the cut, and the epoch tail of the emitted
  word is the arena word restarted from that atom against the dropped
  environment.  This is the packaging bricks β4 and β6 consume: each
  epoch is an `arenaWordFrom` from a boundary atom, the shape the
  replay simulations (`LemArenaReplaySimulation`) and the per-epoch
  transfer (`accepts_iff_of_epoch_segments`) read;
* `syncCuts_arenaWord_closing_env`/`syncCuts_arenaWord_interior_env` --
  each epoch of the environment closes with its `both` round and has no
  interior one;
* `env_both_recurrent_or_trapped`/`arenaFoldSeq_regime_dichotomy` --
  the regime dichotomy: either sync rounds recur, so the epoch
  decomposition exists, or the fold is trapped away from boundary atoms
  forever after some round (the trapped tail handled by
  `LemArenaSuffixTransport`).
-/

namespace DistributedSynthesis

universe u v x y s

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}

/-- Every cut of `syncCuts` is a sync boundary: cut zero is round zero,
and every later cut is marked by construction. -/
theorem syncBoundary_syncCuts
    (w : OmegaWord (RoundRecord In₁ In₂ Graph Out₁ Out₂))
    (hinf : ∀ n : Nat, ∃ m : Nat, n ≤ m ∧ (w m).graph = Graph.both) :
    ∀ k : Nat, SyncBoundary w (syncCuts w hinf k)
  | 0 => Or.inl rfl
  | k + 1 => marked_cutSeq_succ (syncBoundary_unbounded w hinf) k

/-- **The regime dichotomy of an environment**: either synchronizing
rounds recur unboundedly, or from some round on the environment never
synchronizes again. -/
theorem env_both_recurrent_or_trapped (env : EnvironmentSequence In₁ In₂) :
    (∀ n : Nat, ∃ m : Nat, n ≤ m ∧ (env m).graph = Graph.both) ∨
      ∃ N : Nat, ∀ m : Nat, N ≤ m -> (env m).graph ≠ Graph.both := by
  rcases Classical.em
      (∀ n : Nat, ∃ m : Nat, n ≤ m ∧ (env m).graph = Graph.both) with
    h | h
  · exact Or.inl h
  · obtain ⟨N, hN⟩ := Classical.not_forall.mp h
    exact Or.inr ⟨N, fun m hm hboth => hN ⟨m, hm, hboth⟩⟩

namespace DetParityAutomaton

variable
  {A :
    DetParityAutomaton.{max u v x y, s}
      (RoundRecord In₁ In₂ Graph Out₁ Out₂)}
  {C_L C_R C_V : Type max u v x y s}

/-- The emitted record carries the environment's round graph: the sync
structure of the arena word is the sync structure of the environment. -/
theorem arenaWord_graph (plans : PlanFamily (In₁ := In₁) A C_L C_R C_V)
    (env : EnvironmentSequence In₁ In₂) (n : Nat) :
    (arenaWord plans env n).graph = (env n).graph := by
  show (arenaRecord plans (arenaFoldSeq plans env n) (env n)).graph =
    (env n).graph
  rcases hpos : arenaFoldSeq plans env n with
    ⟨state, minState⟩ | committed |
    ⟨plan, chain, control, state, minState⟩ |
    ⟨plan, chain, control, state, minState⟩ |
    ⟨chain, control, entry, state, minState⟩ |
    ⟨chain, control, entry, state, minState⟩
  · cases hgraph : (env n).graph <;>
      simp [arenaRecord, hgraph, leftRoundRecord, rightRoundRecord,
        bothRoundRecord]
  · exact absurd hpos (arenaFoldSeq_ne_committed plans env n committed)
  · cases hgraph : (env n).graph <;>
      simp [arenaRecord, hgraph, leftRoundRecord, rightRoundRecord,
        bothRoundRecord]
  · cases hgraph : (env n).graph <;>
      simp [arenaRecord, hgraph, leftRoundRecord, rightRoundRecord,
        bothRoundRecord]
  · cases hgraph : (env n).graph <;>
      simp [arenaRecord, hgraph, leftRoundRecord, rightRoundRecord,
        bothRoundRecord]
  · cases hgraph : (env n).graph <;>
      simp [arenaRecord, hgraph, leftRoundRecord, rightRoundRecord,
        bothRoundRecord]

/-- A synchronizing round moves every reachable position to a boundary
atom: all `both` targets of the arena step are of the first tier. -/
theorem arenaStep_boundary_of_both
    (plans : PlanFamily (In₁ := In₁) A C_L C_R C_V)
    (position : BoundaryGamePosition (In₁ := In₁) A C_L C_R C_V)
    (envRound : EnvironmentRound In₁ In₂)
    (hnc : ∀ committed, position ≠ Sum.inr (Sum.inl committed))
    (hboth : envRound.graph = Graph.both) :
    ∃ p : A.State × A.State,
      arenaStep plans position envRound = Sum.inl p := by
  rcases h : arenaStep plans position envRound with p | q
  · exact ⟨p, rfl⟩
  · exfalso
    rcases position with
      ⟨state, minState⟩ | committed |
      ⟨plan, chain, control, state, minState⟩ |
      ⟨plan, chain, control, state, minState⟩ |
      ⟨chain, control, entry, state, minState⟩ |
      ⟨chain, control, entry, state, minState⟩
    · simp [arenaStep, hboth, boundaryBothTarget] at h
    · exact hnc committed rfl
    · simp [arenaStep, hboth, leftCloseTarget] at h
    · simp [arenaStep, hboth, rightCloseTarget] at h
    · simp [arenaStep, hboth, revLeftCloseTarget] at h
    · simp [arenaStep, hboth, revRightCloseTarget] at h

/-- A non-synchronizing round never reaches a boundary atom: all `left`
and `right` targets of the arena step stay in the block tiers. -/
theorem arenaStep_ne_boundary_of_ne_both
    (plans : PlanFamily (In₁ := In₁) A C_L C_R C_V)
    (position : BoundaryGamePosition (In₁ := In₁) A C_L C_R C_V)
    (envRound : EnvironmentRound In₁ In₂)
    (hne : envRound.graph ≠ Graph.both) :
    ∀ p : A.State × A.State,
      arenaStep plans position envRound ≠ Sum.inl p := by
  intro p hp
  rcases position with
    ⟨state, minState⟩ | committed |
    ⟨plan, chain, control, state, minState⟩ |
    ⟨plan, chain, control, state, minState⟩ |
    ⟨chain, control, entry, state, minState⟩ |
    ⟨chain, control, entry, state, minState⟩
  · cases hgraph : envRound.graph
    · simp [arenaStep, hgraph, boundaryOpenLeftTarget] at hp
    · simp [arenaStep, hgraph, boundaryOpenRightTarget] at hp
    · exact hne hgraph
  · simp [arenaStep] at hp
  · cases hgraph : envRound.graph
    · simp [arenaStep, hgraph, leftContinueTarget] at hp
    · simp [arenaStep, hgraph, leftReverseTarget] at hp
    · exact hne hgraph
  · cases hgraph : envRound.graph
    · simp [arenaStep, hgraph, rightReverseTarget] at hp
    · simp [arenaStep, hgraph, rightContinueTarget] at hp
    · exact hne hgraph
  · cases hgraph : envRound.graph
    · simp [arenaStep, hgraph, revLeftContinueTarget] at hp
    · simp [arenaStep, hgraph, revLeftReverseTarget] at hp
    · exact hne hgraph
  · cases hgraph : envRound.graph
    · simp [arenaStep, hgraph, revRightReverseTarget] at hp
    · simp [arenaStep, hgraph, revRightContinueTarget] at hp
    · exact hne hgraph

/-- The fold rests at a boundary atom after round `n` exactly when
round `n` synchronizes. -/
theorem arenaFoldSeq_succ_boundary_iff
    (plans : PlanFamily (In₁ := In₁) A C_L C_R C_V)
    (env : EnvironmentSequence In₁ In₂) (n : Nat) :
    (∃ p : A.State × A.State,
        arenaFoldSeq plans env (n + 1) = Sum.inl p) ↔
      (env n).graph = Graph.both := by
  have hsucc :
      arenaFoldSeq plans env (n + 1) =
        arenaStep plans (arenaFoldSeq plans env n) (env n) := rfl
  constructor
  · rintro ⟨p, hp⟩
    by_contra hne
    rw [hsucc] at hp
    exact
      arenaStep_ne_boundary_of_ne_both plans (arenaFoldSeq plans env n)
        (env n) hne p hp
  · intro hboth
    rw [hsucc]
    exact
      arenaStep_boundary_of_both plans (arenaFoldSeq plans env n) (env n)
        (arenaFoldSeq_ne_committed plans env n) hboth

/-- **Cut/position correspondence**: the sync boundaries of the emitted
word are exactly the rounds at which the fold rests at a boundary
atom. -/
theorem syncBoundary_arenaWord_iff
    (plans : PlanFamily (In₁ := In₁) A C_L C_R C_V)
    (env : EnvironmentSequence In₁ In₂) (n : Nat) :
    SyncBoundary (arenaWord plans env) n ↔
      ∃ p : A.State × A.State,
        arenaFoldSeq plans env n = Sum.inl p := by
  cases n with
  | zero =>
      exact
        iff_of_true (Or.inl rfl) ⟨(A.initial, A.initial), rfl⟩
  | succ m =>
      have hg := arenaWord_graph plans env m
      constructor
      · rintro (h0 | hboth)
        · exact absurd h0 (Nat.succ_ne_zero m)
        · refine (arenaFoldSeq_succ_boundary_iff plans env m).2 ?_
          rw [← hg]
          simpa using hboth
      · intro hp
        refine Or.inr ?_
        have hboth := (arenaFoldSeq_succ_boundary_iff plans env m).1 hp
        rw [← hg] at hboth
        simpa using hboth

/-- **Arena run identity at a boundary atom**: the run of the emitted
word at a round where the fold rests at a boundary atom is the atom's
state component. -/
theorem run_arenaWord_of_boundary_atom
    (plans : PlanFamily (In₁ := In₁) A C_L C_R C_V)
    (env : EnvironmentSequence In₁ In₂) {n : Nat}
    {p : A.State × A.State}
    (hp : arenaFoldSeq plans env n = Sum.inl p) :
    A.run (arenaWord plans env) n = p.1 := by
  have h := positionState_arenaFoldSeq plans env n
  rw [hp] at h
  obtain ⟨p1, p2⟩ := p
  exact h.symm

/-- The arena word restarted from the position reached at `k`, against
the dropped environment, is the tail of the arena word at `k`. -/
theorem arenaWordFrom_arenaWord
    (plans : PlanFamily (In₁ := In₁) A C_L C_R C_V)
    (env : EnvironmentSequence In₁ In₂) (k m : Nat) :
    arenaWordFrom plans (arenaFoldSeq plans env k)
        (OmegaWord.drop env k) m =
      arenaWord plans env (k + m) := by
  show arenaRecord plans
      (arenaFoldSeqFrom plans (arenaFoldSeq plans env k)
        (OmegaWord.drop env k) m)
      (OmegaWord.drop env k m) = _
  rw [arenaFoldSeqFrom_arenaFoldSeq]
  rfl

/-- Sync recurrence transfers between the emitted word and the
environment. -/
theorem arenaWord_both_recurrent_iff
    (plans : PlanFamily (In₁ := In₁) A C_L C_R C_V)
    (env : EnvironmentSequence In₁ In₂) :
    (∀ n : Nat, ∃ m : Nat, n ≤ m ∧
        (arenaWord plans env m).graph = Graph.both) ↔
      ∀ n : Nat, ∃ m : Nat, n ≤ m ∧ (env m).graph = Graph.both := by
  constructor <;>
    · intro h n
      obtain ⟨m, hnm, hboth⟩ := h n
      refine ⟨m, hnm, ?_⟩
      rw [arenaWord_graph plans env m] at *
      exact hboth

/-- **The assembled epoch-cut endpoint.**  With recurring sync rounds,
every cut of the emitted word carries a boundary atom whose state
component is the run at the cut, and the epoch tail of the emitted word
is the arena word restarted from that atom against the dropped
environment.  Each epoch of the arena play is therefore an
`arenaWordFrom` from a boundary atom, the exact shape the replay
simulations and the per-epoch acceptance transfer consume. -/
theorem arenaWord_epoch_cut
    (plans : PlanFamily (In₁ := In₁) A C_L C_R C_V)
    (env : EnvironmentSequence In₁ In₂)
    (hinf : ∀ n : Nat, ∃ m : Nat, n ≤ m ∧
      (arenaWord plans env m).graph = Graph.both)
    (k : Nat) :
    ∃ p : A.State × A.State,
      arenaFoldSeq plans env (syncCuts (arenaWord plans env) hinf k) =
          Sum.inl p ∧
        p.1 =
          A.run (arenaWord plans env)
            (syncCuts (arenaWord plans env) hinf k) ∧
        ∀ j : Nat,
          arenaWord plans env
              (syncCuts (arenaWord plans env) hinf k + j) =
            arenaWordFrom plans (Sum.inl p)
              (OmegaWord.drop env (syncCuts (arenaWord plans env) hinf k))
              j := by
  obtain ⟨p, hp⟩ :=
    (syncBoundary_arenaWord_iff plans env _).1
      (syncBoundary_syncCuts (arenaWord plans env) hinf k)
  refine
    ⟨p, hp, (run_arenaWord_of_boundary_atom plans env hp).symm, fun j => ?_⟩
  rw [← arenaWordFrom_arenaWord plans env _ j, hp]

/-- Each epoch of the environment closes with its `both` round. -/
theorem syncCuts_arenaWord_closing_env
    (plans : PlanFamily (In₁ := In₁) A C_L C_R C_V)
    (env : EnvironmentSequence In₁ In₂)
    (hinf : ∀ n : Nat, ∃ m : Nat, n ≤ m ∧
      (arenaWord plans env m).graph = Graph.both)
    (k : Nat) :
    (env (syncCuts (arenaWord plans env) hinf (k + 1) - 1)).graph =
      Graph.both := by
  rw [← arenaWord_graph plans env]
  exact syncCuts_closing (arenaWord plans env) hinf k

/-- No epoch of the environment contains an interior `both` round. -/
theorem syncCuts_arenaWord_interior_env
    (plans : PlanFamily (In₁ := In₁) A C_L C_R C_V)
    (env : EnvironmentSequence In₁ In₂)
    (hinf : ∀ n : Nat, ∃ m : Nat, n ≤ m ∧
      (arenaWord plans env m).graph = Graph.both)
    (k : Nat) {j : Nat}
    (h1 : syncCuts (arenaWord plans env) hinf k ≤ j)
    (h2 : j + 1 < syncCuts (arenaWord plans env) hinf (k + 1)) :
    (env j).graph ≠ Graph.both := by
  rw [← arenaWord_graph plans env]
  exact syncCuts_interior (arenaWord plans env) hinf k h1 h2

/-- In the trapped regime the fold never returns to a boundary atom:
after the last sync round every position is a block or reversed
position. -/
theorem arenaFoldSeq_trapped_tail
    (plans : PlanFamily (In₁ := In₁) A C_L C_R C_V)
    (env : EnvironmentSequence In₁ In₂) {N : Nat}
    (hN : ∀ m : Nat, N ≤ m -> (env m).graph ≠ Graph.both) :
    ∀ n : Nat, N < n ->
      ∀ p : A.State × A.State,
        arenaFoldSeq plans env n ≠ Sum.inl p := by
  intro n hn p hp
  obtain ⟨m, rfl⟩ : ∃ m : Nat, n = m + 1 := ⟨n - 1, by omega⟩
  exact
    hN m (by omega)
      ((arenaFoldSeq_succ_boundary_iff plans env m).1 ⟨p, hp⟩)

/-- **The regime dichotomy of the arena fold**: either sync rounds of
the emitted word recur, so the epoch decomposition of
`arenaWord_epoch_cut` exists, or the fold is trapped away from boundary
atoms forever after some round. -/
theorem arenaFoldSeq_regime_dichotomy
    (plans : PlanFamily (In₁ := In₁) A C_L C_R C_V)
    (env : EnvironmentSequence In₁ In₂) :
    (∀ n : Nat, ∃ m : Nat, n ≤ m ∧
        (arenaWord plans env m).graph = Graph.both) ∨
      ∃ N : Nat, ∀ n : Nat, N < n ->
        ∀ p : A.State × A.State,
          arenaFoldSeq plans env n ≠ Sum.inl p := by
  rcases env_both_recurrent_or_trapped env with h | ⟨N, hN⟩
  · exact Or.inl ((arenaWord_both_recurrent_iff plans env).2 h)
  · exact Or.inr ⟨N, arenaFoldSeq_trapped_tail plans env hN⟩

end DetParityAutomaton

end DistributedSynthesis
