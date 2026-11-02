/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmFiniteMemoryExtraction

/-!
# Hierarchical observation parity games

Two-process product strategies, their trajectory semantics, and their
relationship with the perfect-information parity arena. Distributed
realizability implies perfect-information winnability. When both observation
maps are injective, a winning memoryless product strategy exists.
-/

namespace DistributedSynthesis

/-- A **hierarchical two-observation parity game**: two cooperating processes observe `Obs1`/`Obs2`
with `obs2` **refining** `obs1` (`refines`: same finer observation ⇒ same coarser one -- the informed
side sees at least what the blind side sees).  A distributed strategy is a *product* of
two observation-based strategies (`Obs1 → Action1` and `Obs2 → Action2`); the environment resolves the
rest.  This is the arena for the hierarchical finite-memory extraction. -/
structure HierarchicalObservationParityGame where
  State : Type u
  Action1 : Type u
  Action2 : Type u
  Env : Type u
  Obs1 : Type v
  Obs2 : Type w
  [stateCountable : Countable State]
  [action1Countable : Countable Action1]
  [action2Countable : Countable Action2]
  [action1Inhabited : Inhabited Action1]
  [action2Inhabited : Inhabited Action2]
  [envInhabited : Inhabited Env]
  /-- The blind (less-informed) process's observation. -/
  obs1 : State -> Obs1
  /-- The informed (more-informed) process's observation. -/
  obs2 : State -> Obs2
  /-- **The refinement hierarchy**: the informed observation determines the blind one. -/
  refines : ∀ s t : State, obs2 s = obs2 t -> obs1 s = obs1 t
  next : State -> Action1 -> Action2 -> Env -> State
  priority : State -> Nat
  priority_finite : Set.Finite (Set.range priority)

namespace HierarchicalObservationParityGame

attribute [instance] stateCountable action1Countable action2Countable
  action1Inhabited action2Inhabited envInhabited

variable (H : HierarchicalObservationParityGame.{u, v, w})

/-- A **memoryless product distributed strategy**: process 1 acts on its own observation, process 2 on
its own -- exactly the shape of `summaryController o1 o2` (each output from its own summary). -/
abbrev ProductStrategy := (H.Obs1 -> H.Action1) × (H.Obs2 -> H.Action2)

/-- Positions of the embedded game: a coalition `State` (`Sum.inl`) or an environment position
carrying both committed actions (`Sum.inr`). -/
abbrev Pos := H.State ⊕ (H.State × H.Action1 × H.Action2)

/-- **The hierarchical game embedded into a `CountableParityGame`.**  The coalition (owned by `even`)
commits a *joint* action `(a1, a2)`; the environment (`odd`) picks a response; priority is the state's.
The proved positional determinacy applies to this arena; the observation-*product* constraint on
strategies is what the finite-memory reduction must handle. -/
def toGame : CountableParityGame.{u} where
  Position := H.Pos
  positionCountable := inferInstance
  owner := Sum.elim (fun _ => ParityPlayer.even) fun _ => ParityPlayer.odd
  step p q :=
    match p, q with
    | Sum.inl s, Sum.inr saa => saa.1 = s
    | Sum.inr saa, Sum.inl s' => ∃ e : H.Env, s' = H.next saa.1 saa.2.1 saa.2.2 e
    | _, _ => False
  step_total p := by
    cases p with
    | inl s => exact ⟨Sum.inr (s, default, default), rfl⟩
    | inr saa => exact ⟨Sum.inl (H.next saa.1 saa.2.1 saa.2.2 default), default, rfl⟩
  priority := Sum.elim H.priority fun saa => H.priority saa.1
  priority_finite := by
    apply H.priority_finite.subset
    rintro _ ⟨p, rfl⟩
    cases p with
    | inl s => exact ⟨s, rfl⟩
    | inr saa => exact ⟨saa.1, rfl⟩

/-- The positional strategy on the hierarchical arena induced by a memoryless product strategy: at a
coalition state `s` it commits the joint action `(p.1 (obs1 s), p.2 (obs2 s))` -- process 1 acting on its
own observation, process 2 on its own.  Each component reads only its own observation. -/
def productPositional (p : H.ProductStrategy) :
    H.toGame.PositionalStrategy ParityPlayer.even where
  move pos :=
    match pos with
    | Sum.inl s => Sum.inr (s, p.1 (H.obs1 s), p.2 (H.obs2 s))
    | Sum.inr saa => Sum.inl (H.next saa.1 saa.2.1 saa.2.2 default)
  legal pos hp := by
    cases pos with
    | inl s => exact rfl
    | inr saa => exact absurd hp (by simp [toGame])

/-- A memoryless product strategy **wins** from a start state when its induced positional strategy wins
the hierarchical arena from the coalition position. -/
def ProductWins (p : H.ProductStrategy) (start : H.State) : Prop :=
  CountableParityGame.PositionalStrategy.WinningFrom (G := H.toGame)
    (H.productPositional p) (Sum.inl start)

/-!
## History-dependent product strategies

Each process reads its own observation history. A memoryless product strategy
is the special case that reads only the current observation. Both use the
same min-even parity objective.
-/

/-- A **history-dependent product distributed strategy**: process `i` chooses its action from the
history of its OWN observations (`List Obsᵢ`), never the global state.  This is the general
observation-based coalition strategy; the memoryless `ProductStrategy` is the special case reading only
the last observation. -/
abbrev HistProductStrategy := (List H.Obs1 -> H.Action1) × (List H.Obs2 -> H.Action2)

/-- The state paired with both accumulated observation histories after `n` steps, under a
history-dependent product strategy and an environment sequence.  Histories are built forward and
include the current state's observation, so at step `n` process `i` reads
`[obsᵢ(traj 0), …, obsᵢ(traj n)]`. -/
def histState (q : H.HistProductStrategy) (start : H.State) (env : Nat -> H.Env) :
    Nat -> H.State × List H.Obs1 × List H.Obs2
  | 0 => (start, [H.obs1 start], [H.obs2 start])
  | n + 1 =>
      let prev : H.State × List H.Obs1 × List H.Obs2 := histState q start env n
      let s' := H.next prev.1 (q.1 prev.2.1) (q.2 prev.2.2) (env n)
      (s', prev.2.1 ++ [H.obs1 s'], prev.2.2 ++ [H.obs2 s'])

/-- The state trajectory induced by a history-dependent product strategy against an environment. -/
def histTraj (q : H.HistProductStrategy) (start : H.State) (env : Nat -> H.Env) (n : Nat) : H.State :=
  (H.histState q start env n).1

/-- A priority value is seen infinitely often along a priority sequence. -/
def SeqInfOften (f : Nat -> Nat) (p : Nat) : Prop := ∀ n : Nat, ∃ k : Nat, n ≤ k ∧ f k = p

/-- The min-even parity objective on a priority sequence: the least priority seen infinitely often is
even.  This is the trajectory-level image of the arena objective `MinPriorityEven`. -/
def SeqMinEven (f : Nat -> Nat) : Prop :=
  ∃ p : Nat, DetParityAutomaton.NatEven p ∧ SeqInfOften f p ∧
    ∀ q : Nat, SeqInfOften f q -> p ≤ q

/-- A history-dependent product strategy **wins** from `start` when, against every environment
sequence, the induced state trajectory satisfies min-even parity. -/
def HistProductWins (q : H.HistProductStrategy) (start : H.State) : Prop :=
  ∀ env : Nat -> H.Env, SeqMinEven (fun n => H.priority (H.histTraj q start env n))

/-- Read a memoryless product strategy as a history-dependent one that consults only the most recent
observation.  (Histories from `histState` are always nonempty, ending at the current state's
observation, so the `none` branch -- guarded by `default`, using that actions are inhabited -- never
fires on real plays.) -/
def memoToHist (p : H.ProductStrategy) : H.HistProductStrategy :=
  (fun h => match h.getLast? with | some o => p.1 o | none => default,
   fun h => match h.getLast? with | some o => p.2 o | none => default)

/-- The **positional trajectory** of a memoryless product strategy: at each step process `i` acts on
the current state's own observation, `p.i (obsᵢ sₙ)`.  This is the intended memoryless play. -/
def posTraj (p : H.ProductStrategy) (start : H.State) (env : Nat -> H.Env) : Nat -> H.State
  | 0 => start
  | n + 1 =>
      let s := posTraj p start env n
      H.next s (p.1 (H.obs1 s)) (p.2 (H.obs2 s)) (env n)

/-- Reading `memoToHist p`'s first component on a history ending at `o` returns `p.1 o`. -/
theorem memoToHist_fst_apply (p : H.ProductStrategy) {h : List H.Obs1} {o : H.Obs1}
    (hh : h.getLast? = some o) : (H.memoToHist p).1 h = p.1 o := by
  simp only [memoToHist, hh]

/-- Reading `memoToHist p`'s second component on a history ending at `o` returns `p.2 o`. -/
theorem memoToHist_snd_apply (p : H.ProductStrategy) {h : List H.Obs2} {o : H.Obs2}
    (hh : h.getLast? = some o) : (H.memoToHist p).2 h = p.2 o := by
  simp only [memoToHist, hh]

/-- The first component of `histState` is the trajectory (definitional). -/
theorem histState_fst (q : H.HistProductStrategy) (start : H.State) (env : Nat -> H.Env) (n : Nat) :
    (H.histState q start env n).1 = H.histTraj q start env n := rfl

/-- Step law for the accumulated first-observation history: it grows by the new state's own
observation. -/
theorem histState_succ_snd_fst (q : H.HistProductStrategy) (start : H.State) (env : Nat -> H.Env)
    (n : Nat) :
    (H.histState q start env (n + 1)).2.1 =
      (H.histState q start env n).2.1 ++ [H.obs1 (H.histTraj q start env (n + 1))] := rfl

/-- Step law for the accumulated second-observation history. -/
theorem histState_succ_snd_snd (q : H.HistProductStrategy) (start : H.State) (env : Nat -> H.Env)
    (n : Nat) :
    (H.histState q start env (n + 1)).2.2 =
      (H.histState q start env n).2.2 ++ [H.obs2 (H.histTraj q start env (n + 1))] := rfl

/-- **The memoryless collapse.**  Reading a memoryless product strategy history-freely (`memoToHist`)
reproduces exactly its positional trajectory, and the accumulated observation histories always end at the
current state's own observation.  So `memoToHist p` genuinely plays memorylessly: the history it carries
is inert, consulted only at its last entry.  This is the bridge the reduction's conclusion needs -- a
`memoToHist`-winner is a bona fide memoryless (positional-product) winner. -/
theorem histTraj_memoToHist_eq (p : H.ProductStrategy) (start : H.State) (env : Nat -> H.Env) :
    ∀ n : Nat,
      H.histTraj (H.memoToHist p) start env n = H.posTraj p start env n ∧
        (H.histState (H.memoToHist p) start env n).2.1.getLast? =
          some (H.obs1 (H.posTraj p start env n)) ∧
        (H.histState (H.memoToHist p) start env n).2.2.getLast? =
          some (H.obs2 (H.posTraj p start env n)) := by
  intro n
  induction n with
  | zero => exact ⟨rfl, rfl, rfl⟩
  | succ n ih =>
    obtain ⟨htraj, hlast1, hlast2⟩ := ih
    -- The action process `i` commits at step `n` reads its history's last entry, which is `obsᵢ sₙ`.
    have hact1 :
        (H.memoToHist p).1 (H.histState (H.memoToHist p) start env n).2.1 =
          p.1 (H.obs1 (H.posTraj p start env n)) :=
      H.memoToHist_fst_apply p hlast1
    have hact2 :
        (H.memoToHist p).2 (H.histState (H.memoToHist p) start env n).2.2 =
          p.2 (H.obs2 (H.posTraj p start env n)) :=
      H.memoToHist_snd_apply p hlast2
    have hnext :
        H.histTraj (H.memoToHist p) start env (n + 1) = H.posTraj p start env (n + 1) := by
      have hstep : H.histTraj (H.memoToHist p) start env (n + 1) =
          H.next (H.histTraj (H.memoToHist p) start env n)
            ((H.memoToHist p).1 (H.histState (H.memoToHist p) start env n).2.1)
            ((H.memoToHist p).2 (H.histState (H.memoToHist p) start env n).2.2) (env n) := rfl
      rw [hstep, hact1, hact2, htraj]
      rfl
    refine ⟨hnext, ?_, ?_⟩
    · rw [H.histState_succ_snd_fst (H.memoToHist p) start env n, List.getLast?_concat, hnext]
    · rw [H.histState_succ_snd_snd (H.memoToHist p) start env n, List.getLast?_concat, hnext]

/-- The memoryless-collapse in trajectory form: the induced state trajectory of `memoToHist p` is the
positional trajectory `posTraj p`. -/
theorem histTraj_memoToHist (p : H.ProductStrategy) (start : H.State) (env : Nat -> H.Env) (n : Nat) :
    H.histTraj (H.memoToHist p) start env n = H.posTraj p start env n :=
  (H.histTraj_memoToHist_eq p start env n).1

/--
A memoryless product strategy has the same winning condition in the
history-dependent and positional trajectory presentations.
-/
theorem histProductWins_memoToHist_iff (p : H.ProductStrategy) (start : H.State) :
    H.HistProductWins (H.memoToHist p) start ↔
      ∀ env : Nat -> H.Env, SeqMinEven (fun n => H.priority (H.posTraj p start env n)) := by
  have hfun : ∀ env : Nat -> H.Env,
      (fun n => H.priority (H.histTraj (H.memoToHist p) start env n)) =
        (fun n => H.priority (H.posTraj p start env n)) := by
    intro env; funext n; rw [H.histTraj_memoToHist]
  constructor
  · intro h env; rw [← hfun env]; exact h env
  · intro h env; rw [hfun env]; exact h env

/-!
## Relating trajectories and arena plays

The canonical interleaved arena play repeats each trajectory priority twice.
Its min-even parity condition therefore agrees with the trajectory objective.
-/

/-- The canonical interleaved `toGame` play induced by a positional product strategy and an environment:
coalition position `inl sₙ` at even time, environment position `inr (sₙ, a1ₙ, a2ₙ)` at odd time. -/
def canonPath (p : H.ProductStrategy) (start : H.State) (env : Nat -> H.Env) (k : Nat) :
    H.toGame.Position :=
  if k % 2 = 0 then Sum.inl (H.posTraj p start env (k / 2))
  else Sum.inr (H.posTraj p start env (k / 2),
    p.1 (H.obs1 (H.posTraj p start env (k / 2))), p.2 (H.obs2 (H.posTraj p start env (k / 2))))

theorem canonPath_two_mul (p : H.ProductStrategy) (start : H.State) (env : Nat -> H.Env) (n : Nat) :
    H.canonPath p start env (2 * n) = Sum.inl (H.posTraj p start env n) := by
  simp only [canonPath]
  rw [if_pos (by omega : 2 * n % 2 = 0), show 2 * n / 2 = n from by omega]

theorem canonPath_two_mul_add_one (p : H.ProductStrategy) (start : H.State) (env : Nat -> H.Env)
    (n : Nat) :
    H.canonPath p start env (2 * n + 1) =
      Sum.inr (H.posTraj p start env n,
        p.1 (H.obs1 (H.posTraj p start env n)), p.2 (H.obs2 (H.posTraj p start env n))) := by
  simp only [canonPath]
  rw [if_neg (by omega : ¬ (2 * n + 1) % 2 = 0), show (2 * n + 1) / 2 = n from by omega]

theorem priority_canonPath (p : H.ProductStrategy) (start : H.State) (env : Nat -> H.Env) (k : Nat) :
    H.toGame.priority (H.canonPath p start env k) = H.priority (H.posTraj p start env (k / 2)) := by
  rcases (by omega : k % 2 = 0 ∨ k % 2 = 1) with h | h
  · obtain ⟨n, rfl⟩ : ∃ n, k = 2 * n := ⟨k / 2, by omega⟩
    rw [canonPath_two_mul, show 2 * n / 2 = n from by omega]; rfl
  · obtain ⟨n, rfl⟩ : ∃ n, k = 2 * n + 1 := ⟨k / 2, by omega⟩
    rw [canonPath_two_mul_add_one, show (2 * n + 1) / 2 = n from by omega]; rfl

theorem canonPath_play (p : H.ProductStrategy) (start : H.State) (env : Nat -> H.Env) :
    H.toGame.Play (H.canonPath p start env) := by
  intro k
  rcases (by omega : k % 2 = 0 ∨ k % 2 = 1) with h | h
  · obtain ⟨n, rfl⟩ : ∃ n, k = 2 * n := ⟨k / 2, by omega⟩
    rw [canonPath_two_mul, canonPath_two_mul_add_one]
    exact rfl
  · obtain ⟨n, rfl⟩ : ∃ n, k = 2 * n + 1 := ⟨k / 2, by omega⟩
    rw [canonPath_two_mul_add_one, show 2 * n + 1 + 1 = 2 * (n + 1) from by omega, canonPath_two_mul]
    exact ⟨env n, rfl⟩

theorem canonPath_playFrom (p : H.ProductStrategy) (start : H.State) (env : Nat -> H.Env) :
    H.toGame.PlayFrom (Sum.inl start) (H.canonPath p start env) := by
  refine ⟨?_, H.canonPath_play p start env⟩
  rw [show (0 : Nat) = 2 * 0 from rfl, canonPath_two_mul]; rfl

theorem canonPath_consistent (p : H.ProductStrategy) (start : H.State) (env : Nat -> H.Env) :
    (H.productPositional p).Consistent (H.canonPath p start env) := by
  intro k howner
  rcases (by omega : k % 2 = 0 ∨ k % 2 = 1) with h | h
  · obtain ⟨n, rfl⟩ : ∃ n, k = 2 * n := ⟨k / 2, by omega⟩
    rw [canonPath_two_mul, canonPath_two_mul_add_one]
    rfl
  · obtain ⟨n, rfl⟩ : ∃ n, k = 2 * n + 1 := ⟨k / 2, by omega⟩
    rw [canonPath_two_mul_add_one] at howner
    exact absurd howner (by simp [toGame])

theorem prioritySeen_canonPath_iff (p : H.ProductStrategy) (start : H.State) (env : Nat -> H.Env)
    (q : Nat) :
    H.toGame.PrioritySeenInfinitelyOften (H.canonPath p start env) q ↔
      SeqInfOften (fun n => H.priority (H.posTraj p start env n)) q := by
  constructor
  · intro hseen n
    obtain ⟨k, hk, hkq⟩ := hseen (2 * n)
    refine ⟨k / 2, by omega, ?_⟩
    have hp := H.priority_canonPath p start env k
    rw [hp] at hkq
    exact hkq
  · intro hseen n
    obtain ⟨m, hm, hmq⟩ := hseen n
    refine ⟨2 * m, by omega, ?_⟩
    have hp := H.priority_canonPath p start env (2 * m)
    rw [show 2 * m / 2 = m from by omega] at hp
    rw [hp]
    exact hmq

theorem minPriorityEven_canonPath_iff (p : H.ProductStrategy) (start : H.State) (env : Nat -> H.Env) :
    H.toGame.MinPriorityEven (H.canonPath p start env) ↔
      SeqMinEven (fun n => H.priority (H.posTraj p start env n)) := by
  have h := fun q => H.prioritySeen_canonPath_iff p start env q
  simp only [CountableParityGame.MinPriorityEven, SeqMinEven]
  constructor
  · rintro ⟨pr, hev, hs, hmin⟩
    exact ⟨pr, hev, (h pr).mp hs, fun q hq => hmin q ((h q).mpr hq)⟩
  · rintro ⟨pr, hev, hs, hmin⟩
    exact ⟨pr, hev, (h pr).mpr hs, fun q hq => hmin q ((h q).mp hq)⟩

/--
A winning positional product strategy satisfies the trajectory objective
against every environment sequence.
-/
theorem productWins_imp_seqMinEven (p : H.ProductStrategy) (start : H.State)
    (hpw : H.ProductWins p start) :
    ∀ env : Nat -> H.Env, SeqMinEven (fun n => H.priority (H.posTraj p start env n)) := by
  intro env
  rw [← minPriorityEven_canonPath_iff]
  have hwin := hpw (H.canonPath p start env) (H.canonPath_playFrom p start env)
    (H.canonPath_consistent p start env)
  simpa [CountableParityGame.PlayerWinsPath] using hwin

/--
A product strategy winning the arena also wins in the history-dependent
trajectory presentation.
-/
theorem histProductWins_memoToHist_of_productWins (p : H.ProductStrategy) (start : H.State)
    (hpw : H.ProductWins p start) :
    H.HistProductWins (H.memoToHist p) start :=
  (H.histProductWins_memoToHist_iff p start).mpr (H.productWins_imp_seqMinEven p start hpw)

/-!
## Factorization with injective observations

When both observations are injective, each process can recover the state.
A positional joint strategy therefore factors into local strategies.
-/

/--
If both observations are injective, a winning positional strategy factors
into a winning product strategy. Each local strategy recovers the state
from its observation and selects its component of the joint action.
-/
theorem productWins_of_positionalWinner_of_injective
    (hinj1 : Function.Injective H.obs1) (hinj2 : Function.Injective H.obs2)
    (start : H.State) (τ : H.toGame.PositionalStrategy ParityPlayer.even)
    (hτ : CountableParityGame.PositionalStrategy.WinningFrom (G := H.toGame) τ (Sum.inl start)) :
    ∃ p : H.ProductStrategy, H.ProductWins p start := by
  haveI : Nonempty H.State := ⟨start⟩
  -- Every coalition move of `τ` commits `inr (s, a1 s, a2 s)` (legality forces the first slot to be `s`).
  have hmove : ∀ s : H.State, ∃ a1 : H.Action1, ∃ a2 : H.Action2,
      τ.move (Sum.inl s) = Sum.inr (s, a1, a2) := by
    intro s
    have hleg := τ.legal (Sum.inl s) rfl
    cases hm : τ.move (Sum.inl s) with
    | inl s' => rw [hm] at hleg; exact absurd hleg (by simp [toGame])
    | inr saa =>
      rw [hm] at hleg
      obtain ⟨s', a1, a2⟩ := saa
      have hs' : s' = s := by simpa [toGame] using hleg
      exact ⟨a1, a2, by rw [hs']⟩
  choose a1 a2 hmove' using hmove
  -- Route each action component through the invertible observation.
  set p : H.ProductStrategy :=
    (fun o => a1 (Function.invFun H.obs1 o), fun o => a2 (Function.invFun H.obs2 o)) with hp
  have hagree : ∀ s : H.State, (H.productPositional p).move (Sum.inl s) = τ.move (Sum.inl s) := by
    intro s
    show Sum.inr (s, p.1 (H.obs1 s), p.2 (H.obs2 s)) = τ.move (Sum.inl s)
    have e1 : Function.invFun H.obs1 (H.obs1 s) = s := Function.leftInverse_invFun hinj1 s
    have e2 : Function.invFun H.obs2 (H.obs2 s) = s := Function.leftInverse_invFun hinj2 s
    simp only [hp, e1, e2]
    exact (hmove' s).symm
  refine ⟨p, ?_⟩
  intro path hplay hcons
  apply hτ path hplay
  intro n howner
  obtain ⟨s, hs⟩ : ∃ s, path n = Sum.inl s := by
    cases hpn : path n with
    | inl s => exact ⟨s, rfl⟩
    | inr saa => rw [hpn] at howner; exact absurd howner (by simp [toGame])
  rw [hcons n howner, hs]
  exact hagree s

/-- The coalition wins the *perfect-information* arena from `start`. -/
def CoalitionWinnable (start : H.State) : Prop :=
  Sum.inl start ∈ H.toGame.WinningRegion ParityPlayer.even

/--
Distributed realizability implies that the coalition wins the
perfect-information arena.
-/
def RealizableImpWinnable : Prop :=
  ∀ start : H.State,
    (∃ q : H.HistProductStrategy, H.HistProductWins q start) -> H.CoalitionWinnable start

/--
Every winning coalition position admits a winning product strategy.
The theorem below establishes this property for injective observations.
-/
def PositionalWinnerFactors : Prop :=
  ∀ start : H.State, H.CoalitionWinnable start -> ∃ p : H.ProductStrategy, H.ProductWins p start

/--
With injective observations, positional determinacy and factorization
produce a winning product strategy from every winning coalition position.
-/
theorem positionalWinnerFactors_of_injective
    (hinj1 : Function.Injective H.obs1) (hinj2 : Function.Injective H.obs2) :
    H.PositionalWinnerFactors := by
  intro start hwin
  obtain ⟨τ, hτ⟩ := H.toGame.uniformPositionalDeterminacy ParityPlayer.even
  exact H.productWins_of_positionalWinner_of_injective hinj1 hinj2 start τ (hτ _ hwin)

/-!
## Distributed strategies induce perfect-information strategies
-/

open Classical in
/-- The state carried by a `toGame` position: a coalition position `inl s` carries `s`, an environment
position `inr (s, _, _)` carries `s`. -/
def posState : H.Pos -> H.State := Sum.elim id fun saa => saa.1

@[simp] theorem posState_inl (s : H.State) : H.posState (Sum.inl s) = s := rfl

@[simp] theorem posState_inr (saa : H.State × H.Action1 × H.Action2) :
    H.posState (Sum.inr saa) = saa.1 := rfl

/-- The state paired with both observation histories after `n` steps of playing the distributed strategy
`q` against odd's positional strategy `ρ`: at each step the coalition commits `q`'s action and `ρ` picks
the environment response.  Mirrors `histState` with `next … (env n)` replaced by advancing via `ρ`. -/
def qRhoState (q : H.HistProductStrategy) (ρ : H.toGame.PositionalStrategy ParityPlayer.odd)
    (start : H.State) : Nat -> H.State × List H.Obs1 × List H.Obs2
  | 0 => (start, [H.obs1 start], [H.obs2 start])
  | n + 1 =>
      let prev : H.State × List H.Obs1 × List H.Obs2 := qRhoState q ρ start n
      let s' : H.State :=
        H.posState (ρ.move (Sum.inr (prev.1, q.1 prev.2.1, q.2 prev.2.2)))
      (s', prev.2.1 ++ [H.obs1 s'], prev.2.2 ++ [H.obs2 s'])

theorem qRhoState_succ_fst (q : H.HistProductStrategy)
    (ρ : H.toGame.PositionalStrategy ParityPlayer.odd) (start : H.State) (n : Nat) :
    (H.qRhoState q ρ start (n + 1)).1 =
      H.posState (ρ.move (Sum.inr ((H.qRhoState q ρ start n).1,
        q.1 (H.qRhoState q ρ start n).2.1, q.2 (H.qRhoState q ρ start n).2.2))) := rfl

theorem qRhoState_succ_snd_fst (q : H.HistProductStrategy)
    (ρ : H.toGame.PositionalStrategy ParityPlayer.odd) (start : H.State) (n : Nat) :
    (H.qRhoState q ρ start (n + 1)).2.1 =
      (H.qRhoState q ρ start n).2.1 ++ [H.obs1 (H.qRhoState q ρ start (n + 1)).1] := rfl

theorem qRhoState_succ_snd_snd (q : H.HistProductStrategy)
    (ρ : H.toGame.PositionalStrategy ParityPlayer.odd) (start : H.State) (n : Nat) :
    (H.qRhoState q ρ start (n + 1)).2.2 =
      (H.qRhoState q ρ start n).2.2 ++ [H.obs2 (H.qRhoState q ρ start (n + 1)).1] := rfl

/-- `ρ`'s response to the coalition's committed move is the next coalition position (legality forces `ρ`
to move from an odd-owned environment position to a coalition position). -/
theorem qRho_move_inl (q : H.HistProductStrategy)
    (ρ : H.toGame.PositionalStrategy ParityPlayer.odd) (start : H.State) (n : Nat) :
    ρ.move (Sum.inr ((H.qRhoState q ρ start n).1,
        q.1 (H.qRhoState q ρ start n).2.1, q.2 (H.qRhoState q ρ start n).2.2)) =
      Sum.inl (H.qRhoState q ρ start (n + 1)).1 := by
  have hfst := H.qRhoState_succ_fst q ρ start n
  have hleg := ρ.legal (Sum.inr ((H.qRhoState q ρ start n).1,
    q.1 (H.qRhoState q ρ start n).2.1, q.2 (H.qRhoState q ρ start n).2.2)) rfl
  cases hm : ρ.move (Sum.inr ((H.qRhoState q ρ start n).1,
      q.1 (H.qRhoState q ρ start n).2.1, q.2 (H.qRhoState q ρ start n).2.2)) with
  | inr saa' => rw [hm] at hleg; exact absurd hleg (by simp [toGame])
  | inl s' =>
    rw [hm] at hfst
    simp only [posState_inl] at hfst
    rw [hfst]

/-- The environment `ρ` induces at step `n`: some `e` with the next state equal to `next` under `q`'s
actions.  Extracted from the arena step underlying `ρ`'s legal move. -/
theorem qRho_exists_env (q : H.HistProductStrategy)
    (ρ : H.toGame.PositionalStrategy ParityPlayer.odd) (start : H.State) (n : Nat) :
    ∃ e : H.Env, (H.qRhoState q ρ start (n + 1)).1 =
      H.next (H.qRhoState q ρ start n).1
        (q.1 (H.qRhoState q ρ start n).2.1) (q.2 (H.qRhoState q ρ start n).2.2) e := by
  have hleg := ρ.legal (Sum.inr ((H.qRhoState q ρ start n).1,
    q.1 (H.qRhoState q ρ start n).2.1, q.2 (H.qRhoState q ρ start n).2.2)) rfl
  rw [H.qRho_move_inl q ρ start n] at hleg
  simpa [toGame] using hleg

/-- **The `q`-vs-`ρ` trajectory satisfies min-even parity.**  Playing `q` against `ρ` realizes some
environment sequence (extracted from `ρ`'s moves), so the trajectory *is* `histTraj q` for that
environment, and `HistProductWins q` applies. -/
theorem qRho_seqMinEven (q : H.HistProductStrategy)
    (ρ : H.toGame.PositionalStrategy ParityPlayer.odd) (start : H.State)
    (hq : H.HistProductWins q start) :
    SeqMinEven (fun n => H.priority (H.qRhoState q ρ start n).1) := by
  choose e he using H.qRho_exists_env q ρ start
  have hcoin : ∀ n, H.qRhoState q ρ start n = H.histState q start e n := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      have hs : (H.qRhoState q ρ start (n + 1)).1 = (H.histState q start e (n + 1)).1 := by
        rw [he n, ih]; rfl
      have h1 : (H.qRhoState q ρ start (n + 1)).2.1 = (H.histState q start e (n + 1)).2.1 := by
        rw [H.qRhoState_succ_snd_fst q ρ start n, ih, hs]; rfl
      have h2 : (H.qRhoState q ρ start (n + 1)).2.2 = (H.histState q start e (n + 1)).2.2 := by
        rw [H.qRhoState_succ_snd_snd q ρ start n, ih, hs]; rfl
      exact Prod.ext_iff.mpr ⟨hs, Prod.ext_iff.mpr ⟨h1, h2⟩⟩
  have hpri : (fun n => H.priority (H.qRhoState q ρ start n).1) =
      (fun n => H.priority (H.histTraj q start e n)) := by
    funext n
    show H.priority (H.qRhoState q ρ start n).1 = H.priority (H.histState q start e n).1
    rw [hcoin n]
  rw [hpri]
  exact hq e

/-- The interleaved `toGame` play of `q` against `ρ`. -/
def qRhoPath (q : H.HistProductStrategy) (ρ : H.toGame.PositionalStrategy ParityPlayer.odd)
    (start : H.State) (k : Nat) : H.toGame.Position :=
  if k % 2 = 0 then Sum.inl (H.qRhoState q ρ start (k / 2)).1
  else Sum.inr ((H.qRhoState q ρ start (k / 2)).1,
    q.1 (H.qRhoState q ρ start (k / 2)).2.1, q.2 (H.qRhoState q ρ start (k / 2)).2.2)

theorem qRhoPath_two_mul (q : H.HistProductStrategy)
    (ρ : H.toGame.PositionalStrategy ParityPlayer.odd) (start : H.State) (n : Nat) :
    H.qRhoPath q ρ start (2 * n) = Sum.inl (H.qRhoState q ρ start n).1 := by
  simp only [qRhoPath]
  rw [if_pos (by omega : 2 * n % 2 = 0), show 2 * n / 2 = n from by omega]

theorem qRhoPath_two_mul_add_one (q : H.HistProductStrategy)
    (ρ : H.toGame.PositionalStrategy ParityPlayer.odd) (start : H.State) (n : Nat) :
    H.qRhoPath q ρ start (2 * n + 1) =
      Sum.inr ((H.qRhoState q ρ start n).1,
        q.1 (H.qRhoState q ρ start n).2.1, q.2 (H.qRhoState q ρ start n).2.2) := by
  simp only [qRhoPath]
  rw [if_neg (by omega : ¬ (2 * n + 1) % 2 = 0), show (2 * n + 1) / 2 = n from by omega]

theorem priority_qRhoPath (q : H.HistProductStrategy)
    (ρ : H.toGame.PositionalStrategy ParityPlayer.odd) (start : H.State) (k : Nat) :
    H.toGame.priority (H.qRhoPath q ρ start k) = H.priority (H.qRhoState q ρ start (k / 2)).1 := by
  rcases (by omega : k % 2 = 0 ∨ k % 2 = 1) with h | h
  · obtain ⟨n, rfl⟩ : ∃ n, k = 2 * n := ⟨k / 2, by omega⟩
    rw [qRhoPath_two_mul, show 2 * n / 2 = n from by omega]; rfl
  · obtain ⟨n, rfl⟩ : ∃ n, k = 2 * n + 1 := ⟨k / 2, by omega⟩
    rw [qRhoPath_two_mul_add_one, show (2 * n + 1) / 2 = n from by omega]; rfl

theorem qRhoPath_play (q : H.HistProductStrategy)
    (ρ : H.toGame.PositionalStrategy ParityPlayer.odd) (start : H.State) :
    H.toGame.Play (H.qRhoPath q ρ start) := by
  intro k
  rcases (by omega : k % 2 = 0 ∨ k % 2 = 1) with h | h
  · obtain ⟨n, rfl⟩ : ∃ n, k = 2 * n := ⟨k / 2, by omega⟩
    rw [qRhoPath_two_mul, qRhoPath_two_mul_add_one]
    exact rfl
  · obtain ⟨n, rfl⟩ : ∃ n, k = 2 * n + 1 := ⟨k / 2, by omega⟩
    rw [qRhoPath_two_mul_add_one, show 2 * n + 1 + 1 = 2 * (n + 1) from by omega, qRhoPath_two_mul]
    exact H.qRho_exists_env q ρ start n

theorem qRhoPath_playFrom (q : H.HistProductStrategy)
    (ρ : H.toGame.PositionalStrategy ParityPlayer.odd) (start : H.State) :
    H.toGame.PlayFrom (Sum.inl start) (H.qRhoPath q ρ start) := by
  refine ⟨?_, H.qRhoPath_play q ρ start⟩
  rw [show (0 : Nat) = 2 * 0 from rfl, qRhoPath_two_mul]; rfl

theorem qRhoPath_consistent_odd (q : H.HistProductStrategy)
    (ρ : H.toGame.PositionalStrategy ParityPlayer.odd) (start : H.State) :
    ρ.Consistent (H.qRhoPath q ρ start) := by
  intro k howner
  rcases (by omega : k % 2 = 0 ∨ k % 2 = 1) with h | h
  · obtain ⟨n, rfl⟩ : ∃ n, k = 2 * n := ⟨k / 2, by omega⟩
    rw [qRhoPath_two_mul] at howner
    exact absurd howner (by simp [toGame])
  · obtain ⟨n, rfl⟩ : ∃ n, k = 2 * n + 1 := ⟨k / 2, by omega⟩
    rw [show 2 * n + 1 + 1 = 2 * (n + 1) from by omega, qRhoPath_two_mul, qRhoPath_two_mul_add_one]
    exact (H.qRho_move_inl q ρ start n).symm

theorem prioritySeen_qRhoPath_iff (q : H.HistProductStrategy)
    (ρ : H.toGame.PositionalStrategy ParityPlayer.odd) (start : H.State) (r : Nat) :
    H.toGame.PrioritySeenInfinitelyOften (H.qRhoPath q ρ start) r ↔
      SeqInfOften (fun n => H.priority (H.qRhoState q ρ start n).1) r := by
  constructor
  · intro hseen n
    obtain ⟨k, hk, hkr⟩ := hseen (2 * n)
    refine ⟨k / 2, by omega, ?_⟩
    have hp := H.priority_qRhoPath q ρ start k
    rw [hp] at hkr
    exact hkr
  · intro hseen n
    obtain ⟨m, hm, hmr⟩ := hseen n
    refine ⟨2 * m, by omega, ?_⟩
    have hp := H.priority_qRhoPath q ρ start (2 * m)
    rw [show 2 * m / 2 = m from by omega] at hp
    rw [hp]
    exact hmr

theorem minPriorityEven_qRhoPath_iff (q : H.HistProductStrategy)
    (ρ : H.toGame.PositionalStrategy ParityPlayer.odd) (start : H.State) :
    H.toGame.MinPriorityEven (H.qRhoPath q ρ start) ↔
      SeqMinEven (fun n => H.priority (H.qRhoState q ρ start n).1) := by
  have h := fun r => H.prioritySeen_qRhoPath_iff q ρ start r
  simp only [CountableParityGame.MinPriorityEven, SeqMinEven]
  constructor
  · rintro ⟨pr, hev, hs, hmin⟩
    exact ⟨pr, hev, (h pr).mp hs, fun r hr => hmin r ((h r).mpr hr)⟩
  · rintro ⟨pr, hev, hs, hmin⟩
    exact ⟨pr, hev, (h pr).mpr hs, fun r hr => hmin r ((h r).mp hr)⟩

/-- No path is won by both players: the least priority seen infinitely often cannot be both even and
odd. -/
theorem not_minPriorityEven_and_minPriorityOdd (path : Nat -> H.toGame.Position)
    (hE : H.toGame.MinPriorityEven path) (hO : H.toGame.MinPriorityOdd path) : False := by
  obtain ⟨p, hpe, hps, hpm⟩ := hE
  obtain ⟨p', hpo, hp's, hp'm⟩ := hO
  have hle1 : p ≤ p' := hpm p' hp's
  have hle2 : p' ≤ p := hp'm p hps
  have hpp : p = p' := le_antisymm hle1 hle2
  rw [hpp] at hpe
  exact hpo hpe

/--
A distributed winner induces a winner in the perfect-information arena.
Otherwise an odd positional winner would yield a consistent play satisfying
both min-even and min-odd parity.
-/
theorem realizableImpWinnable : H.RealizableImpWinnable := by
  intro start hex
  obtain ⟨q, hq⟩ := hex
  rcases H.toGame.positionalGameDetermined (Sum.inl start) with heven | hodd
  · exact H.toGame.positionalWinningRegion_subset_winningRegion ParityPlayer.even heven
  · exfalso
    obtain ⟨ρ, hρ⟩ := hodd
    have hEven : H.toGame.MinPriorityEven (H.qRhoPath q ρ start) :=
      (H.minPriorityEven_qRhoPath_iff q ρ start).mpr (H.qRho_seqMinEven q ρ start hq)
    have hOdd : H.toGame.MinPriorityOdd (H.qRhoPath q ρ start) := by
      have hwin := hρ (H.qRhoPath q ρ start) (H.qRhoPath_playFrom q ρ start)
        (H.qRhoPath_consistent_odd q ρ start)
      simpa [CountableParityGame.PlayerWinsPath] using hwin
    exact H.not_minPriorityEven_and_minPriorityOdd (H.qRhoPath q ρ start) hEven hOdd

/-- With injective observations, every winning history-dependent product strategy
has a winning memoryless product strategy. -/
theorem memorylessWinner_of_injective
    (hinj1 : Function.Injective H.obs1) (hinj2 : Function.Injective H.obs2)
    (start : H.State)
    (hwin : ∃ q : H.HistProductStrategy, H.HistProductWins q start) :
    ∃ p : H.ProductStrategy, H.HistProductWins (H.memoToHist p) start := by
  obtain ⟨p, hp⟩ := H.positionalWinnerFactors_of_injective hinj1 hinj2 start
    (H.realizableImpWinnable start hwin)
  exact ⟨p, H.histProductWins_memoToHist_of_productWins p start hp⟩

end HierarchicalObservationParityGame

end DistributedSynthesis
