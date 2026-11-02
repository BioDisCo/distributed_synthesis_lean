/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmCrossFreeEngine
import DistributedSynthesis.Formalizations.Theorem.ThmCrossFreeBeliefGame
import DistributedSynthesis.Formalizations.Theorem.ThmBundleDeterminization

/-!
# Static two-player hierarchical synthesis (Reif / Peterson--Reif)

This file states, as a clean **standalone and reusable** theorem, the fixed
two-player hierarchical synthesis result: in a finite concurrent game where one
player is at least as informed as the other after *every* history, distributed
synthesis is decidable and every realizable objective has finite Moore-controller
realizers.  This is the two-player case of the classical hierarchical-information
synthesis theorem (Reif, *The complexity of two-player games of incomplete
information*, JCSS 1984; Peterson--Reif, FOCS 1979), obtained by the knowledge
(belief) subset construction plus positional determinacy of the induced parity
game.

The interface is deliberately generic: `FiniteConcurrentGame`,
`OneDeterminesTwoAt`, and `FiniteStateSynthesisCertificate` carry no
project-specific machinery, so the theorem can be instantiated wherever a fixed
hierarchy arises.  In this development it is instantiated at the rank-permuted
shadow game (`commonSignalShadowGame`, whose fixed hierarchy is proved), which is
how the dynamic-hierarchy synthesis endpoint consumes it.

## Proof route (the classical construction, not invented here)

`StaticHierarchyFiniteStateSolvable` follows from two halves:

* **completeness** (`StaticHierarchyComplete`) -- a distributed winner yields a
  finite-state winner.  Classical route: fold the follower's strategy onto its
  own belief (the belief is a finite sufficient statistic under the hierarchy),
  reducing the leader to a single-player imperfect-information parity game solved
  by the belief subset construction and the tree's proved
  `positionalGameDetermined`; and
* **decidability** (`StaticHierarchyDecidable`) -- finite-state realizability is
  decidable, a finite search over belief-bounded follower controllers.

Both are assembled through the already-proved certificate glue
`finiteStateSynthesisCertificate_of_complete`.  The reusable determinacy input is
`ThmZielonkaCountableParity.positionalGameDetermined`; the two halves are the
remaining knowledge-construction content, whose exact interface this file fixes.
-/

namespace DistributedSynthesis

universe u

namespace FiniteConcurrentGame

variable (G : FiniteConcurrentGame.{u})

/-- The static hierarchy hypothesis: player one is at least as informed as player
two after every history, so leadership is fixed. -/
def StaticHierarchy : Prop :=
  ∀ history : G.PlayHistory, G.OneDeterminesTwoAt history

/-- **The static two-player synthesis theorem** (target).  Under a fixed
hierarchy, distributed synthesis is finite-state solvable: realizability is
decidable and every realizable objective has finite Moore-controller realizers.
This is the specialized two-player Peterson--Reif result the synthesis endpoint consumes
after crossing elimination and the shadow reduction. -/
def StaticHierarchyFiniteStateSolvable : Prop :=
  G.StaticHierarchy -> Nonempty G.FiniteStateSynthesisCertificate

/-- **Completeness half.**  Under a fixed hierarchy, a distributed winner yields a
finite-state winner.  This is the Peterson--Reif belief-sufficiency content: the
follower's strategy is belief-bounded and the leader's residual is a single
imperfect-information parity synthesis. -/
def StaticHierarchyComplete : Prop :=
  G.StaticHierarchy -> G.HistoryRealizable -> G.FiniteStateRealizable

/-- **Decidability half.**  Under a fixed hierarchy, finite-state realizability is
decidable: a finite search over belief-bounded follower controllers, each
followed by a single-player leader synthesis. -/
def StaticHierarchyDecidable : Prop :=
  G.StaticHierarchy -> Nonempty (Decidable G.FiniteStateRealizable)

/-- **The static theorem assembles from its two halves.**  Given completeness and
decidability under the fixed hierarchy, the finite-state synthesis certificate
follows through `finiteStateSynthesisCertificate_of_complete`. -/
theorem staticHierarchyFiniteStateSolvable_of_halves
    (hcomplete : G.StaticHierarchyComplete)
    (hdecidable : G.StaticHierarchyDecidable) :
    G.StaticHierarchyFiniteStateSolvable := by
  intro hstatic
  obtain ⟨hdec⟩ := hdecidable hstatic
  exact ⟨G.finiteStateSynthesisCertificate_of_complete (hcomplete hstatic) hdec⟩

/-! ### Reducing completeness to bundle acceptance

Through the finite-state readback `finiteStateRealizable_of_measurableBundleAccepts`,
the completeness half reduces to a single crisp obligation: under a fixed
hierarchy, a distributed winner yields belief-output functions whose measurable
strategy is bundle-accepted on every environment.  This is the genuine
Peterson--Reif sufficient-statistic content -- the follower's strategy folds onto
its belief without losing plays -- isolated from all the finite-memory plumbing. -/

/-- **The remaining Peterson--Reif core.**  Under a fixed hierarchy, a distributed
winner induces belief-output functions `f1`, `f2` whose measurable strategy the
unified bundle accepts on every environment.  The sufficient-statistic content:
the follower's strategy folds onto its own belief and every belief-consistent
thread still wins. -/
def StaticBundleAcceptance : Prop :=
  G.StaticHierarchy -> G.HistoryRealizable ->
    ∃ (f1 : G.Belief -> G.Action1) (f2 : G.Belief -> G.Action2),
      ∀ nature : Nat -> G.Nature, ∃ leaderSeq : Nat -> Bool,
        G.beliefBundleU.Accepts
          (G.beliefLetterWordU (G.measurableStrategy f1 f2) nature f1 f2 leaderSeq)

/-- **Completeness reduces to bundle acceptance.**  Given the sufficient-statistic
bundle acceptance, the completeness half follows through the finite-state
readback. -/
theorem staticHierarchyComplete_of_bundleAcceptance
    (h : G.StaticBundleAcceptance) : G.StaticHierarchyComplete := by
  intro hstatic hreal
  obtain ⟨f1, f2, hacc⟩ := h hstatic hreal
  exact G.finiteStateRealizable_of_measurableBundleAccepts f1 f2 hacc

/-! ### The knowledge set (belief subset construction)

The classical knowledge subset construction tracks, along a player's observation
history, the finite set of game states still consistent with those
observations, over *all* action profiles and Nature moves.  This is the finite
memory a Moore strategy carries, and the finite sufficient statistic that makes
the follower's strategy belief-measurable.  Here is player two's (the
follower's) knowledge; player one's is the mirror. -/

open Classical in
/-- One knowledge-set step for player two: the states reachable from the current
set under any action profile and Nature, keeping those matching the observed
letter. -/
noncomputable def knowledgeStep2 (K : Finset G.State) (o2 : G.Observation2) :
    Finset G.State :=
  Finset.univ.filter fun t =>
    (∃ s ∈ K, ∃ (a1 : G.Action1) (a2 : G.Action2) (env : G.Nature),
      G.next s a1 a2 env = t) ∧ G.observe2 t = o2

/-- Player two's knowledge along an observation history: the fold of the
knowledge step from the singleton initial set, ignoring the initial observation
(the initial state is common knowledge). -/
noncomputable def knowledge2 (obs : List G.Observation2) : Finset G.State :=
  obs.tail.foldl G.knowledgeStep2 {G.initial}

theorem mem_knowledgeStep2 (K : Finset G.State) (o2 : G.Observation2)
    (t : G.State) :
    t ∈ G.knowledgeStep2 K o2 ↔
      (∃ s ∈ K, ∃ (a1 : G.Action1) (a2 : G.Action2) (env : G.Nature),
        G.next s a1 a2 env = t) ∧ G.observe2 t = o2 := by
  simp [knowledgeStep2]

/-- The knowledge fold advances by one step along a play's growing view. -/
theorem knowledge2_succ (strategy : G.HistoryProductStrategy)
    (nature : Nat -> G.Nature) (n : Nat) :
    G.knowledge2 (G.strategyState strategy nature (n + 1)).2.2 =
      G.knowledgeStep2 (G.knowledge2 (G.strategyState strategy nature n).2.2)
        (G.observe2 (G.strategyState strategy nature (n + 1)).1) := by
  rw [knowledge2, knowledge2, view2_tail_succ, List.foldl_append,
    List.foldl_cons, List.foldl_nil]

/-- **Follower-knowledge membership.**  Along any play, the true current state is
in player two's knowledge set of its observation history.  This is the
consistency invariant of the belief subset construction (the follower's `I1`). -/
theorem mem_knowledge2 (strategy : G.HistoryProductStrategy)
    (nature : Nat -> G.Nature) (n : Nat) :
    (G.strategyState strategy nature n).1 ∈
      G.knowledge2 (G.strategyState strategy nature n).2.2 := by
  induction n with
  | zero => simp [knowledge2, strategyState]
  | succ n ih =>
      rw [knowledge2_succ, mem_knowledgeStep2]
      exact ⟨⟨(G.strategyState strategy nature n).1, ih,
        strategy.1 (G.strategyState strategy nature n).2.1,
        strategy.2 (G.strategyState strategy nature n).2.2, nature n, rfl⟩, rfl⟩

open Classical in
/-- One knowledge-set step for player one (the leader): the mirror of
`knowledgeStep2`. -/
noncomputable def knowledgeStep1 (K : Finset G.State) (o1 : G.Observation1) :
    Finset G.State :=
  Finset.univ.filter fun t =>
    (∃ s ∈ K, ∃ (a1 : G.Action1) (a2 : G.Action2) (env : G.Nature),
      G.next s a1 a2 env = t) ∧ G.observe1 t = o1

/-- Player one's knowledge along an observation history: the mirror of
`knowledge2`. -/
noncomputable def knowledge1 (obs : List G.Observation1) : Finset G.State :=
  obs.tail.foldl G.knowledgeStep1 {G.initial}

theorem mem_knowledgeStep1 (K : Finset G.State) (o1 : G.Observation1)
    (t : G.State) :
    t ∈ G.knowledgeStep1 K o1 ↔
      (∃ s ∈ K, ∃ (a1 : G.Action1) (a2 : G.Action2) (env : G.Nature),
        G.next s a1 a2 env = t) ∧ G.observe1 t = o1 := by
  simp [knowledgeStep1]

/-- The leader knowledge fold advances by one step along a play. -/
theorem knowledge1_succ (strategy : G.HistoryProductStrategy)
    (nature : Nat -> G.Nature) (n : Nat) :
    G.knowledge1 (G.strategyState strategy nature (n + 1)).2.1 =
      G.knowledgeStep1 (G.knowledge1 (G.strategyState strategy nature n).2.1)
        (G.observe1 (G.strategyState strategy nature (n + 1)).1) := by
  rw [knowledge1, knowledge1, view1_tail_succ, List.foldl_append,
    List.foldl_cons, List.foldl_nil]

/-- **Leader-knowledge membership**: the mirror of `mem_knowledge2`. -/
theorem mem_knowledge1 (strategy : G.HistoryProductStrategy)
    (nature : Nat -> G.Nature) (n : Nat) :
    (G.strategyState strategy nature n).1 ∈
      G.knowledge1 (G.strategyState strategy nature n).2.1 := by
  induction n with
  | zero => simp [knowledge1, strategyState]
  | succ n ih =>
      rw [knowledge1_succ, mem_knowledgeStep1]
      exact ⟨⟨(G.strategyState strategy nature n).1, ih,
        strategy.1 (G.strategyState strategy nature n).2.1,
        strategy.2 (G.strategyState strategy nature n).2.2, nature n, rfl⟩, rfl⟩

/-! ### The play-history bridge

The static-hierarchy hypothesis `OneDeterminesTwoAt` quantifies over
`PlayHistory`, whereas a running play is presented by `strategyState`.  The
bridge reifies a `(strategy, nature, n)` play as the legal history taking the
strategy's actions, so the hypothesis applies verbatim along any play.  This is
where the fixed-hierarchy assumption is consumed. -/

/-- The legal history generated by running `strategy` against `nature` for `n`
rounds, taking the strategy's own actions at each step. -/
def playHistory (strategy : G.HistoryProductStrategy) (nature : Nat -> G.Nature) :
    Nat -> G.PlayHistory
  | 0 => .initial
  | n + 1 =>
      (playHistory strategy nature n).step
        (strategy.1 (G.strategyState strategy nature n).2.1)
        (strategy.2 (G.strategyState strategy nature n).2.2) (nature n)

/-- The reified history ends at the play's current state. -/
theorem playHistory_lastState (strategy : G.HistoryProductStrategy)
    (nature : Nat -> G.Nature) (n : Nat) :
    (G.playHistory strategy nature n).lastState =
      (G.strategyState strategy nature n).1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [playHistory]
      show G.next (G.playHistory strategy nature n).lastState
          (strategy.1 (G.strategyState strategy nature n).2.1)
          (strategy.2 (G.strategyState strategy nature n).2.2) (nature n) =
        G.next (G.strategyState strategy nature n).1
          (strategy.1 (G.strategyState strategy nature n).2.1)
          (strategy.2 (G.strategyState strategy nature n).2.2) (nature n)
      rw [ih]

/-- The reified history reproduces player one's view. -/
theorem playHistory_observations1 (strategy : G.HistoryProductStrategy)
    (nature : Nat -> G.Nature) (n : Nat) :
    (G.playHistory strategy nature n).observations1 =
      (G.strategyState strategy nature n).2.1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [playHistory, PlayHistory.observations1_step, playHistory_lastState, ih]
      rfl

/-- The reified history reproduces player two's view. -/
theorem playHistory_observations2 (strategy : G.HistoryProductStrategy)
    (nature : Nat -> G.Nature) (n : Nat) :
    (G.playHistory strategy nature n).observations2 =
      (G.strategyState strategy nature n).2.2 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [playHistory, PlayHistory.observations2_step, playHistory_lastState, ih]
      rfl

/-! ### The hierarchy connection

The single place where the fixed-hierarchy hypothesis is consumed: along any two
plays, whenever the leader's views coincide the follower's views coincide too.
Equivalently the follower's view -- hence its knowledge set -- is a function of
the leader's view.  This is what lets the leader simulate the follower and
collapses the team synthesis to a single-player imperfect-information game. -/

/-- **Leader views determine follower views.**  Under a fixed hierarchy, two plays
with equal player-one views have equal player-two views.  This consumes
`StaticHierarchy` through the play-history bridge. -/
theorem view2_of_view1 (hstatic : G.StaticHierarchy)
    (strategy strategy' : G.HistoryProductStrategy)
    (nature nature' : Nat -> G.Nature) (n m : Nat)
    (h : (G.strategyState strategy nature n).2.1 =
      (G.strategyState strategy' nature' m).2.1) :
    (G.strategyState strategy nature n).2.2 =
      (G.strategyState strategy' nature' m).2.2 := by
  have hobs1 : (G.playHistory strategy nature n).observations1 =
      (G.playHistory strategy' nature' m).observations1 := by
    rw [playHistory_observations1, playHistory_observations1, h]
  have hobs2 := hstatic (G.playHistory strategy' nature' m)
    (G.playHistory strategy nature n) hobs1
  rwa [playHistory_observations2, playHistory_observations2] at hobs2

/-- **The follower's knowledge is leader-computable.**  Under a fixed hierarchy,
plays with equal leader views have equal follower knowledge sets.  This is the
finite sufficient statistic the leader tracks about the follower. -/
theorem knowledge2_of_view1 (hstatic : G.StaticHierarchy)
    (strategy strategy' : G.HistoryProductStrategy)
    (nature nature' : Nat -> G.Nature) (n m : Nat)
    (h : (G.strategyState strategy nature n).2.1 =
      (G.strategyState strategy' nature' m).2.1) :
    G.knowledge2 (G.strategyState strategy nature n).2.2 =
      G.knowledge2 (G.strategyState strategy' nature' m).2.2 := by
  rw [G.view2_of_view1 hstatic strategy strategy' nature nature' n m h]

/-! ### Knowledge sets are exactly the observation-consistent states

The leader-knowledge fold collects precisely the states reachable by *some* play
whose player-one observations match the given history.  Reifying such a play as a
`PlayHistory` lets the static hierarchy speak about every member of the knowledge
set -- in particular forcing all members to share the same follower observation,
which is what makes `o2` recoverable from the leader's own knowledge. -/

/-- **Knowledge membership yields a witnessing history.**  Every state in the
leader-knowledge fold over `l` is the last state of a legal history whose
player-one observations are `observe1 initial :: l`. -/
theorem exists_playHistory_of_mem_knowledgeFold1 (l : List G.Observation1) :
    ∀ t : G.State, t ∈ l.foldl G.knowledgeStep1 {G.initial} →
      ∃ H : G.PlayHistory,
        H.observations1 = G.observe1 G.initial :: l ∧ H.lastState = t := by
  induction l using List.reverseRecOn with
  | nil =>
      intro t ht
      rw [List.foldl_nil, Finset.mem_singleton] at ht
      subst ht
      exact ⟨.initial, rfl, rfl⟩
  | append_singleton l' o ih =>
      intro t ht
      rw [List.foldl_append, List.foldl_cons, List.foldl_nil,
        mem_knowledgeStep1] at ht
      obtain ⟨⟨s, hs, a1, a2, env, hnext⟩, hobs⟩ := ht
      obtain ⟨H, hH1, hHlast⟩ := ih s hs
      refine ⟨H.step a1 a2 env, ?_, ?_⟩
      · rw [PlayHistory.observations1_step, hH1, hHlast, hnext, hobs]
        simp
      · show G.next H.lastState a1 a2 env = t
        rw [hHlast, hnext]

/-- The last follower observation of a history is that of its last state. -/
theorem observations2_getLast? (H : G.PlayHistory) :
    H.observations2.getLast? = some (G.observe2 H.lastState) := by
  induction H with
  | initial => rfl
  | step H a1 a2 env _ =>
      rw [PlayHistory.observations2_step, List.getLast?_concat]
      rfl

/-- **Follower observation is constant on the leader's knowledge.**  Under a fixed
hierarchy, any two states consistent with the same player-one view share the same
follower observation, so `o2` is recoverable from the leader's knowledge set. -/
theorem observe2_const_on_knowledgeFold1 (hstatic : G.StaticHierarchy)
    (l : List G.Observation1) (t t' : G.State)
    (ht : t ∈ l.foldl G.knowledgeStep1 {G.initial})
    (ht' : t' ∈ l.foldl G.knowledgeStep1 {G.initial}) :
    G.observe2 t = G.observe2 t' := by
  obtain ⟨H, hH1, hHlast⟩ := G.exists_playHistory_of_mem_knowledgeFold1 l t ht
  obtain ⟨H', hH1', hHlast'⟩ := G.exists_playHistory_of_mem_knowledgeFold1 l t' ht'
  have hobs2 := hstatic H' H (by rw [hH1, hH1'])
  have hlast := congrArg List.getLast? hobs2
  rw [observations2_getLast?, observations2_getLast?, hHlast, hHlast'] at hlast
  exact (Option.some.inj hlast)

/-- Player one's view starts with the initial observation. -/
theorem view1_cons (strategy : G.HistoryProductStrategy)
    (nature : Nat -> G.Nature) (n : Nat) :
    ∃ rest : List G.Observation1,
      (G.strategyState strategy nature n).2.1 = G.observe1 G.initial :: rest := by
  induction n with
  | zero => exact ⟨[], rfl⟩
  | succ n ih =>
      obtain ⟨rest, hrest⟩ := ih
      refine ⟨rest ++ [G.observe1 (G.strategyState strategy nature (n + 1)).1], ?_⟩
      show (G.strategyState strategy nature n).2.1 ++
        [G.observe1 (G.strategyState strategy nature (n + 1)).1] = _
      rw [hrest]
      rfl

/-! ### The leader's determinized objective

Fix a follower table `f2 : Belief -> Action2`.  The leader's residual game is a
single-player imperfect-information parity game: the leader picks its action,
Nature reveals both observations, and *every* state consistent with the leader's
information must satisfy parity.  The belief subset construction determinizes
this conjunction-of-parities through the reusable
`FiniteThreadSystem.universalRunDPA` (guess-violation Buchi to checked Piterman).
Because Nature reveals the true observations -- the leader announces nothing --
there is no announcement laundering, and because the determinization state is a
function of the leader's own observations there is no measurability gap. -/

/-- The letter driving the leader's determinization: the leader action, the
current follower belief (leader-computable under the hierarchy), and both
observations (Nature-revealed). -/
abbrev LeaderLetter :=
  G.Action1 × G.Belief × G.Observation1 × G.Observation2

open Classical in
/-- The leader's thread system.  Threads are candidate current states (`none` is
a dead thread that fell off the observed letter); a thread steps by the leader
action and the belief-driven follower action `f2`, surviving only if it
reproduces both revealed observations.  Dead threads carry priority `0` (even),
so they are automatically excluded from the parity constraint. -/
noncomputable def leaderThreadSystem (f2 : G.Belief -> G.Action2) :
    FiniteThreadSystem.{u, u, u} G.LeaderLetter where
  State := Option G.State
  stateFinite := inferInstance
  initial := some G.initial
  Resolution := G.Nature
  step := fun st letter env =>
    match st with
    | none => none
    | some s =>
        let s' := G.next s letter.1 (f2 letter.2.1) env
        if G.observe1 s' = letter.2.2.1 ∧ G.observe2 s' = letter.2.2.2 then
          some s'
        else none
  priority := fun st =>
    match st with
    | none => 0
    | some s => G.priority s

/-- The determinized objective for the leader's residual game: a deterministic
parity automaton accepting exactly the letter words on which every consistent
run satisfies min-even parity. -/
noncomputable def leaderObjectiveDPA (f2 : G.Belief -> G.Action2) :
    DetParityAutomaton.{u, u} G.LeaderLetter :=
  (G.leaderThreadSystem f2).universalRunDPA

/-- **The leader objective is universally correct.**  It accepts a letter word
iff every consistent thread run has min-even parity -- the leader wins against
this letter sequence. -/
theorem leaderObjectiveDPA_accepts_iff (f2 : G.Belief -> G.Action2)
    (word : OmegaWord G.LeaderLetter) :
    (G.leaderObjectiveDPA f2).Accepts word ↔
      ∀ q : Nat -> (G.leaderThreadSystem f2).State,
        (G.leaderThreadSystem f2).IsRun word q ->
          NatSeqMinEvenParity (fun n => (G.leaderThreadSystem f2).priority (q n)) :=
  (G.leaderThreadSystem f2).universalRunDPA_accepts_iff word

/-! ### The leader's residual parity game

A turn-based two-player parity game (leader = Even, Nature = Odd) over the
determinized objective.  At a leader position the leader picks its action; at a
Nature position Nature reveals both observations, driving the objective DPA and
the follower belief forward.  The game priority is the objective DPA priority,
so a play is won by Even exactly when the induced letter word is accepted. -/

variable [Inhabited G.Action1] [Inhabited G.Observation1] [Inhabited G.Observation2]

/-- Positions of the leader's residual game.  Leader-owned (`inl`) positions
carry the objective state and follower belief; Nature-owned (`inr`) positions
additionally carry the chosen leader action, pending the revealed observations. -/
abbrev LeaderArenaPos (f2 : G.Belief -> G.Action2) :=
  ((G.leaderObjectiveDPA f2).State × G.Belief) ⊕
    ((G.leaderObjectiveDPA f2).State × G.Belief × G.Action1)

/-- The arena owner: the leader (Even) moves at `inl`, Nature (Odd) at `inr`. -/
def leaderArenaOwner (f2 : G.Belief -> G.Action2) :
    G.LeaderArenaPos f2 -> ParityPlayer
  | Sum.inl _ => ParityPlayer.even
  | Sum.inr _ => ParityPlayer.odd

/-- The arena edges: the leader chooses an action (holding the objective state
and belief), then Nature reveals both observations, stepping the objective DPA
by the assembled letter and advancing the follower belief. -/
def leaderArenaStep (f2 : G.Belief -> G.Action2) :
    G.LeaderArenaPos f2 -> G.LeaderArenaPos f2 -> Prop
  | Sum.inl (d, k2), Sum.inr (d', k2', _) => d' = d ∧ k2' = k2
  | Sum.inr (d, k2, a1), Sum.inl (d', k2') =>
      ∃ (o1 : G.Observation1) (o2 : G.Observation2),
        d' = (G.leaderObjectiveDPA f2).step d (a1, k2, o1, o2) ∧
          k2' = G.knowledgeStep2 k2 o2
  | _, _ => False

/-- The arena priority is the objective DPA priority of the carried state. -/
noncomputable def leaderArenaPriority (f2 : G.Belief -> G.Action2) :
    G.LeaderArenaPos f2 -> Nat
  | Sum.inl (d, _) => (G.leaderObjectiveDPA f2).priority d
  | Sum.inr (d, _, _) => (G.leaderObjectiveDPA f2).priority d

/-- The leader's residual parity game as a `CountableParityGame`. -/
noncomputable def leaderArena (f2 : G.Belief -> G.Action2) :
    CountableParityGame.{u} where
  Position := G.LeaderArenaPos f2
  positionCountable := inferInstance
  owner := G.leaderArenaOwner f2
  step := G.leaderArenaStep f2
  step_total := by
    rintro (⟨d, k2⟩ | ⟨d, k2, a1⟩)
    · exact ⟨Sum.inr (d, k2, default), rfl, rfl⟩
    · exact ⟨Sum.inl ((G.leaderObjectiveDPA f2).step d (a1, k2, default, default),
        G.knowledgeStep2 k2 default), default, default, rfl, rfl⟩
  priority := G.leaderArenaPriority f2
  priority_finite := Set.finite_range _

/-- The initial position of the leader's residual game: the objective's initial
state and the follower's initial belief `{initial}`. -/
noncomputable def leaderArenaInitial (f2 : G.Belief -> G.Action2) :
    (G.leaderArena f2).Position :=
  Sum.inl ((G.leaderObjectiveDPA f2).initial, G.beliefInitial)

/-- **The leader's residual game is positionally determined** -- the tree's
Zielonka determinacy (`positionalGameDetermined`) applied to the finite arena:
from the initial position either the leader (Even) has a positional winning
strategy or Nature (Odd) does. -/
theorem leaderArena_determined (f2 : G.Belief -> G.Action2) :
    G.leaderArenaInitial f2 ∈
        (G.leaderArena f2).PositionalWinningRegion ParityPlayer.even ∨
      G.leaderArenaInitial f2 ∈
        (G.leaderArena f2).PositionalWinningRegion ParityPlayer.odd :=
  (G.leaderArena f2).positionalGameDetermined _

/-! ### Readback: a leader positional winner yields finite controllers

The leader's finite memory is `(objective state, leader knowledge, follower
belief)`.  Reading only its own observation `o1`, it advances its knowledge by
`knowledgeStep1`, recovers the follower observation `o2` from the updated
knowledge (`predictObserve2`, correct under the hierarchy), and advances the
follower belief and objective state -- so its arena position is reconstructed
from `o1` alone.  The follower's memory is its belief, advanced by its own `o2`
and output through `f2`. -/

open Classical in
/-- The follower observation predicted from the leader's knowledge set: the
follower observation of any consistent state, well-defined under the hierarchy. -/
noncomputable def predictObserve2 (K : G.Belief) : G.Observation2 :=
  if h : K.Nonempty then G.observe2 h.choose else default

omit [Inhabited G.Action1] [Inhabited G.Observation1] in
/-- **Prediction is correct along real plays.**  Under a fixed hierarchy, the
follower observation predicted from the leader's knowledge equals the true
follower observation. -/
theorem predictObserve2_eq (hstatic : G.StaticHierarchy)
    (strategy : G.HistoryProductStrategy) (nature : Nat -> G.Nature) (n : Nat) :
    G.predictObserve2 (G.knowledge1 (G.strategyState strategy nature n).2.1) =
      G.observe2 (G.strategyState strategy nature n).1 := by
  have hmem : (G.strategyState strategy nature n).1 ∈
      G.knowledge1 (G.strategyState strategy nature n).2.1 :=
    G.mem_knowledge1 strategy nature n
  have hne : (G.knowledge1 (G.strategyState strategy nature n).2.1).Nonempty :=
    ⟨_, hmem⟩
  rw [predictObserve2, dif_pos hne]
  exact G.observe2_const_on_knowledgeFold1 hstatic _ _ _ hne.choose_spec hmem

open Classical in
/-- The leader action committed by a positional Even strategy at a leader
position. -/
noncomputable def leaderMove (f2 : G.Belief -> G.Action2)
    (τ : (G.leaderArena f2).PositionalStrategy ParityPlayer.even)
    (d : (G.leaderObjectiveDPA f2).State) (k2 : G.Belief) : G.Action1 :=
  match τ.move (Sum.inl (d, k2)) with
  | Sum.inr (_, _, a1) => a1
  | Sum.inl _ => default

/-- **The committed move has the expected shape.**  A positional Even strategy at
a leader position moves to the matching Nature position carrying its committed
action -- a consequence of arena legality. -/
theorem leaderArena_move_shape (f2 : G.Belief -> G.Action2)
    (τ : (G.leaderArena f2).PositionalStrategy ParityPlayer.even)
    (d : (G.leaderObjectiveDPA f2).State) (k2 : G.Belief) :
    τ.move (Sum.inl (d, k2)) = Sum.inr (d, k2, G.leaderMove f2 τ d k2) := by
  have hstep := τ.legal (Sum.inl (d, k2)) (by rfl)
  cases hmove : τ.move (Sum.inl (d, k2)) with
  | inr triple =>
      obtain ⟨d', k2', a1⟩ := triple
      rw [hmove] at hstep
      obtain ⟨hd, hk⟩ := hstep
      subst hd; subst hk
      rw [leaderMove, hmove]
  | inl pair =>
      rw [hmove] at hstep
      exact hstep.elim

/-- The follower's Moore controller: its memory is its belief, advanced by its
own observation through `knowledgeStep2`, output through `f2`.  The `Option`
wrapper drops the common-knowledge initial observation. -/
noncomputable def followerController (f2 : G.Belief -> G.Action2) :
    MooreController.{u, u, u} G.Observation2 G.Action2 where
  Memory := Option G.Belief
  memoryFinite := inferInstance
  initial := none
  update := fun m o2 =>
    match m with
    | none => some G.beliefInitial
    | some K => some (G.knowledgeStep2 K o2)
  output := fun m =>
    match m with
    | none => f2 G.beliefInitial
    | some K => f2 K

omit [Inhabited G.Action1] [Inhabited G.Observation1] [Inhabited G.Observation2] in
theorem followerController_foldl_some (f2 : G.Belief -> G.Action2)
    (K : G.Belief) (l : List G.Observation2) :
    l.foldl (G.followerController f2).update (some K) =
      some (l.foldl G.knowledgeStep2 K) := by
  induction l generalizing K with
  | nil => rfl
  | cons o l ih =>
      simp only [List.foldl_cons, followerController]
      exact ih _

omit [Inhabited G.Action1] [Inhabited G.Observation1] [Inhabited G.Observation2] in
/-- **The follower controller tracks its knowledge.**  On a nonempty view the
follower controller reaches the belief `knowledge2` of that view. -/
theorem followerController_run (f2 : G.Belief -> G.Action2)
    (o2 : G.Observation2) (tail : List G.Observation2) :
    (G.followerController f2).run (o2 :: tail) =
      some (G.knowledge2 (o2 :: tail)) := by
  rw [MooreController.run, knowledge2, List.tail_cons]
  show (tail.foldl (G.followerController f2).update)
    (some G.beliefInitial) = _
  exact G.followerController_foldl_some f2 G.beliefInitial tail

/-- The leader's memory triple `(objective state, leader knowledge, follower
belief)` advanced by one observation: it recovers the follower observation from
its updated knowledge, then steps the objective by its committed action and the
follower belief, and advances the follower belief. -/
noncomputable def leaderTripleStep (f2 : G.Belief -> G.Action2)
    (τ : (G.leaderArena f2).PositionalStrategy ParityPlayer.even)
    (m : (G.leaderObjectiveDPA f2).State × G.Belief × G.Belief)
    (o1 : G.Observation1) :
    (G.leaderObjectiveDPA f2).State × G.Belief × G.Belief :=
  ((G.leaderObjectiveDPA f2).step m.1
      (G.leaderMove f2 τ m.1 m.2.2, m.2.2, o1,
        G.predictObserve2 (G.knowledgeStep1 m.2.1 o1)),
    G.knowledgeStep1 m.2.1 o1,
    G.knowledgeStep2 m.2.2 (G.predictObserve2 (G.knowledgeStep1 m.2.1 o1)))

/-- The leader's initial memory triple. -/
noncomputable def leaderTripleInitial (f2 : G.Belief -> G.Action2) :
    (G.leaderObjectiveDPA f2).State × G.Belief × G.Belief :=
  ((G.leaderObjectiveDPA f2).initial, G.beliefInitial, G.beliefInitial)

/-- The leader's Moore controller: its memory is `(objective state, leader
knowledge, follower belief)`, advanced by its own observation alone, output the
committed action at the induced leader position. -/
noncomputable def leaderController (f2 : G.Belief -> G.Action2)
    (τ : (G.leaderArena f2).PositionalStrategy ParityPlayer.even) :
    MooreController.{u, u, u} G.Observation1 G.Action1 where
  Memory := Option ((G.leaderObjectiveDPA f2).State × G.Belief × G.Belief)
  memoryFinite := inferInstance
  initial := none
  update := fun m o1 =>
    match m with
    | none => some (G.leaderTripleInitial f2)
    | some triple => some (G.leaderTripleStep f2 τ triple o1)
  output := fun m =>
    match m with
    | none => default
    | some triple => G.leaderMove f2 τ triple.1 triple.2.2

theorem leaderController_foldl_some (f2 : G.Belief -> G.Action2)
    (τ : (G.leaderArena f2).PositionalStrategy ParityPlayer.even)
    (m : (G.leaderObjectiveDPA f2).State × G.Belief × G.Belief)
    (l : List G.Observation1) :
    l.foldl (G.leaderController f2 τ).update (some m) =
      some (l.foldl (G.leaderTripleStep f2 τ) m) := by
  induction l generalizing m with
  | nil => rfl
  | cons o l ih =>
      simp only [List.foldl_cons, leaderController]
      exact ih _

/-- **The leader controller tracks its memory triple.**  On a nonempty view the
leader controller reaches the triple folded from its initial memory. -/
theorem leaderController_run (f2 : G.Belief -> G.Action2)
    (τ : (G.leaderArena f2).PositionalStrategy ParityPlayer.even)
    (o1 : G.Observation1) (tail : List G.Observation1) :
    (G.leaderController f2 τ).run (o1 :: tail) =
      some (tail.foldl (G.leaderTripleStep f2 τ) (G.leaderTripleInitial f2)) := by
  rw [MooreController.run]
  show (tail.foldl (G.leaderController f2 τ).update)
    (some (G.leaderTripleInitial f2)) = _
  exact G.leaderController_foldl_some f2 τ (G.leaderTripleInitial f2) tail

/-- The leader-knowledge component of the memory fold is the plain
`knowledgeStep1` fold: it evolves independently of the objective and follower
belief. -/
theorem leaderTripleFold_fst (f2 : G.Belief -> G.Action2)
    (τ : (G.leaderArena f2).PositionalStrategy ParityPlayer.even)
    (m : (G.leaderObjectiveDPA f2).State × G.Belief × G.Belief)
    (l : List G.Observation1) :
    (l.foldl (G.leaderTripleStep f2 τ) m).2.1 = l.foldl G.knowledgeStep1 m.2.1 := by
  induction l generalizing m with
  | nil => rfl
  | cons o l ih =>
      rw [List.foldl_cons, List.foldl_cons]
      exact ih (G.leaderTripleStep f2 τ m o)

/-- **The leader tracks the follower belief.**  Along any play, the follower-belief
component of the leader's memory fold equals `knowledge2` of the follower view.
This consumes the fixed hierarchy through `predictObserve2_eq`: the leader's
recovered follower observation equals the true one, so its belief fold matches
the follower's. -/
theorem leaderTripleFold_snd (hstatic : G.StaticHierarchy)
    (f2 : G.Belief -> G.Action2)
    (τ : (G.leaderArena f2).PositionalStrategy ParityPlayer.even)
    (strat : G.HistoryProductStrategy) (nature : Nat -> G.Nature) (n : Nat) :
    ((G.strategyState strat nature n).2.1.tail.foldl (G.leaderTripleStep f2 τ)
        (G.leaderTripleInitial f2)).2.2 =
      G.knowledge2 (G.strategyState strat nature n).2.2 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [view1_tail_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      set m := (G.strategyState strat nature n).2.1.tail.foldl (G.leaderTripleStep f2 τ)
        (G.leaderTripleInitial f2) with hm
      have hfst : m.2.1 = G.knowledge1 (G.strategyState strat nature n).2.1 := by
        rw [hm, leaderTripleFold_fst]; rfl
      show G.knowledgeStep2 m.2.2
          (G.predictObserve2 (G.knowledgeStep1 m.2.1
            (G.observe1 (G.strategyState strat nature (n + 1)).1))) = _
      rw [ih, hfst, ← G.knowledge1_succ strat nature n,
        G.predictObserve2_eq hstatic strat nature (n + 1), G.knowledge2_succ]

/-! ### The induced play and its arena path -/

/-- The finite-controller product strategy read back from `τ` and `f2`. -/
noncomputable def readbackControllers (f2 : G.Belief -> G.Action2)
    (τ : (G.leaderArena f2).PositionalStrategy ParityPlayer.even) :
    G.FiniteStateProductStrategy where
  one := G.leaderController f2 τ
  two := G.followerController f2

/-- The leader memory triple reached along the induced play. -/
noncomputable def rbTriple (f2 : G.Belief -> G.Action2)
    (τ : (G.leaderArena f2).PositionalStrategy ParityPlayer.even)
    (nature : Nat -> G.Nature) (n : Nat) :
    (G.leaderObjectiveDPA f2).State × G.Belief × G.Belief :=
  (G.strategyState (G.readbackControllers f2 τ).toHistory nature n).2.1.tail.foldl
    (G.leaderTripleStep f2 τ) (G.leaderTripleInitial f2)

/-- The induced-play memory triple advances by one `leaderTripleStep`. -/
theorem rbTriple_succ (f2 : G.Belief -> G.Action2)
    (τ : (G.leaderArena f2).PositionalStrategy ParityPlayer.even)
    (nature : Nat -> G.Nature) (n : Nat) :
    G.rbTriple f2 τ nature (n + 1) =
      G.leaderTripleStep f2 τ (G.rbTriple f2 τ nature n)
        (G.observe1 (G.strategyState (G.readbackControllers f2 τ).toHistory
          nature (n + 1)).1) := by
  rw [rbTriple, rbTriple, view1_tail_succ, List.foldl_append, List.foldl_cons,
    List.foldl_nil]

/-- **The leader plays its committed action along the induced play.** -/
theorem readback_leader_action (f2 : G.Belief -> G.Action2)
    (τ : (G.leaderArena f2).PositionalStrategy ParityPlayer.even)
    (nature : Nat -> G.Nature) (n : Nat) :
    (G.readbackControllers f2 τ).toHistory.1
        (G.strategyState (G.readbackControllers f2 τ).toHistory nature n).2.1 =
      G.leaderMove f2 τ (G.rbTriple f2 τ nature n).1 (G.rbTriple f2 τ nature n).2.2 := by
  obtain ⟨rest, hrest⟩ :=
    G.view1_cons (G.readbackControllers f2 τ).toHistory nature n
  have htriple : G.rbTriple f2 τ nature n =
      rest.foldl (G.leaderTripleStep f2 τ) (G.leaderTripleInitial f2) := by
    rw [rbTriple, hrest]; rfl
  show (G.leaderController f2 τ).strategy
      (G.strategyState (G.readbackControllers f2 τ).toHistory nature n).2.1 = _
  rw [MooreController.strategy, hrest, leaderController_run, ← htriple]
  rfl

/-- **The follower plays `f2` of its belief along the induced play.** -/
theorem readback_follower_action (f2 : G.Belief -> G.Action2)
    (τ : (G.leaderArena f2).PositionalStrategy ParityPlayer.even)
    (nature : Nat -> G.Nature) (n : Nat) :
    (G.readbackControllers f2 τ).toHistory.2
        (G.strategyState (G.readbackControllers f2 τ).toHistory nature n).2.2 =
      f2 (G.knowledge2
        (G.strategyState (G.readbackControllers f2 τ).toHistory nature n).2.2) := by
  obtain ⟨a, l, hal⟩ := List.exists_cons_of_ne_nil
    (G.view2_ne_nil (G.readbackControllers f2 τ).toHistory nature n)
  show (G.followerController f2).strategy
      (G.strategyState (G.readbackControllers f2 τ).toHistory nature n).2.2 = _
  rw [MooreController.strategy, hal, followerController_run]
  rfl

/-- A min-even parity condition on a `2`-stutter transfers to the base sequence:
the two sequences see the same priorities infinitely often. -/
theorem natSeqMinEvenParity_of_stutter {a : Nat -> Nat}
    (h : NatSeqMinEvenParity (fun m => a (m / 2))) : NatSeqMinEvenParity a := by
  have hseen : ∀ p : Nat,
      NatSeqSeenInfinitelyOften (fun m => a (m / 2)) p ↔
        NatSeqSeenInfinitelyOften a p := by
    intro p
    constructor
    · intro hinf n
      obtain ⟨k, hk, hval⟩ := hinf (2 * n)
      exact ⟨k / 2, by omega, hval⟩
    · intro hinf n
      obtain ⟨k, hk, hval⟩ := hinf n
      exact ⟨2 * k, by omega, by
        show a (2 * k / 2) = p
        rw [Nat.mul_div_cancel_left k (by norm_num : 0 < 2)]; exact hval⟩
  obtain ⟨p, hpEven, hpSeen, hpMin⟩ := h
  exact ⟨p, hpEven, (hseen p).mp hpSeen, fun q hq => hpMin q ((hseen q).mpr hq)⟩

/-- The deterministic-objective letter word driving the induced play: at step `n`
the leader's committed action, the follower belief, the leader's next
observation, and the recovered follower observation. -/
noncomputable def rbWord (f2 : G.Belief -> G.Action2)
    (τ : (G.leaderArena f2).PositionalStrategy ParityPlayer.even)
    (nature : Nat -> G.Nature) : OmegaWord G.LeaderLetter := fun n =>
  (G.leaderMove f2 τ (G.rbTriple f2 τ nature n).1 (G.rbTriple f2 τ nature n).2.2,
    (G.rbTriple f2 τ nature n).2.2,
    G.observe1 (G.strategyState (G.readbackControllers f2 τ).toHistory nature (n + 1)).1,
    G.predictObserve2 (G.knowledgeStep1 (G.rbTriple f2 τ nature n).2.1
      (G.observe1 (G.strategyState (G.readbackControllers f2 τ).toHistory
        nature (n + 1)).1)))

/-- The objective state advances by the objective DPA on the letter word. -/
theorem rbTriple_fst_step (f2 : G.Belief -> G.Action2)
    (τ : (G.leaderArena f2).PositionalStrategy ParityPlayer.even)
    (nature : Nat -> G.Nature) (n : Nat) :
    (G.rbTriple f2 τ nature (n + 1)).1 =
      (G.leaderObjectiveDPA f2).step (G.rbTriple f2 τ nature n).1
        (G.rbWord f2 τ nature n) := by
  rw [rbTriple_succ]; rfl

/-- **The objective state along the play is the objective DPA run.** -/
theorem rbTriple_fst_eq_run (f2 : G.Belief -> G.Action2)
    (τ : (G.leaderArena f2).PositionalStrategy ParityPlayer.even)
    (nature : Nat -> G.Nature) (n : Nat) :
    (G.rbTriple f2 τ nature n).1 =
      (G.leaderObjectiveDPA f2).runFrom (G.leaderObjectiveDPA f2).initial
        (G.rbWord f2 τ nature) n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [rbTriple_fst_step, ih]; rfl

/-- The follower-belief component along the play is `knowledge2` of the follower
view (consumes the hierarchy). -/
theorem rbTriple_snd (hstatic : G.StaticHierarchy) (f2 : G.Belief -> G.Action2)
    (τ : (G.leaderArena f2).PositionalStrategy ParityPlayer.even)
    (nature : Nat -> G.Nature) (n : Nat) :
    (G.rbTriple f2 τ nature n).2.2 =
      G.knowledge2 (G.strategyState (G.readbackControllers f2 τ).toHistory nature n).2.2 :=
  G.leaderTripleFold_snd hstatic f2 τ (G.readbackControllers f2 τ).toHistory nature n

/-- The leader-knowledge component along the play is `knowledge1` of the leader
view. -/
theorem rbTriple_fst_knowledge (f2 : G.Belief -> G.Action2)
    (τ : (G.leaderArena f2).PositionalStrategy ParityPlayer.even)
    (nature : Nat -> G.Nature) (n : Nat) :
    (G.rbTriple f2 τ nature n).2.1 =
      G.knowledge1 (G.strategyState (G.readbackControllers f2 τ).toHistory nature n).2.1 := by
  simp only [rbTriple]
  rw [leaderTripleFold_fst]; rfl

/-- The real state successor along the induced play, expressed through the
letter word. -/
theorem rbState_succ (hstatic : G.StaticHierarchy) (f2 : G.Belief -> G.Action2)
    (τ : (G.leaderArena f2).PositionalStrategy ParityPlayer.even)
    (nature : Nat -> G.Nature) (n : Nat) :
    (G.strategyState (G.readbackControllers f2 τ).toHistory nature (n + 1)).1 =
      G.next (G.strategyState (G.readbackControllers f2 τ).toHistory nature n).1
        (G.rbWord f2 τ nature n).1 (f2 (G.rbWord f2 τ nature n).2.1) (nature n) := by
  show G.next (G.strategyState (G.readbackControllers f2 τ).toHistory nature n).1
      ((G.readbackControllers f2 τ).toHistory.1
        (G.strategyState (G.readbackControllers f2 τ).toHistory nature n).2.1)
      ((G.readbackControllers f2 τ).toHistory.2
        (G.strategyState (G.readbackControllers f2 τ).toHistory nature n).2.2)
      (nature n) = _
  rw [G.readback_leader_action f2 τ nature n, G.readback_follower_action f2 τ nature n,
    ← G.rbTriple_snd hstatic f2 τ nature n]
  rfl

/-- **The real play is a run of the leader thread system on the letter word.**
Consumes the hierarchy: the leader's recovered follower observation matches the
real one, so the true state survives every step. -/
theorem rbRealThread_isRun (hstatic : G.StaticHierarchy) (f2 : G.Belief -> G.Action2)
    (τ : (G.leaderArena f2).PositionalStrategy ParityPlayer.even)
    (nature : Nat -> G.Nature) :
    (G.leaderThreadSystem f2).IsRun (G.rbWord f2 τ nature)
      (fun n =>
        some (G.strategyState (G.readbackControllers f2 τ).toHistory nature n).1) := by
  classical
  refine ⟨rfl, fun n => ⟨nature n, ?_⟩⟩
  have ho2 :
      G.observe2 (G.strategyState (G.readbackControllers f2 τ).toHistory nature (n + 1)).1 =
        (G.rbWord f2 τ nature n).2.2.2 := by
    show G.observe2 _ = G.predictObserve2 (G.knowledgeStep1 (G.rbTriple f2 τ nature n).2.1
      (G.observe1 (G.strategyState (G.readbackControllers f2 τ).toHistory nature (n + 1)).1))
    rw [rbTriple_fst_knowledge,
      ← G.knowledge1_succ (G.readbackControllers f2 τ).toHistory nature n,
      G.predictObserve2_eq hstatic (G.readbackControllers f2 τ).toHistory nature (n + 1)]
  have hstep :
      (G.leaderThreadSystem f2).step
          (some (G.strategyState (G.readbackControllers f2 τ).toHistory nature n).1)
          (G.rbWord f2 τ nature n) (nature n) =
        some (G.strategyState (G.readbackControllers f2 τ).toHistory nature (n + 1)).1 := by
    show (if G.observe1 (G.next (G.strategyState (G.readbackControllers f2 τ).toHistory nature n).1
        (G.rbWord f2 τ nature n).1 (f2 (G.rbWord f2 τ nature n).2.1) (nature n)) =
          (G.rbWord f2 τ nature n).2.2.1 ∧
        G.observe2 (G.next (G.strategyState (G.readbackControllers f2 τ).toHistory nature n).1
          (G.rbWord f2 τ nature n).1 (f2 (G.rbWord f2 τ nature n).2.1) (nature n)) =
          (G.rbWord f2 τ nature n).2.2.2 then
          some (G.next (G.strategyState (G.readbackControllers f2 τ).toHistory nature n).1
            (G.rbWord f2 τ nature n).1 (f2 (G.rbWord f2 τ nature n).2.1) (nature n))
        else none) = _
    rw [← G.rbState_succ hstatic f2 τ nature n, if_pos ⟨rfl, ho2⟩]
  exact hstep.symm

/-- The follower belief advances by `knowledgeStep2` on the recovered
observation along the play. -/
theorem rbTriple_snd_step (f2 : G.Belief -> G.Action2)
    (τ : (G.leaderArena f2).PositionalStrategy ParityPlayer.even)
    (nature : Nat -> G.Nature) (n : Nat) :
    (G.rbTriple f2 τ nature (n + 1)).2.2 =
      G.knowledgeStep2 (G.rbTriple f2 τ nature n).2.2 (G.rbWord f2 τ nature n).2.2.2 := by
  rw [rbTriple_succ]; rfl

/-- The leader-owned arena position along the play. -/
noncomputable def rbLeaderPos (f2 : G.Belief -> G.Action2)
    (τ : (G.leaderArena f2).PositionalStrategy ParityPlayer.even)
    (nature : Nat -> G.Nature) (n : Nat) : (G.leaderArena f2).Position :=
  Sum.inl ((G.rbTriple f2 τ nature n).1, (G.rbTriple f2 τ nature n).2.2)

/-- The Nature-owned arena position along the play. -/
noncomputable def rbNaturePos (f2 : G.Belief -> G.Action2)
    (τ : (G.leaderArena f2).PositionalStrategy ParityPlayer.even)
    (nature : Nat -> G.Nature) (n : Nat) : (G.leaderArena f2).Position :=
  Sum.inr ((G.rbTriple f2 τ nature n).1, (G.rbTriple f2 τ nature n).2.2,
    G.leaderMove f2 τ (G.rbTriple f2 τ nature n).1 (G.rbTriple f2 τ nature n).2.2)

/-- The arena play induced by `τ` and `f2`: alternating leader and Nature
positions tracking the play's objective state and follower belief. -/
noncomputable def rbArenaPath (f2 : G.Belief -> G.Action2)
    (τ : (G.leaderArena f2).PositionalStrategy ParityPlayer.even)
    (nature : Nat -> G.Nature) (m : Nat) : (G.leaderArena f2).Position :=
  if m % 2 = 0 then G.rbLeaderPos f2 τ nature (m / 2)
  else G.rbNaturePos f2 τ nature (m / 2)

theorem rbArenaPath_even (f2 : G.Belief -> G.Action2)
    (τ : (G.leaderArena f2).PositionalStrategy ParityPlayer.even)
    (nature : Nat -> G.Nature) (n : Nat) :
    G.rbArenaPath f2 τ nature (2 * n) = G.rbLeaderPos f2 τ nature n := by
  rw [rbArenaPath, if_pos (by omega : 2 * n % 2 = 0), show 2 * n / 2 = n by omega]

theorem rbArenaPath_odd (f2 : G.Belief -> G.Action2)
    (τ : (G.leaderArena f2).PositionalStrategy ParityPlayer.even)
    (nature : Nat -> G.Nature) (n : Nat) :
    G.rbArenaPath f2 τ nature (2 * n + 1) = G.rbNaturePos f2 τ nature n := by
  rw [rbArenaPath, if_neg (by omega : ¬ (2 * n + 1) % 2 = 0),
    show (2 * n + 1) / 2 = n by omega]

theorem rbArenaPath_zero (f2 : G.Belief -> G.Action2)
    (τ : (G.leaderArena f2).PositionalStrategy ParityPlayer.even)
    (nature : Nat -> G.Nature) :
    G.rbArenaPath f2 τ nature 0 = G.leaderArenaInitial f2 := by
  show G.rbArenaPath f2 τ nature (2 * 0) = _
  rw [rbArenaPath_even]
  rfl

/-- The induced arena play follows the arena edges. -/
theorem rbArenaPath_play (f2 : G.Belief -> G.Action2)
    (τ : (G.leaderArena f2).PositionalStrategy ParityPlayer.even)
    (nature : Nat -> G.Nature) :
    (G.leaderArena f2).Play (G.rbArenaPath f2 τ nature) := by
  intro m
  obtain ⟨n, hn | hn⟩ := Nat.even_or_odd' m
  · subst hn
    rw [rbArenaPath_even, rbArenaPath_odd]
    exact ⟨rfl, rfl⟩
  · subst hn
    rw [rbArenaPath_odd, show 2 * n + 1 + 1 = 2 * (n + 1) by ring, rbArenaPath_even]
    exact ⟨(G.rbWord f2 τ nature n).2.2.1, (G.rbWord f2 τ nature n).2.2.2,
      G.rbTriple_fst_step f2 τ nature n, G.rbTriple_snd_step f2 τ nature n⟩

/-- The induced arena play is consistent with the positional strategy `τ`. -/
theorem rbArenaPath_consistent (f2 : G.Belief -> G.Action2)
    (τ : (G.leaderArena f2).PositionalStrategy ParityPlayer.even)
    (nature : Nat -> G.Nature) :
    τ.Consistent (G.rbArenaPath f2 τ nature) := by
  intro m howner
  obtain ⟨n, hn | hn⟩ := Nat.even_or_odd' m
  · subst hn
    rw [rbArenaPath_even, rbArenaPath_odd, rbLeaderPos, leaderArena_move_shape]
    rfl
  · subst hn
    rw [rbArenaPath_odd] at howner
    have hodd : (G.leaderArena f2).owner (G.rbNaturePos f2 τ nature n) =
        ParityPlayer.odd := rfl
    rw [hodd] at howner
    exact ParityPlayer.noConfusion howner

/-- The arena priority along the play is the objective priority of the DPA run,
stuttered by two. -/
theorem rbArenaPath_priority (f2 : G.Belief -> G.Action2)
    (τ : (G.leaderArena f2).PositionalStrategy ParityPlayer.even)
    (nature : Nat -> G.Nature) (m : Nat) :
    (G.leaderArena f2).priority (G.rbArenaPath f2 τ nature m) =
      (G.leaderObjectiveDPA f2).priority
        ((G.leaderObjectiveDPA f2).runFrom (G.leaderObjectiveDPA f2).initial
          (G.rbWord f2 τ nature) (m / 2)) := by
  obtain ⟨n, hn | hn⟩ := Nat.even_or_odd' m
  · subst hn
    rw [rbArenaPath_even, show 2 * n / 2 = n by omega]
    show (G.leaderObjectiveDPA f2).priority (G.rbTriple f2 τ nature n).1 = _
    rw [rbTriple_fst_eq_run]
  · subst hn
    rw [rbArenaPath_odd, show (2 * n + 1) / 2 = n by omega]
    show (G.leaderObjectiveDPA f2).priority (G.rbTriple f2 τ nature n).1 = _
    rw [rbTriple_fst_eq_run]

/-- **A leader winner's letter word is accepted by the objective.**  The arena
win transfers to the objective DPA through the stutter equivalence. -/
theorem rbWord_accepted (f2 : G.Belief -> G.Action2)
    (τ : (G.leaderArena f2).PositionalStrategy ParityPlayer.even)
    (nature : Nat -> G.Nature)
    (hτ : CountableParityGame.PositionalStrategy.WinningFrom (G := G.leaderArena f2) τ (G.leaderArenaInitial f2)) :
    (G.leaderObjectiveDPA f2).Accepts (G.rbWord f2 τ nature) := by
  have hwin : (G.leaderArena f2).MinPriorityEven (G.rbArenaPath f2 τ nature) :=
    hτ (G.rbArenaPath f2 τ nature)
      ⟨G.rbArenaPath_zero f2 τ nature, G.rbArenaPath_play f2 τ nature⟩
      (G.rbArenaPath_consistent f2 τ nature)
  have heq : (fun m => (G.leaderArena f2).priority (G.rbArenaPath f2 τ nature m)) =
      (fun m => (G.leaderObjectiveDPA f2).priority
        ((G.leaderObjectiveDPA f2).runFrom (G.leaderObjectiveDPA f2).initial
          (G.rbWord f2 τ nature) (m / 2))) :=
    funext (fun m => G.rbArenaPath_priority f2 τ nature m)
  have hstut : NatSeqMinEvenParity
      (fun m => (G.leaderObjectiveDPA f2).priority
        ((G.leaderObjectiveDPA f2).runFrom (G.leaderObjectiveDPA f2).initial
          (G.rbWord f2 τ nature) (m / 2))) := heq ▸ hwin
  exact natSeqMinEvenParity_of_stutter hstut

/-- **Soundness of the readback.**  A positional Even winner of the leader arena,
together with the follower table `f2`, yields winning finite Moore controllers. -/
theorem finiteStateRealizable_of_leaderArena_winner (hstatic : G.StaticHierarchy)
    (f2 : G.Belief -> G.Action2)
    (τ : (G.leaderArena f2).PositionalStrategy ParityPlayer.even)
    (hτ : CountableParityGame.PositionalStrategy.WinningFrom (G := G.leaderArena f2) τ (G.leaderArenaInitial f2)) :
    G.FiniteStateRealizable := by
  refine ⟨G.readbackControllers f2 τ, ?_⟩
  intro nature
  rw [parityAccepts_iff_natSeqMinEvenParity]
  have hacc := G.rbWord_accepted f2 τ nature hτ
  rw [leaderObjectiveDPA_accepts_iff] at hacc
  exact hacc
    (fun n => some (G.strategyState (G.readbackControllers f2 τ).toHistory nature n).1)
    (G.rbRealThread_isRun hstatic f2 τ nature)

/-! ### The leader-side completeness (R2): the arena is complete for the leader

The dual of soundness.  If the concrete game is realizable with the follower
hardwired to the belief table `f2`, then Even wins the leader arena.  This is the
knowledge/subset-construction completeness for the more-informed player: a
positional Nature arena winner would keep a live min-odd thread, but every
consistent thread is a play of the winning leader strategy against some
environment, hence min-even -- contradiction.  This reduces the arena-flavoured
completeness certificate to the concrete Reif-shaped statement (follower
belief-sufficiency). -/

/-- The follower's belief-table strategy: it plays `f2` of its own knowledge. -/
noncomputable def beliefFollower (f2 : G.Belief -> G.Action2) :
    List G.Observation2 -> G.Action2 :=
  fun view2 => f2 (G.knowledge2 view2)

/-- The concrete game is realizable with the follower hardwired to belief table
`f2`: some perfect-recall leader strategy wins against every environment. -/
def FollowerTableRealizable (f2 : G.Belief -> G.Action2) : Prop :=
  ∃ σ1 : List G.Observation1 -> G.Action1,
    G.HistoryStrategyWins (σ1, G.beliefFollower f2)

/-- Abbreviation for the shadow state: objective state, follower belief, and the
two accumulated views. -/
abbrev ShadowState (f2 : G.Belief -> G.Action2) :=
  (G.leaderObjectiveDPA f2).State × G.Belief × List G.Observation1 ×
    List G.Observation2

open Classical in
/-- The observation pair Nature's positional strategy `ν` reveals at the shadow
Nature position, extracted from its (legal) move. -/
noncomputable def shadowObs (f2 : G.Belief -> G.Action2)
    (σ1 : List G.Observation1 -> G.Action1)
    (ν : (G.leaderArena f2).PositionalStrategy ParityPlayer.odd)
    (m : G.ShadowState f2) : G.Observation1 × G.Observation2 :=
  if h : ∃ (o1 : G.Observation1) (o2 : G.Observation2),
      ν.move (Sum.inr (m.1, m.2.1, σ1 m.2.2.1)) =
        Sum.inl ((G.leaderObjectiveDPA f2).step m.1 (σ1 m.2.2.1, m.2.1, o1, o2),
          G.knowledgeStep2 m.2.1 o2) then
    (h.choose, h.choose_spec.choose)
  else (default, default)

/-- One shadow round: the leader plays `σ1` of its view, Nature reveals
`shadowObs`, advancing the objective state, the follower belief, and both
views. -/
noncomputable def shadowNext (f2 : G.Belief -> G.Action2)
    (σ1 : List G.Observation1 -> G.Action1)
    (ν : (G.leaderArena f2).PositionalStrategy ParityPlayer.odd)
    (m : G.ShadowState f2) : G.ShadowState f2 :=
  ((G.leaderObjectiveDPA f2).step m.1
      (σ1 m.2.2.1, m.2.1, (G.shadowObs f2 σ1 ν m).1, (G.shadowObs f2 σ1 ν m).2),
    G.knowledgeStep2 m.2.1 (G.shadowObs f2 σ1 ν m).2,
    m.2.2.1 ++ [(G.shadowObs f2 σ1 ν m).1],
    m.2.2.2 ++ [(G.shadowObs f2 σ1 ν m).2])

/-- The shadow state after `n` rounds. -/
noncomputable def shadowSt (f2 : G.Belief -> G.Action2)
    (σ1 : List G.Observation1 -> G.Action1)
    (ν : (G.leaderArena f2).PositionalStrategy ParityPlayer.odd) :
    Nat -> G.ShadowState f2
  | 0 => ((G.leaderObjectiveDPA f2).initial, G.beliefInitial,
      [G.observe1 G.initial], [G.observe2 G.initial])
  | n + 1 => G.shadowNext f2 σ1 ν (shadowSt f2 σ1 ν n)

/-- **Nature's move matches the shadow advance.**  At the shadow Nature position,
`ν`'s legal move is exactly the `inl` successor recorded by `shadowNext` -- so the
shadow play is `ν`-consistent, and `shadowObs` is a genuine witnessing observation
pair. -/
theorem shadowObs_move (f2 : G.Belief -> G.Action2)
    (σ1 : List G.Observation1 -> G.Action1)
    (ν : (G.leaderArena f2).PositionalStrategy ParityPlayer.odd)
    (m : G.ShadowState f2) :
    ν.move (Sum.inr (m.1, m.2.1, σ1 m.2.2.1)) =
      Sum.inl ((G.leaderObjectiveDPA f2).step m.1
          (σ1 m.2.2.1, m.2.1, (G.shadowObs f2 σ1 ν m).1, (G.shadowObs f2 σ1 ν m).2),
        G.knowledgeStep2 m.2.1 (G.shadowObs f2 σ1 ν m).2) := by
  classical
  have hlegal := ν.legal (Sum.inr (m.1, m.2.1, σ1 m.2.2.1)) rfl
  have hex : ∃ (o1 : G.Observation1) (o2 : G.Observation2),
      ν.move (Sum.inr (m.1, m.2.1, σ1 m.2.2.1)) =
        Sum.inl ((G.leaderObjectiveDPA f2).step m.1 (σ1 m.2.2.1, m.2.1, o1, o2),
          G.knowledgeStep2 m.2.1 o2) := by
    cases hmove : ν.move (Sum.inr (m.1, m.2.1, σ1 m.2.2.1)) with
    | inl p =>
        obtain ⟨d', k2'⟩ := p
        rw [hmove] at hlegal
        obtain ⟨o1, o2, hd, hk⟩ := hlegal
        exact ⟨o1, o2, by rw [hd, hk]⟩
    | inr p =>
        rw [hmove] at hlegal
        exact hlegal.elim
  simp only [shadowObs]
  split
  · rename_i h
    simpa using h.choose_spec.choose_spec
  · rename_i h
    exact absurd hex h

/-- The objective letter word driving the shadow play. -/
noncomputable def shadowWord (f2 : G.Belief -> G.Action2)
    (σ1 : List G.Observation1 -> G.Action1)
    (ν : (G.leaderArena f2).PositionalStrategy ParityPlayer.odd) :
    OmegaWord G.LeaderLetter := fun n =>
  (σ1 (G.shadowSt f2 σ1 ν n).2.2.1, (G.shadowSt f2 σ1 ν n).2.1,
    (G.shadowObs f2 σ1 ν (G.shadowSt f2 σ1 ν n)).1,
    (G.shadowObs f2 σ1 ν (G.shadowSt f2 σ1 ν n)).2)

/-- The shadow objective state advances by the objective DPA on the letter word. -/
theorem shadowSt_succ_fst (f2 : G.Belief -> G.Action2)
    (σ1 : List G.Observation1 -> G.Action1)
    (ν : (G.leaderArena f2).PositionalStrategy ParityPlayer.odd) (n : Nat) :
    (G.shadowSt f2 σ1 ν (n + 1)).1 =
      (G.leaderObjectiveDPA f2).step (G.shadowSt f2 σ1 ν n).1
        (G.shadowWord f2 σ1 ν n) := rfl

/-- The shadow objective state is the objective DPA run. -/
theorem shadowSt_fst_eq_run (f2 : G.Belief -> G.Action2)
    (σ1 : List G.Observation1 -> G.Action1)
    (ν : (G.leaderArena f2).PositionalStrategy ParityPlayer.odd) (n : Nat) :
    (G.shadowSt f2 σ1 ν n).1 =
      (G.leaderObjectiveDPA f2).runFrom (G.leaderObjectiveDPA f2).initial
        (G.shadowWord f2 σ1 ν) n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [shadowSt_succ_fst, ih]; rfl

/-- The shadow arena play: alternating leader and Nature positions tracking the
shadow objective state and follower belief. -/
noncomputable def shadowPath (f2 : G.Belief -> G.Action2)
    (σ1 : List G.Observation1 -> G.Action1)
    (ν : (G.leaderArena f2).PositionalStrategy ParityPlayer.odd) (m : Nat) :
    (G.leaderArena f2).Position :=
  if m % 2 = 0 then
    Sum.inl ((G.shadowSt f2 σ1 ν (m / 2)).1, (G.shadowSt f2 σ1 ν (m / 2)).2.1)
  else
    Sum.inr ((G.shadowSt f2 σ1 ν (m / 2)).1, (G.shadowSt f2 σ1 ν (m / 2)).2.1,
      σ1 (G.shadowSt f2 σ1 ν (m / 2)).2.2.1)

theorem shadowPath_even (f2 : G.Belief -> G.Action2)
    (σ1 : List G.Observation1 -> G.Action1)
    (ν : (G.leaderArena f2).PositionalStrategy ParityPlayer.odd) (n : Nat) :
    G.shadowPath f2 σ1 ν (2 * n) =
      Sum.inl ((G.shadowSt f2 σ1 ν n).1, (G.shadowSt f2 σ1 ν n).2.1) := by
  rw [shadowPath, if_pos (by omega : 2 * n % 2 = 0), show 2 * n / 2 = n by omega]

theorem shadowPath_odd (f2 : G.Belief -> G.Action2)
    (σ1 : List G.Observation1 -> G.Action1)
    (ν : (G.leaderArena f2).PositionalStrategy ParityPlayer.odd) (n : Nat) :
    G.shadowPath f2 σ1 ν (2 * n + 1) =
      Sum.inr ((G.shadowSt f2 σ1 ν n).1, (G.shadowSt f2 σ1 ν n).2.1,
        σ1 (G.shadowSt f2 σ1 ν n).2.2.1) := by
  rw [shadowPath, if_neg (by omega : ¬ (2 * n + 1) % 2 = 0),
    show (2 * n + 1) / 2 = n by omega]

theorem shadowPath_zero (f2 : G.Belief -> G.Action2)
    (σ1 : List G.Observation1 -> G.Action1)
    (ν : (G.leaderArena f2).PositionalStrategy ParityPlayer.odd) :
    G.shadowPath f2 σ1 ν 0 = G.leaderArenaInitial f2 := by
  show G.shadowPath f2 σ1 ν (2 * 0) = _
  rw [shadowPath_even]; rfl

theorem shadowPath_play (f2 : G.Belief -> G.Action2)
    (σ1 : List G.Observation1 -> G.Action1)
    (ν : (G.leaderArena f2).PositionalStrategy ParityPlayer.odd) :
    (G.leaderArena f2).Play (G.shadowPath f2 σ1 ν) := by
  intro m
  obtain ⟨n, hn | hn⟩ := Nat.even_or_odd' m
  · subst hn
    rw [shadowPath_even, shadowPath_odd]
    exact ⟨rfl, rfl⟩
  · subst hn
    rw [shadowPath_odd, show 2 * n + 1 + 1 = 2 * (n + 1) by ring, shadowPath_even]
    exact ⟨(G.shadowObs f2 σ1 ν (G.shadowSt f2 σ1 ν n)).1,
      (G.shadowObs f2 σ1 ν (G.shadowSt f2 σ1 ν n)).2, rfl, rfl⟩

theorem shadowPath_consistent (f2 : G.Belief -> G.Action2)
    (σ1 : List G.Observation1 -> G.Action1)
    (ν : (G.leaderArena f2).PositionalStrategy ParityPlayer.odd) :
    ν.Consistent (G.shadowPath f2 σ1 ν) := by
  intro m howner
  obtain ⟨n, hn | hn⟩ := Nat.even_or_odd' m
  · subst hn
    rw [shadowPath_even] at howner
    have heven : (G.leaderArena f2).owner
        (Sum.inl ((G.shadowSt f2 σ1 ν n).1, (G.shadowSt f2 σ1 ν n).2.1)) =
        ParityPlayer.even := rfl
    rw [heven] at howner
    exact ParityPlayer.noConfusion howner
  · subst hn
    rw [shadowPath_odd, show 2 * n + 1 + 1 = 2 * (n + 1) by ring, shadowPath_even]
    exact (G.shadowObs_move f2 σ1 ν (G.shadowSt f2 σ1 ν n)).symm

theorem shadowPath_priority (f2 : G.Belief -> G.Action2)
    (σ1 : List G.Observation1 -> G.Action1)
    (ν : (G.leaderArena f2).PositionalStrategy ParityPlayer.odd) (m : Nat) :
    (G.leaderArena f2).priority (G.shadowPath f2 σ1 ν m) =
      (G.leaderObjectiveDPA f2).priority
        ((G.leaderObjectiveDPA f2).runFrom (G.leaderObjectiveDPA f2).initial
          (G.shadowWord f2 σ1 ν) (m / 2)) := by
  obtain ⟨n, hn | hn⟩ := Nat.even_or_odd' m
  · subst hn
    rw [shadowPath_even, show 2 * n / 2 = n by omega]
    show (G.leaderObjectiveDPA f2).priority (G.shadowSt f2 σ1 ν n).1 = _
    rw [shadowSt_fst_eq_run]
  · subst hn
    rw [shadowPath_odd, show (2 * n + 1) / 2 = n by omega]
    show (G.leaderObjectiveDPA f2).priority (G.shadowSt f2 σ1 ν n).1 = _
    rw [shadowSt_fst_eq_run]

/-- **A Nature arena winner rejects the shadow word.**  If Nature wins the leader
arena, the shadow play is min-odd, so the objective DPA does not accept the
induced letter word. -/
theorem shadowWord_not_accepted (f2 : G.Belief -> G.Action2)
    (σ1 : List G.Observation1 -> G.Action1)
    (ν : (G.leaderArena f2).PositionalStrategy ParityPlayer.odd)
    (hν : CountableParityGame.PositionalStrategy.WinningFrom
      (G := G.leaderArena f2) ν (G.leaderArenaInitial f2)) :
    ¬ (G.leaderObjectiveDPA f2).Accepts (G.shadowWord f2 σ1 ν) := by
  have hodd : (G.leaderArena f2).MinPriorityOdd (G.shadowPath f2 σ1 ν) :=
    hν (G.shadowPath f2 σ1 ν)
      ⟨G.shadowPath_zero f2 σ1 ν, G.shadowPath_play f2 σ1 ν⟩
      (G.shadowPath_consistent f2 σ1 ν)
  have hrunodd : NatSeqMinOddParity
      (fun n => (G.leaderObjectiveDPA f2).priority
        ((G.leaderObjectiveDPA f2).runFrom (G.leaderObjectiveDPA f2).initial
          (G.shadowWord f2 σ1 ν) n)) :=
    (natSeqMinOddParity_halved (fun m => G.shadowPath_priority f2 σ1 ν m)).mp hodd
  intro hacc
  rw [DetParityAutomaton.accepts_iff_natSeqMinEvenParity] at hacc
  exact not_natSeqMinEvenParity_and_natSeqMinOddParity _ ⟨hacc, hrunodd⟩

omit [Inhabited G.Action1] [Inhabited G.Observation1] [Inhabited G.Observation2] in
/-- Follower knowledge over a nonempty view advances by one `knowledgeStep2`. -/
theorem knowledge2_append_singleton (l : List G.Observation2) (o : G.Observation2)
    (hl : l ≠ []) :
    G.knowledge2 (l ++ [o]) = G.knowledgeStep2 (G.knowledge2 l) o := by
  obtain ⟨a, l', rfl⟩ := List.exists_cons_of_ne_nil hl
  simp only [knowledge2, List.cons_append, List.tail_cons, List.foldl_append,
    List.foldl_cons, List.foldl_nil]

theorem shadowV2_ne_nil (f2 : G.Belief -> G.Action2)
    (σ1 : List G.Observation1 -> G.Action1)
    (ν : (G.leaderArena f2).PositionalStrategy ParityPlayer.odd) (n : Nat) :
    (G.shadowSt f2 σ1 ν n).2.2.2 ≠ [] := by
  induction n with
  | zero => simp [shadowSt]
  | succ n _ => show (G.shadowSt f2 σ1 ν n).2.2.2 ++ [_] ≠ []; simp

/-- The shadow follower belief is the follower knowledge of the shadow view. -/
theorem shadowSt_k2 (f2 : G.Belief -> G.Action2)
    (σ1 : List G.Observation1 -> G.Action1)
    (ν : (G.leaderArena f2).PositionalStrategy ParityPlayer.odd) (n : Nat) :
    (G.shadowSt f2 σ1 ν n).2.1 = G.knowledge2 (G.shadowSt f2 σ1 ν n).2.2.2 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      show G.knowledgeStep2 (G.shadowSt f2 σ1 ν n).2.1
          (G.shadowObs f2 σ1 ν (G.shadowSt f2 σ1 ν n)).2 =
        G.knowledge2 ((G.shadowSt f2 σ1 ν n).2.2.2 ++
          [(G.shadowObs f2 σ1 ν (G.shadowSt f2 σ1 ν n)).2])
      rw [G.knowledge2_append_singleton (G.shadowSt f2 σ1 ν n).2.2.2
        (G.shadowObs f2 σ1 ν (G.shadowSt f2 σ1 ν n)).2 (G.shadowV2_ne_nil f2 σ1 ν n),
        ← ih]

/-- **Every thread run of the shadow word is min-even.**  A run that dies has
priority `0` forever; a run that survives is exactly a play of the winning leader
`σ1` against the resolutions, hence min-even.  This is where `σ1` winning is
consumed. -/
theorem shadowThread_minEven (f2 : G.Belief -> G.Action2)
    (σ1 : List G.Observation1 -> G.Action1)
    (ν : (G.leaderArena f2).PositionalStrategy ParityPlayer.odd)
    (hσ1 : G.HistoryStrategyWins (σ1, G.beliefFollower f2))
    (q : Nat -> (G.leaderThreadSystem f2).State)
    (hq : (G.leaderThreadSystem f2).IsRun (G.shadowWord f2 σ1 ν) q) :
    NatSeqMinEvenParity
      (fun n => (G.leaderThreadSystem f2).priority (q n)) := by
  classical
  by_cases hlive : ∀ n, q n ≠ none
  · set nature' : Nat -> G.Nature := fun n => (hq.2 n).choose with hnat
    have hjoint : ∀ n,
        q n = some (G.strategyState (σ1, G.beliefFollower f2) nature' n).1 ∧
        (G.strategyState (σ1, G.beliefFollower f2) nature' n).2.1 =
          (G.shadowSt f2 σ1 ν n).2.2.1 ∧
        (G.strategyState (σ1, G.beliefFollower f2) nature' n).2.2 =
          (G.shadowSt f2 σ1 ν n).2.2.2 := by
      intro n
      induction n with
      | zero => exact ⟨hq.1, rfl, rfl⟩
      | succ n ih =>
          obtain ⟨hqn, hv1, hv2⟩ := ih
          have hrn : q (n + 1) = (G.leaderThreadSystem f2).step (q n)
              (G.shadowWord f2 σ1 ν n) (nature' n) := (hq.2 n).choose_spec
          have hnxeq : G.next (G.strategyState (σ1, G.beliefFollower f2) nature' n).1
                (G.shadowWord f2 σ1 ν n).1 (f2 (G.shadowWord f2 σ1 ν n).2.1) (nature' n) =
              (G.strategyState (σ1, G.beliefFollower f2) nature' (n + 1)).1 := by
            show _ = G.next (G.strategyState (σ1, G.beliefFollower f2) nature' n).1
                (σ1 (G.strategyState (σ1, G.beliefFollower f2) nature' n).2.1)
                (G.beliefFollower f2 (G.strategyState (σ1, G.beliefFollower f2) nature' n).2.2)
                (nature' n)
            simp only [shadowWord, beliefFollower]
            rw [hv1, hv2, shadowSt_k2]
          rw [hqn] at hrn
          have hcond :
              G.observe1 (G.strategyState (σ1, G.beliefFollower f2) nature' (n + 1)).1 =
                (G.shadowWord f2 σ1 ν n).2.2.1 ∧
              G.observe2 (G.strategyState (σ1, G.beliefFollower f2) nature' (n + 1)).1 =
                (G.shadowWord f2 σ1 ν n).2.2.2 := by
            by_contra hc
            apply hlive (n + 1)
            rw [hrn]
            show (if _ then _ else none) = none
            rw [hnxeq]
            exact if_neg hc
          have hqsucc : q (n + 1) =
              some (G.strategyState (σ1, G.beliefFollower f2) nature' (n + 1)).1 := by
            rw [hrn]
            show (if _ then some _ else none) = _
            rw [hnxeq, if_pos hcond]
          refine ⟨hqsucc, ?_, ?_⟩
          · show (G.strategyState (σ1, G.beliefFollower f2) nature' n).2.1 ++
                [G.observe1 (G.strategyState (σ1, G.beliefFollower f2) nature' (n + 1)).1] =
              (G.shadowSt f2 σ1 ν n).2.2.1 ++
                [(G.shadowObs f2 σ1 ν (G.shadowSt f2 σ1 ν n)).1]
            rw [hv1, hcond.1]; rfl
          · show (G.strategyState (σ1, G.beliefFollower f2) nature' n).2.2 ++
                [G.observe2 (G.strategyState (σ1, G.beliefFollower f2) nature' (n + 1)).1] =
              (G.shadowSt f2 σ1 ν n).2.2.2 ++
                [(G.shadowObs f2 σ1 ν (G.shadowSt f2 σ1 ν n)).2]
            rw [hv2, hcond.2]; rfl
    have hpri : (fun n => (G.leaderThreadSystem f2).priority (q n)) =
        (fun n => G.priority
          (G.strategyState (σ1, G.beliefFollower f2) nature' n).1) := by
      funext n; rw [(hjoint n).1]; rfl
    rw [hpri]
    have hwin := hσ1 nature'
    rwa [parityAccepts_iff_natSeqMinEvenParity] at hwin
  · push Not at hlive
    obtain ⟨N, hN⟩ := hlive
    have hnone : ∀ k, q (N + k) = none := by
      intro k
      induction k with
      | zero => simpa using hN
      | succ k ih =>
          obtain ⟨r, hr⟩ := hq.2 (N + k)
          rw [show N + (k + 1) = (N + k) + 1 by ring, hr, ih]
          rfl
    refine ⟨0, ⟨0, rfl⟩, ?_, ?_⟩
    · intro n
      refine ⟨N + n, by omega, ?_⟩
      show (G.leaderThreadSystem f2).priority (q (N + n)) = 0
      rw [hnone n]; rfl
    · intro q' _
      exact Nat.zero_le q'

/-- **R2: the arena is complete for the leader.**  If the concrete game is
realizable with the follower hardwired to belief table `f2`, then Even wins the
leader arena from the initial position.  A Nature arena winner would reject the
shadow word, but every thread run is min-even, so it accepts -- contradiction. -/
theorem evenWins_of_followerTableRealizable (f2 : G.Belief -> G.Action2)
    (h : G.FollowerTableRealizable f2) :
    G.leaderArenaInitial f2 ∈
      (G.leaderArena f2).PositionalWinningRegion ParityPlayer.even := by
  obtain ⟨σ1, hσ1⟩ := h
  rcases G.leaderArena_determined f2 with hev | hodd
  · exact hev
  · exfalso
    obtain ⟨ν, hν⟩ := hodd
    apply G.shadowWord_not_accepted f2 σ1 ν hν
    rw [leaderObjectiveDPA_accepts_iff]
    intro qq hqq
    exact G.shadowThread_minEven f2 σ1 ν hσ1 qq hqq

/-! ### Completeness: the classical Reif / Peterson--Reif belief-sufficiency

The one classical import of this development.  The soundness direction above
(`finiteStateRealizable_of_leaderArena_winner`), the determinacy of the arena
(`leaderArena_determined`), and the decidability below are all proved here.  The
completeness direction is *not* reproved: it is the belief-sufficiency theorem
for hierarchical games, that an arbitrary distributed winner can be replaced by
a belief-measurable one (a fixed follower table `f2 : Belief -> Action2`) against
which the more-informed leader still wins.  This is genuine mathematics, not
plumbing: an arbitrary `σ₂` is a function of the follower's full view, not of its
belief `K₂`, so no follower table is extractable from `σ₂` directly; that the
leader can compensate is the nested knowledge (subset) construction of Reif
(*The complexity of two-player games of incomplete information*, JCSS 1984) and
Peterson--Reif (*Multiple-person alternation*, FOCS 1979); for the single
imperfect-information player the completeness of knowledge-based strategies is
Chatterjee--Doyen--Henzinger--Raskin (*Algorithms for omega-regular games with
imperfect information*, 2007).  It corresponds to the paper's `prop:starcomplete`. -/

/-- **Reif / Peterson--Reif belief-completeness certificate** (classical; not
reproved here).  Under a fixed hierarchy, a distributed winner is dominated by a
belief-measurable follower table `f2` against which the leader (Even) wins the
induced knowledge parity game from the initial position. -/
def LeaderArenaComplete : Prop :=
  G.StaticHierarchy -> G.HistoryRealizable ->
    ∃ (f2 : G.Belief -> G.Action2)
      (τ : (G.leaderArena f2).PositionalStrategy ParityPlayer.even),
      CountableParityGame.PositionalStrategy.WinningFrom
        (G := G.leaderArena f2) τ (G.leaderArenaInitial f2)

/-- **Completeness from the classical certificate.**  Given Reif belief-
completeness, the completeness half follows through the proved soundness readback
`finiteStateRealizable_of_leaderArena_winner`. -/
theorem staticHierarchyComplete_of_leaderArenaComplete
    (h : G.LeaderArenaComplete) : G.StaticHierarchyComplete := by
  intro hstatic hreal
  obtain ⟨f2, τ, hτ⟩ := h hstatic hreal
  exact G.finiteStateRealizable_of_leaderArena_winner hstatic f2 τ hτ

/-- **The sharp Reif certificate (concrete form).**  Follower belief-sufficiency:
under a fixed hierarchy, an arbitrary distributed winner can be replaced by one
whose follower plays a belief table.  This is the development's concrete
Reif/Peterson--Reif-shaped projection interface -- no arena -- and, given R2, it is *equivalent* to
`LeaderArenaComplete`, so it is the minimal irreducible classical import. -/
def FollowerBeliefSufficiency : Prop :=
  G.StaticHierarchy -> G.HistoryRealizable ->
    ∃ f2 : G.Belief -> G.Action2, G.FollowerTableRealizable f2

/-- **The arena completeness certificate reduces to the concrete Reif statement.**
Through the proved leader-side completeness `evenWins_of_followerTableRealizable`
(R2), belief-sufficiency yields an arena winner.  Hence the whole static theorem
is conditional only on `FollowerBeliefSufficiency` (plus finite-parity-game
solvability). -/
theorem leaderArenaComplete_of_followerBeliefSufficiency
    (h : G.FollowerBeliefSufficiency) : G.LeaderArenaComplete := by
  intro hstatic hreal
  obtain ⟨f2, hf2⟩ := h hstatic hreal
  obtain ⟨τ, hτ⟩ := G.evenWins_of_followerTableRealizable f2 hf2
  exact ⟨f2, τ, hτ⟩

/-! ### Decidability and assembly

The soundness readback and the completeness certificate give
`FiniteStateRealizable ↔ ∃ f2, Even wins the (finite) leader arena` under a fixed
hierarchy.  The follower table `f2 : Belief -> Action2` ranges over a finite
type, so realizability is decidable *provided* the winner of each finite arena is
decidable -- the standard finite-parity-game solvability result (Emerson--Jutla
1991; Zielonka 1998), which the project treats as an interface elsewhere
(`FiniteDynamicHierarchyParityGame.winsDecidable`).  We take it as a small
cited certificate, far more elementary than the Reif completeness import. -/

/-- **Finite-parity-game solvability certificate** (standard; Emerson--Jutla,
Zielonka).  The Even winner of the finite leader arena is decidable from its
initial position, for every follower table. -/
abbrev LeaderArenaWinDecidable :=
  DecidablePred fun f2 : G.Belief -> G.Action2 =>
    G.leaderArenaInitial f2 ∈
      (G.leaderArena f2).PositionalWinningRegion ParityPlayer.even

/-- Under a fixed hierarchy and the completeness certificate, finite-state
realizability is exactly winnability of some finite leader arena. -/
theorem finiteStateRealizable_iff_leaderArenaWin (hstatic : G.StaticHierarchy)
    (hc : G.LeaderArenaComplete) :
    G.FiniteStateRealizable ↔
      ∃ f2 : G.Belief -> G.Action2,
        G.leaderArenaInitial f2 ∈
          (G.leaderArena f2).PositionalWinningRegion ParityPlayer.even := by
  constructor
  · intro hfin
    obtain ⟨f2, τ, hτ⟩ := hc hstatic (G.historyRealizable_of_finiteStateRealizable hfin)
    exact ⟨f2, τ, hτ⟩
  · rintro ⟨f2, τ, hτ⟩
    exact G.finiteStateRealizable_of_leaderArena_winner hstatic f2 τ hτ

/-- **Decidability half from the certificates.**  A finite search over follower
tables, each a finite-arena solve. -/
theorem staticHierarchyDecidable_of_certs (hc : G.LeaderArenaComplete)
    (hd : G.LeaderArenaWinDecidable) : G.StaticHierarchyDecidable := by
  classical
  intro hstatic
  haveI : DecidablePred (fun f2 : G.Belief -> G.Action2 =>
      G.leaderArenaInitial f2 ∈
        (G.leaderArena f2).PositionalWinningRegion ParityPlayer.even) := hd
  haveI : Decidable (∃ f2 : G.Belief -> G.Action2,
      G.leaderArenaInitial f2 ∈
        (G.leaderArena f2).PositionalWinningRegion ParityPlayer.even) :=
    Fintype.decidableExistsFintype
  exact ⟨decidable_of_iff _
    (G.finiteStateRealizable_iff_leaderArenaWin hstatic hc).symm⟩

/-- **The standalone static two-player synthesis theorem, assembled.**  Under a
fixed hierarchy, distributed synthesis is finite-state solvable, conditional on
the classical Reif completeness certificate and finite-parity-game solvability.
Everything else -- the belief construction, the arena, Zielonka determinacy, and
the full soundness readback -- is proved unconditionally above. -/
theorem staticHierarchyFiniteStateSolvable_of_certs (hc : G.LeaderArenaComplete)
    (hd : G.LeaderArenaWinDecidable) : G.StaticHierarchyFiniteStateSolvable :=
  G.staticHierarchyFiniteStateSolvable_of_halves
    (G.staticHierarchyComplete_of_leaderArenaComplete hc)
    (G.staticHierarchyDecidable_of_certs hc hd)

/-- **The standalone static two-player synthesis theorem, conditional on the two
minimal classical imports.**  Given follower belief-sufficiency (the exact Reif /
Peterson--Reif statement) and finite-parity-game solvability, distributed
synthesis over a fixed hierarchy is finite-state solvable.  Everything else --
the belief construction, the arena, Zielonka determinacy, the full soundness
readback, and the leader-side completeness (R2) -- is proved unconditionally. -/
theorem staticHierarchyFiniteStateSolvable_of_followerBeliefSufficiency
    (hc : G.FollowerBeliefSufficiency) (hd : G.LeaderArenaWinDecidable) :
    G.StaticHierarchyFiniteStateSolvable :=
  G.staticHierarchyFiniteStateSolvable_of_certs
    (G.leaderArenaComplete_of_followerBeliefSufficiency hc) hd

end FiniteConcurrentGame

end DistributedSynthesis
