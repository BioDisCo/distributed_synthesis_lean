/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmCommonSignalCrossingElimination
import DistributedSynthesis.Formalizations.Theorem.ThmStaticHierarchySynthesis

/-!
# Realizability transfer across common-signal crossing elimination

The common-signal arena (`commonSignalCrossingEliminationGame`) doubles each
base round into a lifted round and a bridge round; the bridge transition
ignores all choices, and the bridge letter is common to both players.  This
file proves the realizability transfer across that reduction:
`HistoryRealizable` of the base game and of the doubled game coincide (under
the dynamic hierarchy).

Soundness of the backward direction rests on the proved view congruences
(`commonSignalLift_observations1_congr`, `commonSignalLift_observations2_congr`):
along lifted plays the doubled views are *functions* of the base views, so the
doubled game gives neither player any information beyond its base view -- the
common bridge letter is exactly the part of the leader's data that the
hierarchy already makes view-determined.

The core is one play correspondence (`commonSignal_play_correspondence`):
whenever a base strategy and a doubled strategy agree along lifts, the doubled
play under any doubled Nature is round-for-round the lift of the base play
under the even-indexed base Nature, with priorities repeating by the offset
stutter `m ↦ (m + 1) / 2`.
-/

namespace DistributedSynthesis

universe u

/-- Offset-stutter transfer: the priority sequence `m ↦ s ((m + 1) / 2)`
repeats `s 0` once and every later entry twice, so it sees exactly the
priorities of `s` infinitely often. -/
theorem natSeqSeenInfinitelyOften_offset_stutter (s : Nat -> Nat) (p : Nat) :
    NatSeqSeenInfinitelyOften (fun m => s ((m + 1) / 2)) p ↔
      NatSeqSeenInfinitelyOften s p := by
  constructor
  · intro hseen n
    obtain ⟨k, hk, hval⟩ := hseen (2 * n)
    exact ⟨(k + 1) / 2, by omega, hval⟩
  · intro hseen n
    obtain ⟨k, hk, hval⟩ := hseen n
    refine ⟨2 * k, by omega, ?_⟩
    show s ((2 * k + 1) / 2) = p
    rw [show (2 * k + 1) / 2 = k by omega]
    exact hval

/-- Offset-stutter transfer for the min-even parity condition. -/
theorem natSeqMinEvenParity_offset_stutter (s : Nat -> Nat) :
    NatSeqMinEvenParity (fun m => s ((m + 1) / 2)) ↔ NatSeqMinEvenParity s := by
  constructor
  · rintro ⟨p, hpEven, hpSeen, hpMin⟩
    exact ⟨p, hpEven, (natSeqSeenInfinitelyOften_offset_stutter s p).mp hpSeen,
      fun q hq => hpMin q ((natSeqSeenInfinitelyOften_offset_stutter s q).mpr hq)⟩
  · rintro ⟨p, hpEven, hpSeen, hpMin⟩
    exact ⟨p, hpEven, (natSeqSeenInfinitelyOften_offset_stutter s p).mpr hpSeen,
      fun q hq => hpMin q ((natSeqSeenInfinitelyOften_offset_stutter s q).mp hq)⟩

namespace FiniteConcurrentGame

variable (G : FiniteConcurrentGame.{u})

attribute [instance] FiniteConcurrentGame.stateFinite
  FiniteConcurrentGame.action1Finite FiniteConcurrentGame.action2Finite
  FiniteConcurrentGame.natureFinite FiniteConcurrentGame.observation1Finite
  FiniteConcurrentGame.observation2Finite

/-- **The play correspondence, at the level of visited states.**  Whenever a
base strategy `σ` and a doubled strategy `τ` agree along lifts, the doubled
play under any doubled Nature visits, through time `2 n`, exactly the states of
the lifted base play under the even-indexed base Nature.  The histories
themselves differ (the bridge transition ignores `τ`'s bridge actions), but the
state lists -- hence all observations and priorities -- coincide. -/
theorem commonSignal_play_states
    (σ : G.HistoryProductStrategy)
    (τ : G.commonSignalCrossingEliminationGame.HistoryProductStrategy)
    (hagree1 : ∀ h : G.PlayHistory,
      τ.1 (G.commonSignalLift h).observations1 = σ.1 h.observations1)
    (hagree2 : ∀ h : G.PlayHistory,
      τ.2 (G.commonSignalLift h).observations2 = σ.2 h.observations2)
    (natD : Nat -> G.Nature) (n : Nat) :
    (G.commonSignalCrossingEliminationGame.playHistory τ natD (2 * n)).states =
        (G.commonSignalLift
          (G.playHistory σ (fun k => natD (2 * k)) n)).states ∧
      (G.commonSignalCrossingEliminationGame.playHistory τ natD
          (2 * n)).lastState =
        (G.commonSignalLift
          (G.playHistory σ (fun k => natD (2 * k)) n)).lastState := by
  induction n with
  | zero => exact ⟨rfl, rfl⟩
  | succ n ih =>
      obtain ⟨ihStates, ihLast⟩ := ih
      have hobs1 : (G.commonSignalCrossingEliminationGame.playHistory τ natD
            (2 * n)).observations1 =
          (G.commonSignalLift
            (G.playHistory σ (fun k => natD (2 * k)) n)).observations1 := by
        show (G.commonSignalCrossingEliminationGame.playHistory τ natD
            (2 * n)).states.map _ = _
        rw [ihStates]
        rfl
      have hobs2 : (G.commonSignalCrossingEliminationGame.playHistory τ natD
            (2 * n)).observations2 =
          (G.commonSignalLift
            (G.playHistory σ (fun k => natD (2 * k)) n)).observations2 := by
        show (G.commonSignalCrossingEliminationGame.playHistory τ natD
            (2 * n)).states.map _ = _
        rw [ihStates]
        rfl
      have hact1 : τ.1 (G.commonSignalCrossingEliminationGame.strategyState τ natD
            (2 * n)).2.1 =
          σ.1 (G.playHistory σ (fun k => natD (2 * k)) n).observations1 := by
        rw [← G.commonSignalCrossingEliminationGame.playHistory_observations1
            τ natD (2 * n), hobs1]
        exact hagree1 _
      have hact2 : τ.2 (G.commonSignalCrossingEliminationGame.strategyState τ natD
            (2 * n)).2.2 =
          σ.2 (G.playHistory σ (fun k => natD (2 * k)) n).observations2 := by
        rw [← G.commonSignalCrossingEliminationGame.playHistory_observations2
            τ natD (2 * n), hobs2]
        exact hagree2 _
      -- The base step and the two doubled steps.
      have hstep : G.playHistory σ (fun k => natD (2 * k)) (n + 1) =
          (G.playHistory σ (fun k => natD (2 * k)) n).step
            (σ.1 (G.playHistory σ (fun k => natD (2 * k)) n).observations1)
            (σ.2 (G.playHistory σ (fun k => natD (2 * k)) n).observations2)
            (natD (2 * n)) := by
        rw [playHistory,
          G.playHistory_observations1 σ (fun k => natD (2 * k)) n,
          G.playHistory_observations2 σ (fun k => natD (2 * k)) n]
      -- The first doubled step reaches the bridge state of the lifted play.
      have hbridgeState : G.commonSignalCrossingEliminationGame.next
            (G.commonSignalCrossingEliminationGame.playHistory τ natD
              (2 * n)).lastState
            (τ.1 (G.commonSignalCrossingEliminationGame.strategyState τ natD
              (2 * n)).2.1)
            (τ.2 (G.commonSignalCrossingEliminationGame.strategyState τ natD
              (2 * n)).2.2)
            (natD (2 * n)) =
          (G.commonSignalBridgeLift (G.playHistory σ (fun k => natD (2 * k)) n)
            (σ.1 (G.playHistory σ (fun k => natD (2 * k)) n).observations1)
            (σ.2 (G.playHistory σ (fun k => natD (2 * k)) n).observations2)
            (natD (2 * n))).lastState := by
        rw [ihLast, hact1, hact2]
        rfl
      have hbridgePhase : (G.commonSignalBridgeLift
            (G.playHistory σ (fun k => natD (2 * k)) n)
            (σ.1 (G.playHistory σ (fun k => natD (2 * k)) n).observations1)
            (σ.2 (G.playHistory σ (fun k => natD (2 * k)) n).observations2)
            (natD (2 * n))).lastState.1 = true := by
        rw [G.commonSignalBridgeLift_lastState]
      -- The second doubled step ignores everything at the bridge phase.
      have hsecond : ∀ (b1 : G.Action1) (b2 : G.Action2) (env : G.Nature),
          G.commonSignalCrossingEliminationGame.next
              (G.commonSignalBridgeLift (G.playHistory σ (fun k => natD (2 * k)) n)
                (σ.1 (G.playHistory σ (fun k => natD (2 * k)) n).observations1)
                (σ.2 (G.playHistory σ (fun k => natD (2 * k)) n).observations2)
                (natD (2 * n))).lastState b1 b2 env =
            (G.commonSignalLift
              (G.playHistory σ (fun k => natD (2 * k)) (n + 1))).lastState := by
        intro b1 b2 env
        rw [hstep, commonSignalLift]
        show G.crossingEliminationGame.next
            (G.commonSignalBridgeLift (G.playHistory σ (fun k => natD (2 * k)) n)
              (σ.1 (G.playHistory σ (fun k => natD (2 * k)) n).observations1)
              (σ.2 (G.playHistory σ (fun k => natD (2 * k)) n).observations2)
              (natD (2 * n))).lastState b1 b2 env =
          G.crossingEliminationGame.next
            (G.commonSignalBridgeLift (G.playHistory σ (fun k => natD (2 * k)) n)
              (σ.1 (G.playHistory σ (fun k => natD (2 * k)) n).observations1)
              (σ.2 (G.playHistory σ (fun k => natD (2 * k)) n).observations2)
              (natD (2 * n))).lastState
            (σ.1 (G.playHistory σ (fun k => natD (2 * k)) n).observations1)
            (σ.2 (G.playHistory σ (fun k => natD (2 * k)) n).observations2)
            (natD (2 * n))
        rw [G.crossingEliminationGame_next_intermediary _ hbridgePhase,
          G.crossingEliminationGame_next_intermediary _ hbridgePhase]
      -- The odd-time and even-time last states.
      have hlastOdd : (G.commonSignalCrossingEliminationGame.playHistory τ natD
            (2 * n + 1)).lastState =
          (G.commonSignalBridgeLift (G.playHistory σ (fun k => natD (2 * k)) n)
            (σ.1 (G.playHistory σ (fun k => natD (2 * k)) n).observations1)
            (σ.2 (G.playHistory σ (fun k => natD (2 * k)) n).observations2)
            (natD (2 * n))).lastState := by
        show G.commonSignalCrossingEliminationGame.next
            (G.commonSignalCrossingEliminationGame.playHistory τ natD
              (2 * n)).lastState _ _ (natD (2 * n)) = _
        exact hbridgeState
      have hlastEven : (G.commonSignalCrossingEliminationGame.playHistory τ natD
            (2 * (n + 1))).lastState =
          (G.commonSignalLift
            (G.playHistory σ (fun k => natD (2 * k)) (n + 1))).lastState := by
        show G.commonSignalCrossingEliminationGame.next
            (G.commonSignalCrossingEliminationGame.playHistory τ natD
              (2 * n + 1)).lastState _ _ (natD (2 * n + 1)) = _
        rw [hlastOdd]
        exact hsecond _ _ _
      refine ⟨?_, hlastEven⟩
      show (G.commonSignalCrossingEliminationGame.playHistory τ natD
            (2 * n)).states ++
          [(G.commonSignalCrossingEliminationGame.playHistory τ natD
            (2 * n + 1)).lastState] ++
          [(G.commonSignalCrossingEliminationGame.playHistory τ natD
            (2 * (n + 1))).lastState] = _
      rw [ihStates, hlastOdd, hlastEven, hstep, commonSignalLift]
      rfl

/-- At odd times the doubled play sits at the bridge state of the lifted base
play. -/
theorem commonSignal_play_lastState_odd
    (σ : G.HistoryProductStrategy)
    (τ : G.commonSignalCrossingEliminationGame.HistoryProductStrategy)
    (hagree1 : ∀ h : G.PlayHistory,
      τ.1 (G.commonSignalLift h).observations1 = σ.1 h.observations1)
    (hagree2 : ∀ h : G.PlayHistory,
      τ.2 (G.commonSignalLift h).observations2 = σ.2 h.observations2)
    (natD : Nat -> G.Nature) (n : Nat) :
    (G.commonSignalCrossingEliminationGame.playHistory τ natD
        (2 * n + 1)).lastState =
      (G.commonSignalBridgeLift (G.playHistory σ (fun k => natD (2 * k)) n)
        (σ.1 (G.playHistory σ (fun k => natD (2 * k)) n).observations1)
        (σ.2 (G.playHistory σ (fun k => natD (2 * k)) n).observations2)
        (natD (2 * n))).lastState := by
  obtain ⟨ihStates, ihLast⟩ :=
    G.commonSignal_play_states σ τ hagree1 hagree2 natD n
  have hobs1 : (G.commonSignalCrossingEliminationGame.playHistory τ natD
        (2 * n)).observations1 =
      (G.commonSignalLift
        (G.playHistory σ (fun k => natD (2 * k)) n)).observations1 := by
    show (G.commonSignalCrossingEliminationGame.playHistory τ natD
        (2 * n)).states.map _ = _
    rw [ihStates]
    rfl
  have hobs2 : (G.commonSignalCrossingEliminationGame.playHistory τ natD
        (2 * n)).observations2 =
      (G.commonSignalLift
        (G.playHistory σ (fun k => natD (2 * k)) n)).observations2 := by
    show (G.commonSignalCrossingEliminationGame.playHistory τ natD
        (2 * n)).states.map _ = _
    rw [ihStates]
    rfl
  have hact1 : τ.1 (G.commonSignalCrossingEliminationGame.strategyState τ natD
        (2 * n)).2.1 =
      σ.1 (G.playHistory σ (fun k => natD (2 * k)) n).observations1 := by
    rw [← G.commonSignalCrossingEliminationGame.playHistory_observations1
        τ natD (2 * n), hobs1]
    exact hagree1 _
  have hact2 : τ.2 (G.commonSignalCrossingEliminationGame.strategyState τ natD
        (2 * n)).2.2 =
      σ.2 (G.playHistory σ (fun k => natD (2 * k)) n).observations2 := by
    rw [← G.commonSignalCrossingEliminationGame.playHistory_observations2
        τ natD (2 * n), hobs2]
    exact hagree2 _
  show G.commonSignalCrossingEliminationGame.next
      (G.commonSignalCrossingEliminationGame.playHistory τ natD
        (2 * n)).lastState _ _ (natD (2 * n)) = _
  rw [ihLast, hact1, hact2]
  rfl

/-- **Priority correspondence.**  The doubled play's priority sequence is the
base play's priority sequence under the offset stutter `m ↦ (m + 1) / 2`. -/
theorem commonSignal_priority_correspondence
    (σ : G.HistoryProductStrategy)
    (τ : G.commonSignalCrossingEliminationGame.HistoryProductStrategy)
    (hagree1 : ∀ h : G.PlayHistory,
      τ.1 (G.commonSignalLift h).observations1 = σ.1 h.observations1)
    (hagree2 : ∀ h : G.PlayHistory,
      τ.2 (G.commonSignalLift h).observations2 = σ.2 h.observations2)
    (natD : Nat -> G.Nature) (m : Nat) :
    G.commonSignalCrossingEliminationGame.priority
        (G.commonSignalCrossingEliminationGame.strategyState τ natD m).1 =
      G.priority
        (G.strategyState σ (fun k => natD (2 * k)) ((m + 1) / 2)).1 := by
  obtain ⟨n, hn | hn⟩ := Nat.even_or_odd' m
  · subst hn
    rw [show (2 * n + 1) / 2 = n by omega,
      ← G.commonSignalCrossingEliminationGame.playHistory_lastState τ natD (2 * n),
      (G.commonSignal_play_states σ τ hagree1 hagree2 natD n).2,
      ← G.playHistory_lastState σ (fun k => natD (2 * k)) n]
    show G.priority (G.commonSignalLift
        (G.playHistory σ (fun k => natD (2 * k)) n)).lastState.2.1 = _
    rw [G.commonSignalLift_lastState]
  · subst hn
    rw [show (2 * n + 1 + 1) / 2 = n + 1 by omega,
      ← G.commonSignalCrossingEliminationGame.playHistory_lastState τ natD
        (2 * n + 1),
      G.commonSignal_play_lastState_odd σ τ hagree1 hagree2 natD n,
      ← G.playHistory_lastState σ (fun k => natD (2 * k)) (n + 1)]
    show G.priority (G.commonSignalBridgeLift
        (G.playHistory σ (fun k => natD (2 * k)) n)
        (σ.1 (G.playHistory σ (fun k => natD (2 * k)) n).observations1)
        (σ.2 (G.playHistory σ (fun k => natD (2 * k)) n).observations2)
        (natD (2 * n))).lastState.2.1 = _
    rw [G.commonSignalBridgeLift_lastState]
    have hstep : G.playHistory σ (fun k => natD (2 * k)) (n + 1) =
        (G.playHistory σ (fun k => natD (2 * k)) n).step
          (σ.1 (G.playHistory σ (fun k => natD (2 * k)) n).observations1)
          (σ.2 (G.playHistory σ (fun k => natD (2 * k)) n).observations2)
          (natD (2 * n)) := by
      rw [playHistory,
        G.playHistory_observations1 σ (fun k => natD (2 * k)) n,
        G.playHistory_observations2 σ (fun k => natD (2 * k)) n]
    rw [hstep]

/-- **Agreeing strategies transfer wins.**  If a base strategy and a doubled
strategy agree along lifts and the base strategy wins the base game, the
doubled strategy wins the doubled game (and conversely), by the priority
correspondence and the offset stutter. -/
theorem commonSignal_wins_of_agree
    (σ : G.HistoryProductStrategy)
    (τ : G.commonSignalCrossingEliminationGame.HistoryProductStrategy)
    (hagree1 : ∀ h : G.PlayHistory,
      τ.1 (G.commonSignalLift h).observations1 = σ.1 h.observations1)
    (hagree2 : ∀ h : G.PlayHistory,
      τ.2 (G.commonSignalLift h).observations2 = σ.2 h.observations2)
    (hwin : G.HistoryStrategyWins σ) :
    G.commonSignalCrossingEliminationGame.HistoryStrategyWins τ := by
  intro natD
  rw [parityAccepts_iff_natSeqMinEvenParity]
  have hpri : (fun m => G.commonSignalCrossingEliminationGame.priority
        (G.commonSignalCrossingEliminationGame.strategyState τ natD m).1) =
      (fun m => G.priority
        (G.strategyState σ (fun k => natD (2 * k)) ((m + 1) / 2)).1) :=
    funext (G.commonSignal_priority_correspondence σ τ hagree1 hagree2 natD)
  rw [hpri]
  refine (natSeqMinEvenParity_offset_stutter
    (fun k => G.priority
      (G.strategyState σ (fun k => natD (2 * k)) k).1)).mpr ?_
  rw [← parityAccepts_iff_natSeqMinEvenParity]
  exact hwin (fun k => natD (2 * k))

/-- The converse transfer: an agreeing doubled winner yields a base winner. -/
theorem commonSignal_wins_of_agree_reverse
    (σ : G.HistoryProductStrategy)
    (τ : G.commonSignalCrossingEliminationGame.HistoryProductStrategy)
    (hagree1 : ∀ h : G.PlayHistory,
      τ.1 (G.commonSignalLift h).observations1 = σ.1 h.observations1)
    (hagree2 : ∀ h : G.PlayHistory,
      τ.2 (G.commonSignalLift h).observations2 = σ.2 h.observations2)
    (hwin : G.commonSignalCrossingEliminationGame.HistoryStrategyWins τ) :
    G.HistoryStrategyWins σ := by
  intro nature
  have hwinD := hwin (fun m => nature (m / 2))
  rw [parityAccepts_iff_natSeqMinEvenParity] at hwinD ⊢
  have hpri : (fun m => G.commonSignalCrossingEliminationGame.priority
        (G.commonSignalCrossingEliminationGame.strategyState τ
          (fun m => nature (m / 2)) m).1) =
      (fun m => G.priority
        (G.strategyState σ (fun k => nature (2 * k / 2)) ((m + 1) / 2)).1) :=
    funext (G.commonSignal_priority_correspondence σ τ hagree1 hagree2
      (fun m => nature (m / 2)))
  rw [hpri] at hwinD
  have hnat : (fun k => nature (2 * k / 2)) = nature := by
    funext k
    rw [show 2 * k / 2 = k by omega]
  rw [hnat] at hwinD
  exact (natSeqMinEvenParity_offset_stutter _).mp hwinD

/-- The projected doubled strategy of a base strategy: each component reads the
base view off the doubled view. -/
def commonSignalProjectedStrategy (σ : G.HistoryProductStrategy) :
    G.commonSignalCrossingEliminationGame.HistoryProductStrategy :=
  (fun v => σ.1 (v.filterMap G.projectCommonObservationOne),
    fun v => σ.2 (v.filterMap G.projectCommonObservationTwo))

open Classical in
/-- The pulled-back base strategy of a doubled strategy: on a realized base
view, feed the doubled strategy the lifted view of a witnessing history
(well-defined by the lift congruences). -/
noncomputable def commonSignalPulledStrategy
    (τ : G.commonSignalCrossingEliminationGame.HistoryProductStrategy) :
    G.HistoryProductStrategy :=
  (fun v =>
    if h : ∃ history : G.PlayHistory, history.observations1 = v then
      τ.1 (G.commonSignalLift h.choose).observations1
    else τ.1 [],
    fun v =>
    if h : ∃ history : G.PlayHistory, history.observations2 = v then
      τ.2 (G.commonSignalLift h.choose).observations2
    else τ.2 [])

/-- The pulled-back strategy agrees with `τ` along lifts, component one. -/
theorem commonSignalPulledStrategy_agree1
    (τ : G.commonSignalCrossingEliminationGame.HistoryProductStrategy)
    (h : G.PlayHistory) :
    (G.commonSignalPulledStrategy τ).1 h.observations1 =
      τ.1 (G.commonSignalLift h).observations1 := by
  simp only [commonSignalPulledStrategy]
  split
  · rename_i hex
    exact congrArg τ.1
      (G.commonSignalLift_observations1_congr _ _ hex.choose_spec)
  · rename_i hnot
    exact absurd ⟨h, rfl⟩ hnot

/-- The pulled-back strategy agrees with `τ` along lifts, component two. -/
theorem commonSignalPulledStrategy_agree2 (hhier : G.DynamicHierarchy)
    (τ : G.commonSignalCrossingEliminationGame.HistoryProductStrategy)
    (h : G.PlayHistory) :
    (G.commonSignalPulledStrategy τ).2 h.observations2 =
      τ.2 (G.commonSignalLift h).observations2 := by
  simp only [commonSignalPulledStrategy]
  split
  · rename_i hex
    exact congrArg τ.2
      (G.commonSignalLift_observations2_congr hhier _ _ hex.choose_spec)
  · rename_i hnot
    exact absurd ⟨h, rfl⟩ hnot

/-- **Realizability transfers across common-signal crossing elimination.** -/
theorem commonSignal_historyRealizable_iff (hhier : G.DynamicHierarchy) :
    G.commonSignalCrossingEliminationGame.HistoryRealizable ↔
      G.HistoryRealizable := by
  constructor
  · rintro ⟨τ, hτ⟩
    exact ⟨G.commonSignalPulledStrategy τ,
      G.commonSignal_wins_of_agree_reverse _ τ
        (fun h => (G.commonSignalPulledStrategy_agree1 τ h).symm)
        (fun h => (G.commonSignalPulledStrategy_agree2 hhier τ h).symm) hτ⟩
  · rintro ⟨σ, hσ⟩
    refine ⟨G.commonSignalProjectedStrategy σ, ?_⟩
    refine G.commonSignal_wins_of_agree σ _ ?_ ?_ hσ
    · intro h
      show σ.1 ((G.commonSignalLift h).observations1.filterMap
        G.projectCommonObservationOne) = _
      rw [G.project_commonSignalLift_observations1]
    · intro h
      show σ.2 ((G.commonSignalLift h).observations2.filterMap
        G.projectCommonObservationTwo) = _
      rw [G.project_commonSignalLift_observations2 hhier]

/-! ### The Moore back-transfer

A winning Moore pair for the doubled game reads back to a winning Moore pair
for the base game.  The doubled letters along a lifted play are functions of
the base views (the congruences above), but not letter-by-letter computable:
the bridge letter contains the other player's machine data.  The finite
resolution is the subset construction over *crossing data* -- the triples
`(state, rank-one memory, rank-two memory)` consistent with the player's own
view -- from which the doubled letters are extracted by representative, with
agreement guaranteed through witnessing histories and the congruences. -/

/-- The crossing data tracked per consistent thread: the base state and the two
monitor memories. -/
abbrev CrossData :=
  G.State × G.rankOneMachine.Memory × G.rankTwoMachine.Memory

/-- The crossing data of a history. -/
noncomputable def crossDataOf (h : G.PlayHistory) : G.CrossData :=
  (h.lastState, G.rankOneMachine.run h.observations1,
    G.rankTwoMachine.run h.observations2)

/-- The initial crossing thread. -/
noncomputable def crossInitThread : G.CrossData :=
  G.crossDataOf PlayHistory.initial

open Classical in
/-- One thread step for player one: advance each thread by every action profile
and Nature move, keeping the threads matching the observed base letter. -/
noncomputable def crossThreadStep1 (K : Finset G.CrossData)
    (o1 : G.Observation1) : Finset G.CrossData :=
  Finset.univ.filter fun t =>
    (∃ p ∈ K, ∃ (a : G.Action1) (b : G.Action2) (env : G.Nature),
      t.1 = G.next p.1 a b env ∧
        t.2.1 = G.rankOneMachine.update p.2.1 (G.observe1 t.1) ∧
        t.2.2 = G.rankTwoMachine.update p.2.2 (G.observe2 t.1)) ∧
      G.observe1 t.1 = o1

theorem mem_crossThreadStep1 (K : Finset G.CrossData) (o1 : G.Observation1)
    (t : G.CrossData) :
    t ∈ G.crossThreadStep1 K o1 ↔
      ((∃ p ∈ K, ∃ (a : G.Action1) (b : G.Action2) (env : G.Nature),
        t.1 = G.next p.1 a b env ∧
          t.2.1 = G.rankOneMachine.update p.2.1 (G.observe1 t.1) ∧
          t.2.2 = G.rankTwoMachine.update p.2.2 (G.observe2 t.1)) ∧
        G.observe1 t.1 = o1) := by
  simp [crossThreadStep1]

/-- Player one's crossing-thread set along a view, dropping the initial
observation. -/
noncomputable def crossThreads1 (obs : List G.Observation1) : Finset G.CrossData :=
  obs.tail.foldl G.crossThreadStep1 {G.crossInitThread}

/-- Every history's view starts with the initial observation. -/
theorem observations1_head (h : G.PlayHistory) :
    ∃ rest : List G.Observation1,
      h.observations1 = G.observe1 G.initial :: rest := by
  induction h with
  | initial => exact ⟨[], rfl⟩
  | step h a b c ih =>
      obtain ⟨rest, hrest⟩ := ih
      exact ⟨rest ++ [G.observe1 (h.step a b c).lastState],
        by rw [PlayHistory.observations1_step, hrest]; rfl⟩

theorem observations2_head (h : G.PlayHistory) :
    ∃ rest : List G.Observation2,
      h.observations2 = G.observe2 G.initial :: rest := by
  induction h with
  | initial => exact ⟨[], rfl⟩
  | step h a b c ih =>
      obtain ⟨rest, hrest⟩ := ih
      exact ⟨rest ++ [G.observe2 (h.step a b c).lastState],
        by rw [PlayHistory.observations2_step, hrest]; rfl⟩

/-- The thread set advances by one step along a growing view. -/
theorem crossThreads1_append (l : List G.Observation1) (o1 : G.Observation1)
    (hl : l ≠ []) :
    G.crossThreads1 (l ++ [o1]) =
      G.crossThreadStep1 (G.crossThreads1 l) o1 := by
  obtain ⟨a, l', rfl⟩ := List.exists_cons_of_ne_nil hl
  simp only [crossThreads1, List.cons_append, List.tail_cons, List.foldl_append,
    List.foldl_cons, List.foldl_nil]

/-- **Real-thread membership**: every history's crossing data is in the thread
set of its own view. -/
theorem crossDataOf_mem_crossThreads1 (h : G.PlayHistory) :
    G.crossDataOf h ∈ G.crossThreads1 h.observations1 := by
  induction h with
  | initial => simp [crossThreads1, crossInitThread]
  | step h a b c ih =>
      obtain ⟨rest, hrest⟩ := G.observations1_head h
      rw [PlayHistory.observations1_step,
        G.crossThreads1_append _ _ (by rw [hrest]; simp),
        mem_crossThreadStep1]
      refine ⟨⟨G.crossDataOf h, ih, a, b, c, rfl, ?_, ?_⟩, rfl⟩
      · show G.rankOneMachine.run (h.step a b c).observations1 = _
        rw [PlayHistory.observations1_step, MooreController.run_append_singleton]
        rfl
      · show G.rankTwoMachine.run (h.step a b c).observations2 = _
        rw [PlayHistory.observations2_step, MooreController.run_append_singleton]
        rfl

/-- **Witnessing histories**: every member of the thread set over `l` is the
crossing data of a legal history whose view is `observe1 initial :: l`. -/
theorem exists_history_of_mem_crossThreads1Fold (l : List G.Observation1) :
    ∀ t : G.CrossData, t ∈ l.foldl G.crossThreadStep1 {G.crossInitThread} →
      ∃ h : G.PlayHistory,
        h.observations1 = G.observe1 G.initial :: l ∧ t = G.crossDataOf h := by
  induction l using List.reverseRecOn with
  | nil =>
      intro t ht
      rw [List.foldl_nil, Finset.mem_singleton] at ht
      subst ht
      exact ⟨.initial, rfl, rfl⟩
  | append_singleton l' o ih =>
      intro t ht
      rw [List.foldl_append, List.foldl_cons, List.foldl_nil,
        mem_crossThreadStep1] at ht
      obtain ⟨⟨p, hp, a, b, env, hnext, hm1, hm2⟩, hobs⟩ := ht
      obtain ⟨h, hh1, hpdata⟩ := ih p hp
      refine ⟨h.step a b env, ?_, ?_⟩
      · rw [PlayHistory.observations1_step, hh1]
        have hlast : (h.step a b env).lastState = t.1 := by
          rw [hnext, hpdata]
          rfl
        rw [show G.observe1 (G.next h.lastState a b env) =
            G.observe1 (h.step a b env).lastState from rfl, hlast, hobs]
        simp
      · have hlast : (h.step a b env).lastState = t.1 := by
          rw [hnext, hpdata]
          rfl
        refine Prod.ext ?_ (Prod.ext ?_ ?_)
        · exact hlast.symm
        · show t.2.1 = G.rankOneMachine.run (h.step a b env).observations1
          rw [PlayHistory.observations1_step,
            MooreController.run_append_singleton, hm1, hpdata,
            show G.observe1 (G.next h.lastState a b env) =
              G.observe1 (h.step a b env).lastState from rfl, hlast]
          rfl
        · show t.2.2 = G.rankTwoMachine.run (h.step a b env).observations2
          rw [PlayHistory.observations2_step,
            MooreController.run_append_singleton, hm2, hpdata,
            show G.observe2 (G.next h.lastState a b env) =
              G.observe2 (h.step a b env).lastState from rfl, hlast]
          rfl

theorem exists_history_of_mem_crossThreads1 (h : G.PlayHistory)
    (t : G.CrossData) (ht : t ∈ G.crossThreads1 h.observations1) :
    ∃ h' : G.PlayHistory,
      h'.observations1 = h.observations1 ∧ t = G.crossDataOf h' := by
  obtain ⟨rest, hrest⟩ := G.observations1_head h
  rw [hrest] at ht
  obtain ⟨h', hh', hdata⟩ :=
    G.exists_history_of_mem_crossThreads1Fold rest t ht
  exact ⟨h', by rw [hh', hrest], hdata⟩

variable [Inhabited G.Observation1] [Inhabited G.Observation2]

open Classical in
/-- The doubled letter extracted from a thread set at the given phase, read
from a representative thread. -/
noncomputable def crossExtract1 (phase : Bool) (K : Finset G.CrossData) :
    G.commonSignalCrossingEliminationGame.Observation1 :=
  if hK : K.Nonempty then
    G.commonSignalCrossingEliminationGame.observe1 (phase, hK.choose)
  else Sum.inl (default, 0)

omit [Inhabited G.Observation2] in
/-- **Bridge extraction agreement.**  On the thread set of a stepped history's
view, the extracted bridge letter is the true common bridge letter. -/
theorem crossExtract1_bridge (h : G.PlayHistory) (a : G.Action1)
    (b : G.Action2) (c : G.Nature) :
    G.crossExtract1 true (G.crossThreads1 (h.step a b c).observations1) =
      Sum.inr (G.commonBridgeSignalAt (h.step a b c)) := by
  have hne : (G.crossThreads1 (h.step a b c).observations1).Nonempty :=
    ⟨G.crossDataOf (h.step a b c), G.crossDataOf_mem_crossThreads1 _⟩
  rw [crossExtract1, dif_pos hne]
  obtain ⟨h', hobs, hdata⟩ :=
    G.exists_history_of_mem_crossThreads1 (h.step a b c) hne.choose
      hne.choose_spec
  cases h' with
  | initial =>
      exfalso
      have hlen := congrArg List.length hobs
      simp only [PlayHistory.observations1_initial,
        PlayHistory.observations1_step, List.length_append,
        List.length_singleton, List.length_cons] at hlen
      have hpos := G.observations1_length_pos h
      omega
  | step h0 a' b' c' =>
      have hbridge : (true, G.crossDataOf (h0.step a' b' c')) =
          (G.commonSignalBridgeLift h0 a' b' c').lastState := by
        rw [G.commonSignalBridgeLift_lastState]
        rfl
      rw [hdata, hbridge, G.commonSignalBridgeLift_observe1,
        G.commonBridgeSignalAt_congr_observations1 _ _ hobs]

omit [Inhabited G.Observation2] in
/-- **Normal extraction agreement.**  On the thread set of a history's view,
the extracted phase-`false` letter is the true lifted normal letter. -/
theorem crossExtract1_normal (h : G.PlayHistory) :
    G.crossExtract1 false (G.crossThreads1 h.observations1) =
      Sum.inl (G.observe1 h.lastState, G.informationRankOne h) := by
  have hne : (G.crossThreads1 h.observations1).Nonempty :=
    ⟨G.crossDataOf h, G.crossDataOf_mem_crossThreads1 _⟩
  rw [crossExtract1, dif_pos hne]
  obtain ⟨h', hobs, hdata⟩ :=
    G.exists_history_of_mem_crossThreads1 h hne.choose hne.choose_spec
  have hlift : (false, G.crossDataOf h') =
      (G.commonSignalLift h').lastState := by
    rw [G.commonSignalLift_lastState]
    rfl
  rw [hdata, hlift, G.commonSignalLift_observe1]
  have hlastEq : G.observe1 h'.lastState = G.observe1 h.lastState := by
    have hlast := congrArg List.getLast? hobs
    rw [PlayHistory.observations1_getLast?_last,
      PlayHistory.observations1_getLast?_last] at hlast
    exact Option.some.inj hlast
  rw [hlastEq, G.informationRankOne_consistent h' h hobs]

/-- The base Moore controller pulled back from a doubled controller for player
one: it tracks the doubled controller's memory alongside the crossing-thread
set, feeding the doubled controller the extracted bridge and normal letters on
each base observation. -/
noncomputable def basePullbackController1 {A : Type u}
    (C : MooreController.{u, u, u}
      G.commonSignalCrossingEliminationGame.Observation1 A) :
    MooreController.{u, u, u} G.Observation1 A where
  Memory := Option (C.Memory × Finset G.CrossData)
  memoryFinite := by classical infer_instance
  initial := none
  update m o1 :=
    match m with
    | none =>
        some (C.update C.initial
          (G.commonSignalCrossingEliminationGame.observe1
            G.commonSignalCrossingEliminationGame.initial),
          {G.crossInitThread})
    | some (m, K) =>
        some (C.update (C.update m (G.crossExtract1 true (G.crossThreadStep1 K o1)))
            (G.crossExtract1 false (G.crossThreadStep1 K o1)),
          G.crossThreadStep1 K o1)
  output m :=
    match m with
    | none => C.output C.initial
    | some (m, _) => C.output m

omit [Inhabited G.Observation2] in
/-- **The pullback controller simulates the doubled controller.**  On any
history's view it reaches the doubled controller's memory on the lifted view,
alongside the thread set. -/
theorem basePullbackController1_run {A : Type u}
    (C : MooreController.{u, u, u}
      G.commonSignalCrossingEliminationGame.Observation1 A)
    (h : G.PlayHistory) :
    (G.basePullbackController1 C).run h.observations1 =
      some (C.run (G.commonSignalLift h).observations1,
        G.crossThreads1 h.observations1) := by
  induction h with
  | initial => rfl
  | step h a b c ih =>
      obtain ⟨rest, hrest⟩ := G.observations1_head h
      rw [PlayHistory.observations1_step, MooreController.run_append_singleton,
        ih]
      show some (C.update (C.update (C.run (G.commonSignalLift h).observations1)
          (G.crossExtract1 true (G.crossThreadStep1
            (G.crossThreads1 h.observations1)
            (G.observe1 (h.step a b c).lastState))))
          (G.crossExtract1 false (G.crossThreadStep1
            (G.crossThreads1 h.observations1)
            (G.observe1 (h.step a b c).lastState))),
        G.crossThreadStep1 (G.crossThreads1 h.observations1)
          (G.observe1 (h.step a b c).lastState)) = _
      have hK : G.crossThreadStep1 (G.crossThreads1 h.observations1)
            (G.observe1 (h.step a b c).lastState) =
          G.crossThreads1 (h.step a b c).observations1 := by
        rw [PlayHistory.observations1_step,
          G.crossThreads1_append _ _ (by rw [hrest]; simp)]
        rfl
      rw [hK, G.crossExtract1_bridge h a b c, crossExtract1_normal]
      have hliftView : (G.commonSignalLift (h.step a b c)).observations1 =
          (G.commonSignalLift h).observations1 ++
            ([Sum.inr (G.commonBridgeSignalAt (h.step a b c))] :
              List G.commonSignalCrossingEliminationGame.Observation1) ++
            ([Sum.inl (G.observe1 (h.step a b c).lastState,
              G.informationRankOne (h.step a b c))] :
              List G.commonSignalCrossingEliminationGame.Observation1) := by
        rw [commonSignalLift, PlayHistory.observations1_step,
          PlayHistory.observations1_step]
        rw [show (G.commonSignalLift h).step a b c =
          G.commonSignalBridgeLift h a b c from rfl]
        have e1 : G.commonSignalCrossingEliminationGame.observe1
            (G.commonSignalCrossingEliminationGame.next
              (G.commonSignalLift h).lastState a b c) =
            Sum.inr (G.commonBridgeSignalAt (h.step a b c)) := by
          show G.commonSignalCrossingEliminationGame.observe1
            (G.commonSignalBridgeLift h a b c).lastState = _
          exact G.commonSignalBridgeLift_observe1 h a b c
        have e2 : G.commonSignalCrossingEliminationGame.observe1
            (G.commonSignalCrossingEliminationGame.next
              (G.commonSignalBridgeLift h a b c).lastState a b c) =
            Sum.inl (G.observe1 (h.step a b c).lastState,
              G.informationRankOne (h.step a b c)) := by
          show G.commonSignalCrossingEliminationGame.observe1
            (G.commonSignalLift (h.step a b c)).lastState = _
          exact G.commonSignalLift_observe1 (h.step a b c)
        rw [e1, e2]
      rw [hliftView, MooreController.run_append_singleton,
        MooreController.run_append_singleton, PlayHistory.observations1_step]

/-! ### The player-two mirror -/

open Classical in
/-- One thread step for player two. -/
noncomputable def crossThreadStep2 (K : Finset G.CrossData)
    (o2 : G.Observation2) : Finset G.CrossData :=
  Finset.univ.filter fun t =>
    (∃ p ∈ K, ∃ (a : G.Action1) (b : G.Action2) (env : G.Nature),
      t.1 = G.next p.1 a b env ∧
        t.2.1 = G.rankOneMachine.update p.2.1 (G.observe1 t.1) ∧
        t.2.2 = G.rankTwoMachine.update p.2.2 (G.observe2 t.1)) ∧
      G.observe2 t.1 = o2

omit [Inhabited G.Observation1] [Inhabited G.Observation2] in
theorem mem_crossThreadStep2 (K : Finset G.CrossData) (o2 : G.Observation2)
    (t : G.CrossData) :
    t ∈ G.crossThreadStep2 K o2 ↔
      ((∃ p ∈ K, ∃ (a : G.Action1) (b : G.Action2) (env : G.Nature),
        t.1 = G.next p.1 a b env ∧
          t.2.1 = G.rankOneMachine.update p.2.1 (G.observe1 t.1) ∧
          t.2.2 = G.rankTwoMachine.update p.2.2 (G.observe2 t.1)) ∧
        G.observe2 t.1 = o2) := by
  simp [crossThreadStep2]

/-- Player two's crossing-thread set along a view. -/
noncomputable def crossThreads2 (obs : List G.Observation2) : Finset G.CrossData :=
  obs.tail.foldl G.crossThreadStep2 {G.crossInitThread}

section
omit [Inhabited G.Observation1] [Inhabited G.Observation2]

theorem crossThreads2_append (l : List G.Observation2) (o2 : G.Observation2)
    (hl : l ≠ []) :
    G.crossThreads2 (l ++ [o2]) =
      G.crossThreadStep2 (G.crossThreads2 l) o2 := by
  obtain ⟨a, l', rfl⟩ := List.exists_cons_of_ne_nil hl
  simp only [crossThreads2, List.cons_append, List.tail_cons, List.foldl_append,
    List.foldl_cons, List.foldl_nil]

theorem crossDataOf_mem_crossThreads2 (h : G.PlayHistory) :
    G.crossDataOf h ∈ G.crossThreads2 h.observations2 := by
  induction h with
  | initial => simp [crossThreads2, crossInitThread]
  | step h a b c ih =>
      obtain ⟨rest, hrest⟩ := G.observations2_head h
      rw [PlayHistory.observations2_step,
        G.crossThreads2_append _ _ (by rw [hrest]; simp),
        mem_crossThreadStep2]
      refine ⟨⟨G.crossDataOf h, ih, a, b, c, rfl, ?_, ?_⟩, rfl⟩
      · show G.rankOneMachine.run (h.step a b c).observations1 = _
        rw [PlayHistory.observations1_step, MooreController.run_append_singleton]
        rfl
      · show G.rankTwoMachine.run (h.step a b c).observations2 = _
        rw [PlayHistory.observations2_step, MooreController.run_append_singleton]
        rfl

theorem exists_history_of_mem_crossThreads2Fold (l : List G.Observation2) :
    ∀ t : G.CrossData, t ∈ l.foldl G.crossThreadStep2 {G.crossInitThread} →
      ∃ h : G.PlayHistory,
        h.observations2 = G.observe2 G.initial :: l ∧ t = G.crossDataOf h := by
  induction l using List.reverseRecOn with
  | nil =>
      intro t ht
      rw [List.foldl_nil, Finset.mem_singleton] at ht
      subst ht
      exact ⟨.initial, rfl, rfl⟩
  | append_singleton l' o ih =>
      intro t ht
      rw [List.foldl_append, List.foldl_cons, List.foldl_nil,
        mem_crossThreadStep2] at ht
      obtain ⟨⟨p, hp, a, b, env, hnext, hm1, hm2⟩, hobs⟩ := ht
      obtain ⟨h, hh2, hpdata⟩ := ih p hp
      have hlast : (h.step a b env).lastState = t.1 := by
        rw [hnext, hpdata]
        rfl
      refine ⟨h.step a b env, ?_, ?_⟩
      · rw [PlayHistory.observations2_step, hh2,
          show G.observe2 (G.next h.lastState a b env) =
            G.observe2 (h.step a b env).lastState from rfl, hlast, hobs]
        simp
      · refine Prod.ext ?_ (Prod.ext ?_ ?_)
        · exact hlast.symm
        · show t.2.1 = G.rankOneMachine.run (h.step a b env).observations1
          rw [PlayHistory.observations1_step,
            MooreController.run_append_singleton, hm1, hpdata,
            show G.observe1 (G.next h.lastState a b env) =
              G.observe1 (h.step a b env).lastState from rfl, hlast]
          rfl
        · show t.2.2 = G.rankTwoMachine.run (h.step a b env).observations2
          rw [PlayHistory.observations2_step,
            MooreController.run_append_singleton, hm2, hpdata,
            show G.observe2 (G.next h.lastState a b env) =
              G.observe2 (h.step a b env).lastState from rfl, hlast]
          rfl

theorem exists_history_of_mem_crossThreads2 (h : G.PlayHistory)
    (t : G.CrossData) (ht : t ∈ G.crossThreads2 h.observations2) :
    ∃ h' : G.PlayHistory,
      h'.observations2 = h.observations2 ∧ t = G.crossDataOf h' := by
  obtain ⟨rest, hrest⟩ := G.observations2_head h
  rw [hrest] at ht
  obtain ⟨h', hh', hdata⟩ :=
    G.exists_history_of_mem_crossThreads2Fold rest t ht
  exact ⟨h', by rw [hh', hrest], hdata⟩

end

open Classical in
/-- Player two's extracted doubled letter at the given phase. -/
noncomputable def crossExtract2 (phase : Bool) (K : Finset G.CrossData) :
    G.commonSignalCrossingEliminationGame.Observation2 :=
  if hK : K.Nonempty then
    G.commonSignalCrossingEliminationGame.observe2 (phase, hK.choose)
  else Sum.inl (default, 0)

omit [Inhabited G.Observation1] in
theorem crossExtract2_bridge (hhier : G.DynamicHierarchy)
    (h : G.PlayHistory) (a : G.Action1) (b : G.Action2) (c : G.Nature) :
    G.crossExtract2 true (G.crossThreads2 (h.step a b c).observations2) =
      Sum.inr (G.commonBridgeSignalAt (h.step a b c)) := by
  have hne : (G.crossThreads2 (h.step a b c).observations2).Nonempty :=
    ⟨G.crossDataOf (h.step a b c), G.crossDataOf_mem_crossThreads2 _⟩
  rw [crossExtract2, dif_pos hne]
  obtain ⟨h', hobs, hdata⟩ :=
    G.exists_history_of_mem_crossThreads2 (h.step a b c) hne.choose
      hne.choose_spec
  cases h' with
  | initial =>
      exfalso
      have hlen := congrArg List.length hobs
      simp only [PlayHistory.observations2_initial,
        PlayHistory.observations2_step, List.length_append,
        List.length_singleton, List.length_cons] at hlen
      obtain ⟨rest, hrest⟩ := G.observations2_head h
      have hpos : 0 < h.observations2.length := by rw [hrest]; simp
      omega
  | step h0 a' b' c' =>
      have hbridge : (true, G.crossDataOf (h0.step a' b' c')) =
          (G.commonSignalBridgeLift h0 a' b' c').lastState := by
        rw [G.commonSignalBridgeLift_lastState]
        rfl
      rw [hdata, hbridge, G.commonSignalBridgeLift_observe2,
        G.commonBridgeSignalAt_congr_observations2 hhier _ _ hobs]

omit [Inhabited G.Observation1] in
theorem crossExtract2_normal (hhier : G.DynamicHierarchy) (h : G.PlayHistory) :
    G.crossExtract2 false (G.crossThreads2 h.observations2) =
      Sum.inl (G.observe2 h.lastState, G.informationRankTwo h) := by
  have hne : (G.crossThreads2 h.observations2).Nonempty :=
    ⟨G.crossDataOf h, G.crossDataOf_mem_crossThreads2 _⟩
  rw [crossExtract2, dif_pos hne]
  obtain ⟨h', hobs, hdata⟩ :=
    G.exists_history_of_mem_crossThreads2 h hne.choose hne.choose_spec
  have hlift : (false, G.crossDataOf h') =
      (G.commonSignalLift h').lastState := by
    rw [G.commonSignalLift_lastState]
    rfl
  rw [hdata, hlift, G.commonSignalLift_observe2 hhier]
  have hlastEq : G.observe2 h'.lastState = G.observe2 h.lastState := by
    have hlast := congrArg List.getLast? hobs
    rw [PlayHistory.observations2_getLast?_last,
      PlayHistory.observations2_getLast?_last] at hlast
    exact Option.some.inj hlast
  rw [hlastEq, G.informationRankTwo_consistent hhier h' h hobs]

/-- The base Moore controller pulled back for player two. -/
noncomputable def basePullbackController2 {A : Type u}
    (C : MooreController.{u, u, u}
      G.commonSignalCrossingEliminationGame.Observation2 A) :
    MooreController.{u, u, u} G.Observation2 A where
  Memory := Option (C.Memory × Finset G.CrossData)
  memoryFinite := by classical infer_instance
  initial := none
  update m o2 :=
    match m with
    | none =>
        some (C.update C.initial
          (G.commonSignalCrossingEliminationGame.observe2
            G.commonSignalCrossingEliminationGame.initial),
          {G.crossInitThread})
    | some (m, K) =>
        some (C.update (C.update m (G.crossExtract2 true (G.crossThreadStep2 K o2)))
            (G.crossExtract2 false (G.crossThreadStep2 K o2)),
          G.crossThreadStep2 K o2)
  output m :=
    match m with
    | none => C.output C.initial
    | some (m, _) => C.output m

omit [Inhabited G.Observation1] in
theorem basePullbackController2_run (hhier : G.DynamicHierarchy) {A : Type u}
    (C : MooreController.{u, u, u}
      G.commonSignalCrossingEliminationGame.Observation2 A)
    (h : G.PlayHistory) :
    (G.basePullbackController2 C).run h.observations2 =
      some (C.run (G.commonSignalLift h).observations2,
        G.crossThreads2 h.observations2) := by
  induction h with
  | initial => rfl
  | step h a b c ih =>
      obtain ⟨rest, hrest⟩ := G.observations2_head h
      rw [PlayHistory.observations2_step, MooreController.run_append_singleton,
        ih]
      show some (C.update (C.update (C.run (G.commonSignalLift h).observations2)
          (G.crossExtract2 true (G.crossThreadStep2
            (G.crossThreads2 h.observations2)
            (G.observe2 (h.step a b c).lastState))))
          (G.crossExtract2 false (G.crossThreadStep2
            (G.crossThreads2 h.observations2)
            (G.observe2 (h.step a b c).lastState))),
        G.crossThreadStep2 (G.crossThreads2 h.observations2)
          (G.observe2 (h.step a b c).lastState)) = _
      have hK : G.crossThreadStep2 (G.crossThreads2 h.observations2)
            (G.observe2 (h.step a b c).lastState) =
          G.crossThreads2 (h.step a b c).observations2 := by
        rw [PlayHistory.observations2_step,
          G.crossThreads2_append _ _ (by rw [hrest]; simp)]
        rfl
      rw [hK, G.crossExtract2_bridge hhier h a b c, crossExtract2_normal _ hhier]
      have hliftView : (G.commonSignalLift (h.step a b c)).observations2 =
          (G.commonSignalLift h).observations2 ++
            ([Sum.inr (G.commonBridgeSignalAt (h.step a b c))] :
              List G.commonSignalCrossingEliminationGame.Observation2) ++
            ([Sum.inl (G.observe2 (h.step a b c).lastState,
              G.informationRankTwo (h.step a b c))] :
              List G.commonSignalCrossingEliminationGame.Observation2) := by
        rw [commonSignalLift, PlayHistory.observations2_step,
          PlayHistory.observations2_step]
        rw [show (G.commonSignalLift h).step a b c =
          G.commonSignalBridgeLift h a b c from rfl]
        have e1 : G.commonSignalCrossingEliminationGame.observe2
            (G.commonSignalCrossingEliminationGame.next
              (G.commonSignalLift h).lastState a b c) =
            Sum.inr (G.commonBridgeSignalAt (h.step a b c)) := by
          show G.commonSignalCrossingEliminationGame.observe2
            (G.commonSignalBridgeLift h a b c).lastState = _
          exact G.commonSignalBridgeLift_observe2 h a b c
        have e2 : G.commonSignalCrossingEliminationGame.observe2
            (G.commonSignalCrossingEliminationGame.next
              (G.commonSignalBridgeLift h a b c).lastState a b c) =
            Sum.inl (G.observe2 (h.step a b c).lastState,
              G.informationRankTwo (h.step a b c)) := by
          show G.commonSignalCrossingEliminationGame.observe2
            (G.commonSignalLift (h.step a b c)).lastState = _
          exact G.commonSignalLift_observe2 hhier (h.step a b c)
        rw [e1, e2]
      rw [hliftView, MooreController.run_append_singleton,
        MooreController.run_append_singleton, PlayHistory.observations2_step]

/-! ### Finite-state and certificate transfer -/

/-- **The Moore back-transfer.**  A winning Moore pair for the doubled game
pulls back to a winning Moore pair for the base game. -/
theorem finiteStateRealizable_of_commonSignal (hhier : G.DynamicHierarchy)
    (hD : G.commonSignalCrossingEliminationGame.FiniteStateRealizable) :
    G.FiniteStateRealizable := by
  obtain ⟨ctrl, hctrl⟩ := hD
  refine ⟨⟨G.basePullbackController1 ctrl.one,
    G.basePullbackController2 ctrl.two⟩, ?_⟩
  refine G.commonSignal_wins_of_agree_reverse _ ctrl.toHistory ?_ ?_ hctrl
  · intro h
    show ctrl.one.strategy (G.commonSignalLift h).observations1 =
      (G.basePullbackController1 ctrl.one).strategy h.observations1
    rw [MooreController.strategy, MooreController.strategy,
      G.basePullbackController1_run]
    rfl
  · intro h
    show ctrl.two.strategy (G.commonSignalLift h).observations2 =
      (G.basePullbackController2 ctrl.two).strategy h.observations2
    rw [MooreController.strategy, MooreController.strategy,
      G.basePullbackController2_run hhier]
    rfl

/-- **The certificate transfers across common-signal crossing elimination.**
A finite-state synthesis certificate for the doubled game yields one for the
base game: completeness composes the realizability transfer with the Moore
back-transfer, and the decision transfers along the realizability equivalence. -/
noncomputable def commonSignalCertificateTransfer (hhier : G.DynamicHierarchy)
    (cert :
      G.commonSignalCrossingEliminationGame.FiniteStateSynthesisCertificate) :
    G.FiniteStateSynthesisCertificate where
  complete hreal :=
    G.finiteStateRealizable_of_commonSignal hhier
      (cert.complete ((G.commonSignal_historyRealizable_iff hhier).mpr hreal))
  decision := by
    letI := cert.decision
    exact decidable_of_iff _ (G.commonSignal_historyRealizable_iff hhier)

end FiniteConcurrentGame

end DistributedSynthesis
