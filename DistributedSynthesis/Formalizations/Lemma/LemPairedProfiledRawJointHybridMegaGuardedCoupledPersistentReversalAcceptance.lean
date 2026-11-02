/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridMegaGuardedStrictEntryAlignment

/-!
# Persistent reversal from an aligned guarded coupled cut

At a guarded coupled cut the next strict block is either right- or
left-oriented.  If both strict directions recur and no simultaneous round is
left in the suffix, the first opposite strict round exists.  Minimality makes
the preceding block homogeneous, while recurrence supplies termination of
every later strict block.  The checker-aligned guarded handoff theorem can
therefore be applied without any externally supplied block boundary.

This is a proof-side case split only.  Neither endpoint is given the current
graph, a direction, a leader bit, or the selected first reversal.
-/

namespace DistributedSynthesis

universe u v x y s

/-- Recurrence of both strict directions is invariant under a finite drop. -/
theorem BothStrictDirectionsRecurrent.drop
    {graphs : Nat → Graph} (h : BothStrictDirectionsRecurrent graphs)
    (start : Nat) :
    BothStrictDirectionsRecurrent (fun n ↦ graphs (start + n)) := by
  constructor
  · intro after
    rcases h.1 (start + after) with ⟨n, hn, hleft⟩
    have hstart : start ≤ n :=
      Nat.le_trans (Nat.le_add_right start after) hn
    refine ⟨n - start, ?_, ?_⟩
    · omega
    · simpa [Nat.add_sub_of_le hstart] using hleft
  · intro after
    rcases h.2 (start + after) with ⟨n, hn, hright⟩
    have hstart : start ≤ n :=
      Nat.le_trans (Nat.le_add_right start after) hn
    refine ⟨n - start, ?_, ?_⟩
    · omega
    · simpa [Nat.add_sub_of_le hstart] using hright

namespace DetParityAutomaton

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable
  (A : DetParityAutomaton.{max u v x y, s}
    (RoundRecord In₁ In₂ Graph Out₁ Out₂))

noncomputable section

variable [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁]
  [Inhabited Out₂]
variable [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
variable [DecidableEq In₁] [DecidableEq In₂]

variable
  (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
  (hwin : ∀ env : EnvironmentSequence In₁ In₂,
    A.Accepts (execution strategy env))

private abbrev RetainedTag :=
  ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTag A strategy
    hwin

private abbrev Mega
    (controllers : ProfiledRawJointRootCompatibleInitialControllers A strategy)
    (initialBank : ProfiledRawJointInitialControllerBank A strategy)
    (fallbackTag : RetainedTag A strategy hwin) :=
  MegaGuardedLinkedPhysicalController A strategy hwin controllers initialBank
    fallbackTag

/-- The right and left guarded projections of one installation start at the
same represented common DPA coordinate. -/
theorem profiledRawJointHybridGuardedCommonPairAt_entryState_eq
    (installation :
      ProfiledRawJointHybridGuardedSiblingInstallation A strategy hwin) :
    let pair := profiledRawJointHybridGuardedCommonPairAt A strategy hwin
      installation
    pairedCodeStateForRow A .both pair.1.1.1.base.source.1.1 =
      pairedCodeStateForRow A .both pair.1.2.1.base.source.1.1 := by
  cases installation <;> rfl

/-- An aligned guarded coupled cut accepts every subsequent all-strict tail
in which both strict directions recur.  The two entry equations are stated
separately because the right and left guarded projections have dependent
source types; both are coordinates of the same represented common pair. -/
theorem
    profiledRawJointHybridMegaGuarded_accepts_of_coupled_persistentReversal
    (controllers : ProfiledRawJointRootCompatibleInitialControllers A strategy)
    (initialBank : ProfiledRawJointInitialControllerBank A strategy)
    (fallbackTag : RetainedTag A strategy hwin)
    (installation :
      ProfiledRawJointHybridGuardedSiblingInstallation A strategy hwin)
    (oldOutputOne : Out₁) (oldOutputTwo : Out₂)
    (env : EnvironmentSequence In₁ In₂) (start : Nat)
    (hphysical :
      (Mega A strategy hwin controllers initialBank fallbackTag
        ).globalMachine.globalStateTrace env start =
        profiledRawJointHybridMegaGuardedCoupledControls A strategy hwin
          controllers initialBank fallbackTag installation oldOutputOne
            oldOutputTwo)
    (hentryRight :
      let pair := profiledRawJointHybridGuardedCommonPairAt A strategy hwin
        installation
      let mega := Mega A strategy hwin controllers initialBank fallbackTag
      A.run
          (mega.globalMachine.globalMachineTraceWord mega.globalOutputOne
            mega.globalOutputTwo env) start =
        pairedCodeStateForRow A .both pair.1.1.1.base.source.1.1)
    (hnoboth : ∀ k : Nat, (env (start + k)).graph ≠ .both)
    (hstrict :
      BothStrictDirectionsRecurrent (fun k ↦ (env (start + k)).graph)) :
    let mega := Mega A strategy hwin controllers initialBank fallbackTag
    A.Accepts
      (mega.globalMachine.globalMachineTraceWord mega.globalOutputOne
        mega.globalOutputTwo env) := by
  dsimp only at hentryRight ⊢
  let mega := Mega A strategy hwin controllers initialBank fallbackTag
  let graphs : Nat → Graph := fun k ↦ (env (start + k)).graph
  have hentryLeft :
      A.run
          (mega.globalMachine.globalMachineTraceWord mega.globalOutputOne
            mega.globalOutputTwo env) start =
        pairedCodeStateForRow A .both
          (profiledRawJointHybridGuardedCommonPairAt A strategy hwin
            installation).1.2.1.base.source.1.1 :=
    hentryRight.trans
      (profiledRawJointHybridGuardedCommonPairAt_entryState_eq A strategy hwin
        installation)
  cases hgraphZero : graphs 0 with
  | both => exact False.elim (hnoboth 0 hgraphZero)
  | right =>
      have hexists : ∃ close : Nat, graphs close ≠ .right := by
        rcases hstrict.1 0 with ⟨close, _hclose, hleft⟩
        change graphs close = .left at hleft
        exact ⟨close, by rw [hleft]; exact Graph.noConfusion⟩
      let close := Nat.find hexists
      have hcloseNe : graphs close ≠ .right := Nat.find_spec hexists
      have hbefore : ∀ k : Nat, k < close → graphs k = .right := by
        intro k hk
        by_contra hne
        exact (Nat.find_min hexists hk) hne
      have hclosePos : 0 < close := by
        by_contra hnot
        have hzero : close = 0 := by omega
        exact hcloseNe (by simpa [hzero] using hgraphZero)
      have hcloseLeft : graphs close = .left := by
        cases hcloseGraph : graphs close with
        | left => rfl
        | right => exact False.elim (hcloseNe hcloseGraph)
        | both => exact False.elim (hnoboth close hcloseGraph)
      let n := close - 1
      have hnclose : n + 1 = close := by
        dsimp only [n]
        omega
      have hright : ∀ k : Nat, k < n + 1 →
          (env (start + k)).graph = .right := by
        intro k hk
        exact hbefore k (by simpa [hnclose] using hk)
      have hclose : (env (start + (n + 1))).graph = .left := by
        simpa [graphs, hnclose] using hcloseLeft
      have hstrictDrop := BothStrictDirectionsRecurrent.drop hstrict close
      have hterm : OperationalStrictRunsTerminate
          (profiledRawJointPhysicalGraphTail
            (OmegaWord.drop env (start + (n + 1))) 0) := by
        unfold profiledRawJointPhysicalGraphTail
        unfold OmegaWord.drop
        simp only [Nat.zero_add]
        simpa [graphs, hnclose, Nat.add_assoc] using
            (operationalStrictRunsTerminate_of_bothStrictDirectionsRecurrent
              hstrictDrop)
      have hnoBothDrop : ∀ k : Nat,
          profiledRawJointPhysicalGraphTail
              (OmegaWord.drop env (start + (n + 1))) 0 k ≠ .both := by
        intro k
        simpa [graphs, hnclose, profiledRawJointPhysicalGraphTail,
          OmegaWord.drop, Nat.add_assoc] using
            hnoboth (close + k)
      exact
        profiledRawJointHybridMegaGuarded_accepts_of_coupled_rightPrefix_leftClose
          A strategy hwin controllers initialBank fallbackTag installation
            oldOutputOne oldOutputTwo env start n hphysical hentryRight hright
              hclose hterm hnoBothDrop
  | left =>
      have hexists : ∃ close : Nat, graphs close ≠ .left := by
        rcases hstrict.2 0 with ⟨close, _hclose, hright⟩
        change graphs close = .right at hright
        exact ⟨close, by rw [hright]; exact Graph.noConfusion⟩
      let close := Nat.find hexists
      have hcloseNe : graphs close ≠ .left := Nat.find_spec hexists
      have hbefore : ∀ k : Nat, k < close → graphs k = .left := by
        intro k hk
        by_contra hne
        exact (Nat.find_min hexists hk) hne
      have hclosePos : 0 < close := by
        by_contra hnot
        have hzero : close = 0 := by omega
        exact hcloseNe (by simpa [hzero] using hgraphZero)
      have hcloseRight : graphs close = .right := by
        cases hcloseGraph : graphs close with
        | left => exact False.elim (hcloseNe hcloseGraph)
        | right => rfl
        | both => exact False.elim (hnoboth close hcloseGraph)
      let n := close - 1
      have hnclose : n + 1 = close := by
        dsimp only [n]
        omega
      have hleft : ∀ k : Nat, k < n + 1 →
          (env (start + k)).graph = .left := by
        intro k hk
        exact hbefore k (by simpa [hnclose] using hk)
      have hclose : (env (start + (n + 1))).graph = .right := by
        simpa [graphs, hnclose] using hcloseRight
      have hstrictDrop := BothStrictDirectionsRecurrent.drop hstrict close
      have hterm : OperationalStrictRunsTerminate
          (profiledRawJointPhysicalGraphTail
            (OmegaWord.drop env (start + (n + 1))) 0) := by
        unfold profiledRawJointPhysicalGraphTail
        unfold OmegaWord.drop
        simp only [Nat.zero_add]
        simpa [graphs, hnclose, Nat.add_assoc] using
            (operationalStrictRunsTerminate_of_bothStrictDirectionsRecurrent
              hstrictDrop)
      have hnoBothDrop : ∀ k : Nat,
          profiledRawJointPhysicalGraphTail
              (OmegaWord.drop env (start + (n + 1))) 0 k ≠ .both := by
        intro k
        simpa [graphs, hnclose, profiledRawJointPhysicalGraphTail,
          OmegaWord.drop, Nat.add_assoc] using
            hnoboth (close + k)
      exact
        profiledRawJointHybridMegaGuarded_accepts_of_coupled_leftPrefix_rightClose
          A strategy hwin controllers initialBank fallbackTag installation
            oldOutputOne oldOutputTwo env start n hphysical hentryLeft hleft
              hclose hterm hnoBothDrop

end

end DetParityAutomaton

end DistributedSynthesis
