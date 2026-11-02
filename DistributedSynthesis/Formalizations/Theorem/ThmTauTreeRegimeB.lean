/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmTauTreeAccepts
import DistributedSynthesis.Formalizations.Theorem.ThmGlobalTreeWinning

/-!
# Regime (b): a branch trapped in a left block

The second parity regime of the tau-tree acceptance.  A never-sinking
branch that is eventually confined to a single left block has, in its
tail, run priorities equal to the left checker's control fold along
the block's sender word (shifted by the even global shift).  The
checker verdict on that block comes from `winning_iff`: every
environment thread of the narrowed block is a consistent play of the
uniformization game and hence wins, so the block's narrowed tree is
universally winning, the checker wins its subtree, and the branch tail
is min-even once the even shift is stripped.

This file develops the left orientation; the right is the mirror.
-/

set_option linter.unusedSectionVars false

namespace DistributedSynthesis

universe u v x y s

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}

namespace DetParityAutomaton

variable
  {A :
    DetParityAutomaton.{max u v x y, s}
      (RoundRecord In₁ In₂ Graph Out₁ Out₂)}

variable [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
variable [DecidableEq In₁] [DecidableEq In₂] [DecidableEq A.State]
variable (CL : LeftThreadChecker (In₁ := In₁) A)
variable (CR : RightThreadChecker (In₁ := In₁) A)
variable (CC : ChainThreadChecker (In₁ := In₁) (A := A))
variable [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]

/-- The narrowed left-block label tree below a node of an arbitrary
labeled journal tree. -/
def leftBlockNarrowed
    (tree :
      LabeledTree (GlobalJournalBranch (In₁ := In₁) A)
        (GlobalJournalLabel (In₁ := In₁) A))
    (node₀ : TreeNode (GlobalJournalBranch (In₁ := In₁) A)) :
    LabeledTree In₂
      (NarrowedBlockLabel In₁ In₂ Out₁ Out₂ (A.State × A.State)) :=
  fun w =>
    GlobalJournalLabel.leftNarrowed (tree (node₀ ++ senderLNode (A := A) w))

@[simp]
theorem leftBlockNarrowed_nil
    (tree :
      LabeledTree (GlobalJournalBranch (In₁ := In₁) A)
        (GlobalJournalLabel (In₁ := In₁) A))
    (node₀ : TreeNode (GlobalJournalBranch (In₁ := In₁) A)) :
    leftBlockNarrowed tree node₀ [] =
      GlobalJournalLabel.leftNarrowed (tree node₀) := by
  simp [leftBlockNarrowed, senderLNode]

/-- Within a trapped left block the run threads the left checker
through the narrowed labels. -/
theorem globalRunIn_block_left
    (tree :
      LabeledTree (GlobalJournalBranch (In₁ := In₁) A)
        (GlobalJournalLabel (In₁ := In₁) A))
    (node₀ : TreeNode (GlobalJournalBranch (In₁ := In₁) A))
    (atom₀ : A.State × A.State)
    (hrun₀ :
      globalRunIn CL CR CC tree (Sum.inl (A.initial, A.initial)) node₀ =
        Sum.inl atom₀) :
    ∀ (w : TreeNode In₂) (x : In₂),
      ∃ threads,
        globalRunIn CL CR CC tree (Sum.inl (A.initial, A.initial))
            (node₀ ++ senderLNode (A := A) (w ++ [x])) =
          Sum.inr (Sum.inl
            (DeterministicBlockMonitor.controlIn CL.monitor
                (leftBlockNarrowed tree node₀) (CL.start atom₀.1)
                (w ++ [x]),
              threads)) := by
  intro w
  induction w using List.reverseRecOn with
  | nil =>
      intro x
      refine
        ⟨leftOpenSubset atom₀
          (GlobalJournalLabel.leftNarrowed (tree node₀)) x, ?_⟩
      rw [show senderLNode (A := A) (([] : TreeNode In₂) ++ [x]) =
        [Sum.inr (Sum.inl x)] from rfl]
      rw [globalRunIn_append, hrun₀]
      show
        globalJournalStep A CL CR CC (Sum.inl atom₀) (tree node₀)
            (Sum.inr (Sum.inl x)) =
          Sum.inr (Sum.inl
            (CL.monitor.step (CL.start atom₀.1)
                (leftBlockNarrowed tree node₀ []) x,
              leftOpenSubset atom₀
                (GlobalJournalLabel.leftNarrowed (tree node₀)) x))
      rw [leftBlockNarrowed_nil]
      rfl
  | append_singleton w x' ih =>
      intro x
      obtain ⟨threads, hih⟩ := ih x'
      refine
        ⟨leftStepSubset threads
            (GlobalJournalLabel.leftNarrowed
              (tree (node₀ ++ senderLNode (A := A) (w ++ [x'])))) x, ?_⟩
      rw [show node₀ ++ senderLNode (A := A) ((w ++ [x']) ++ [x]) =
        (node₀ ++ senderLNode (A := A) (w ++ [x'])) ++
          [Sum.inr (Sum.inl x)] from by
        rw [senderLNode_append (A := A) (w ++ [x']) x, List.append_assoc]]
      rw [globalRunIn_append, hih,
        DeterministicBlockMonitor.controlIn_append CL.monitor (w ++ [x'])]
      simp only [globalJournalStep, leftBlockNarrowed]

/-- The narrowed right-block label tree below a node. -/
def rightBlockNarrowed
    (tree :
      LabeledTree (GlobalJournalBranch (In₁ := In₁) A)
        (GlobalJournalLabel (In₁ := In₁) A))
    (node₀ : TreeNode (GlobalJournalBranch (In₁ := In₁) A)) :
    LabeledTree In₁
      (NarrowedBlockLabel In₂ In₁ Out₂ Out₁ (A.State × A.State)) :=
  fun w =>
    GlobalJournalLabel.rightNarrowed (tree (node₀ ++ senderRNode (A := A) w))

@[simp]
theorem rightBlockNarrowed_nil
    (tree :
      LabeledTree (GlobalJournalBranch (In₁ := In₁) A)
        (GlobalJournalLabel (In₁ := In₁) A))
    (node₀ : TreeNode (GlobalJournalBranch (In₁ := In₁) A)) :
    rightBlockNarrowed tree node₀ [] =
      GlobalJournalLabel.rightNarrowed (tree node₀) := by
  simp [rightBlockNarrowed, senderRNode]

/-- Within a trapped right block the run threads the right checker
through the narrowed labels. -/
theorem globalRunIn_block_right
    (tree :
      LabeledTree (GlobalJournalBranch (In₁ := In₁) A)
        (GlobalJournalLabel (In₁ := In₁) A))
    (node₀ : TreeNode (GlobalJournalBranch (In₁ := In₁) A))
    (atom₀ : A.State × A.State)
    (hrun₀ :
      globalRunIn CL CR CC tree (Sum.inl (A.initial, A.initial)) node₀ =
        Sum.inl atom₀) :
    ∀ (w : TreeNode In₁) (x : In₁),
      ∃ threads,
        globalRunIn CL CR CC tree (Sum.inl (A.initial, A.initial))
            (node₀ ++ senderRNode (A := A) (w ++ [x])) =
          Sum.inr (Sum.inr (Sum.inl
            (DeterministicBlockMonitor.controlIn CR.monitor
                (rightBlockNarrowed tree node₀) (CR.start atom₀.1)
                (w ++ [x]),
              threads))) := by
  intro w
  induction w using List.reverseRecOn with
  | nil =>
      intro x
      refine
        ⟨rightOpenSubset atom₀
          (GlobalJournalLabel.rightNarrowed (tree node₀)) x, ?_⟩
      rw [show senderRNode (A := A) (([] : TreeNode In₁) ++ [x]) =
        [Sum.inr (Sum.inr x)] from rfl]
      rw [globalRunIn_append, hrun₀]
      show
        globalJournalStep A CL CR CC (Sum.inl atom₀) (tree node₀)
            (Sum.inr (Sum.inr x)) =
          Sum.inr (Sum.inr (Sum.inl
            (CR.monitor.step (CR.start atom₀.1)
                (rightBlockNarrowed tree node₀ []) x,
              rightOpenSubset atom₀
                (GlobalJournalLabel.rightNarrowed (tree node₀)) x)))
      rw [rightBlockNarrowed_nil]
      rfl
  | append_singleton w x' ih =>
      intro x
      obtain ⟨threads, hih⟩ := ih x'
      refine
        ⟨rightStepSubset threads
            (GlobalJournalLabel.rightNarrowed
              (tree (node₀ ++ senderRNode (A := A) (w ++ [x'])))) x, ?_⟩
      rw [show node₀ ++ senderRNode (A := A) ((w ++ [x']) ++ [x]) =
        (node₀ ++ senderRNode (A := A) (w ++ [x'])) ++
          [Sum.inr (Sum.inr x)] from by
        rw [senderRNode_append (A := A) (w ++ [x']) x, List.append_assoc]]
      rw [globalRunIn_append, hih,
        DeterministicBlockMonitor.controlIn_append CR.monitor (w ++ [x'])]
      simp only [globalJournalStep, rightBlockNarrowed]

section Winner

variable [Countable In₁] [Countable In₂] [Countable Out₁] [Countable Out₂]

variable (σ : StrategyPair In₁ In₂ Out₁ Out₂)
variable
  (τ :
    (uniformizationGame A σ).PositionalStrategy ParityPlayer.even)

/-- A boundary state reached by the run is reachable by a consistent
play. -/
theorem reaches_bnd_of_run_inl
    (node : TreeNode (GlobalJournalBranch (In₁ := In₁) A))
    (atom : A.State × A.State)
    (h :
      globalRunIn CL CR CC (tauTree σ τ) (Sum.inl (A.initial, A.initial))
          node =
        Sum.inl atom) :
    Reaches σ τ (.bnd atom) := by
  rcases runGood σ τ CL CR CC node with hs | ⟨a, -, hr, hre⟩ |
    ⟨a, w, c, t, -, hr, -⟩ | ⟨a, w, c, t, -, hr, -⟩ |
    ⟨w, c, t, -, hr, -⟩ | ⟨w, c, t, -, hr, -⟩
  · rw [h] at hs
    exact absurd hs (by simp)
  · have : a = atom := Sum.inl.inj (hr.symm.trans h)
    subst this
    exact hre
  · rw [h] at hr
    exact absurd hr (by simp)
  · rw [h] at hr
    exact absurd hr (by simp)
  · rw [h] at hr
    exact absurd hr (by simp)
  · rw [h] at hr
    exact absurd hr (by simp)

/-- A boundary state carried by the run parses as an atom node. -/
theorem tauNodeState_atNode_of_run_inl
    (node : TreeNode (GlobalJournalBranch (In₁ := In₁) A))
    (atom : A.State × A.State)
    (h :
      globalRunIn CL CR CC (tauTree σ τ) (Sum.inl (A.initial, A.initial))
          node =
        Sum.inl atom) :
    tauNodeState (In₂ := In₂) node = .atNode atom := by
  rcases runGood σ τ CL CR CC node with hs | ⟨a, hpar, hr, -⟩ |
    ⟨a, w, c, t, -, hr, -⟩ | ⟨a, w, c, t, -, hr, -⟩ |
    ⟨w, c, t, -, hr, -⟩ | ⟨w, c, t, -, hr, -⟩
  · rw [h] at hs
    exact absurd hs (by simp)
  · have : a = atom := Sum.inl.inj (hr.symm.trans h)
    subst this
    exact hpar
  · rw [h] at hr
    exact absurd hr (by simp)
  · rw [h] at hr
    exact absurd hr (by simp)
  · rw [h] at hr
    exact absurd hr (by simp)
  · rw [h] at hr
    exact absurd hr (by simp)

/-! ### The environment-driven left-block play -/

/-- One step of the block play: follow the winner at Even positions,
open/continue the left block driven by the environment at Odd
positions. -/
noncomputable def advance (env : Nat -> In₁ × In₂) :
    UniformizationPosition (In₁ := In₁) A ->
      UniformizationPosition (In₁ := In₁) A
  | .committed atom h => .opening atom h (env 0)
  | .openingResolve atom h move o1 _o2 => uOpenLeftTarget σ atom h move o1
  | .blockEnvL h word q mn tbl => .recvL h word q mn tbl (env word.length)
  | .resolveL h word q mn _tbl move o1 =>
      uContinueLTarget σ h word q mn move o1
  | .blockEnvR h word q mn tbl => .recvR h word q mn tbl default
  | .resolveR h word q mn _tbl move o2 =>
      uContinueRTarget σ h word q mn move o2
  | .closeResolveL _ _ q mn _tbl move o1 o2 =>
      uCloseTarget (A := A) q mn move o1 o2
  | .closeResolveR _ _ q mn _tbl move o2 o1 =>
      uCloseTarget (A := A) q mn move o1 o2
  | .revEnvL hc word eqs ems q mn tbl =>
      .revRecvL hc word eqs ems q mn tbl default
  | .revResolveL hc word eqs ems q mn _tbl move o1r _o2r =>
      uRevContinueLTarget σ hc word eqs ems q mn move o1r
  | .revEnvR hc word eqs ems q mn tbl =>
      .revRecvR hc word eqs ems q mn tbl default
  | .revResolveR hc word eqs ems q mn _tbl move _o1r o2r =>
      uRevContinueRTarget σ hc word eqs ems q mn move o2r
  | pos => τ.move pos

/-- Every step of `advance` is a legal move of the uniformization
game. -/
theorem advance_step (env : Nat -> In₁ × In₂)
    (pos : UniformizationPosition (In₁ := In₁) A) :
    (uniformizationGame A σ).step pos (advance σ τ env pos) := by
  cases pos with
  | committed atom h => exact ⟨env 0, rfl⟩
  | openingResolve atom h move o1 o2 => exact Or.inr (Or.inl rfl)
  | blockEnvL h word q mn tbl => exact ⟨env word.length, rfl⟩
  | resolveL h word q mn tbl move o1 => exact Or.inl rfl
  | blockEnvR h word q mn tbl => exact ⟨default, rfl⟩
  | resolveR h word q mn tbl move o2 => exact Or.inl rfl
  | closeResolveL h word q mn tbl move o1 o2 => exact Or.inl rfl
  | closeResolveR h word q mn tbl move o2 o1 => exact Or.inl rfl
  | revEnvL hc word eqs ems q mn tbl => exact ⟨default, rfl⟩
  | revResolveL hc word eqs ems q mn tbl move o1r o2r => exact Or.inl rfl
  | revEnvR hc word eqs ems q mn tbl => exact ⟨default, rfl⟩
  | revResolveR hc word eqs ems q mn tbl move o1r o2r => exact Or.inl rfl
  | bnd atom => exact τ.legal (.bnd atom) rfl
  | opening atom h move => exact τ.legal (.opening atom h move) rfl
  | blockL h word q mn => exact τ.legal (.blockL h word q mn) rfl
  | recvL h word q mn tbl move =>
      exact τ.legal (.recvL h word q mn tbl move) rfl
  | closeL h word q mn tbl move o1 =>
      exact τ.legal (.closeL h word q mn tbl move o1) rfl
  | blockR h word q mn => exact τ.legal (.blockR h word q mn) rfl
  | recvR h word q mn tbl move =>
      exact τ.legal (.recvR h word q mn tbl move) rfl
  | closeR h word q mn tbl move o2 =>
      exact τ.legal (.closeR h word q mn tbl move o2) rfl
  | revCommitL word eqs ems =>
      exact τ.legal (.revCommitL word eqs ems) rfl
  | revBlockL hc word eqs ems q mn =>
      exact τ.legal (.revBlockL hc word eqs ems q mn) rfl
  | revRecvL hc word eqs ems q mn tbl move =>
      exact τ.legal (.revRecvL hc word eqs ems q mn tbl move) rfl
  | revCommitR word eqs ems =>
      exact τ.legal (.revCommitR word eqs ems) rfl
  | revBlockR hc word eqs ems q mn =>
      exact τ.legal (.revBlockR hc word eqs ems q mn) rfl
  | revRecvR hc word eqs ems q mn tbl move =>
      exact τ.legal (.revRecvR hc word eqs ems q mn tbl move) rfl

/-- At Even positions `advance` follows the winner. -/
theorem advance_eq_tau_of_even (env : Nat -> In₁ × In₂)
    (pos : UniformizationPosition (In₁ := In₁) A)
    (h : (uniformizationGame A σ).owner pos = ParityPlayer.even) :
    advance σ τ env pos = τ.move pos := by
  cases pos with
  | bnd atom => rfl
  | opening atom h move => rfl
  | blockL h word q mn => rfl
  | recvL h word q mn tbl move => rfl
  | closeL h word q mn tbl move o1 => rfl
  | blockR h word q mn => rfl
  | recvR h word q mn tbl move => rfl
  | closeR h word q mn tbl move o2 => rfl
  | revCommitL word eqs ems => rfl
  | revBlockL hc word eqs ems q mn => rfl
  | revRecvL hc word eqs ems q mn tbl move => rfl
  | revCommitR word eqs ems => rfl
  | revBlockR hc word eqs ems q mn => rfl
  | revRecvR hc word eqs ems q mn tbl move => rfl
  | committed atom h' =>
      simp [uniformizationGame, uniformizationOwner] at h
  | openingResolve atom h' move o1 o2 =>
      simp [uniformizationGame, uniformizationOwner] at h
  | blockEnvL h' word q mn tbl =>
      simp [uniformizationGame, uniformizationOwner] at h
  | resolveL h' word q mn tbl move o1 =>
      simp [uniformizationGame, uniformizationOwner] at h
  | blockEnvR h' word q mn tbl =>
      simp [uniformizationGame, uniformizationOwner] at h
  | resolveR h' word q mn tbl move o2 =>
      simp [uniformizationGame, uniformizationOwner] at h
  | closeResolveL h' word q mn tbl move o1 o2 =>
      simp [uniformizationGame, uniformizationOwner] at h
  | closeResolveR h' word q mn tbl move o2 o1 =>
      simp [uniformizationGame, uniformizationOwner] at h
  | revEnvL hc word eqs ems q mn tbl =>
      simp [uniformizationGame, uniformizationOwner] at h
  | revResolveL hc word eqs ems q mn tbl move o1r o2r =>
      simp [uniformizationGame, uniformizationOwner] at h
  | revEnvR hc word eqs ems q mn tbl =>
      simp [uniformizationGame, uniformizationOwner] at h
  | revResolveR hc word eqs ems q mn tbl move o1r o2r =>
      simp [uniformizationGame, uniformizationOwner] at h

variable (atom₀ : A.State × A.State)

/-- The block play following the environment from the boundary
`atom₀`. -/
noncomputable def blockLeftPlay (env : Nat -> In₁ × In₂) :
    Nat -> UniformizationPosition (In₁ := In₁) A
  | 0 => .bnd atom₀
  | t + 1 => advance σ τ env (blockLeftPlay env t)

theorem blockLeftPlay_zero (env : Nat -> In₁ × In₂) :
    blockLeftPlay σ τ atom₀ env 0 = .bnd atom₀ :=
  rfl

theorem blockLeftPlay_succ (env : Nat -> In₁ × In₂) (t : Nat) :
    blockLeftPlay σ τ atom₀ env (t + 1) =
      advance σ τ env (blockLeftPlay σ τ atom₀ env t) :=
  rfl

theorem blockLeftPlay_step (env : Nat -> In₁ × In₂) (t : Nat) :
    (uniformizationGame A σ).step (blockLeftPlay σ τ atom₀ env t)
      (blockLeftPlay σ τ atom₀ env (t + 1)) :=
  advance_step σ τ env (blockLeftPlay σ τ atom₀ env t)

theorem blockLeftPlay_consistent (env : Nat -> In₁ × In₂) :
    ∀ t : Nat,
      (uniformizationGame A σ).owner (blockLeftPlay σ τ atom₀ env t) =
          ParityPlayer.even ->
        blockLeftPlay σ τ atom₀ env (t + 1) =
          τ.move (blockLeftPlay σ τ atom₀ env t) := by
  intro t h
  rw [blockLeftPlay_succ]
  exact advance_eq_tau_of_even σ τ env _ h

/-! ### Splicing a continuation onto a reached prefix -/

/-- A consistent continuation from a reached position, spliced onto
the prefix that reaches it, inherits the winner's min-even parity. -/
theorem minPriorityEven_of_reaches_cont
    (hwin :
      CountableParityGame.PositionalStrategy.WinningFrom
        (G := uniformizationGame A σ) τ (.bnd (A.initial, A.initial)))
    (start : UniformizationPosition (In₁ := In₁) A)
    (hstart : Reaches σ τ start)
    (cont : Nat -> UniformizationPosition (In₁ := In₁) A)
    (hc0 : cont 0 = start)
    (hstep :
      ∀ n, (uniformizationGame A σ).step (cont n) (cont (n + 1)))
    (hcons :
      ∀ n,
        (uniformizationGame A σ).owner (cont n) = ParityPlayer.even ->
          cont (n + 1) = τ.move (cont n)) :
    (uniformizationGame A σ).MinPriorityEven cont := by
  obtain ⟨p, N, hpf, hpc, hpN⟩ := hstart
  have hqtail :
      ∀ n, (fun m => if m ≤ N then p m else cont (m - N)) (N + n) =
        cont n := by
    intro n
    simp only []
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · subst h0
      rw [Nat.add_zero, if_pos (Nat.le_refl N), hpN, hc0]
    · rw [if_neg (by omega), show N + n - N = n by omega]
  have hqplay :
      (uniformizationGame A σ).PlayFrom (.bnd (A.initial, A.initial))
        (fun m => if m ≤ N then p m else cont (m - N)) := by
    refine ⟨?_, ?_⟩
    · simp only []
      rw [if_pos (Nat.zero_le N)]
      exact hpf.1
    · intro m
      simp only []
      rcases Nat.lt_trichotomy m N with hlt | heq | hgt
      · rw [if_pos (by omega), if_pos (by omega)]
        exact hpf.2 m
      · subst heq
        rw [if_pos (Nat.le_refl m), if_neg (by omega),
          show m + 1 - m = 1 by omega, hpN]
        have h0 := hstep 0
        rw [hc0] at h0
        exact h0
      · rw [if_neg (by omega), if_neg (by omega),
          show m + 1 - N = m - N + 1 by omega]
        exact hstep (m - N)
  have hqcons :
      CountableParityGame.PositionalStrategy.Consistent
        (G := uniformizationGame A σ) τ
        (fun m => if m ≤ N then p m else cont (m - N)) := by
    intro m hm
    simp only [] at hm ⊢
    rcases Nat.lt_trichotomy m N with hlt | heq | hgt
    · rw [if_pos (by omega)] at hm ⊢
      rw [if_pos (by omega)]
      exact hpc m hm
    · subst heq
      rw [if_pos (Nat.le_refl m)] at hm ⊢
      rw [if_neg (by omega), show m + 1 - m = 1 by omega]
      rw [hpN] at hm ⊢
      have hcc := hcons 0 (by rw [hc0]; exact hm)
      rw [hc0] at hcc
      exact hcc
    · rw [if_neg (by omega)] at hm ⊢
      rw [if_neg (by omega), show m + 1 - N = m - N + 1 by omega]
      exact hcons (m - N) hm
  have hqwin :
      (uniformizationGame A σ).MinPriorityEven
        (fun m => if m ≤ N then p m else cont (m - N)) :=
    hwin _ hqplay hqcons
  have hs :
      NatSeqMinEvenParity
        (fun m =>
          (uniformizationGame A σ).priority
            ((fun m => if m ≤ N then p m else cont (m - N)) m)) :=
    hqwin
  have hshift :=
    (natSeqMinEvenParity_shift
      (fun m =>
        (uniformizationGame A σ).priority
          ((fun m => if m ≤ N then p m else cont (m - N)) m))
      N).mpr hs
  show
    NatSeqMinEvenParity
      (fun n => (uniformizationGame A σ).priority (cont n))
  have heq :
      (fun n => (uniformizationGame A σ).priority (cont n)) =
        fun n =>
          (uniformizationGame A σ).priority
            ((fun m => if m ≤ N then p m else cont (m - N)) (N + n)) := by
    funext n
    rw [hqtail n]
  rw [heq]
  exact hshift

/-! ### Label alignment of the narrowed block tree -/

/-- Below an atom node, adding sender inputs parses into a left
block. -/
theorem tauNodeState_senderLNode_snoc
    (node₀ : TreeNode (GlobalJournalBranch (In₁ := In₁) A))
    (atom₀ : A.State × A.State)
    (hp : tauNodeState (In₂ := In₂) node₀ = .atNode atom₀)
    (w : TreeNode In₂) (x : In₂) :
    tauNodeState (In₂ := In₂) (node₀ ++ senderLNode (A := A) (w ++ [x])) =
      .inLeft atom₀ (w ++ [x]) := by
  induction w using List.reverseRecOn generalizing x with
  | nil =>
      rw [show senderLNode (A := A) (([] : TreeNode In₂) ++ [x]) =
        [Sum.inr (Sum.inl x)] from rfl, tauNodeState_append, hp]
      rfl
  | append_singleton w x' ih =>
      rw [show senderLNode (A := A) ((w ++ [x']) ++ [x]) =
        senderLNode (A := A) (w ++ [x']) ++ [Sum.inr (Sum.inl x)] from by
        rw [senderLNode_append], ← List.append_assoc,
        tauNodeState_append, ih x']
      rfl

/-- The narrowed label below an atom node, on a nonempty sender word,
is the in-block table. -/
theorem leftBlockNarrowed_tauTree_snoc
    (node₀ : TreeNode (GlobalJournalBranch (In₁ := In₁) A))
    (atom₀ : A.State × A.State)
    (hp : tauNodeState (In₂ := In₂) node₀ = .atNode atom₀)
    (w : TreeNode In₂) (x : In₂) :
    leftBlockNarrowed (tauTree σ τ) node₀ (w ++ [x]) =
      tauLeftLabel σ τ atom₀ (w ++ [x]) := by
  show
    GlobalJournalLabel.leftNarrowed
        (tauLabelOf σ τ
          (tauNodeState (node₀ ++ senderLNode (A := A) (w ++ [x])))) =
      _
  rw [tauNodeState_senderLNode_snoc node₀ atom₀ hp w x]
  rfl

/-- The narrowed label below an atom node, on the empty sender word,
is the opening table. -/
theorem leftBlockNarrowed_tauTree_nil
    (node₀ : TreeNode (GlobalJournalBranch (In₁ := In₁) A))
    (atom₀ : A.State × A.State)
    (hp : tauNodeState (In₂ := In₂) node₀ = .atNode atom₀) :
    leftBlockNarrowed (tauTree σ τ) node₀ [] =
      tauOpeningLeftLabel σ τ atom₀ := by
  rw [leftBlockNarrowed_nil]
  show GlobalJournalLabel.leftNarrowed (tauLabelOf σ τ (tauNodeState node₀)) = _
  rw [hp]
  rfl

/-! ### Three-step block advance and prelude -/

variable (atom₀ : A.State × A.State) (env : Nat -> In₁ × In₂)

theorem blockLeftPlay_one :
    blockLeftPlay σ τ atom₀ env 1 =
      .committed atom₀ (commitmentOf σ τ atom₀) := by
  show advance σ τ env (blockLeftPlay σ τ atom₀ env 0) = _
  rw [blockLeftPlay_zero]
  exact commitmentOf_spec σ τ atom₀

theorem blockLeftPlay_two :
    blockLeftPlay σ τ atom₀ env 2 =
      .opening atom₀ (commitmentOf σ τ atom₀) (env 0) := by
  show advance σ τ env (blockLeftPlay σ τ atom₀ env 1) = _
  rw [blockLeftPlay_one]
  rfl

theorem blockLeftPlay_three :
    blockLeftPlay σ τ atom₀ env 3 =
      .openingResolve atom₀ (commitmentOf σ τ atom₀) (env 0)
        (openingChoice σ τ atom₀ (env 0)).1
        (openingChoice σ τ atom₀ (env 0)).2 := by
  show advance σ τ env (blockLeftPlay σ τ atom₀ env 2) = _
  rw [blockLeftPlay_two]
  exact openingChoice_spec σ τ atom₀ (env 0)

/-- Four advance steps from a left-block position produce the next
left-block position: commit the reversal table, receive the
environment move, answer, and continue. -/
theorem blockAdvance4_blockL (word : List In₂) (q mn : A.State) :
    advance σ τ env
        (advance σ τ env
          (advance σ τ env
            (advance σ τ env
              (.blockL (commitmentOf σ τ atom₀) word q mn)))) =
      .blockL (commitmentOf σ τ atom₀) (word ++ [(env word.length).2])
        (A.step q
          (leftRoundRecord (env word.length)
            (recvChoiceL σ τ atom₀ word q mn (env word.length))
            (blockSenderTwo σ (commitmentOf σ τ atom₀) word
              (env word.length).2)))
        (A.minPriorityState mn
          (A.step q
            (leftRoundRecord (env word.length)
              (recvChoiceL σ τ atom₀ word q mn (env word.length))
              (blockSenderTwo σ (commitmentOf σ τ atom₀) word
                (env word.length).2)))) := by
  rw [show
    advance σ τ env (.blockL (commitmentOf σ τ atom₀) word q mn) =
      τ.move (.blockL (commitmentOf σ τ atom₀) word q mn) from rfl,
    blockRevTableL_spec σ τ atom₀ word q mn]
  show
    advance σ τ env
        (advance σ τ env
          (.recvL (commitmentOf σ τ atom₀) word q mn
            (blockRevTableL σ τ atom₀ word q mn) (env word.length))) =
      _
  rw [show
    advance σ τ env
        (.recvL (commitmentOf σ τ atom₀) word q mn
          (blockRevTableL σ τ atom₀ word q mn) (env word.length)) =
      τ.move
        (.recvL (commitmentOf σ τ atom₀) word q mn
          (blockRevTableL σ τ atom₀ word q mn) (env word.length))
    from rfl,
    recvChoiceL_spec σ τ atom₀ word q mn (env word.length)]
  rfl

/-! ### The tracking induction -/

theorem senderWord_branchNode_length (k : Nat) :
    (senderWord (branchNode env k)).length = k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [show branchNode env (k + 1) = branchNode env k ++ [env k]
          from rfl, senderWord_append, List.length_append, ih]
      rfl

theorem narrowedThreadState_succ (node₀ : TreeNode (GlobalJournalBranch (In₁ := In₁) A))
    (k : Nat) :
    narrowedThreadState (A.leftBlockMonitor atom₀.1)
        (leftBlockNarrowed (tauTree σ τ) node₀) env (k + 1) =
      (A.leftBlockMonitor atom₀.1).step
        (narrowedThreadState (A.leftBlockMonitor atom₀.1)
          (leftBlockNarrowed (tauTree σ τ) node₀) env k)
        (narrowedRecord (A.leftBlockMonitor atom₀.1)
          (leftBlockNarrowed (tauTree σ τ) node₀
            (senderWord (branchNode env k)))
          (narrowedThreadState (A.leftBlockMonitor atom₀.1)
            (leftBlockNarrowed (tauTree σ τ) node₀) env k)
          (env k)) := by
  show
    narrowedControl (A.leftBlockMonitor atom₀.1)
        (leftBlockNarrowed (tauTree σ τ) node₀) (branchNode env (k + 1)) =
      _
  rw [show branchNode env (k + 1) = branchNode env k ++ [env k] from rfl,
    narrowedControl_append (A.leftBlockMonitor atom₀.1)
      (leftBlockNarrowed (tauTree σ τ) node₀) (branchNode env k) (env k)]
  rfl

/-- The narrowed label at a nonempty sender word of the play is the
in-block table. -/
theorem leftBlockNarrowed_senderWord
    (node₀ : TreeNode (GlobalJournalBranch (In₁ := In₁) A))
    (hp : tauNodeState (In₂ := In₂) node₀ = .atNode atom₀) (k : Nat) :
    leftBlockNarrowed (tauTree σ τ) node₀
        (senderWord (branchNode env (k + 1))) =
      tauLeftLabel σ τ atom₀ (senderWord (branchNode env (k + 1))) := by
  rw [show senderWord (branchNode env (k + 1)) =
      senderWord (branchNode env k) ++ [(env k).2] from by
      rw [show branchNode env (k + 1) = branchNode env k ++ [env k]
          from rfl, senderWord_append]]
  exact
    leftBlockNarrowed_tauTree_snoc σ τ node₀ atom₀ hp
      (senderWord (branchNode env k)) ((env k).2)

/-- The round positions of the block play track the narrowed thread
fold of the trapped block. -/
theorem blockLeftPlay_blockL
    (node₀ : TreeNode (GlobalJournalBranch (In₁ := In₁) A))
    (hp : tauNodeState (In₂ := In₂) node₀ = .atNode atom₀) :
    ∀ k : Nat,
      blockLeftPlay σ τ atom₀ env (4 * k + 4) =
        .blockL (commitmentOf σ τ atom₀)
          (senderWord (branchNode env (k + 1)))
          (narrowedThreadState (A.leftBlockMonitor atom₀.1)
            (leftBlockNarrowed (tauTree σ τ) node₀) env (k + 1)).1
          (narrowedThreadState (A.leftBlockMonitor atom₀.1)
            (leftBlockNarrowed (tauTree σ τ) node₀) env (k + 1)).2 := by
  intro k
  induction k with
  | zero =>
      rw [show blockLeftPlay σ τ atom₀ env 4 =
          advance σ τ env (blockLeftPlay σ τ atom₀ env 3) from rfl,
        blockLeftPlay_three,
        narrowedThreadState_succ σ τ atom₀ env node₀ 0,
        show senderWord (branchNode env 0) = ([] : List In₂) from rfl,
        leftBlockNarrowed_tauTree_nil σ τ node₀ atom₀ hp,
        show senderWord (branchNode env 1) = [(env 0).2] from rfl]
      rfl
  | succ k ih =>
      rw [show 4 * (k + 1) + 4 = (4 * k + 4) + 4 by ring,
        show blockLeftPlay σ τ atom₀ env ((4 * k + 4) + 4) =
          advance σ τ env
            (advance σ τ env
              (advance σ τ env
                (advance σ τ env
                  (blockLeftPlay σ τ atom₀ env (4 * k + 4)))))
          from rfl,
        ih,
        blockAdvance4_blockL σ τ atom₀ env
          (senderWord (branchNode env (k + 1)))
          (narrowedThreadState (A.leftBlockMonitor atom₀.1)
            (leftBlockNarrowed (tauTree σ τ) node₀) env (k + 1)).1
          (narrowedThreadState (A.leftBlockMonitor atom₀.1)
            (leftBlockNarrowed (tauTree σ τ) node₀) env (k + 1)).2,
        senderWord_branchNode_length env (k + 1),
        narrowedThreadState_succ σ τ atom₀ env node₀ (k + 1),
        leftBlockNarrowed_senderWord σ τ atom₀ env node₀ hp k]
      congr 1
      rw [show branchNode env (k + 1 + 1) =
        branchNode env (k + 1) ++ [env (k + 1)] from rfl,
        senderWord_append]

/-! ### From play parity to thread parity -/

/-- Fourfold repetition preserves min-even parity. -/
theorem natSeqMinEvenParity_div4 {s : Nat -> Nat} :
    NatSeqMinEvenParity (fun t => s (t / 4)) ↔ NatSeqMinEvenParity s := by
  have hseen :
      ∀ p, NatSeqSeenInfinitelyOften (fun t => s (t / 4)) p ↔
        NatSeqSeenInfinitelyOften s p := by
    intro p
    constructor
    · intro hinf n
      obtain ⟨k, hk, hval⟩ := hinf (4 * n)
      exact ⟨k / 4, by omega, hval⟩
    · intro hinf n
      obtain ⟨j, hj, hval⟩ := hinf n
      refine ⟨4 * j, by omega, ?_⟩
      show s (4 * j / 4) = p
      rw [show 4 * j / 4 = j by omega]
      exact hval
  constructor
  · rintro ⟨p, hpEven, hpSeen, hpMin⟩
    exact
      ⟨p, hpEven, (hseen p).mp hpSeen,
        fun q hq => hpMin q ((hseen q).mpr hq)⟩
  · rintro ⟨p, hpEven, hpSeen, hpMin⟩
    exact
      ⟨p, hpEven, (hseen p).mpr hpSeen,
        fun q hq => hpMin q ((hseen q).mp hq)⟩

/-- Within a block the table-commit position keeps the round state. -/
theorem blockEnvL_priority (word : List In₂) (q mn : A.State) :
    uniformizationPriority
        (advance σ τ env (.blockL (commitmentOf σ τ atom₀) word q mn)) =
      A.priority q := by
  rw [show
    advance σ τ env (.blockL (commitmentOf σ τ atom₀) word q mn) =
      τ.move (.blockL (commitmentOf σ τ atom₀) word q mn) from rfl,
    blockRevTableL_spec σ τ atom₀ word q mn]
  rfl

/-- Within a block the recv position keeps the round state. -/
theorem recvL_priority (word : List In₂) (q mn : A.State) :
    uniformizationPriority
        (advance σ τ env
          (advance σ τ env
            (.blockL (commitmentOf σ τ atom₀) word q mn))) =
      A.priority q := by
  rw [show
    advance σ τ env (.blockL (commitmentOf σ τ atom₀) word q mn) =
      τ.move (.blockL (commitmentOf σ τ atom₀) word q mn) from rfl,
    blockRevTableL_spec σ τ atom₀ word q mn]
  rfl

/-- Within a block the resolve position keeps the round state. -/
theorem resolveL_priority (word : List In₂) (q mn : A.State) :
    uniformizationPriority
        (advance σ τ env
          (advance σ τ env
            (advance σ τ env
              (.blockL (commitmentOf σ τ atom₀) word q mn)))) =
      A.priority q := by
  rw [show
    advance σ τ env (.blockL (commitmentOf σ τ atom₀) word q mn) =
      τ.move (.blockL (commitmentOf σ τ atom₀) word q mn) from rfl,
    blockRevTableL_spec σ τ atom₀ word q mn]
  show
    uniformizationPriority
        (advance σ τ env
          (.recvL (commitmentOf σ τ atom₀) word q mn
            (blockRevTableL σ τ atom₀ word q mn) (env word.length))) =
      _
  rw [show
    advance σ τ env
        (.recvL (commitmentOf σ τ atom₀) word q mn
          (blockRevTableL σ τ atom₀ word q mn) (env word.length)) =
      τ.move
        (.recvL (commitmentOf σ τ atom₀) word q mn
          (blockRevTableL σ τ atom₀ word q mn) (env word.length))
    from rfl,
    recvChoiceL_spec σ τ atom₀ word q mn (env word.length)]
  rfl

/-- The block play's priority at each round phase is the thread's
priority. -/
theorem blockLeftPlay_priority
    (node₀ : TreeNode (GlobalJournalBranch (In₁ := In₁) A))
    (hp : tauNodeState (In₂ := In₂) node₀ = .atNode atom₀) (t : Nat) :
    uniformizationPriority (blockLeftPlay σ τ atom₀ env (t + 4)) =
      (A.leftBlockMonitor atom₀.1).priority
        (narrowedThreadState (A.leftBlockMonitor atom₀.1)
          (leftBlockNarrowed (tauTree σ τ) node₀) env (t / 4 + 1)) := by
  obtain ⟨r, p, hp4, rfl⟩ :
      ∃ r p, p < 4 ∧ t = 4 * r + p := ⟨t / 4, t % 4, by omega, by omega⟩
  rw [show (4 * r + p) / 4 + 1 = r + 1 by omega,
    show (A.leftBlockMonitor atom₀.1).priority
        (narrowedThreadState (A.leftBlockMonitor atom₀.1)
          (leftBlockNarrowed (tauTree σ τ) node₀) env (r + 1)) =
      A.priority
        (narrowedThreadState (A.leftBlockMonitor atom₀.1)
          (leftBlockNarrowed (tauTree σ τ) node₀) env (r + 1)).1 from rfl]
  match r, p, hp4 with
  | r, 0, _ =>
      rw [show 4 * r + 0 + 4 = 4 * r + 4 by omega,
        blockLeftPlay_blockL σ τ atom₀ env node₀ hp r]
      rfl
  | r, 1, _ =>
      rw [show 4 * r + 1 + 4 = 4 * r + 4 + 1 by omega,
        show blockLeftPlay σ τ atom₀ env (4 * r + 4 + 1) =
          advance σ τ env (blockLeftPlay σ τ atom₀ env (4 * r + 4))
          from rfl,
        blockLeftPlay_blockL σ τ atom₀ env node₀ hp r,
        blockEnvL_priority]
  | r, 2, _ =>
      rw [show 4 * r + 2 + 4 = 4 * r + 4 + 1 + 1 by omega,
        show blockLeftPlay σ τ atom₀ env (4 * r + 4 + 1 + 1) =
          advance σ τ env
            (advance σ τ env (blockLeftPlay σ τ atom₀ env (4 * r + 4)))
          from rfl,
        blockLeftPlay_blockL σ τ atom₀ env node₀ hp r,
        recvL_priority]
  | r, 3, _ =>
      rw [show 4 * r + 3 + 4 = 4 * r + 4 + 1 + 1 + 1 by omega,
        show blockLeftPlay σ τ atom₀ env (4 * r + 4 + 1 + 1 + 1) =
          advance σ τ env
            (advance σ τ env
              (advance σ τ env (blockLeftPlay σ τ atom₀ env (4 * r + 4))))
          from rfl,
        blockLeftPlay_blockL σ τ atom₀ env node₀ hp r,
        resolveL_priority]

/-- Every environment thread of the trapped left block is min-even:
the block's narrowed tree is universally winning. -/
theorem narrowedAllThreadsWin_left
    (node₀ : TreeNode (GlobalJournalBranch (In₁ := In₁) A))
    (atom₀ : A.State × A.State)
    (hp : tauNodeState (In₂ := In₂) node₀ = .atNode atom₀)
    (hreach : Reaches σ τ (.bnd atom₀))
    (hwin :
      CountableParityGame.PositionalStrategy.WinningFrom
        (G := uniformizationGame A σ) τ
        (.bnd (A.initial, A.initial))) :
    NarrowedAllThreadsWin (A.leftBlockMonitor atom₀.1)
      (leftBlockNarrowed (tauTree σ τ) node₀) := by
  intro env
  have hplay :
      (uniformizationGame A σ).MinPriorityEven
        (blockLeftPlay σ τ atom₀ env) :=
    minPriorityEven_of_reaches_cont σ τ hwin (.bnd atom₀) hreach
      (blockLeftPlay σ τ atom₀ env) rfl
      (blockLeftPlay_step σ τ atom₀ env)
      (blockLeftPlay_consistent σ τ atom₀ env)
  have hshift0 :=
    (natSeqMinEvenParity_shift
      (fun t => uniformizationPriority (blockLeftPlay σ τ atom₀ env t))
      4).mpr hplay
  have hshift :
      NatSeqMinEvenParity
        (fun t =>
          uniformizationPriority
            (blockLeftPlay σ τ atom₀ env (t + 4))) := by
    have hcomm :
        (fun t =>
            uniformizationPriority
              (blockLeftPlay σ τ atom₀ env (t + 4))) =
          fun n =>
            uniformizationPriority
              (blockLeftPlay σ τ atom₀ env (4 + n)) := by
      funext t
      rw [Nat.add_comm]
    rw [hcomm]
    exact hshift0
  have hfun :
      (fun t =>
          uniformizationPriority
            (blockLeftPlay σ τ atom₀ env (t + 4))) =
        fun t =>
          (A.leftBlockMonitor atom₀.1).priority
            (narrowedThreadState (A.leftBlockMonitor atom₀.1)
              (leftBlockNarrowed (tauTree σ τ) node₀) env (t / 4 + 1)) := by
    funext t
    exact blockLeftPlay_priority σ τ atom₀ env node₀ hp t
  rw [hfun] at hshift
  have hround :=
    (natSeqMinEvenParity_div4
      (s := fun k =>
        (A.leftBlockMonitor atom₀.1).priority
          (narrowedThreadState (A.leftBlockMonitor atom₀.1)
            (leftBlockNarrowed (tauTree σ τ) node₀) env (k + 1)))).mp
      hshift
  have hcomm2 :
      (fun t =>
          (A.leftBlockMonitor atom₀.1).priority
            (narrowedThreadState (A.leftBlockMonitor atom₀.1)
              (leftBlockNarrowed (tauTree σ τ) node₀) env (t + 1))) =
        fun n =>
          (A.leftBlockMonitor atom₀.1).priority
            (narrowedThreadState (A.leftBlockMonitor atom₀.1)
              (leftBlockNarrowed (tauTree σ τ) node₀) env (1 + n)) := by
    funext t
    rw [Nat.add_comm]
  rw [hcomm2] at hround
  exact
    (natSeqMinEvenParity_shift
      (fun k =>
        (A.leftBlockMonitor atom₀.1).priority
          (narrowedThreadState (A.leftBlockMonitor atom₀.1)
            (leftBlockNarrowed (tauTree σ τ) node₀) env k))
      1).mp hround

/-! ### Regime (b) left endpoint: a trapped branch is min-even -/

/-- A never-sinking branch trapped in a left block from round `M` has
min-even run priorities. -/
theorem tauTree_priorities_min_even_of_trapped_left
    (branch : Nat -> GlobalJournalBranch (In₁ := In₁) A) (M : Nat)
    (boundary : A.State × A.State) (leftInput : Nat -> In₂)
    (hrun :
      globalRunIn CL CR CC (tauTree σ τ) (Sum.inl (A.initial, A.initial))
          (branchNode branch M) =
        Sum.inl boundary)
    (htail :
      ∀ j : Nat, branch (M + j) = Sum.inr (Sum.inl (leftInput j)))
    (hwin :
      CountableParityGame.PositionalStrategy.WinningFrom
        (G := uniformizationGame A σ) τ
        (.bnd (A.initial, A.initial))) :
    NatSeqMinEvenParity
      (fun n =>
        globalJournalPriority A CL CR CC
          (globalRunIn CL CR CC (tauTree σ τ)
            (Sum.inl (A.initial, A.initial)) (branchNode branch n))) := by
  have hp :
      tauNodeState (In₂ := In₂) (branchNode branch M) = .atNode boundary :=
    tauNodeState_atNode_of_run_inl CL CR CC σ τ (branchNode branch M)
      boundary hrun
  have hreach : Reaches σ τ (.bnd boundary) :=
    reaches_bnd_of_run_inl CL CR CC σ τ (branchNode branch M) boundary hrun
  have hwt :
      DeterministicBlockMonitor.WinningTree
        { CL.monitor with initial := CL.start boundary.1 }
        (leftBlockNarrowed (tauTree σ τ) (branchNode branch M)) :=
    (CL.winning_iff boundary.1
        (leftBlockNarrowed (tauTree σ τ) (branchNode branch M))).mpr
      (narrowedAllThreadsWin_left σ τ (branchNode branch M) boundary hp
        hreach hwin)
  have htail_node :
      ∀ j : Nat,
        branchNode branch (M + j) =
          branchNode branch M ++ senderLNode (A := A)
            (branchNode leftInput j) := by
    intro j
    induction j with
    | zero =>
        show branchNode branch M = branchNode branch M ++ _
        rw [show senderLNode (A := A) (branchNode leftInput 0) =
          ([] : TreeNode _) from rfl, List.append_nil]
    | succ j ih =>
        rw [show M + (j + 1) = M + j + 1 by omega,
          show branchNode branch (M + j + 1) =
            branchNode branch (M + j) ++ [branch (M + j)] from rfl,
          ih, htail j,
          show branchNode leftInput (j + 1) =
            branchNode leftInput j ++ [leftInput j] from rfl,
          senderLNode_append, ← List.append_assoc]
  have hpri :
      ∀ j : Nat,
        globalJournalPriority A CL CR CC
            (globalRunIn CL CR CC (tauTree σ τ)
              (Sum.inl (A.initial, A.initial))
              (branchNode branch (M + (j + 1)))) =
          ({ CL.monitor with initial := CL.start boundary.1 }).priority
            (({ CL.monitor with initial := CL.start boundary.1 }).control
              (leftBlockNarrowed (tauTree σ τ) (branchNode branch M))
              (branchNode leftInput (j + 1))) +
            globalShift (In₁ := In₁) A := by
    intro j
    rw [htail_node (j + 1)]
    obtain ⟨threads, hrt⟩ :=
      globalRunIn_block_left CL CR CC (tauTree σ τ) (branchNode branch M)
        boundary hrun (branchNode leftInput j) (leftInput j)
    rw [show branchNode leftInput (j + 1) =
      branchNode leftInput j ++ [leftInput j] from rfl, hrt]
    show
      CL.monitor.priority
          (CL.monitor.controlIn
            (leftBlockNarrowed (tauTree σ τ) (branchNode branch M))
            (CL.start boundary.1)
            (branchNode leftInput j ++ [leftInput j])) +
          globalShift (In₁ := In₁) A =
        _
    rw [DeterministicBlockMonitor.control,
      DeterministicBlockMonitor.controlIn_update_initial CL.monitor
        (CL.start boundary.1) (branchNode leftInput j ++ [leftInput j])
        (leftBlockNarrowed (tauTree σ τ) (branchNode branch M))
        (CL.start boundary.1)]
  have hshift :=
    (natSeqMinEvenParity_shift
      (fun j =>
        ({ CL.monitor with initial := CL.start boundary.1 }).priority
          (({ CL.monitor with initial := CL.start boundary.1 }).control
            (leftBlockNarrowed (tauTree σ τ) (branchNode branch M))
            (branchNode leftInput j)))
      1).mpr (hwt leftInput)
  have hshift' :
      NatSeqMinEvenParity
        (fun j =>
          ({ CL.monitor with initial := CL.start boundary.1 }).priority
            (({ CL.monitor with initial := CL.start boundary.1 }).control
              (leftBlockNarrowed (tauTree σ τ) (branchNode branch M))
              (branchNode leftInput (j + 1)))) := by
    have hc :
        (fun j =>
            ({ CL.monitor with initial := CL.start boundary.1 }).priority
              (({ CL.monitor with initial := CL.start boundary.1 }).control
                (leftBlockNarrowed (tauTree σ τ) (branchNode branch M))
                (branchNode leftInput (j + 1)))) =
          fun j =>
            ({ CL.monitor with initial := CL.start boundary.1 }).priority
              (({ CL.monitor with initial := CL.start boundary.1 }).control
                (leftBlockNarrowed (tauTree σ τ) (branchNode branch M))
                (branchNode leftInput (1 + j))) := by
      funext j
      rw [Nat.add_comm]
    rw [hc]
    exact hshift
  rw [← natSeqMinEvenParity_shift
    (fun n =>
      globalJournalPriority A CL CR CC
        (globalRunIn CL CR CC (tauTree σ τ) (Sum.inl (A.initial, A.initial))
          (branchNode branch n)))
    (M + 1)]
  have hgoal :
      (fun j =>
          globalJournalPriority A CL CR CC
            (globalRunIn CL CR CC (tauTree σ τ)
              (Sum.inl (A.initial, A.initial))
              (branchNode branch (M + 1 + j)))) =
        fun j =>
          ({ CL.monitor with initial := CL.start boundary.1 }).priority
            (({ CL.monitor with initial := CL.start boundary.1 }).control
              (leftBlockNarrowed (tauTree σ τ) (branchNode branch M))
              (branchNode leftInput (j + 1))) +
            globalShift (In₁ := In₁) A := by
    funext j
    rw [show M + 1 + j = M + (j + 1) by omega]
    exact hpri j
  rw [hgoal]
  exact
    (natSeqMinEvenParity_add_const (globalShift_even A)).mpr hshift'

/-! ### The right-orientation mirror -/

/-- One step of the right-block play. -/
noncomputable def advanceR (env : Nat -> In₁ × In₂) :
    UniformizationPosition (In₁ := In₁) A ->
      UniformizationPosition (In₁ := In₁) A
  | .committed atom h => .opening atom h (env 0)
  | .openingResolve atom h move _o1 o2 => uOpenRightTarget σ atom h move o2
  | .blockEnvR h word q mn tbl => .recvR h word q mn tbl (env word.length)
  | .resolveR h word q mn _tbl move o2 =>
      uContinueRTarget σ h word q mn move o2
  | .blockEnvL h word q mn tbl => .recvL h word q mn tbl default
  | .resolveL h word q mn _tbl move o1 =>
      uContinueLTarget σ h word q mn move o1
  | .closeResolveL _ _ q mn _tbl move o1 o2 =>
      uCloseTarget (A := A) q mn move o1 o2
  | .closeResolveR _ _ q mn _tbl move o2 o1 =>
      uCloseTarget (A := A) q mn move o1 o2
  | .revEnvL hc word eqs ems q mn tbl =>
      .revRecvL hc word eqs ems q mn tbl default
  | .revResolveL hc word eqs ems q mn _tbl move o1r _o2r =>
      uRevContinueLTarget σ hc word eqs ems q mn move o1r
  | .revEnvR hc word eqs ems q mn tbl =>
      .revRecvR hc word eqs ems q mn tbl default
  | .revResolveR hc word eqs ems q mn _tbl move _o1r o2r =>
      uRevContinueRTarget σ hc word eqs ems q mn move o2r
  | pos => τ.move pos

theorem advanceR_step (env : Nat -> In₁ × In₂)
    (pos : UniformizationPosition (In₁ := In₁) A) :
    (uniformizationGame A σ).step pos (advanceR σ τ env pos) := by
  cases pos with
  | committed atom h => exact ⟨env 0, rfl⟩
  | openingResolve atom h move o1 o2 => exact Or.inr (Or.inr rfl)
  | blockEnvR h word q mn tbl => exact ⟨env word.length, rfl⟩
  | resolveR h word q mn tbl move o2 => exact Or.inl rfl
  | blockEnvL h word q mn tbl => exact ⟨default, rfl⟩
  | resolveL h word q mn tbl move o1 => exact Or.inl rfl
  | closeResolveL h word q mn tbl move o1 o2 => exact Or.inl rfl
  | closeResolveR h word q mn tbl move o2 o1 => exact Or.inl rfl
  | revEnvL hc word eqs ems q mn tbl => exact ⟨default, rfl⟩
  | revResolveL hc word eqs ems q mn tbl move o1r o2r => exact Or.inl rfl
  | revEnvR hc word eqs ems q mn tbl => exact ⟨default, rfl⟩
  | revResolveR hc word eqs ems q mn tbl move o1r o2r => exact Or.inl rfl
  | bnd atom => exact τ.legal (.bnd atom) rfl
  | opening atom h move => exact τ.legal (.opening atom h move) rfl
  | blockL h word q mn => exact τ.legal (.blockL h word q mn) rfl
  | recvL h word q mn tbl move =>
      exact τ.legal (.recvL h word q mn tbl move) rfl
  | closeL h word q mn tbl move o1 =>
      exact τ.legal (.closeL h word q mn tbl move o1) rfl
  | blockR h word q mn => exact τ.legal (.blockR h word q mn) rfl
  | recvR h word q mn tbl move =>
      exact τ.legal (.recvR h word q mn tbl move) rfl
  | closeR h word q mn tbl move o2 =>
      exact τ.legal (.closeR h word q mn tbl move o2) rfl
  | revCommitL word eqs ems =>
      exact τ.legal (.revCommitL word eqs ems) rfl
  | revBlockL hc word eqs ems q mn =>
      exact τ.legal (.revBlockL hc word eqs ems q mn) rfl
  | revRecvL hc word eqs ems q mn tbl move =>
      exact τ.legal (.revRecvL hc word eqs ems q mn tbl move) rfl
  | revCommitR word eqs ems =>
      exact τ.legal (.revCommitR word eqs ems) rfl
  | revBlockR hc word eqs ems q mn =>
      exact τ.legal (.revBlockR hc word eqs ems q mn) rfl
  | revRecvR hc word eqs ems q mn tbl move =>
      exact τ.legal (.revRecvR hc word eqs ems q mn tbl move) rfl

theorem advanceR_eq_tau_of_even (env : Nat -> In₁ × In₂)
    (pos : UniformizationPosition (In₁ := In₁) A)
    (h : (uniformizationGame A σ).owner pos = ParityPlayer.even) :
    advanceR σ τ env pos = τ.move pos := by
  cases pos with
  | bnd atom => rfl
  | opening atom h move => rfl
  | blockL h word q mn => rfl
  | recvL h word q mn tbl move => rfl
  | closeL h word q mn tbl move o1 => rfl
  | blockR h word q mn => rfl
  | recvR h word q mn tbl move => rfl
  | closeR h word q mn tbl move o2 => rfl
  | revCommitL word eqs ems => rfl
  | revBlockL hc word eqs ems q mn => rfl
  | revRecvL hc word eqs ems q mn tbl move => rfl
  | revCommitR word eqs ems => rfl
  | revBlockR hc word eqs ems q mn => rfl
  | revRecvR hc word eqs ems q mn tbl move => rfl
  | committed atom h' =>
      simp [uniformizationGame, uniformizationOwner] at h
  | openingResolve atom h' move o1 o2 =>
      simp [uniformizationGame, uniformizationOwner] at h
  | blockEnvL h' word q mn tbl =>
      simp [uniformizationGame, uniformizationOwner] at h
  | resolveL h' word q mn tbl move o1 =>
      simp [uniformizationGame, uniformizationOwner] at h
  | blockEnvR h' word q mn tbl =>
      simp [uniformizationGame, uniformizationOwner] at h
  | resolveR h' word q mn tbl move o2 =>
      simp [uniformizationGame, uniformizationOwner] at h
  | closeResolveL h' word q mn tbl move o1 o2 =>
      simp [uniformizationGame, uniformizationOwner] at h
  | closeResolveR h' word q mn tbl move o2 o1 =>
      simp [uniformizationGame, uniformizationOwner] at h
  | revEnvL hc word eqs ems q mn tbl =>
      simp [uniformizationGame, uniformizationOwner] at h
  | revResolveL hc word eqs ems q mn tbl move o1r o2r =>
      simp [uniformizationGame, uniformizationOwner] at h
  | revEnvR hc word eqs ems q mn tbl =>
      simp [uniformizationGame, uniformizationOwner] at h
  | revResolveR hc word eqs ems q mn tbl move o1r o2r =>
      simp [uniformizationGame, uniformizationOwner] at h

noncomputable def blockRightPlay (env : Nat -> In₁ × In₂) :
    Nat -> UniformizationPosition (In₁ := In₁) A
  | 0 => .bnd atom₀
  | t + 1 => advanceR σ τ env (blockRightPlay env t)

theorem blockRightPlay_zero (env : Nat -> In₁ × In₂) :
    blockRightPlay σ τ atom₀ env 0 = .bnd atom₀ :=
  rfl

theorem blockRightPlay_succ (env : Nat -> In₁ × In₂) (t : Nat) :
    blockRightPlay σ τ atom₀ env (t + 1) =
      advanceR σ τ env (blockRightPlay σ τ atom₀ env t) :=
  rfl

theorem blockRightPlay_step (env : Nat -> In₁ × In₂) (t : Nat) :
    (uniformizationGame A σ).step (blockRightPlay σ τ atom₀ env t)
      (blockRightPlay σ τ atom₀ env (t + 1)) :=
  advanceR_step σ τ env (blockRightPlay σ τ atom₀ env t)

theorem blockRightPlay_consistent (env : Nat -> In₁ × In₂) :
    ∀ t : Nat,
      (uniformizationGame A σ).owner (blockRightPlay σ τ atom₀ env t) =
          ParityPlayer.even ->
        blockRightPlay σ τ atom₀ env (t + 1) =
          τ.move (blockRightPlay σ τ atom₀ env t) := by
  intro t h
  rw [blockRightPlay_succ]
  exact advanceR_eq_tau_of_even σ τ env _ h

/-- Below an atom node, adding sender inputs parses into a right
block. -/
theorem tauNodeState_senderRNode_snoc
    (node₀ : TreeNode (GlobalJournalBranch (In₁ := In₁) A))
    (boundary : A.State × A.State)
    (hp : tauNodeState (In₂ := In₂) node₀ = .atNode boundary)
    (w : TreeNode In₁) (x : In₁) :
    tauNodeState (In₂ := In₂) (node₀ ++ senderRNode (A := A) (w ++ [x])) =
      .inRight boundary (w ++ [x]) := by
  induction w using List.reverseRecOn generalizing x with
  | nil =>
      rw [show senderRNode (A := A) (([] : TreeNode In₁) ++ [x]) =
        [Sum.inr (Sum.inr x)] from rfl, tauNodeState_append, hp]
      rfl
  | append_singleton w x' ih =>
      rw [show senderRNode (A := A) ((w ++ [x']) ++ [x]) =
        senderRNode (A := A) (w ++ [x']) ++ [Sum.inr (Sum.inr x)] from by
        rw [senderRNode_append], ← List.append_assoc,
        tauNodeState_append, ih x']
      rfl

theorem rightBlockNarrowed_tauTree_snoc
    (node₀ : TreeNode (GlobalJournalBranch (In₁ := In₁) A))
    (boundary : A.State × A.State)
    (hp : tauNodeState (In₂ := In₂) node₀ = .atNode boundary)
    (w : TreeNode In₁) (x : In₁) :
    rightBlockNarrowed (tauTree σ τ) node₀ (w ++ [x]) =
      tauRightLabel σ τ boundary (w ++ [x]) := by
  show
    GlobalJournalLabel.rightNarrowed
        (tauLabelOf σ τ
          (tauNodeState (node₀ ++ senderRNode (A := A) (w ++ [x])))) =
      _
  rw [tauNodeState_senderRNode_snoc node₀ boundary hp w x]
  rfl

theorem rightBlockNarrowed_tauTree_nil
    (node₀ : TreeNode (GlobalJournalBranch (In₁ := In₁) A))
    (boundary : A.State × A.State)
    (hp : tauNodeState (In₂ := In₂) node₀ = .atNode boundary) :
    rightBlockNarrowed (tauTree σ τ) node₀ [] =
      tauOpeningRightLabel σ τ boundary := by
  rw [rightBlockNarrowed_nil]
  show GlobalJournalLabel.rightNarrowed (tauLabelOf σ τ (tauNodeState node₀)) = _
  rw [hp]
  rfl

theorem rightBlockNarrowed_senderWord
    (node₀ : TreeNode (GlobalJournalBranch (In₁ := In₁) A))
    (hp : tauNodeState (In₂ := In₂) node₀ = .atNode atom₀)
    (renv : Nat -> In₂ × In₁) (k : Nat) :
    rightBlockNarrowed (tauTree σ τ) node₀
        (senderWord (branchNode renv (k + 1))) =
      tauRightLabel σ τ atom₀ (senderWord (branchNode renv (k + 1))) := by
  rw [show senderWord (branchNode renv (k + 1)) =
      senderWord (branchNode renv k) ++ [(renv k).2] from by
      rw [show branchNode renv (k + 1) = branchNode renv k ++ [renv k]
          from rfl, senderWord_append]]
  exact
    rightBlockNarrowed_tauTree_snoc σ τ node₀ atom₀ hp
      (senderWord (branchNode renv k)) ((renv k).2)

/-! ### Right prelude and three-step advance -/

variable (renv : Nat -> In₂ × In₁)

/-- The In₁-by-In₂ move driving the play, from the In₂-by-In₁ thread
environment. -/
def swapEnv (renv : Nat -> In₂ × In₁) : Nat -> In₁ × In₂ :=
  fun k => ((renv k).2, (renv k).1)

theorem blockRightPlay_one :
    blockRightPlay σ τ atom₀ (swapEnv renv) 1 =
      .committed atom₀ (commitmentOf σ τ atom₀) := by
  show advanceR σ τ (swapEnv renv) (blockRightPlay σ τ atom₀ (swapEnv renv) 0) = _
  rw [blockRightPlay_zero]
  exact commitmentOf_spec σ τ atom₀

theorem blockRightPlay_two :
    blockRightPlay σ τ atom₀ (swapEnv renv) 2 =
      .opening atom₀ (commitmentOf σ τ atom₀) (swapEnv renv 0) := by
  show advanceR σ τ (swapEnv renv) (blockRightPlay σ τ atom₀ (swapEnv renv) 1) = _
  rw [blockRightPlay_one]
  rfl

theorem blockRightPlay_three :
    blockRightPlay σ τ atom₀ (swapEnv renv) 3 =
      .openingResolve atom₀ (commitmentOf σ τ atom₀) (swapEnv renv 0)
        (openingChoice σ τ atom₀ (swapEnv renv 0)).1
        (openingChoice σ τ atom₀ (swapEnv renv 0)).2 := by
  show advanceR σ τ (swapEnv renv) (blockRightPlay σ τ atom₀ (swapEnv renv) 2) = _
  rw [blockRightPlay_two]
  exact openingChoice_spec σ τ atom₀ (swapEnv renv 0)

/-- Three advance steps from a right-block position produce the next
right-block position. -/
theorem blockAdvance4R_blockR (word : List In₁) (q mn : A.State) :
    advanceR σ τ (swapEnv renv)
        (advanceR σ τ (swapEnv renv)
          (advanceR σ τ (swapEnv renv)
            (advanceR σ τ (swapEnv renv)
              (.blockR (commitmentOf σ τ atom₀) word q mn)))) =
      .blockR (commitmentOf σ τ atom₀) (word ++ [(swapEnv renv word.length).1])
        (A.step q
          (rightRoundRecord
            ((swapEnv renv word.length).2, (swapEnv renv word.length).1)
            (blockSenderOne σ (commitmentOf σ τ atom₀) word
              (swapEnv renv word.length).1)
            (recvChoiceR σ τ atom₀ word q mn (swapEnv renv word.length))))
        (A.minPriorityState mn
          (A.step q
            (rightRoundRecord
              ((swapEnv renv word.length).2, (swapEnv renv word.length).1)
              (blockSenderOne σ (commitmentOf σ τ atom₀) word
                (swapEnv renv word.length).1)
              (recvChoiceR σ τ atom₀ word q mn
                (swapEnv renv word.length))))) := by
  rw [show
    advanceR σ τ (swapEnv renv)
        (.blockR (commitmentOf σ τ atom₀) word q mn) =
      τ.move (.blockR (commitmentOf σ τ atom₀) word q mn) from rfl,
    blockRevTableR_spec σ τ atom₀ word q mn]
  show
    advanceR σ τ (swapEnv renv)
        (advanceR σ τ (swapEnv renv)
          (.recvR (commitmentOf σ τ atom₀) word q mn
            (blockRevTableR σ τ atom₀ word q mn)
            (swapEnv renv word.length))) =
      _
  rw [show
    advanceR σ τ (swapEnv renv)
        (.recvR (commitmentOf σ τ atom₀) word q mn
          (blockRevTableR σ τ atom₀ word q mn)
          (swapEnv renv word.length)) =
      τ.move
        (.recvR (commitmentOf σ τ atom₀) word q mn
          (blockRevTableR σ τ atom₀ word q mn)
          (swapEnv renv word.length))
    from rfl,
    recvChoiceR_spec σ τ atom₀ word q mn (swapEnv renv word.length)]
  rfl

/-! ### The right tracking induction -/

theorem senderWordR_branchNode_length (k : Nat) :
    (senderWord (branchNode renv k)).length = k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [show branchNode renv (k + 1) = branchNode renv k ++ [renv k]
          from rfl, senderWord_append, List.length_append, ih]
      rfl

theorem narrowedThreadStateR_succ
    (node₀ : TreeNode (GlobalJournalBranch (In₁ := In₁) A)) (k : Nat) :
    narrowedThreadState (A.rightBlockMonitor atom₀.1)
        (rightBlockNarrowed (tauTree σ τ) node₀) renv (k + 1) =
      (A.rightBlockMonitor atom₀.1).step
        (narrowedThreadState (A.rightBlockMonitor atom₀.1)
          (rightBlockNarrowed (tauTree σ τ) node₀) renv k)
        (narrowedRecord (A.rightBlockMonitor atom₀.1)
          (rightBlockNarrowed (tauTree σ τ) node₀
            (senderWord (branchNode renv k)))
          (narrowedThreadState (A.rightBlockMonitor atom₀.1)
            (rightBlockNarrowed (tauTree σ τ) node₀) renv k)
          (renv k)) := by
  show
    narrowedControl (A.rightBlockMonitor atom₀.1)
        (rightBlockNarrowed (tauTree σ τ) node₀) (branchNode renv (k + 1)) =
      _
  rw [show branchNode renv (k + 1) = branchNode renv k ++ [renv k] from rfl,
    narrowedControl_append (A.rightBlockMonitor atom₀.1)
      (rightBlockNarrowed (tauTree σ τ) node₀) (branchNode renv k) (renv k)]
  rfl

/-- The round positions of the right block play track the narrowed
thread fold. -/
theorem blockRightPlay_blockR
    (node₀ : TreeNode (GlobalJournalBranch (In₁ := In₁) A))
    (hp : tauNodeState (In₂ := In₂) node₀ = .atNode atom₀) :
    ∀ k : Nat,
      blockRightPlay σ τ atom₀ (swapEnv renv) (4 * k + 4) =
        .blockR (commitmentOf σ τ atom₀)
          (senderWord (branchNode renv (k + 1)))
          (narrowedThreadState (A.rightBlockMonitor atom₀.1)
            (rightBlockNarrowed (tauTree σ τ) node₀) renv (k + 1)).1
          (narrowedThreadState (A.rightBlockMonitor atom₀.1)
            (rightBlockNarrowed (tauTree σ τ) node₀) renv (k + 1)).2 := by
  intro k
  induction k with
  | zero =>
      rw [show blockRightPlay σ τ atom₀ (swapEnv renv) 4 =
          advanceR σ τ (swapEnv renv)
            (blockRightPlay σ τ atom₀ (swapEnv renv) 3) from rfl,
        blockRightPlay_three,
        narrowedThreadStateR_succ σ τ atom₀ renv node₀ 0,
        show senderWord (branchNode renv 0) = ([] : List In₁) from rfl,
        rightBlockNarrowed_tauTree_nil σ τ node₀ atom₀ hp,
        show senderWord (branchNode renv 1) = [(renv 0).2] from rfl]
      rfl
  | succ k ih =>
      rw [show 4 * (k + 1) + 4 = (4 * k + 4) + 4 by ring,
        show blockRightPlay σ τ atom₀ (swapEnv renv) ((4 * k + 4) + 4) =
          advanceR σ τ (swapEnv renv)
            (advanceR σ τ (swapEnv renv)
              (advanceR σ τ (swapEnv renv)
                (advanceR σ τ (swapEnv renv)
                  (blockRightPlay σ τ atom₀ (swapEnv renv) (4 * k + 4)))))
          from rfl,
        ih,
        blockAdvance4R_blockR σ τ atom₀ renv
          (senderWord (branchNode renv (k + 1)))
          (narrowedThreadState (A.rightBlockMonitor atom₀.1)
            (rightBlockNarrowed (tauTree σ τ) node₀) renv (k + 1)).1
          (narrowedThreadState (A.rightBlockMonitor atom₀.1)
            (rightBlockNarrowed (tauTree σ τ) node₀) renv (k + 1)).2,
        senderWordR_branchNode_length renv (k + 1),
        narrowedThreadStateR_succ σ τ atom₀ renv node₀ (k + 1),
        rightBlockNarrowed_senderWord σ τ atom₀ node₀ hp renv k]
      congr 1
      simp only [swapEnv,
        show branchNode renv (k + 1 + 1) =
          branchNode renv (k + 1) ++ [renv (k + 1)] from rfl,
        senderWord_append]

/-! ### Right play parity to thread parity -/

theorem blockEnvR_priority (word : List In₁) (q mn : A.State) :
    uniformizationPriority
        (advanceR σ τ (swapEnv renv)
          (.blockR (commitmentOf σ τ atom₀) word q mn)) =
      A.priority q := by
  rw [show
    advanceR σ τ (swapEnv renv)
        (.blockR (commitmentOf σ τ atom₀) word q mn) =
      τ.move (.blockR (commitmentOf σ τ atom₀) word q mn) from rfl,
    blockRevTableR_spec σ τ atom₀ word q mn]
  rfl

theorem recvR_priority (word : List In₁) (q mn : A.State) :
    uniformizationPriority
        (advanceR σ τ (swapEnv renv)
          (advanceR σ τ (swapEnv renv)
            (.blockR (commitmentOf σ τ atom₀) word q mn))) =
      A.priority q := by
  rw [show
    advanceR σ τ (swapEnv renv)
        (.blockR (commitmentOf σ τ atom₀) word q mn) =
      τ.move (.blockR (commitmentOf σ τ atom₀) word q mn) from rfl,
    blockRevTableR_spec σ τ atom₀ word q mn]
  rfl

theorem resolveR_priority (word : List In₁) (q mn : A.State) :
    uniformizationPriority
        (advanceR σ τ (swapEnv renv)
          (advanceR σ τ (swapEnv renv)
            (advanceR σ τ (swapEnv renv)
              (.blockR (commitmentOf σ τ atom₀) word q mn)))) =
      A.priority q := by
  rw [show
    advanceR σ τ (swapEnv renv)
        (.blockR (commitmentOf σ τ atom₀) word q mn) =
      τ.move (.blockR (commitmentOf σ τ atom₀) word q mn) from rfl,
    blockRevTableR_spec σ τ atom₀ word q mn]
  show
    uniformizationPriority
        (advanceR σ τ (swapEnv renv)
          (.recvR (commitmentOf σ τ atom₀) word q mn
            (blockRevTableR σ τ atom₀ word q mn)
            (swapEnv renv word.length))) =
      _
  rw [show
    advanceR σ τ (swapEnv renv)
        (.recvR (commitmentOf σ τ atom₀) word q mn
          (blockRevTableR σ τ atom₀ word q mn)
          (swapEnv renv word.length)) =
      τ.move
        (.recvR (commitmentOf σ τ atom₀) word q mn
          (blockRevTableR σ τ atom₀ word q mn)
          (swapEnv renv word.length))
    from rfl,
    recvChoiceR_spec σ τ atom₀ word q mn (swapEnv renv word.length)]
  rfl

theorem blockRightPlay_priority
    (node₀ : TreeNode (GlobalJournalBranch (In₁ := In₁) A))
    (hp : tauNodeState (In₂ := In₂) node₀ = .atNode atom₀) (t : Nat) :
    uniformizationPriority
        (blockRightPlay σ τ atom₀ (swapEnv renv) (t + 4)) =
      (A.rightBlockMonitor atom₀.1).priority
        (narrowedThreadState (A.rightBlockMonitor atom₀.1)
          (rightBlockNarrowed (tauTree σ τ) node₀) renv (t / 4 + 1)) := by
  obtain ⟨r, p, hp4, rfl⟩ :
      ∃ r p, p < 4 ∧ t = 4 * r + p := ⟨t / 4, t % 4, by omega, by omega⟩
  rw [show (4 * r + p) / 4 + 1 = r + 1 by omega,
    show (A.rightBlockMonitor atom₀.1).priority
        (narrowedThreadState (A.rightBlockMonitor atom₀.1)
          (rightBlockNarrowed (tauTree σ τ) node₀) renv (r + 1)) =
      A.priority
        (narrowedThreadState (A.rightBlockMonitor atom₀.1)
          (rightBlockNarrowed (tauTree σ τ) node₀) renv (r + 1)).1 from rfl]
  match r, p, hp4 with
  | r, 0, _ =>
      rw [show 4 * r + 0 + 4 = 4 * r + 4 by omega,
        blockRightPlay_blockR σ τ atom₀ renv node₀ hp r]
      rfl
  | r, 1, _ =>
      rw [show 4 * r + 1 + 4 = 4 * r + 4 + 1 by omega,
        show blockRightPlay σ τ atom₀ (swapEnv renv) (4 * r + 4 + 1) =
          advanceR σ τ (swapEnv renv)
            (blockRightPlay σ τ atom₀ (swapEnv renv) (4 * r + 4))
          from rfl,
        blockRightPlay_blockR σ τ atom₀ renv node₀ hp r,
        blockEnvR_priority]
  | r, 2, _ =>
      rw [show 4 * r + 2 + 4 = 4 * r + 4 + 1 + 1 by omega,
        show blockRightPlay σ τ atom₀ (swapEnv renv)
            (4 * r + 4 + 1 + 1) =
          advanceR σ τ (swapEnv renv)
            (advanceR σ τ (swapEnv renv)
              (blockRightPlay σ τ atom₀ (swapEnv renv) (4 * r + 4)))
          from rfl,
        blockRightPlay_blockR σ τ atom₀ renv node₀ hp r,
        recvR_priority]
  | r, 3, _ =>
      rw [show 4 * r + 3 + 4 = 4 * r + 4 + 1 + 1 + 1 by omega,
        show blockRightPlay σ τ atom₀ (swapEnv renv)
            (4 * r + 4 + 1 + 1 + 1) =
          advanceR σ τ (swapEnv renv)
            (advanceR σ τ (swapEnv renv)
              (advanceR σ τ (swapEnv renv)
                (blockRightPlay σ τ atom₀ (swapEnv renv) (4 * r + 4))))
          from rfl,
        blockRightPlay_blockR σ τ atom₀ renv node₀ hp r,
        resolveR_priority]

/-- Every environment thread of the trapped right block is min-even. -/
theorem narrowedAllThreadsWin_right
    (node₀ : TreeNode (GlobalJournalBranch (In₁ := In₁) A))
    (boundary : A.State × A.State)
    (hp : tauNodeState (In₂ := In₂) node₀ = .atNode boundary)
    (hreach : Reaches σ τ (.bnd boundary))
    (hwin :
      CountableParityGame.PositionalStrategy.WinningFrom
        (G := uniformizationGame A σ) τ
        (.bnd (A.initial, A.initial))) :
    NarrowedAllThreadsWin (A.rightBlockMonitor boundary.1)
      (rightBlockNarrowed (tauTree σ τ) node₀) := by
  intro env
  have hplay :
      (uniformizationGame A σ).MinPriorityEven
        (blockRightPlay σ τ boundary (swapEnv env)) :=
    minPriorityEven_of_reaches_cont σ τ hwin (.bnd boundary) hreach
      (blockRightPlay σ τ boundary (swapEnv env)) rfl
      (blockRightPlay_step σ τ boundary (swapEnv env))
      (blockRightPlay_consistent σ τ boundary (swapEnv env))
  have hshift0 :=
    (natSeqMinEvenParity_shift
      (fun t =>
        uniformizationPriority
          (blockRightPlay σ τ boundary (swapEnv env) t))
      4).mpr hplay
  have hshift :
      NatSeqMinEvenParity
        (fun t =>
          uniformizationPriority
            (blockRightPlay σ τ boundary (swapEnv env) (t + 4))) := by
    have hcomm :
        (fun t =>
            uniformizationPriority
              (blockRightPlay σ τ boundary (swapEnv env) (t + 4))) =
          fun n =>
            uniformizationPriority
              (blockRightPlay σ τ boundary (swapEnv env) (4 + n)) := by
      funext t
      rw [Nat.add_comm]
    rw [hcomm]
    exact hshift0
  have hfun :
      (fun t =>
          uniformizationPriority
            (blockRightPlay σ τ boundary (swapEnv env) (t + 4))) =
        fun t =>
          (A.rightBlockMonitor boundary.1).priority
            (narrowedThreadState (A.rightBlockMonitor boundary.1)
              (rightBlockNarrowed (tauTree σ τ) node₀) env
              (t / 4 + 1)) := by
    funext t
    exact blockRightPlay_priority σ τ boundary env node₀ hp t
  rw [hfun] at hshift
  have hround :=
    (natSeqMinEvenParity_div4
      (s := fun k =>
        (A.rightBlockMonitor boundary.1).priority
          (narrowedThreadState (A.rightBlockMonitor boundary.1)
            (rightBlockNarrowed (tauTree σ τ) node₀) env (k + 1)))).mp
      hshift
  have hcomm2 :
      (fun t =>
          (A.rightBlockMonitor boundary.1).priority
            (narrowedThreadState (A.rightBlockMonitor boundary.1)
              (rightBlockNarrowed (tauTree σ τ) node₀) env (t + 1))) =
        fun n =>
          (A.rightBlockMonitor boundary.1).priority
            (narrowedThreadState (A.rightBlockMonitor boundary.1)
              (rightBlockNarrowed (tauTree σ τ) node₀) env (1 + n)) := by
    funext t
    rw [Nat.add_comm]
  rw [hcomm2] at hround
  exact
    (natSeqMinEvenParity_shift
      (fun k =>
        (A.rightBlockMonitor boundary.1).priority
          (narrowedThreadState (A.rightBlockMonitor boundary.1)
            (rightBlockNarrowed (tauTree σ τ) node₀) env k))
      1).mp hround

/-! ### Regime (b) right endpoint: a trapped branch is min-even -/

/-- A never-sinking branch trapped in a right block from round `M` has
min-even run priorities. -/
theorem tauTree_priorities_min_even_of_trapped_right
    (branch : Nat -> GlobalJournalBranch (In₁ := In₁) A) (M : Nat)
    (boundary : A.State × A.State) (rightInput : Nat -> In₁)
    (hrun :
      globalRunIn CL CR CC (tauTree σ τ) (Sum.inl (A.initial, A.initial))
          (branchNode branch M) =
        Sum.inl boundary)
    (htail :
      ∀ j : Nat, branch (M + j) = Sum.inr (Sum.inr (rightInput j)))
    (hwin :
      CountableParityGame.PositionalStrategy.WinningFrom
        (G := uniformizationGame A σ) τ
        (.bnd (A.initial, A.initial))) :
    NatSeqMinEvenParity
      (fun n =>
        globalJournalPriority A CL CR CC
          (globalRunIn CL CR CC (tauTree σ τ)
            (Sum.inl (A.initial, A.initial)) (branchNode branch n))) := by
  have hp :
      tauNodeState (In₂ := In₂) (branchNode branch M) = .atNode boundary :=
    tauNodeState_atNode_of_run_inl CL CR CC σ τ (branchNode branch M)
      boundary hrun
  have hreach : Reaches σ τ (.bnd boundary) :=
    reaches_bnd_of_run_inl CL CR CC σ τ (branchNode branch M) boundary hrun
  have hwt :
      DeterministicBlockMonitor.WinningTree
        { CR.monitor with initial := CR.start boundary.1 }
        (rightBlockNarrowed (tauTree σ τ) (branchNode branch M)) :=
    (CR.winning_iff boundary.1
        (rightBlockNarrowed (tauTree σ τ) (branchNode branch M))).mpr
      (narrowedAllThreadsWin_right σ τ (branchNode branch M) boundary hp
        hreach hwin)
  have htail_node :
      ∀ j : Nat,
        branchNode branch (M + j) =
          branchNode branch M ++ senderRNode (A := A)
            (branchNode rightInput j) := by
    intro j
    induction j with
    | zero =>
        show branchNode branch M = branchNode branch M ++ _
        rw [show senderRNode (A := A) (branchNode rightInput 0) =
          ([] : TreeNode _) from rfl, List.append_nil]
    | succ j ih =>
        rw [show M + (j + 1) = M + j + 1 by omega,
          show branchNode branch (M + j + 1) =
            branchNode branch (M + j) ++ [branch (M + j)] from rfl,
          ih, htail j,
          show branchNode rightInput (j + 1) =
            branchNode rightInput j ++ [rightInput j] from rfl,
          senderRNode_append, ← List.append_assoc]
  have hpri :
      ∀ j : Nat,
        globalJournalPriority A CL CR CC
            (globalRunIn CL CR CC (tauTree σ τ)
              (Sum.inl (A.initial, A.initial))
              (branchNode branch (M + (j + 1)))) =
          ({ CR.monitor with initial := CR.start boundary.1 }).priority
            (({ CR.monitor with initial := CR.start boundary.1 }).control
              (rightBlockNarrowed (tauTree σ τ) (branchNode branch M))
              (branchNode rightInput (j + 1))) +
            globalShift (In₁ := In₁) A := by
    intro j
    rw [htail_node (j + 1)]
    obtain ⟨threads, hrt⟩ :=
      globalRunIn_block_right CL CR CC (tauTree σ τ) (branchNode branch M)
        boundary hrun (branchNode rightInput j) (rightInput j)
    rw [show branchNode rightInput (j + 1) =
      branchNode rightInput j ++ [rightInput j] from rfl, hrt]
    show
      CR.monitor.priority
          (CR.monitor.controlIn
            (rightBlockNarrowed (tauTree σ τ) (branchNode branch M))
            (CR.start boundary.1)
            (branchNode rightInput j ++ [rightInput j])) +
          globalShift (In₁ := In₁) A =
        _
    rw [DeterministicBlockMonitor.control,
      DeterministicBlockMonitor.controlIn_update_initial CR.monitor
        (CR.start boundary.1)
        (branchNode rightInput j ++ [rightInput j])
        (rightBlockNarrowed (tauTree σ τ) (branchNode branch M))
        (CR.start boundary.1)]
  have hshift :=
    (natSeqMinEvenParity_shift
      (fun j =>
        ({ CR.monitor with initial := CR.start boundary.1 }).priority
          (({ CR.monitor with initial := CR.start boundary.1 }).control
            (rightBlockNarrowed (tauTree σ τ) (branchNode branch M))
            (branchNode rightInput j)))
      1).mpr (hwt rightInput)
  have hshift' :
      NatSeqMinEvenParity
        (fun j =>
          ({ CR.monitor with initial := CR.start boundary.1 }).priority
            (({ CR.monitor with initial := CR.start boundary.1 }).control
              (rightBlockNarrowed (tauTree σ τ) (branchNode branch M))
              (branchNode rightInput (j + 1)))) := by
    have hc :
        (fun j =>
            ({ CR.monitor with initial := CR.start boundary.1 }).priority
              (({ CR.monitor with initial := CR.start boundary.1 }).control
                (rightBlockNarrowed (tauTree σ τ) (branchNode branch M))
                (branchNode rightInput (j + 1)))) =
          fun j =>
            ({ CR.monitor with initial := CR.start boundary.1 }).priority
              (({ CR.monitor with initial := CR.start boundary.1 }).control
                (rightBlockNarrowed (tauTree σ τ) (branchNode branch M))
                (branchNode rightInput (1 + j))) := by
      funext j
      rw [Nat.add_comm]
    rw [hc]
    exact hshift
  rw [← natSeqMinEvenParity_shift
    (fun n =>
      globalJournalPriority A CL CR CC
        (globalRunIn CL CR CC (tauTree σ τ) (Sum.inl (A.initial, A.initial))
          (branchNode branch n)))
    (M + 1)]
  have hgoal :
      (fun j =>
          globalJournalPriority A CL CR CC
            (globalRunIn CL CR CC (tauTree σ τ)
              (Sum.inl (A.initial, A.initial))
              (branchNode branch (M + 1 + j)))) =
        fun j =>
          ({ CR.monitor with initial := CR.start boundary.1 }).priority
            (({ CR.monitor with initial := CR.start boundary.1 }).control
              (rightBlockNarrowed (tauTree σ τ) (branchNode branch M))
              (branchNode rightInput (j + 1))) +
            globalShift (In₁ := In₁) A := by
    funext j
    rw [show M + 1 + j = M + (j + 1) by omega]
    exact hpri j
  rw [hgoal]
  exact
    (natSeqMinEvenParity_add_const (globalShift_even A)).mpr hshift'

end Winner

end DetParityAutomaton

end DistributedSynthesis
