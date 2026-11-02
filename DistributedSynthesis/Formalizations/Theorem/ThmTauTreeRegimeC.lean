/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmTauTreeRegimeB
import DistributedSynthesis.Formalizations.Theorem.ThmTauTreeDichotomy

/-!
# Regime (c): a branch trapped in the reversal chain

The chain-tail regime of the tau-tree acceptance (obligation M2-3b).
A never-sinking branch that eventually stays in the reversed modes
has, in its tail, run priorities equal to the chain checker's control
fold along the mixed direction word (shifted by the even global
shift).  The checker verdict comes from `winning_iff` at the first
handoff thread set: every composed thread of the chain is realized at
a reversed-block position of the uniformization game (`runGood`), the
environment-driven chain play from that position tracks the
composed-thread fold round by round, and the winner's min-even parity
transfers to the fold.

The word-state of the chain (the reversed word since the last
orientation switch, tagged by the current orientation) drives all
three layers at once: the tau-tree parse, the labels the automaton
reads, and the game position words.
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

/-! ### The word-state of a reversal chain -/

/-- One step of the chain word-state: a same-sorted direction extends
the current reversed word, a cross-sorted direction reverses again
and restarts the word at that direction. -/
def chainWordStep :
    List In₂ ⊕ List In₁ -> In₂ ⊕ In₁ -> List In₂ ⊕ List In₁
  | Sum.inl wordL, Sum.inl inputTwo => Sum.inl (wordL ++ [inputTwo])
  | Sum.inl _, Sum.inr inputOne => Sum.inr [inputOne]
  | Sum.inr wordR, Sum.inr inputOne => Sum.inr (wordR ++ [inputOne])
  | Sum.inr _, Sum.inl inputTwo => Sum.inl [inputTwo]

/-- The chain word-state after a mixed direction word. -/
def chainWord (init : List In₂ ⊕ List In₁)
    (w : List (In₂ ⊕ In₁)) : List In₂ ⊕ List In₁ :=
  w.foldl chainWordStep init

@[simp]
theorem chainWord_nil (init : List In₂ ⊕ List In₁) :
    chainWord init [] = init :=
  rfl

theorem chainWord_append (init : List In₂ ⊕ List In₁)
    (w : List (In₂ ⊕ In₁)) (d : In₂ ⊕ In₁) :
    chainWord init (w ++ [d]) = chainWordStep (chainWord init w) d := by
  simp [chainWord, List.foldl_append]

/-- The tau-tree parse of a chain word-state. -/
def revParse :
    List In₂ ⊕ List In₁ ->
      TauNodeState (In₁ := In₁) (In₂ := In₂) (A := A)
  | Sum.inl wordL => .inRevLeft wordL
  | Sum.inr wordR => .inRevRight wordR

/-- The tree node of a mixed direction word within the chain. -/
def chainNode (w : List (In₂ ⊕ In₁)) :
    TreeNode (GlobalJournalBranch (In₁ := In₁) A) :=
  w.map Sum.inr

/-! ### The narrowed chain label tree of the winner -/

section Winner

variable [Countable In₁] [Countable In₂] [Countable Out₁] [Countable Out₂]

variable (σ : StrategyPair In₁ In₂ Out₁ Out₂)
variable
  (τ :
    (uniformizationGame A σ).PositionalStrategy ParityPlayer.even)

/-- The reversed-block labels the winner stages along the chain,
indexed by the mixed direction words below the chain root. -/
noncomputable def chainNarrowed (init : List In₂ ⊕ List In₁) :
    LabeledTree (In₂ ⊕ In₁)
      (ChainLabel In₁ In₂ Out₁ Out₂ (A.State × A.State)) :=
  fun w =>
    match chainWord init w with
    | Sum.inl wordL => Sum.inl (tauRevLeftLabel σ τ wordL)
    | Sum.inr wordR => Sum.inr (tauRevRightLabel σ τ wordR)

theorem chainNarrowed_eq_left (init : List In₂ ⊕ List In₁)
    (w : List (In₂ ⊕ In₁)) (wordL : List In₂)
    (h : chainWord init w = Sum.inl wordL) :
    chainNarrowed σ τ init w = Sum.inl (tauRevLeftLabel σ τ wordL) := by
  unfold chainNarrowed
  rw [h]

theorem chainNarrowed_eq_right (init : List In₂ ⊕ List In₁)
    (w : List (In₂ ⊕ In₁)) (wordR : List In₁)
    (h : chainWord init w = Sum.inr wordR) :
    chainNarrowed σ τ init w = Sum.inr (tauRevRightLabel σ τ wordR) := by
  unfold chainNarrowed
  rw [h]

/-- The reversed-mode automaton state of a chain word-state. -/
def revModeState :
    (List In₂ ⊕ List In₁) -> CC.monitor.State ->
      Finset (ChainThread A) ->
      GlobalJournalState (In₁ := In₁) A CL CR CC
  | Sum.inl _, checker, threads =>
      Sum.inr (Sum.inr (Sum.inr (Sum.inl (checker, threads))))
  | Sum.inr _, checker, threads =>
      Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl (checker, threads)))))

theorem globalJournalPriority_revModeState
    (ws : List In₂ ⊕ List In₁) (checker : CC.monitor.State)
    (threads : Finset (ChainThread A)) :
    globalJournalPriority A CL CR CC
        (revModeState CL CR CC ws checker threads) =
      CC.monitor.priority checker + globalShift (In₁ := In₁) A := by
  cases ws <;> rfl

/-! ### Parse alignment along the chain -/

theorem tauNodeState_chainNode
    (node₁ : TreeNode (GlobalJournalBranch (In₁ := In₁) A))
    (init : List In₂ ⊕ List In₁)
    (hp : tauNodeState (In₂ := In₂) node₁ = revParse (A := A) init) :
    ∀ w : List (In₂ ⊕ In₁),
      tauNodeState (In₂ := In₂) (node₁ ++ chainNode (A := A) w) =
        revParse (A := A) (chainWord init w) := by
  intro w
  induction w using List.reverseRecOn with
  | nil => simpa [chainNode] using hp
  | append_singleton w d ih =>
      rw [show node₁ ++ chainNode (A := A) (w ++ [d]) =
          (node₁ ++ chainNode (A := A) w) ++ [Sum.inr d] from by
            simp [chainNode],
        tauNodeState_append, ih, chainWord_append]
      rcases chainWord init w with wordL | wordR <;>
        rcases d with inputTwo | inputOne <;> rfl

/-- The tree label at a chain node is the parsed reversed-block
label. -/
theorem tauTree_chainNode
    (node₁ : TreeNode (GlobalJournalBranch (In₁ := In₁) A))
    (init : List In₂ ⊕ List In₁)
    (hp : tauNodeState (In₂ := In₂) node₁ = revParse (A := A) init)
    (w : List (In₂ ⊕ In₁)) :
    tauTree σ τ (node₁ ++ chainNode (A := A) w) =
      tauLabelOf σ τ (revParse (A := A) (chainWord init w)) := by
  show tauLabelOf σ τ (tauNodeState (node₁ ++ chainNode (A := A) w)) = _
  rw [tauNodeState_chainNode node₁ init hp w]

/-! ### The chain tracking induction -/

/-- Within the reversal chain the run threads the chain checker
through the staged reversed-block labels: the checker is stepped,
never restarted, across continuations and re-reversals alike. -/
theorem globalRunIn_chain
    (node₁ : TreeNode (GlobalJournalBranch (In₁ := In₁) A))
    (init : List In₂ ⊕ List In₁)
    (T₀ : Finset (ChainThread A))
    (hp : tauNodeState (In₂ := In₂) node₁ = revParse (A := A) init)
    (hrun₁ :
      globalRunIn CL CR CC (tauTree σ τ) (Sum.inl (A.initial, A.initial))
          node₁ =
        revModeState CL CR CC init (CC.start T₀) T₀) :
    ∀ w : List (In₂ ⊕ In₁),
      ∃ threads,
        globalRunIn CL CR CC (tauTree σ τ)
            (Sum.inl (A.initial, A.initial))
            (node₁ ++ chainNode (A := A) w) =
          revModeState CL CR CC (chainWord init w)
            (DeterministicBlockMonitor.controlIn CC.monitor
              (chainNarrowed σ τ init) (CC.start T₀) w)
            threads := by
  intro w
  induction w using List.reverseRecOn with
  | nil =>
      refine ⟨T₀, ?_⟩
      simpa [chainNode] using hrun₁
  | append_singleton w d ih =>
      obtain ⟨threads, hih⟩ := ih
      have hnode :
          node₁ ++ chainNode (A := A) (w ++ [d]) =
            (node₁ ++ chainNode (A := A) w) ++ [Sum.inr d] := by
        simp [chainNode]
      have htree := tauTree_chainNode σ τ node₁ init hp w
      rcases hcw : chainWord init w with wordL | wordR <;>
        rcases d with inputTwo | inputOne <;>
        rw [hcw] at hih htree
      · refine
          ⟨revLeftStepSubset threads (tauRevLeftLabel σ τ wordL)
            inputTwo, ?_⟩
        rw [hnode, globalRunIn_append, hih, htree, chainWord_append,
          hcw,
          DeterministicBlockMonitor.controlIn_append CC.monitor w
            (chainNarrowed σ τ init) (CC.start T₀),
          chainNarrowed_eq_left σ τ init w wordL hcw]
        rfl
      · refine
          ⟨revLeftReverseSubset threads (tauRevLeftLabel σ τ wordL)
            inputOne, ?_⟩
        rw [hnode, globalRunIn_append, hih, htree, chainWord_append,
          hcw,
          DeterministicBlockMonitor.controlIn_append CC.monitor w
            (chainNarrowed σ τ init) (CC.start T₀),
          chainNarrowed_eq_left σ τ init w wordL hcw]
        rfl
      · refine
          ⟨revRightReverseSubset threads (tauRevRightLabel σ τ wordR)
            inputTwo, ?_⟩
        rw [hnode, globalRunIn_append, hih, htree, chainWord_append,
          hcw,
          DeterministicBlockMonitor.controlIn_append CC.monitor w
            (chainNarrowed σ τ init) (CC.start T₀),
          chainNarrowed_eq_right σ τ init w wordR hcw]
        rfl
      · refine
          ⟨revRightStepSubset threads (tauRevRightLabel σ τ wordR)
            inputOne, ?_⟩
        rw [hnode, globalRunIn_append, hih, htree, chainWord_append,
          hcw,
          DeterministicBlockMonitor.controlIn_append CC.monitor w
            (chainNarrowed σ τ init) (CC.start T₀),
          chainNarrowed_eq_right σ τ init w wordR hcw]
        rfl

/-! ### The environment-driven chain play -/

/-- The reversed-block position of a chain word-state and a composed
thread. -/
noncomputable def mkRevBlock :
    (List In₂ ⊕ List In₁) -> ChainThread A ->
      UniformizationPosition (In₁ := In₁) A
  | Sum.inl wordL, th =>
      .revBlockL (commitmentRevL σ τ [wordL.headD default] th.1.1 th.1.2)
        wordL th.1.1 th.1.2 th.2.1 th.2.2
  | Sum.inr wordR, th =>
      .revBlockR (commitmentRevR σ τ [wordR.headD default] th.1.1 th.1.2)
        wordR th.1.1 th.1.2 th.2.1 th.2.2

/-- The game move realizing a chain round: the direction supplies the
new receiver's input, the universal move the other component. -/
def gameMove (mv : (In₁ × In₂) × (In₂ ⊕ In₁)) : In₁ × In₂ :=
  match mv.2 with
  | Sum.inl inputTwo => (mv.1.1, inputTwo)
  | Sum.inr inputOne => (inputOne, mv.1.2)

theorem gameMove_left (mv : (In₁ × In₂) × (In₂ ⊕ In₁))
    (inputTwo : In₂) (h : mv.2 = Sum.inl inputTwo) :
    gameMove mv = (mv.1.1, inputTwo) := by
  show (match mv.2 with
    | Sum.inl inputTwo => (mv.1.1, inputTwo)
    | Sum.inr inputOne => (inputOne, mv.1.2)) = _
  rw [h]

theorem gameMove_right (mv : (In₁ × In₂) × (In₂ ⊕ In₁))
    (inputOne : In₁) (h : mv.2 = Sum.inr inputOne) :
    gameMove mv = (inputOne, mv.1.2) := by
  show (match mv.2 with
    | Sum.inl inputTwo => (mv.1.1, inputTwo)
    | Sum.inr inputOne => (inputOne, mv.1.2)) = _
  rw [h]

/-- One step of the chain play: follow the winner at Even positions,
drive the reversed blocks by the chain round at Odd positions (the
direction sort selects continue versus reverse again). -/
noncomputable def chainAdvance (mv : (In₁ × In₂) × (In₂ ⊕ In₁)) :
    UniformizationPosition (In₁ := In₁) A ->
      UniformizationPosition (In₁ := In₁) A
  | .committed atom h => .opening atom h default
  | .openingResolve atom h move o1 _o2 => uOpenLeftTarget σ atom h move o1
  | .blockEnvL h word q mn tbl => .recvL h word q mn tbl default
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
      .revRecvL hc word eqs ems q mn tbl (gameMove mv)
  | .revEnvR hc word eqs ems q mn tbl =>
      .revRecvR hc word eqs ems q mn tbl (gameMove mv)
  | .revResolveL hc word eqs ems q mn tbl move o1r o2r =>
      match mv.2 with
      | Sum.inl _ =>
          uRevContinueLTarget σ hc word eqs ems q mn move o1r
      | Sum.inr _ =>
          uRevReverseRTarget (A := A) q mn move (tbl move.1) o2r
  | .revResolveR hc word eqs ems q mn tbl move o1r o2r =>
      match mv.2 with
      | Sum.inl _ =>
          uRevReverseLTarget (A := A) q mn move o1r (tbl move.2)
      | Sum.inr _ =>
          uRevContinueRTarget σ hc word eqs ems q mn move o2r
  | pos => τ.move pos

theorem chainAdvance_step (mv : (In₁ × In₂) × (In₂ ⊕ In₁))
    (pos : UniformizationPosition (In₁ := In₁) A) :
    (uniformizationGame A σ).step pos (chainAdvance σ τ mv pos) := by
  obtain ⟨m, d⟩ := mv
  cases pos with
  | committed atom h => exact ⟨default, rfl⟩
  | openingResolve atom h move o1 o2 => exact Or.inr (Or.inl rfl)
  | blockEnvL h word q mn tbl => exact ⟨default, rfl⟩
  | resolveL h word q mn tbl move o1 => exact Or.inl rfl
  | blockEnvR h word q mn tbl => exact ⟨default, rfl⟩
  | resolveR h word q mn tbl move o2 => exact Or.inl rfl
  | closeResolveL h word q mn tbl move o1 o2 => exact Or.inl rfl
  | closeResolveR h word q mn tbl move o2 o1 => exact Or.inl rfl
  | revEnvL hc word eqs ems q mn tbl => exact ⟨gameMove (m, d), rfl⟩
  | revEnvR hc word eqs ems q mn tbl => exact ⟨gameMove (m, d), rfl⟩
  | revResolveL hc word eqs ems q mn tbl move o1r o2r =>
      cases d with
      | inl inputTwo => exact Or.inl rfl
      | inr inputOne => exact Or.inr (Or.inr rfl)
  | revResolveR hc word eqs ems q mn tbl move o1r o2r =>
      cases d with
      | inl inputTwo => exact Or.inr (Or.inr rfl)
      | inr inputOne => exact Or.inl rfl
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

theorem chainAdvance_eq_tau_of_even (mv : (In₁ × In₂) × (In₂ ⊕ In₁))
    (pos : UniformizationPosition (In₁ := In₁) A)
    (h : (uniformizationGame A σ).owner pos = ParityPlayer.even) :
    chainAdvance σ τ mv pos = τ.move pos := by
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

/-- The chain play together with its round counter.  The play drives
the reversed blocks by the direction of the current round; the counter
increments once per round, exactly when the play leaves a resolve
position.  Since a round has variable length (four game steps for a
continuation, five for a reversal), the counter — not `t / 3` — is what
indexes the environment and reindexes the fold. -/
noncomputable def chainAux (env : Nat -> (In₁ × In₂) × (In₂ ⊕ In₁))
    (start : UniformizationPosition (In₁ := In₁) A) :
    Nat -> UniformizationPosition (In₁ := In₁) A × Nat
  | 0 => (start, 0)
  | t + 1 =>
      let pr := chainAux env start t
      (chainAdvance σ τ (env pr.2) pr.1,
        match pr.1 with
        | .revResolveL _ _ _ _ _ _ _ _ _ _ => pr.2 + 1
        | .revResolveR _ _ _ _ _ _ _ _ _ _ => pr.2 + 1
        | _ => pr.2)

/-- The chain play. -/
noncomputable def chainPlay (env : Nat -> (In₁ × In₂) × (In₂ ⊕ In₁))
    (start : UniformizationPosition (In₁ := In₁) A) (t : Nat) :
    UniformizationPosition (In₁ := In₁) A :=
  (chainAux σ τ env start t).1

/-- The round counter of the chain play. -/
noncomputable def roundAt (env : Nat -> (In₁ × In₂) × (In₂ ⊕ In₁))
    (start : UniformizationPosition (In₁ := In₁) A) (t : Nat) : Nat :=
  (chainAux σ τ env start t).2

theorem chainPlay_zero (env : Nat -> (In₁ × In₂) × (In₂ ⊕ In₁))
    (start : UniformizationPosition (In₁ := In₁) A) :
    chainPlay σ τ env start 0 = start :=
  rfl

theorem roundAt_zero (env : Nat -> (In₁ × In₂) × (In₂ ⊕ In₁))
    (start : UniformizationPosition (In₁ := In₁) A) :
    roundAt σ τ env start 0 = 0 :=
  rfl

theorem chainPlay_succ (env : Nat -> (In₁ × In₂) × (In₂ ⊕ In₁))
    (start : UniformizationPosition (In₁ := In₁) A) (t : Nat) :
    chainPlay σ τ env start (t + 1) =
      chainAdvance σ τ (env (roundAt σ τ env start t))
        (chainPlay σ τ env start t) :=
  rfl

theorem roundAt_succ (env : Nat -> (In₁ × In₂) × (In₂ ⊕ In₁))
    (start : UniformizationPosition (In₁ := In₁) A) (t : Nat) :
    roundAt σ τ env start (t + 1) =
      match chainPlay σ τ env start t with
      | .revResolveL _ _ _ _ _ _ _ _ _ _ => roundAt σ τ env start t + 1
      | .revResolveR _ _ _ _ _ _ _ _ _ _ => roundAt σ τ env start t + 1
      | _ => roundAt σ τ env start t :=
  rfl

theorem chainPlay_step (env : Nat -> (In₁ × In₂) × (In₂ ⊕ In₁))
    (start : UniformizationPosition (In₁ := In₁) A) (t : Nat) :
    (uniformizationGame A σ).step (chainPlay σ τ env start t)
      (chainPlay σ τ env start (t + 1)) := by
  rw [chainPlay_succ]
  exact chainAdvance_step σ τ (env (roundAt σ τ env start t))
    (chainPlay σ τ env start t)

theorem chainPlay_consistent (env : Nat -> (In₁ × In₂) × (In₂ ⊕ In₁))
    (start : UniformizationPosition (In₁ := In₁) A) (t : Nat)
    (h :
      (uniformizationGame A σ).owner (chainPlay σ τ env start t) =
        ParityPlayer.even) :
    chainPlay σ τ env start (t + 1) =
      τ.move (chainPlay σ τ env start t) := by
  rw [chainPlay_succ]
  exact chainAdvance_eq_tau_of_even σ τ (env (roundAt σ τ env start t))
    (chainPlay σ τ env start t) h

/-! ### The three-step round advance on reversed blocks -/

theorem chainAdvance_revResolveL_continue
    (mv : (In₁ × In₂) × (In₂ ⊕ In₁)) (inputTwo : In₂)
    (hd : mv.2 = Sum.inl inputTwo)
    (hc : History In₁ In₂ Graph Out₁ Out₂) (word : List In₂)
    (eqs ems q mn : A.State) (tbl : In₁ -> Out₁) (move : In₁ × In₂)
    (o1r : Out₁) (o2r : Out₂) :
    chainAdvance σ τ mv
        (.revResolveL hc word eqs ems q mn tbl move o1r o2r) =
      uRevContinueLTarget σ hc word eqs ems q mn move o1r := by
  show (match mv.2 with
    | Sum.inl _ => uRevContinueLTarget σ hc word eqs ems q mn move o1r
    | Sum.inr _ =>
        uRevReverseRTarget (A := A) q mn move (tbl move.1) o2r) = _
  rw [hd]

theorem chainAdvance_revResolveL_reverse
    (mv : (In₁ × In₂) × (In₂ ⊕ In₁)) (inputOne : In₁)
    (hd : mv.2 = Sum.inr inputOne)
    (hc : History In₁ In₂ Graph Out₁ Out₂) (word : List In₂)
    (eqs ems q mn : A.State) (tbl : In₁ -> Out₁) (move : In₁ × In₂)
    (o1r : Out₁) (o2r : Out₂) :
    chainAdvance σ τ mv
        (.revResolveL hc word eqs ems q mn tbl move o1r o2r) =
      uRevReverseRTarget (A := A) q mn move (tbl move.1) o2r := by
  show (match mv.2 with
    | Sum.inl _ => uRevContinueLTarget σ hc word eqs ems q mn move o1r
    | Sum.inr _ =>
        uRevReverseRTarget (A := A) q mn move (tbl move.1) o2r) = _
  rw [hd]

theorem chainAdvance_revResolveR_continue
    (mv : (In₁ × In₂) × (In₂ ⊕ In₁)) (inputOne : In₁)
    (hd : mv.2 = Sum.inr inputOne)
    (hc : History In₁ In₂ Graph Out₁ Out₂) (word : List In₁)
    (eqs ems q mn : A.State) (tbl : In₂ -> Out₂) (move : In₁ × In₂)
    (o1r : Out₁) (o2r : Out₂) :
    chainAdvance σ τ mv
        (.revResolveR hc word eqs ems q mn tbl move o1r o2r) =
      uRevContinueRTarget σ hc word eqs ems q mn move o2r := by
  show (match mv.2 with
    | Sum.inl _ =>
        uRevReverseLTarget (A := A) q mn move o1r (tbl move.2)
    | Sum.inr _ => uRevContinueRTarget σ hc word eqs ems q mn move o2r) =
      _
  rw [hd]

theorem chainAdvance_revResolveR_reverse
    (mv : (In₁ × In₂) × (In₂ ⊕ In₁)) (inputTwo : In₂)
    (hd : mv.2 = Sum.inl inputTwo)
    (hc : History In₁ In₂ Graph Out₁ Out₂) (word : List In₁)
    (eqs ems q mn : A.State) (tbl : In₂ -> Out₂) (move : In₁ × In₂)
    (o1r : Out₁) (o2r : Out₂) :
    chainAdvance σ τ mv
        (.revResolveR hc word eqs ems q mn tbl move o1r o2r) =
      uRevReverseLTarget (A := A) q mn move o1r (tbl move.2) := by
  show (match mv.2 with
    | Sum.inl _ =>
        uRevReverseLTarget (A := A) q mn move o1r (tbl move.2)
    | Sum.inr _ => uRevContinueRTarget σ hc word eqs ems q mn move o2r) =
      _
  rw [hd]

/-- The first three advances from a reversed left block: commit the
blind-send table, receive the round move, and answer, landing at the
resolve position. -/
theorem revBlockL_three (mv : (In₁ × In₂) × (In₂ ⊕ In₁))
    (hc : History In₁ In₂ Graph Out₁ Out₂) (word : List In₂)
    (es em s ms : A.State) :
    chainAdvance σ τ mv (chainAdvance σ τ mv (chainAdvance σ τ mv
        (.revBlockL hc word es em s ms))) =
      .revResolveL hc word es em s ms
        (revSendTableL σ τ hc word es em s ms) (gameMove mv)
        (revRecvChoiceL σ τ hc word es em s ms (gameMove mv)).1
        (revRecvChoiceL σ τ hc word es em s ms (gameMove mv)).2 := by
  rw [show chainAdvance σ τ mv (.revBlockL hc word es em s ms) =
        τ.move (.revBlockL hc word es em s ms) from rfl,
      revSendTableL_spec σ τ hc word es em s ms]
  rw [show chainAdvance σ τ mv (chainAdvance σ τ mv
        (.revEnvL hc word es em s ms
          (revSendTableL σ τ hc word es em s ms))) =
        τ.move (.revRecvL hc word es em s ms
          (revSendTableL σ τ hc word es em s ms) (gameMove mv)) from rfl,
      revRecvChoiceL_spec σ τ hc word es em s ms (gameMove mv)]

/-- The mirror of `revBlockL_three` for reversed right blocks. -/
theorem revBlockR_three (mv : (In₁ × In₂) × (In₂ ⊕ In₁))
    (hc : History In₁ In₂ Graph Out₁ Out₂) (word : List In₁)
    (es em s ms : A.State) :
    chainAdvance σ τ mv (chainAdvance σ τ mv (chainAdvance σ τ mv
        (.revBlockR hc word es em s ms))) =
      .revResolveR hc word es em s ms
        (revSendTableR σ τ hc word es em s ms) (gameMove mv)
        (revRecvChoiceR σ τ hc word es em s ms (gameMove mv)).1
        (revRecvChoiceR σ τ hc word es em s ms (gameMove mv)).2 := by
  rw [show chainAdvance σ τ mv (.revBlockR hc word es em s ms) =
        τ.move (.revBlockR hc word es em s ms) from rfl,
      revSendTableR_spec σ τ hc word es em s ms]
  rw [show chainAdvance σ τ mv (chainAdvance σ τ mv
        (.revEnvR hc word es em s ms
          (revSendTableR σ τ hc word es em s ms))) =
        τ.move (.revRecvR hc word es em s ms
          (revSendTableR σ τ hc word es em s ms) (gameMove mv)) from rfl,
      revRecvChoiceR_spec σ τ hc word es em s ms (gameMove mv)]

/-- One advance from a right-reversal commit position opens the fresh
reversed right block. -/
theorem revCommitR_advance (mv : (In₁ × In₂) × (In₂ ⊕ In₁))
    (word : List In₁) (es em : A.State) :
    chainAdvance σ τ mv (.revCommitR word es em) =
      .revBlockR (commitmentRevR σ τ word es em) word es em es em := by
  rw [show chainAdvance σ τ mv (.revCommitR word es em) =
        τ.move (.revCommitR word es em) from rfl,
      commitmentRevR_spec σ τ word es em]

/-- The mirror of `revCommitR_advance`. -/
theorem revCommitL_advance (mv : (In₁ × In₂) × (In₂ ⊕ In₁))
    (word : List In₂) (es em : A.State) :
    chainAdvance σ τ mv (.revCommitL word es em) =
      .revBlockL (commitmentRevL σ τ word es em) word es em es em := by
  rw [show chainAdvance σ τ mv (.revCommitL word es em) =
        τ.move (.revCommitL word es em) from rfl,
      commitmentRevL_spec σ τ word es em]

/-- The fifth advance of a reverse round out of a left block: the
right-reversal target commits and opens the new right block. -/
theorem uRevReverseRTarget_advance (mv : (In₁ × In₂) × (In₂ ⊕ In₁))
    (state minState : A.State) (move : In₁ × In₂) (o1s : Out₁)
    (o2r : Out₂) :
    chainAdvance σ τ mv (uRevReverseRTarget (A := A) state minState move
        o1s o2r) =
      .revBlockR
        (commitmentRevR σ τ [move.1]
          (A.step state (rightRoundRecord (move.2, move.1) o1s o2r))
          (A.minPriorityState minState
            (A.step state (rightRoundRecord (move.2, move.1) o1s o2r))))
        [move.1]
        (A.step state (rightRoundRecord (move.2, move.1) o1s o2r))
        (A.minPriorityState minState
          (A.step state (rightRoundRecord (move.2, move.1) o1s o2r)))
        (A.step state (rightRoundRecord (move.2, move.1) o1s o2r))
        (A.minPriorityState minState
          (A.step state (rightRoundRecord (move.2, move.1) o1s o2r))) :=
  revCommitR_advance σ τ mv [move.1]
    (A.step state (rightRoundRecord (move.2, move.1) o1s o2r))
    (A.minPriorityState minState
      (A.step state (rightRoundRecord (move.2, move.1) o1s o2r)))

/-- The mirror: the reverse round out of a right block opens a new left
block. -/
theorem uRevReverseLTarget_advance (mv : (In₁ × In₂) × (In₂ ⊕ In₁))
    (state minState : A.State) (move : In₁ × In₂) (o1r : Out₁)
    (o2s : Out₂) :
    chainAdvance σ τ mv (uRevReverseLTarget (A := A) state minState move
        o1r o2s) =
      .revBlockL
        (commitmentRevL σ τ [move.2]
          (A.step state (leftRoundRecord move o1r o2s))
          (A.minPriorityState minState
            (A.step state (leftRoundRecord move o1r o2s))))
        [move.2]
        (A.step state (leftRoundRecord move o1r o2s))
        (A.minPriorityState minState
          (A.step state (leftRoundRecord move o1r o2s)))
        (A.step state (leftRoundRecord move o1r o2s))
        (A.minPriorityState minState
          (A.step state (leftRoundRecord move o1r o2s))) :=
  revCommitL_advance σ τ mv [move.2]
    (A.step state (leftRoundRecord move o1r o2s))
    (A.minPriorityState minState
      (A.step state (leftRoundRecord move o1r o2s)))

/-- A continuation round of a reversed left block is four advances: the
reversed word grows and the composed thread steps. -/
theorem chainAdvance4_left_continue
    (mv : (In₁ × In₂) × (In₂ ⊕ In₁)) (inputTwo : In₂)
    (hd : mv.2 = Sum.inl inputTwo) (wordL : List In₂)
    (hne : wordL ≠ []) (th : ChainThread A) :
    chainAdvance σ τ mv (chainAdvance σ τ mv (chainAdvance σ τ mv
        (chainAdvance σ τ mv (mkRevBlock σ τ (Sum.inl wordL) th)))) =
      mkRevBlock σ τ (Sum.inl (wordL ++ [inputTwo]))
        (revLeftThreadStep A th (tauRevLeftLabel σ τ wordL) mv.1.1
          inputTwo) := by
  obtain ⟨a, t, rfl⟩ := List.exists_cons_of_ne_nil hne
  rw [show mkRevBlock σ τ (Sum.inl (a :: t)) th =
        .revBlockL (commitmentRevL σ τ [a] th.1.1 th.1.2) (a :: t)
          th.1.1 th.1.2 th.2.1 th.2.2 from rfl,
      revBlockL_three σ τ mv (commitmentRevL σ τ [a] th.1.1 th.1.2)
        (a :: t) th.1.1 th.1.2 th.2.1 th.2.2,
      chainAdvance_revResolveL_continue σ τ mv inputTwo hd,
      gameMove_left mv inputTwo hd]
  rfl

/-- A continuation round of a reversed right block is four advances. -/
theorem chainAdvance4_right_continue
    (mv : (In₁ × In₂) × (In₂ ⊕ In₁)) (inputOne : In₁)
    (hd : mv.2 = Sum.inr inputOne) (wordR : List In₁)
    (hne : wordR ≠ []) (th : ChainThread A) :
    chainAdvance σ τ mv (chainAdvance σ τ mv (chainAdvance σ τ mv
        (chainAdvance σ τ mv (mkRevBlock σ τ (Sum.inr wordR) th)))) =
      mkRevBlock σ τ (Sum.inr (wordR ++ [inputOne]))
        (revRightThreadStep A th (tauRevRightLabel σ τ wordR) inputOne
          mv.1.2) := by
  obtain ⟨a, t, rfl⟩ := List.exists_cons_of_ne_nil hne
  rw [show mkRevBlock σ τ (Sum.inr (a :: t)) th =
        .revBlockR (commitmentRevR σ τ [a] th.1.1 th.1.2) (a :: t)
          th.1.1 th.1.2 th.2.1 th.2.2 from rfl,
      revBlockR_three σ τ mv (commitmentRevR σ τ [a] th.1.1 th.1.2)
        (a :: t) th.1.1 th.1.2 th.2.1 th.2.2,
      chainAdvance_revResolveR_continue σ τ mv inputOne hd,
      gameMove_right mv inputOne hd]
  rfl

/-- A reverse round out of a reversed left block is five advances: the
extra commit opens the new right block; the composed thread doubles. -/
theorem chainAdvance5_left_reverse
    (mv : (In₁ × In₂) × (In₂ ⊕ In₁)) (inputOne : In₁)
    (hd : mv.2 = Sum.inr inputOne) (wordL : List In₂)
    (th : ChainThread A) :
    chainAdvance σ τ mv (chainAdvance σ τ mv (chainAdvance σ τ mv
        (chainAdvance σ τ mv (chainAdvance σ τ mv
          (mkRevBlock σ τ (Sum.inl wordL) th))))) =
      mkRevBlock σ τ (Sum.inr [inputOne])
        (revLeftThreadReverse A th (tauRevLeftLabel σ τ wordL) inputOne
          mv.1.2) := by
  rw [show mkRevBlock σ τ (Sum.inl wordL) th =
        .revBlockL (commitmentRevL σ τ [wordL.headD default] th.1.1 th.1.2)
          wordL th.1.1 th.1.2 th.2.1 th.2.2 from rfl,
      revBlockL_three σ τ mv
        (commitmentRevL σ τ [wordL.headD default] th.1.1 th.1.2) wordL
        th.1.1 th.1.2 th.2.1 th.2.2,
      chainAdvance_revResolveL_reverse σ τ mv inputOne hd,
      gameMove_right mv inputOne hd,
      uRevReverseRTarget_advance σ τ mv th.2.1 th.2.2 (inputOne, mv.1.2)
        _ _]
  rfl

/-- The mirror: a reverse round out of a reversed right block. -/
theorem chainAdvance5_right_reverse
    (mv : (In₁ × In₂) × (In₂ ⊕ In₁)) (inputTwo : In₂)
    (hd : mv.2 = Sum.inl inputTwo) (wordR : List In₁)
    (th : ChainThread A) :
    chainAdvance σ τ mv (chainAdvance σ τ mv (chainAdvance σ τ mv
        (chainAdvance σ τ mv (chainAdvance σ τ mv
          (mkRevBlock σ τ (Sum.inr wordR) th))))) =
      mkRevBlock σ τ (Sum.inl [inputTwo])
        (revRightThreadReverse A th (tauRevRightLabel σ τ wordR) mv.1.1
          inputTwo) := by
  rw [show mkRevBlock σ τ (Sum.inr wordR) th =
        .revBlockR (commitmentRevR σ τ [wordR.headD default] th.1.1 th.1.2)
          wordR th.1.1 th.1.2 th.2.1 th.2.2 from rfl,
      revBlockR_three σ τ mv
        (commitmentRevR σ τ [wordR.headD default] th.1.1 th.1.2) wordR
        th.1.1 th.1.2 th.2.1 th.2.2,
      chainAdvance_revResolveR_reverse σ τ mv inputTwo hd,
      gameMove_left mv inputTwo hd,
      uRevReverseLTarget_advance σ τ mv th.2.1 th.2.2 (mv.1.1, inputTwo)
        _ _]
  rfl

/-! ### The chain tracking of the play -/

theorem chainFold_snoc
    (narrowed :
      LabeledTree (In₂ ⊕ In₁)
        (ChainLabel In₁ In₂ Out₁ Out₂ (A.State × A.State))) :
    ∀ (steps : TreeNode ((In₁ × In₂) × (In₂ ⊕ In₁)))
      (word : List (In₂ ⊕ In₁)) (th : ChainThread A)
      (st : (In₁ × In₂) × (In₂ ⊕ In₁)),
      chainFold A narrowed word th (steps ++ [st]) =
        chainThreadStep A (chainFold A narrowed word th steps)
          (narrowed (word ++ steps.map Prod.snd)) st.2 st.1
  | [], word, th, st => by simp [chainFold]
  | s :: rest, word, th, st => by
      show chainFold A narrowed (word ++ [s.2])
          (chainThreadStep A th (narrowed word) s.2 s.1) (rest ++ [st]) =
        _
      rw [chainFold_snoc narrowed rest (word ++ [s.2]) _ st,
        List.append_assoc]
      rfl

theorem chainFold_snoc_nil
    (narrowed :
      LabeledTree (In₂ ⊕ In₁)
        (ChainLabel In₁ In₂ Out₁ Out₂ (A.State × A.State)))
    (steps : TreeNode ((In₁ × In₂) × (In₂ ⊕ In₁)))
    (th : ChainThread A) (st : (In₁ × In₂) × (In₂ ⊕ In₁)) :
    chainFold A narrowed [] th (steps ++ [st]) =
      chainThreadStep A (chainFold A narrowed [] th steps)
        (narrowed (steps.map Prod.snd)) st.2 st.1 := by
  rw [chainFold_snoc]
  rfl

theorem branchNode_map_snd (env : Nat -> (In₁ × In₂) × (In₂ ⊕ In₁)) :
    ∀ k : Nat,
      (branchNode env k).map Prod.snd =
        branchNode (fun n => (env n).2) k
  | 0 => rfl
  | k + 1 => by
      rw [show branchNode env (k + 1) = branchNode env k ++ [env k]
          from rfl,
        List.map_append, branchNode_map_snd env k]
      rfl

/-! ### The round-phase invariant of the chain play

A chain-play position is at one of the phases of the round it belongs to,
carrying that round's reversed word `W` and composed thread `F`.  Every
such position has priority `A.priority F.2.1` (the composed thread's
current tracked state), which is exactly the fold-side sequence of
`ChainAllThreadsWin`.  The reversal commit that opens a fresh block is
recorded abstractly (it advances to `mkRevBlock W F` and its entry state
already carries `F.2.1`), so the doubled-thread and singleton-word facts
of a reversal need not be respelled. -/

/-- The reversal-commit position opening a block of orientation `W`. -/
noncomputable def revCommitOf (W : List In₂ ⊕ List In₁) (es em : A.State) :
    UniformizationPosition (In₁ := In₁) A :=
  match W with
  | Sum.inl wordL => .revCommitL wordL es em
  | Sum.inr wordR => .revCommitR wordR es em

/-- The phases of a single reversed-chain round. -/
noncomputable def RoundPhase (mv : (In₁ × In₂) × (In₂ ⊕ In₁))
    (W : List In₂ ⊕ List In₁) (F : ChainThread A)
    (p : UniformizationPosition (In₁ := In₁) A) : Prop :=
  p = mkRevBlock σ τ W F ∨
  (∃ es em : A.State,
      p = revCommitOf (A := A) W es em ∧
        chainAdvance σ τ mv p = mkRevBlock σ τ W F ∧
        A.priority es = A.priority F.2.1) ∨
  (match W with
   | Sum.inl wordL =>
       p = .revEnvL (commitmentRevL σ τ [wordL.headD default] F.1.1 F.1.2)
             wordL F.1.1 F.1.2 F.2.1 F.2.2
             (revSendTableL σ τ
               (commitmentRevL σ τ [wordL.headD default] F.1.1 F.1.2)
               wordL F.1.1 F.1.2 F.2.1 F.2.2) ∨
       p = .revRecvL (commitmentRevL σ τ [wordL.headD default] F.1.1 F.1.2)
             wordL F.1.1 F.1.2 F.2.1 F.2.2
             (revSendTableL σ τ
               (commitmentRevL σ τ [wordL.headD default] F.1.1 F.1.2)
               wordL F.1.1 F.1.2 F.2.1 F.2.2)
             (gameMove mv) ∨
       p = .revResolveL
             (commitmentRevL σ τ [wordL.headD default] F.1.1 F.1.2)
             wordL F.1.1 F.1.2 F.2.1 F.2.2
             (revSendTableL σ τ
               (commitmentRevL σ τ [wordL.headD default] F.1.1 F.1.2)
               wordL F.1.1 F.1.2 F.2.1 F.2.2)
             (gameMove mv)
             (revRecvChoiceL σ τ
               (commitmentRevL σ τ [wordL.headD default] F.1.1 F.1.2)
               wordL F.1.1 F.1.2 F.2.1 F.2.2 (gameMove mv)).1
             (revRecvChoiceL σ τ
               (commitmentRevL σ τ [wordL.headD default] F.1.1 F.1.2)
               wordL F.1.1 F.1.2 F.2.1 F.2.2 (gameMove mv)).2
   | Sum.inr wordR =>
       p = .revEnvR (commitmentRevR σ τ [wordR.headD default] F.1.1 F.1.2)
             wordR F.1.1 F.1.2 F.2.1 F.2.2
             (revSendTableR σ τ
               (commitmentRevR σ τ [wordR.headD default] F.1.1 F.1.2)
               wordR F.1.1 F.1.2 F.2.1 F.2.2) ∨
       p = .revRecvR (commitmentRevR σ τ [wordR.headD default] F.1.1 F.1.2)
             wordR F.1.1 F.1.2 F.2.1 F.2.2
             (revSendTableR σ τ
               (commitmentRevR σ τ [wordR.headD default] F.1.1 F.1.2)
               wordR F.1.1 F.1.2 F.2.1 F.2.2)
             (gameMove mv) ∨
       p = .revResolveR
             (commitmentRevR σ τ [wordR.headD default] F.1.1 F.1.2)
             wordR F.1.1 F.1.2 F.2.1 F.2.2
             (revSendTableR σ τ
               (commitmentRevR σ τ [wordR.headD default] F.1.1 F.1.2)
               wordR F.1.1 F.1.2 F.2.1 F.2.2)
             (gameMove mv)
             (revRecvChoiceR σ τ
               (commitmentRevR σ τ [wordR.headD default] F.1.1 F.1.2)
               wordR F.1.1 F.1.2 F.2.1 F.2.2 (gameMove mv)).1
             (revRecvChoiceR σ τ
               (commitmentRevR σ τ [wordR.headD default] F.1.1 F.1.2)
               wordR F.1.1 F.1.2 F.2.1 F.2.2 (gameMove mv)).2)

/-- Every phase of a round carries the composed thread's tracked state. -/
theorem roundPhase_priority (mv : (In₁ × In₂) × (In₂ ⊕ In₁))
    (W : List In₂ ⊕ List In₁) (F : ChainThread A)
    (p : UniformizationPosition (In₁ := In₁) A)
    (h : RoundPhase σ τ mv W F p) :
    uniformizationPriority p = A.priority F.2.1 := by
  rcases h with hb | ⟨es, em, hp, -, hpri⟩ | hmid
  · subst hb; cases W <;> rfl
  · subst hp; cases W <;> exact hpri
  · cases W with
    | inl wordL => rcases hmid with h | h | h <;> subst h <;> rfl
    | inr wordR => rcases hmid with h | h | h <;> subst h <;> rfl

/-- Nonemptiness of a chain word-state, in either orientation. -/
def chainWordNonempty : List In₂ ⊕ List In₁ -> Prop
  | Sum.inl wordL => wordL ≠ []
  | Sum.inr wordR => wordR ≠ []

/-! ### Single-step phase advances -/

theorem advance_revBlock_left (mv : (In₁ × In₂) × (In₂ ⊕ In₁))
    (wordL : List In₂) (F : ChainThread A) :
    chainAdvance σ τ mv (mkRevBlock σ τ (Sum.inl wordL) F) =
      .revEnvL (commitmentRevL σ τ [wordL.headD default] F.1.1 F.1.2)
        wordL F.1.1 F.1.2 F.2.1 F.2.2
        (revSendTableL σ τ
          (commitmentRevL σ τ [wordL.headD default] F.1.1 F.1.2) wordL
          F.1.1 F.1.2 F.2.1 F.2.2) := by
  rw [show chainAdvance σ τ mv (mkRevBlock σ τ (Sum.inl wordL) F) =
        τ.move (.revBlockL
          (commitmentRevL σ τ [wordL.headD default] F.1.1 F.1.2) wordL
          F.1.1 F.1.2 F.2.1 F.2.2) from rfl,
      revSendTableL_spec σ τ
        (commitmentRevL σ τ [wordL.headD default] F.1.1 F.1.2) wordL
        F.1.1 F.1.2 F.2.1 F.2.2]

theorem advance_revBlock_right (mv : (In₁ × In₂) × (In₂ ⊕ In₁))
    (wordR : List In₁) (F : ChainThread A) :
    chainAdvance σ τ mv (mkRevBlock σ τ (Sum.inr wordR) F) =
      .revEnvR (commitmentRevR σ τ [wordR.headD default] F.1.1 F.1.2)
        wordR F.1.1 F.1.2 F.2.1 F.2.2
        (revSendTableR σ τ
          (commitmentRevR σ τ [wordR.headD default] F.1.1 F.1.2) wordR
          F.1.1 F.1.2 F.2.1 F.2.2) := by
  rw [show chainAdvance σ τ mv (mkRevBlock σ τ (Sum.inr wordR) F) =
        τ.move (.revBlockR
          (commitmentRevR σ τ [wordR.headD default] F.1.1 F.1.2) wordR
          F.1.1 F.1.2 F.2.1 F.2.2) from rfl,
      revSendTableR_spec σ τ
        (commitmentRevR σ τ [wordR.headD default] F.1.1 F.1.2) wordR
        F.1.1 F.1.2 F.2.1 F.2.2]

theorem advance_revEnv_left (mv : (In₁ × In₂) × (In₂ ⊕ In₁))
    (hc : History In₁ In₂ Graph Out₁ Out₂) (word : List In₂)
    (es em s ms : A.State) (tbl : In₁ -> Out₁) :
    chainAdvance σ τ mv (.revEnvL hc word es em s ms tbl) =
      .revRecvL hc word es em s ms tbl (gameMove mv) :=
  rfl

theorem advance_revEnv_right (mv : (In₁ × In₂) × (In₂ ⊕ In₁))
    (hc : History In₁ In₂ Graph Out₁ Out₂) (word : List In₁)
    (es em s ms : A.State) (tbl : In₂ -> Out₂) :
    chainAdvance σ τ mv (.revEnvR hc word es em s ms tbl) =
      .revRecvR hc word es em s ms tbl (gameMove mv) :=
  rfl

theorem advance_revRecv_left (mv : (In₁ × In₂) × (In₂ ⊕ In₁))
    (hc : History In₁ In₂ Graph Out₁ Out₂) (word : List In₂)
    (es em s ms : A.State) (move : In₁ × In₂) :
    chainAdvance σ τ mv
        (.revRecvL hc word es em s ms
          (revSendTableL σ τ hc word es em s ms) move) =
      .revResolveL hc word es em s ms
        (revSendTableL σ τ hc word es em s ms) move
        (revRecvChoiceL σ τ hc word es em s ms move).1
        (revRecvChoiceL σ τ hc word es em s ms move).2 := by
  rw [show chainAdvance σ τ mv
        (.revRecvL hc word es em s ms
          (revSendTableL σ τ hc word es em s ms) move) =
        τ.move (.revRecvL hc word es em s ms
          (revSendTableL σ τ hc word es em s ms) move) from rfl,
      revRecvChoiceL_spec σ τ hc word es em s ms move]

theorem advance_revRecv_right (mv : (In₁ × In₂) × (In₂ ⊕ In₁))
    (hc : History In₁ In₂ Graph Out₁ Out₂) (word : List In₁)
    (es em s ms : A.State) (move : In₁ × In₂) :
    chainAdvance σ τ mv
        (.revRecvR hc word es em s ms
          (revSendTableR σ τ hc word es em s ms) move) =
      .revResolveR hc word es em s ms
        (revSendTableR σ τ hc word es em s ms) move
        (revRecvChoiceR σ τ hc word es em s ms move).1
        (revRecvChoiceR σ τ hc word es em s ms move).2 := by
  rw [show chainAdvance σ τ mv
        (.revRecvR hc word es em s ms
          (revSendTableR σ τ hc word es em s ms) move) =
        τ.move (.revRecvR hc word es em s ms
          (revSendTableR σ τ hc word es em s ms) move) from rfl,
      revRecvChoiceR_spec σ τ hc word es em s ms move]

/-- The chain play tracks the composed-thread fold round by round. -/
theorem chainPlay_track
    (env : Nat -> (In₁ × In₂) × (In₂ ⊕ In₁))
    (init : List In₂ ⊕ List In₁) (th₀ : ChainThread A)
    (hinit : chainWordNonempty init) (t : Nat) :
    RoundPhase σ τ
        (env (roundAt σ τ env (mkRevBlock σ τ init th₀) t))
        (chainWord init
          (branchNode (fun n => (env n).2)
            (roundAt σ τ env (mkRevBlock σ τ init th₀) t)))
        (chainFold A (chainNarrowed σ τ init) [] th₀
          (branchNode env (roundAt σ τ env (mkRevBlock σ τ init th₀) t)))
        (chainPlay σ τ env (mkRevBlock σ τ init th₀) t) ∧
      chainWordNonempty
        (chainWord init
          (branchNode (fun n => (env n).2)
            (roundAt σ τ env (mkRevBlock σ τ init th₀) t))) := by
  induction t with
  | zero => exact ⟨Or.inl rfl, hinit⟩
  | succ t ih =>
      obtain ⟨ihP, ihNE⟩ := ih
      set k := roundAt σ τ env (mkRevBlock σ τ init th₀) t with hk
      rw [chainPlay_succ, ← hk]
      have hWnext :
          chainWord init (branchNode (fun n => (env n).2) (k + 1)) =
            chainWordStep
              (chainWord init (branchNode (fun n => (env n).2) k))
              (env k).2 := by
        rw [show branchNode (fun n => (env n).2) (k + 1) =
              branchNode (fun n => (env n).2) k ++ [(env k).2] from rfl,
          chainWord_append]
      have hFnext :
          chainFold A (chainNarrowed σ τ init) [] th₀
              (branchNode env (k + 1)) =
            chainThreadStep A
              (chainFold A (chainNarrowed σ τ init) [] th₀
                (branchNode env k))
              (chainNarrowed σ τ init
                (branchNode (fun n => (env n).2) k))
              (env k).2 (env k).1 := by
        rw [show branchNode env (k + 1) = branchNode env k ++ [env k]
              from rfl,
          chainFold_snoc_nil, branchNode_map_snd env k]
      rcases hW : chainWord init (branchNode (fun n => (env n).2) k) with
        wordL | wordR
      · -- LEFT orientation of the current round
        rw [hW] at ihP ihNE
        rcases ihP with hb | ⟨es, em, hpc, hadvc, hpri⟩ | hmid
        · -- block phase
          have hr :
              roundAt σ τ env (mkRevBlock σ τ init th₀) (t + 1) = k := by
            rw [roundAt_succ, hb]; rfl
          rw [hr, hb, hW]
          exact
            ⟨Or.inr (Or.inr (Or.inl
              (advance_revBlock_left σ τ (env k) wordL _))), ihNE⟩
        · -- commit phase
          have hr :
              roundAt σ τ env (mkRevBlock σ τ init th₀) (t + 1) = k := by
            rw [roundAt_succ, hpc]; rfl
          rw [hr, hpc, hW]
          refine ⟨Or.inl ?_, ihNE⟩
          rw [← hpc]; exact hadvc
        · -- env / recv / resolve phases
          rcases hmid with hEnv | hRecv | hResolve
          · -- env → recv
            have hr :
                roundAt σ τ env (mkRevBlock σ τ init th₀) (t + 1) = k := by
              rw [roundAt_succ, hEnv]
            rw [hr, hEnv, hW]
            exact
              ⟨Or.inr (Or.inr (Or.inr (Or.inl
                (advance_revEnv_left σ τ (env k) _ wordL _ _ _ _ _)))),
                ihNE⟩
          · -- recv → resolve
            have hr :
                roundAt σ τ env (mkRevBlock σ τ init th₀) (t + 1) = k := by
              rw [roundAt_succ, hRecv]
            rw [hr, hRecv, hW]
            exact
              ⟨Or.inr (Or.inr (Or.inr (Or.inr
                (advance_revRecv_left σ τ (env k) _ wordL _ _ _ _ _)))),
                ihNE⟩
          · -- resolve → next round
            have hr :
                roundAt σ τ env (mkRevBlock σ τ init th₀) (t + 1) =
                  k + 1 := by
              rw [roundAt_succ, hResolve]
            rw [hr, hResolve, hWnext, hFnext, hW,
              chainNarrowed_eq_left σ τ init _ wordL hW]
            rcases hd : (env k).2 with inputTwo | inputOne
            · -- continuation (left round on a left block)
              obtain ⟨a, tl, rfl⟩ :=
                List.exists_cons_of_ne_nil (show wordL ≠ [] from ihNE)
              rw [chainAdvance_revResolveL_continue σ τ (env k) inputTwo hd,
                gameMove_left (env k) inputTwo hd]
              exact ⟨Or.inl rfl, by simp [chainWordNonempty, chainWordStep]⟩
            · -- reversal (right round on a left block) → right commit
              rw [chainAdvance_revResolveL_reverse σ τ (env k) inputOne hd,
                gameMove_right (env k) inputOne hd]
              refine ⟨Or.inr (Or.inl ⟨_, _, rfl, ?_, rfl⟩),
                by simp [chainWordNonempty, chainWordStep]⟩
              rw [uRevReverseRTarget_advance σ τ (env (k + 1)) _ _
                (inputOne, _) _ _]
              rfl
      · -- RIGHT orientation of the current round
        rw [hW] at ihP ihNE
        rcases ihP with hb | ⟨es, em, hpc, hadvc, hpri⟩ | hmid
        · -- block phase
          have hr :
              roundAt σ τ env (mkRevBlock σ τ init th₀) (t + 1) = k := by
            rw [roundAt_succ, hb]; rfl
          rw [hr, hb, hW]
          exact
            ⟨Or.inr (Or.inr (Or.inl
              (advance_revBlock_right σ τ (env k) wordR _))), ihNE⟩
        · -- commit phase
          have hr :
              roundAt σ τ env (mkRevBlock σ τ init th₀) (t + 1) = k := by
            rw [roundAt_succ, hpc]; rfl
          rw [hr, hpc, hW]
          refine ⟨Or.inl ?_, ihNE⟩
          rw [← hpc]; exact hadvc
        · -- env / recv / resolve phases
          rcases hmid with hEnv | hRecv | hResolve
          · -- env → recv
            have hr :
                roundAt σ τ env (mkRevBlock σ τ init th₀) (t + 1) = k := by
              rw [roundAt_succ, hEnv]
            rw [hr, hEnv, hW]
            exact
              ⟨Or.inr (Or.inr (Or.inr (Or.inl
                (advance_revEnv_right σ τ (env k) _ wordR _ _ _ _ _)))),
                ihNE⟩
          · -- recv → resolve
            have hr :
                roundAt σ τ env (mkRevBlock σ τ init th₀) (t + 1) = k := by
              rw [roundAt_succ, hRecv]
            rw [hr, hRecv, hW]
            exact
              ⟨Or.inr (Or.inr (Or.inr (Or.inr
                (advance_revRecv_right σ τ (env k) _ wordR _ _ _ _ _)))),
                ihNE⟩
          · -- resolve → next round
            have hr :
                roundAt σ τ env (mkRevBlock σ τ init th₀) (t + 1) =
                  k + 1 := by
              rw [roundAt_succ, hResolve]
            rw [hr, hResolve, hWnext, hFnext, hW,
              chainNarrowed_eq_right σ τ init _ wordR hW]
            rcases hd : (env k).2 with inputTwo | inputOne
            · -- reversal (left round on a right block) → left commit
              rw [chainAdvance_revResolveR_reverse σ τ (env k) inputTwo hd,
                gameMove_left (env k) inputTwo hd]
              refine ⟨Or.inr (Or.inl ⟨_, _, rfl, ?_, rfl⟩),
                by simp [chainWordNonempty, chainWordStep]⟩
              rw [uRevReverseLTarget_advance σ τ (env (k + 1)) _ _
                (_, inputTwo) _ _]
              rfl
            · -- continuation (right round on a right block)
              obtain ⟨a, tl, rfl⟩ :=
                List.exists_cons_of_ne_nil (show wordR ≠ [] from ihNE)
              rw [chainAdvance_revResolveR_continue σ τ (env k) inputOne hd,
                gameMove_right (env k) inputOne hd]
              exact ⟨Or.inl rfl, by simp [chainWordNonempty, chainWordStep]⟩

/-! ### From play parity to composed-thread parity -/

/-- The priority of any chain-play position equals the composed
thread's tracked state at that round (the reindex value `hval`). -/
theorem chainPlay_hval (env : Nat -> (In₁ × In₂) × (In₂ ⊕ In₁))
    (init : List In₂ ⊕ List In₁) (th₀ : ChainThread A)
    (hinit : chainWordNonempty init) (t : Nat) :
    uniformizationPriority
        (chainPlay σ τ env (mkRevBlock σ τ init th₀) t) =
      A.priority
        (chainFold A (chainNarrowed σ τ init) [] th₀
          (branchNode env
            (roundAt σ τ env (mkRevBlock σ τ init th₀) t))).2.1 :=
  roundPhase_priority σ τ _ _ _ _
    (chainPlay_track σ τ env init th₀ hinit t).1

theorem roundAt_monotone (env : Nat -> (In₁ × In₂) × (In₂ ⊕ In₁))
    (start : UniformizationPosition (In₁ := In₁) A) :
    Monotone (roundAt σ τ env start) :=
  monotone_nat_of_le_succ fun t => by
    have h :
        roundAt σ τ env start (t + 1) = roundAt σ τ env start t ∨
          roundAt σ τ env start (t + 1) = roundAt σ τ env start t + 1 := by
      rw [roundAt_succ]; split <;> simp
    rcases h with h | h <;> omega

/-- Every round is reached: the block of round `k` is a chain-play
position with counter `k`.  Hence the counter is surjective. -/
theorem chainRound_reach
    (env : Nat -> (In₁ × In₂) × (In₂ ⊕ In₁))
    (init : List In₂ ⊕ List In₁) (th₀ : ChainThread A)
    (hinit : chainWordNonempty init) :
    ∀ k, ∃ t, roundAt σ τ env (mkRevBlock σ τ init th₀) t = k ∧
      chainPlay σ τ env (mkRevBlock σ τ init th₀) t =
        mkRevBlock σ τ
          (chainWord init (branchNode (fun n => (env n).2) k))
          (chainFold A (chainNarrowed σ τ init) [] th₀
            (branchNode env k)) := by
  intro k
  induction k with
  | zero => exact ⟨0, rfl, rfl⟩
  | succ k ih =>
      obtain ⟨t, hrt, hbt⟩ := ih
      set Fk := chainFold A (chainNarrowed σ τ init) [] th₀
        (branchNode env k) with hFk
      have hWkne :
          chainWordNonempty
            (chainWord init (branchNode (fun n => (env n).2) k)) :=
        hrt ▸ (chainPlay_track σ τ env init th₀ hinit t).2
      have hWnext :
          chainWord init (branchNode (fun n => (env n).2) (k + 1)) =
            chainWordStep
              (chainWord init (branchNode (fun n => (env n).2) k))
              (env k).2 := by
        rw [show branchNode (fun n => (env n).2) (k + 1) =
              branchNode (fun n => (env n).2) k ++ [(env k).2] from rfl,
          chainWord_append]
      have hFnext :
          chainFold A (chainNarrowed σ τ init) [] th₀
              (branchNode env (k + 1)) =
            chainThreadStep A Fk
              (chainNarrowed σ τ init
                (branchNode (fun n => (env n).2) k))
              (env k).2 (env k).1 := by
        rw [hFk,
          show branchNode env (k + 1) = branchNode env k ++ [env k]
            from rfl,
          chainFold_snoc_nil, branchNode_map_snd env k]
      rcases hWk : chainWord init (branchNode (fun n => (env n).2) k) with
        wordL | wordR
      · rw [hWk] at hbt hWkne
        rcases hd : (env k).2 with inputTwo | inputOne
        · -- continuation of a left block: four game steps
          obtain ⟨a, tl, rfl⟩ :=
            List.exists_cons_of_ne_nil (show wordL ≠ [] from hWkne)
          have hp1 : chainPlay σ τ env (mkRevBlock σ τ init th₀) (t + 1) =
              chainAdvance σ τ (env k)
                (mkRevBlock σ τ (Sum.inl (a :: tl)) Fk) := by
            rw [chainPlay_succ, hrt, hbt]
          have hr1 :
              roundAt σ τ env (mkRevBlock σ τ init th₀) (t + 1) = k := by
            rw [roundAt_succ, hbt]; exact hrt
          have hp2 : chainPlay σ τ env (mkRevBlock σ τ init th₀) (t + 2) =
              chainAdvance σ τ (env k)
                (chainPlay σ τ env (mkRevBlock σ τ init th₀) (t + 1)) := by
            rw [chainPlay_succ, hr1]
          have hr2 :
              roundAt σ τ env (mkRevBlock σ τ init th₀) (t + 2) = k := by
            rw [roundAt_succ, hp1,
              advance_revBlock_left σ τ (env k) (a :: tl) Fk]
            exact hr1
          have hp3 : chainPlay σ τ env (mkRevBlock σ τ init th₀) (t + 3) =
              chainAdvance σ τ (env k)
                (chainPlay σ τ env (mkRevBlock σ τ init th₀) (t + 2)) := by
            rw [chainPlay_succ, hr2]
          have hr3 :
              roundAt σ τ env (mkRevBlock σ τ init th₀) (t + 3) = k := by
            rw [roundAt_succ, hp2, hp1,
              advance_revBlock_left σ τ (env k) (a :: tl) Fk,
              advance_revEnv_left σ τ (env k) _ (a :: tl) _ _ _ _ _]
            exact hr2
          refine ⟨t + 4, ?_, ?_⟩
          · rw [roundAt_succ, hp3, hp2, hp1,
              advance_revBlock_left σ τ (env k) (a :: tl) Fk,
              advance_revEnv_left σ τ (env k) _ (a :: tl) _ _ _ _ _,
              advance_revRecv_left σ τ (env k) _ (a :: tl) _ _ _ _ _, hr3]
          · rw [chainPlay_succ, hr3, hp3, hp2, hp1,
              chainAdvance4_left_continue σ τ (env k) inputTwo hd (a :: tl)
                (by simp) Fk,
              hWnext, hFnext, hWk, hd,
              chainNarrowed_eq_left σ τ init _ (a :: tl) hWk]
            rfl
        · -- reversal of a left block: five game steps
          have hp1 : chainPlay σ τ env (mkRevBlock σ τ init th₀) (t + 1) =
              chainAdvance σ τ (env k)
                (mkRevBlock σ τ (Sum.inl wordL) Fk) := by
            rw [chainPlay_succ, hrt, hbt]
          have hr1 :
              roundAt σ τ env (mkRevBlock σ τ init th₀) (t + 1) = k := by
            rw [roundAt_succ, hbt]; exact hrt
          have hp2 : chainPlay σ τ env (mkRevBlock σ τ init th₀) (t + 2) =
              chainAdvance σ τ (env k)
                (chainPlay σ τ env (mkRevBlock σ τ init th₀) (t + 1)) := by
            rw [chainPlay_succ, hr1]
          have hr2 :
              roundAt σ τ env (mkRevBlock σ τ init th₀) (t + 2) = k := by
            rw [roundAt_succ, hp1, advance_revBlock_left σ τ (env k) wordL Fk]
            exact hr1
          have hp3 : chainPlay σ τ env (mkRevBlock σ τ init th₀) (t + 3) =
              chainAdvance σ τ (env k)
                (chainPlay σ τ env (mkRevBlock σ τ init th₀) (t + 2)) := by
            rw [chainPlay_succ, hr2]
          have hr3 :
              roundAt σ τ env (mkRevBlock σ τ init th₀) (t + 3) = k := by
            rw [roundAt_succ, hp2, hp1,
              advance_revBlock_left σ τ (env k) wordL Fk,
              advance_revEnv_left σ τ (env k) _ wordL _ _ _ _ _]
            exact hr2
          have hp4 : chainPlay σ τ env (mkRevBlock σ τ init th₀) (t + 4) =
              chainAdvance σ τ (env k)
                (chainPlay σ τ env (mkRevBlock σ τ init th₀) (t + 3)) := by
            rw [chainPlay_succ, hr3]
          have hr4 :
              roundAt σ τ env (mkRevBlock σ τ init th₀) (t + 4) = k + 1 := by
            rw [roundAt_succ, hp3, hp2, hp1,
              advance_revBlock_left σ τ (env k) wordL Fk,
              advance_revEnv_left σ τ (env k) _ wordL _ _ _ _ _,
              advance_revRecv_left σ τ (env k) _ wordL _ _ _ _ _, hr3]
          refine ⟨t + 5, ?_, ?_⟩
          · rw [roundAt_succ, hp4, hp3, hp2, hp1,
              advance_revBlock_left σ τ (env k) wordL Fk,
              advance_revEnv_left σ τ (env k) _ wordL _ _ _ _ _,
              advance_revRecv_left σ τ (env k) _ wordL _ _ _ _ _,
              chainAdvance_revResolveL_reverse σ τ (env k) inputOne hd,
              gameMove_right (env k) inputOne hd]
            exact hr4
          · rw [chainPlay_succ, hr4, hp4, hp3, hp2, hp1,
              advance_revBlock_left σ τ (env k) wordL Fk,
              advance_revEnv_left σ τ (env k) _ wordL _ _ _ _ _,
              advance_revRecv_left σ τ (env k) _ wordL _ _ _ _ _,
              chainAdvance_revResolveL_reverse σ τ (env k) inputOne hd,
              gameMove_right (env k) inputOne hd,
              uRevReverseRTarget_advance σ τ (env (k + 1)) _ _
                (inputOne, _) _ _, hWnext, hFnext, hWk, hd,
              chainNarrowed_eq_left σ τ init _ wordL hWk]
            rfl
      · rw [hWk] at hbt hWkne
        rcases hd : (env k).2 with inputTwo | inputOne
        · -- reversal of a right block: five game steps
          have hp1 : chainPlay σ τ env (mkRevBlock σ τ init th₀) (t + 1) =
              chainAdvance σ τ (env k)
                (mkRevBlock σ τ (Sum.inr wordR) Fk) := by
            rw [chainPlay_succ, hrt, hbt]
          have hr1 :
              roundAt σ τ env (mkRevBlock σ τ init th₀) (t + 1) = k := by
            rw [roundAt_succ, hbt]; exact hrt
          have hp2 : chainPlay σ τ env (mkRevBlock σ τ init th₀) (t + 2) =
              chainAdvance σ τ (env k)
                (chainPlay σ τ env (mkRevBlock σ τ init th₀) (t + 1)) := by
            rw [chainPlay_succ, hr1]
          have hr2 :
              roundAt σ τ env (mkRevBlock σ τ init th₀) (t + 2) = k := by
            rw [roundAt_succ, hp1,
              advance_revBlock_right σ τ (env k) wordR Fk]
            exact hr1
          have hp3 : chainPlay σ τ env (mkRevBlock σ τ init th₀) (t + 3) =
              chainAdvance σ τ (env k)
                (chainPlay σ τ env (mkRevBlock σ τ init th₀) (t + 2)) := by
            rw [chainPlay_succ, hr2]
          have hr3 :
              roundAt σ τ env (mkRevBlock σ τ init th₀) (t + 3) = k := by
            rw [roundAt_succ, hp2, hp1,
              advance_revBlock_right σ τ (env k) wordR Fk,
              advance_revEnv_right σ τ (env k) _ wordR _ _ _ _ _]
            exact hr2
          have hp4 : chainPlay σ τ env (mkRevBlock σ τ init th₀) (t + 4) =
              chainAdvance σ τ (env k)
                (chainPlay σ τ env (mkRevBlock σ τ init th₀) (t + 3)) := by
            rw [chainPlay_succ, hr3]
          have hr4 :
              roundAt σ τ env (mkRevBlock σ τ init th₀) (t + 4) = k + 1 := by
            rw [roundAt_succ, hp3, hp2, hp1,
              advance_revBlock_right σ τ (env k) wordR Fk,
              advance_revEnv_right σ τ (env k) _ wordR _ _ _ _ _,
              advance_revRecv_right σ τ (env k) _ wordR _ _ _ _ _, hr3]
          refine ⟨t + 5, ?_, ?_⟩
          · rw [roundAt_succ, hp4, hp3, hp2, hp1,
              advance_revBlock_right σ τ (env k) wordR Fk,
              advance_revEnv_right σ τ (env k) _ wordR _ _ _ _ _,
              advance_revRecv_right σ τ (env k) _ wordR _ _ _ _ _,
              chainAdvance_revResolveR_reverse σ τ (env k) inputTwo hd,
              gameMove_left (env k) inputTwo hd]
            exact hr4
          · rw [chainPlay_succ, hr4, hp4, hp3, hp2, hp1,
              advance_revBlock_right σ τ (env k) wordR Fk,
              advance_revEnv_right σ τ (env k) _ wordR _ _ _ _ _,
              advance_revRecv_right σ τ (env k) _ wordR _ _ _ _ _,
              chainAdvance_revResolveR_reverse σ τ (env k) inputTwo hd,
              gameMove_left (env k) inputTwo hd,
              uRevReverseLTarget_advance σ τ (env (k + 1)) _ _
                (_, inputTwo) _ _, hWnext, hFnext, hWk, hd,
              chainNarrowed_eq_right σ τ init _ wordR hWk]
            rfl
        · -- continuation of a right block: four game steps
          obtain ⟨a, tl, rfl⟩ :=
            List.exists_cons_of_ne_nil (show wordR ≠ [] from hWkne)
          have hp1 : chainPlay σ τ env (mkRevBlock σ τ init th₀) (t + 1) =
              chainAdvance σ τ (env k)
                (mkRevBlock σ τ (Sum.inr (a :: tl)) Fk) := by
            rw [chainPlay_succ, hrt, hbt]
          have hr1 :
              roundAt σ τ env (mkRevBlock σ τ init th₀) (t + 1) = k := by
            rw [roundAt_succ, hbt]; exact hrt
          have hp2 : chainPlay σ τ env (mkRevBlock σ τ init th₀) (t + 2) =
              chainAdvance σ τ (env k)
                (chainPlay σ τ env (mkRevBlock σ τ init th₀) (t + 1)) := by
            rw [chainPlay_succ, hr1]
          have hr2 :
              roundAt σ τ env (mkRevBlock σ τ init th₀) (t + 2) = k := by
            rw [roundAt_succ, hp1,
              advance_revBlock_right σ τ (env k) (a :: tl) Fk]
            exact hr1
          have hp3 : chainPlay σ τ env (mkRevBlock σ τ init th₀) (t + 3) =
              chainAdvance σ τ (env k)
                (chainPlay σ τ env (mkRevBlock σ τ init th₀) (t + 2)) := by
            rw [chainPlay_succ, hr2]
          have hr3 :
              roundAt σ τ env (mkRevBlock σ τ init th₀) (t + 3) = k := by
            rw [roundAt_succ, hp2, hp1,
              advance_revBlock_right σ τ (env k) (a :: tl) Fk,
              advance_revEnv_right σ τ (env k) _ (a :: tl) _ _ _ _ _]
            exact hr2
          refine ⟨t + 4, ?_, ?_⟩
          · rw [roundAt_succ, hp3, hp2, hp1,
              advance_revBlock_right σ τ (env k) (a :: tl) Fk,
              advance_revEnv_right σ τ (env k) _ (a :: tl) _ _ _ _ _,
              advance_revRecv_right σ τ (env k) _ (a :: tl) _ _ _ _ _, hr3]
          · rw [chainPlay_succ, hr3, hp3, hp2, hp1,
              chainAdvance4_right_continue σ τ (env k) inputOne hd (a :: tl)
                (by simp) Fk,
              hWnext, hFnext, hWk, hd,
              chainNarrowed_eq_right σ τ init _ (a :: tl) hWk]
            rfl

theorem chainPlay_hsurj
    (env : Nat -> (In₁ × In₂) × (In₂ ⊕ In₁))
    (init : List In₂ ⊕ List In₁) (th₀ : ChainThread A)
    (hinit : chainWordNonempty init) (k : Nat) :
    ∃ t, roundAt σ τ env (mkRevBlock σ τ init th₀) t = k :=
  let ⟨t, hr, _⟩ := chainRound_reach σ τ env init th₀ hinit k
  ⟨t, hr⟩

theorem chainPlay_htend
    (env : Nat -> (In₁ × In₂) × (In₂ ⊕ In₁))
    (init : List In₂ ⊕ List In₁) (th₀ : ChainThread A)
    (hinit : chainWordNonempty init) (N : Nat) :
    ∃ T, ∀ t, T ≤ t → N ≤ roundAt σ τ env (mkRevBlock σ τ init th₀) t := by
  obtain ⟨T, hT⟩ := chainPlay_hsurj σ τ env init th₀ hinit N
  exact ⟨T, fun t ht => by
    rw [← hT]
    exact roundAt_monotone σ τ env (mkRevBlock σ τ init th₀) ht⟩

/-- A composed thread realized at a reversed-block position wins:
the chain play from the reached position is consistent with the
winner, so its min-even parity transfers to the fold along the round
reindexing. -/
theorem chainAllThreadsWin_of_reaches
    (init : List In₂ ⊕ List In₁) (th₀ : ChainThread A)
    (hinit : chainWordNonempty init)
    (hreach : Reaches σ τ (mkRevBlock σ τ init th₀))
    (hwin :
      CountableParityGame.PositionalStrategy.WinningFrom
        (G := uniformizationGame A σ) τ
        (.bnd (A.initial, A.initial))) :
    ChainAllThreadsWin A (chainNarrowed σ τ init) th₀ := by
  intro env
  have hplay :
      (uniformizationGame A σ).MinPriorityEven
        (chainPlay σ τ env (mkRevBlock σ τ init th₀)) :=
    minPriorityEven_of_reaches_cont σ τ hwin
      (mkRevBlock σ τ init th₀) hreach
      (chainPlay σ τ env (mkRevBlock σ τ init th₀)) rfl
      (chainPlay_step σ τ env (mkRevBlock σ τ init th₀))
      (chainPlay_consistent σ τ env (mkRevBlock σ τ init th₀))
  have hs :
      NatSeqMinEvenParity
        (fun t =>
          uniformizationPriority
            (chainPlay σ τ env (mkRevBlock σ τ init th₀) t)) :=
    hplay
  exact
    (natSeqMinEvenParity_reindex
      (chainPlay_hval σ τ env init th₀ hinit)
      (chainPlay_htend σ τ env init th₀ hinit)
      (chainPlay_hsurj σ τ env init th₀ hinit)).mp hs

/-! ### Regime (c) endpoint: a chain-trapped branch is min-even -/

/-- From a first-handoff start (the chain checker at the handoff
thread set) with a reversed tail, the branch priorities are
min-even. -/
theorem chain_tail_min_even_from_start
    (branch : Nat -> GlobalJournalBranch (In₁ := In₁) A)
    (N : Nat) (T₀ : Finset (ChainThread A))
    (hstart :
      branchRun σ τ CL CR CC branch N =
        Sum.inr (Sum.inr (Sum.inr (Sum.inl (CC.start T₀, T₀)))) ∨
      branchRun σ τ CL CR CC branch N =
        Sum.inr
          (Sum.inr (Sum.inr (Sum.inr (Sum.inl (CC.start T₀, T₀))))))
    (htailN :
      ∀ k,
        (∃ c t, branchRun σ τ CL CR CC branch (N + k) =
          Sum.inr (Sum.inr (Sum.inr (Sum.inl (c, t))))) ∨
        ∃ c t, branchRun σ τ CL CR CC branch (N + k) =
          Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl (c, t))))))
    (hwin :
      CountableParityGame.PositionalStrategy.WinningFrom
        (G := uniformizationGame A σ) τ
        (.bnd (A.initial, A.initial))) :
    NatSeqMinEvenParity
      (fun n =>
        globalJournalPriority A CL CR CC
          (branchRun σ τ CL CR CC branch n)) := by
  obtain ⟨init, hparse₁, hrun₁, hreal₁, hinit₁⟩ :
      ∃ init : List In₂ ⊕ List In₁,
        tauNodeState (In₂ := In₂) (branchNode branch N) =
            revParse (A := A) init ∧
          globalRunIn CL CR CC (tauTree σ τ)
              (Sum.inl (A.initial, A.initial)) (branchNode branch N) =
            revModeState CL CR CC init (CC.start T₀) T₀ ∧
          (∀ qm ∈ T₀, Reaches σ τ (mkRevBlock σ τ init qm)) ∧
            chainWordNonempty init := by
    rcases hstart with hstart | hstart <;>
      (have hstartG :
          globalRunIn CL CR CC (tauTree σ τ)
              (Sum.inl (A.initial, A.initial)) (branchNode branch N) =
            _ := hstart) <;>
      rcases runGood σ τ CL CR CC (branchNode branch N) with hsink |
        ⟨atom, -, hrun', -⟩ | ⟨atom, w, c, t, -, hrun', -⟩ |
        ⟨atom, w, c, t, -, hrun', -⟩ |
        ⟨word₀, c, t, hparse', hrun', hne', hreal'⟩ |
        ⟨word₀, c, t, hparse', hrun', hne', hreal'⟩
    · exact absurd (hsink.symm.trans hstartG) (by simp)
    · exact absurd (hrun'.symm.trans hstartG) (by simp)
    · exact absurd (hrun'.symm.trans hstartG) (by simp)
    · exact absurd (hrun'.symm.trans hstartG) (by simp)
    · obtain ⟨hc, ht⟩ : c = CC.start T₀ ∧ t = T₀ := by
        simpa using hrun'.symm.trans hstartG
      subst hc; subst ht
      exact
        ⟨Sum.inl word₀, hparse', hrun', (fun qm hqm => hreal' qm hqm),
          hne'⟩
    · exact absurd (hrun'.symm.trans hstartG) (by simp)
    · exact absurd (hsink.symm.trans hstartG) (by simp)
    · exact absurd (hrun'.symm.trans hstartG) (by simp)
    · exact absurd (hrun'.symm.trans hstartG) (by simp)
    · exact absurd (hrun'.symm.trans hstartG) (by simp)
    · exact absurd (hrun'.symm.trans hstartG) (by simp)
    · obtain ⟨hc, ht⟩ : c = CC.start T₀ ∧ t = T₀ := by
        simpa using hrun'.symm.trans hstartG
      subst hc; subst ht
      exact
        ⟨Sum.inr word₀, hparse', hrun', (fun qm hqm => hreal' qm hqm),
          hne'⟩
  have hwt :
      DeterministicBlockMonitor.WinningTree
        { CC.monitor with initial := CC.start T₀ }
        (chainNarrowed σ τ init) :=
    (CC.winning_iff T₀ (chainNarrowed σ τ init)).mpr
      (fun qm hqm =>
        chainAllThreadsWin_of_reaches σ τ init qm hinit₁ (hreal₁ qm hqm)
          hwin)
  have hdir : ∀ k, ∃ d : In₂ ⊕ In₁, branch (N + k) = Sum.inr d := by
    intro k
    rcases hb : branch (N + k) with atom' | inputTwo | inputOne
    · exfalso
      have hk1 := htailN (k + 1)
      have hsucc := branchRun_succ σ τ CL CR CC branch (N + k)
      rw [hb] at hsucc
      rw [show N + (k + 1) = N + k + 1 from rfl] at hk1
      rcases htailN k with ⟨c, t, hk⟩ | ⟨c, t, hk⟩ <;>
        rw [hk] at hsucc <;>
        rcases hk1 with ⟨c', t', hk1⟩ | ⟨c', t', hk1⟩ <;>
        rw [hsucc] at hk1 <;>
        exact
          absurd hk1 (by simp only [globalJournalStep]; split <;> simp)
    · exact ⟨Sum.inl inputTwo, rfl⟩
    · exact ⟨Sum.inr inputOne, rfl⟩
  choose dirs hdirs using hdir
  have hnode :
      ∀ k,
        branchNode branch (N + k) =
          branchNode branch N ++ chainNode (A := A) (branchNode dirs k) := by
    intro k
    induction k with
    | zero =>
        rw [show branchNode dirs 0 = ([] : TreeNode (In₂ ⊕ In₁))
          from rfl]
        simp [chainNode]
    | succ k ih =>
        rw [show N + (k + 1) = N + k + 1 from rfl,
          show branchNode branch (N + k + 1) =
            branchNode branch (N + k) ++ [branch (N + k)] from rfl,
          ih, hdirs k,
          show branchNode dirs (k + 1) = branchNode dirs k ++ [dirs k]
            from rfl]
        simp [chainNode]
  have hpri :
      ∀ k,
        globalJournalPriority A CL CR CC
            (branchRun σ τ CL CR CC branch (N + k)) =
          CC.monitor.priority
              (DeterministicBlockMonitor.controlIn CC.monitor
                (chainNarrowed σ τ init) (CC.start T₀)
                (branchNode dirs k)) +
            globalShift (In₁ := In₁) A := by
    intro k
    obtain ⟨threads_k, htr⟩ :=
      globalRunIn_chain CL CR CC σ τ (branchNode branch N) init T₀
        hparse₁ hrun₁ (branchNode dirs k)
    have hbrk :
        branchRun σ τ CL CR CC branch (N + k) =
          revModeState CL CR CC (chainWord init (branchNode dirs k))
            (DeterministicBlockMonitor.controlIn CC.monitor
              (chainNarrowed σ τ init) (CC.start T₀)
              (branchNode dirs k)) threads_k := by
      show globalRunIn CL CR CC (tauTree σ τ)
          (Sum.inl (A.initial, A.initial))
          (branchNode branch (N + k)) = _
      rw [hnode k]
      exact htr
    rw [hbrk, globalJournalPriority_revModeState]
  rw [← natSeqMinEvenParity_shift
    (fun n =>
      globalJournalPriority A CL CR CC (branchRun σ τ CL CR CC branch n))
    N]
  have hgoal :
      (fun j =>
          globalJournalPriority A CL CR CC
            (branchRun σ τ CL CR CC branch (N + j))) =
        fun j =>
          CC.monitor.priority
              (DeterministicBlockMonitor.controlIn CC.monitor
                (chainNarrowed σ τ init) (CC.start T₀)
                (branchNode dirs j)) +
            globalShift (In₁ := In₁) A :=
    funext fun j => hpri j
  rw [hgoal]
  refine (natSeqMinEvenParity_add_const (globalShift_even A)).mpr ?_
  have hwtd := hwt dirs
  have hc :
      (fun n =>
          ({ CC.monitor with initial := CC.start T₀ } :
              DeterministicBlockMonitor _ _).priority
            (({ CC.monitor with initial := CC.start T₀ } :
                DeterministicBlockMonitor _ _).control
              (chainNarrowed σ τ init) (branchNode dirs n))) =
        fun n =>
          CC.monitor.priority
            (DeterministicBlockMonitor.controlIn CC.monitor
              (chainNarrowed σ τ init) (CC.start T₀)
              (branchNode dirs n)) := by
    funext n
    rw [DeterministicBlockMonitor.control,
      DeterministicBlockMonitor.controlIn_update_initial]
  rw [hc] at hwtd
  exact hwtd

/-- A never-sinking branch whose run eventually stays in the reversed
modes has min-even run priorities: walking back to the last entry
into the chain exposes the first handoff, where the chain checker
starts at the handoff thread set. -/
theorem tauTree_priorities_min_even_of_chain_tail
    (branch : Nat -> GlobalJournalBranch (In₁ := In₁) A) (S : Nat)
    (htail :
      ∀ k,
        (∃ c t, branchRun σ τ CL CR CC branch (S + k) =
          Sum.inr (Sum.inr (Sum.inr (Sum.inl (c, t))))) ∨
        ∃ c t, branchRun σ τ CL CR CC branch (S + k) =
          Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl (c, t))))))
    (hwin :
      CountableParityGame.PositionalStrategy.WinningFrom
        (G := uniformizationGame A σ) τ
        (.bnd (A.initial, A.initial))) :
    NatSeqMinEvenParity
      (fun n =>
        globalJournalPriority A CL CR CC
          (branchRun σ τ CL CR CC branch n)) := by
  classical
  set Rev : Nat -> Prop := fun n =>
    (∃ c t, branchRun σ τ CL CR CC branch n =
      Sum.inr (Sum.inr (Sum.inr (Sum.inl (c, t))))) ∨
    ∃ c t, branchRun σ τ CL CR CC branch n =
      Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl (c, t)))))
    with hRev
  have hrev0 : ¬ Rev 0 := by
    rintro (⟨c, t, h⟩ | ⟨c, t, h⟩) <;>
      (rw [show branchRun σ τ CL CR CC branch 0 =
          Sum.inl (A.initial, A.initial) from rfl] at h;
       simp at h)
  set M : Nat := Nat.findGreatest (fun n => ¬ Rev n) S with hM
  have hMnot : ¬ Rev M := by
    rw [hM]
    exact Nat.findGreatest_spec (P := fun n => ¬ Rev n) (Nat.zero_le S)
      hrev0
  have hafter : ∀ n, M < n -> Rev n := by
    intro n hn
    by_cases hns' : n ≤ S
    · have h :=
        Nat.findGreatest_is_greatest (P := fun n => ¬ Rev n) (n := S)
          (k := n) (by rw [← hM]; exact hn) hns'
      exact not_not.mp h
    · have := htail (n - S)
      rw [show S + (n - S) = n by omega] at this
      exact this
  have htail1 : ∀ k, Rev (M + 1 + k) := fun k =>
    hafter (M + 1 + k) (by omega)
  have hrev1 : Rev (M + 1) := by
    have := htail1 0
    rwa [Nat.add_zero] at this
  rcases hM' : branchRun σ τ CL CR CC branch M with atom |
    ⟨cL, tL⟩ | ⟨cR, tR⟩ | ⟨cc, tc⟩ | ⟨cc, tc⟩ | u
  · exfalso
    have hsucc := branchRun_succ σ τ CL CR CC branch M
    rw [hM'] at hsucc
    rcases hb : branch M with atom' | inputTwo | inputOne <;>
      rw [hb] at hsucc <;>
      rcases hrev1 with ⟨c', t', h1⟩ | ⟨c', t', h1⟩ <;>
      rw [hsucc] at h1
    · exact absurd h1 (by simp only [globalJournalStep]; split <;> simp)
    · exact absurd h1 (by simp only [globalJournalStep]; split <;> simp)
    · exact absurd h1 (by simp [globalJournalStep])
    · exact absurd h1 (by simp [globalJournalStep])
    · exact absurd h1 (by simp [globalJournalStep])
    · exact absurd h1 (by simp [globalJournalStep])
  · -- entry out of a left block
    have hsucc := branchRun_succ σ τ CL CR CC branch M
    rw [hM'] at hsucc
    rcases hb : branch M with atom' | inputTwo | inputOne <;>
      rw [hb] at hsucc
    · exfalso
      rcases hrev1 with ⟨c', t', h1⟩ | ⟨c', t', h1⟩ <;>
        rw [hsucc] at h1 <;>
        exact
          absurd h1 (by simp only [globalJournalStep]; split <;> simp)
    · exfalso
      rcases hrev1 with ⟨c', t', h1⟩ | ⟨c', t', h1⟩ <;>
        rw [hsucc] at h1 <;>
        exact absurd h1 (by simp [globalJournalStep])
    · exact
        chain_tail_min_even_from_start CL CR CC σ τ branch (M + 1)
          (leftReverseSubset tL
            (GlobalJournalLabel.leftClose
              (tauTree σ τ (branchNode branch M)))
            (GlobalJournalLabel.leftRev
              (tauTree σ τ (branchNode branch M)))
            inputOne)
          (Or.inr hsucc) htail1 hwin
  · -- entry out of a right block
    have hsucc := branchRun_succ σ τ CL CR CC branch M
    rw [hM'] at hsucc
    rcases hb : branch M with atom' | inputTwo | inputOne <;>
      rw [hb] at hsucc
    · exfalso
      rcases hrev1 with ⟨c', t', h1⟩ | ⟨c', t', h1⟩ <;>
        rw [hsucc] at h1 <;>
        exact
          absurd h1 (by simp only [globalJournalStep]; split <;> simp)
    · exact
        chain_tail_min_even_from_start CL CR CC σ τ branch (M + 1)
          (rightReverseSubset tR
            (GlobalJournalLabel.rightClose
              (tauTree σ τ (branchNode branch M)))
            (GlobalJournalLabel.rightRev
              (tauTree σ τ (branchNode branch M)))
            inputTwo)
          (Or.inl hsucc) htail1 hwin
    · exfalso
      rcases hrev1 with ⟨c', t', h1⟩ | ⟨c', t', h1⟩ <;>
        rw [hsucc] at h1 <;>
        exact absurd h1 (by simp [globalJournalStep])
  · exact absurd (Or.inl ⟨cc, tc, hM'⟩) hMnot
  · exact absurd (Or.inr ⟨cc, tc, hM'⟩) hMnot
  · exfalso
    cases u
    have hsucc := branchRun_succ σ τ CL CR CC branch M
    rw [hM'] at hsucc
    rcases hrev1 with ⟨c', t', h1⟩ | ⟨c', t', h1⟩ <;>
      rw [hsucc] at h1 <;>
      exact absurd h1 (by simp [globalJournalStep])

end Winner

end DetParityAutomaton

end DistributedSynthesis
