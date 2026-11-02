/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmTauTreeGlobalPlay
import DistributedSynthesis.Formalizations.Theorem.ThmTauTreeRegimeC

/-!
# Segments crossing direct reversals

The reversal-crossing segment builders of the extraction (obligation
M2-3a).  A segment from boundary `a` to boundary `a'` that reverses
mid-block consists of a normal-block prefix, the handoff round out of
the block (played through the close-resolve position's reversal
target), a reversal chain driven by the traced composed-thread
rounds, and a synchronizing close out of the final reversed block.
The chain part reuses the environment-driven chain play of
`ThmTauTreeRegimeC.lean`; the block prefix reuses the block play of
`ThmTauTreeRegimeB.lean`.  The composed-thread trace inverts the
realized thread sets round by round, mirroring `leftThread_trace`.
-/

set_option linter.unusedSectionVars false

namespace DistributedSynthesis

universe u v x y s

namespace DetParityAutomaton

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}

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
variable [Countable In₁] [Countable In₂] [Countable Out₁] [Countable Out₂]

/-! ### Composed-thread fold bookkeeping -/

theorem chainFold_append
    (narrowed :
      LabeledTree (In₂ ⊕ In₁)
        (ChainLabel In₁ In₂ Out₁ Out₂ (A.State × A.State))) :
    ∀ (l₁ l₂ : TreeNode ((In₁ × In₂) × (In₂ ⊕ In₁)))
      (word : List (In₂ ⊕ In₁)) (th : ChainThread A),
      chainFold A narrowed word th (l₁ ++ l₂) =
        chainFold A narrowed (word ++ l₁.map Prod.snd)
          (chainFold A narrowed word th l₁) l₂
  | [], l₂, word, th => by rw [List.map_nil, List.append_nil]; rfl
  | s :: rest, l₂, word, th => by
      show chainFold A narrowed (word ++ [s.2])
          (chainThreadStep A th (narrowed word) s.2 s.1) (rest ++ l₂) = _
      rw [chainFold_append narrowed rest l₂ (word ++ [s.2]) _,
        List.append_assoc]
      rfl

/-- The sampled minimum of a composed thread never rises. -/
theorem chainFold_snd_le
    (narrowed :
      LabeledTree (In₂ ⊕ In₁)
        (ChainLabel In₁ In₂ Out₁ Out₂ (A.State × A.State))) :
    ∀ (es : TreeNode ((In₁ × In₂) × (In₂ ⊕ In₁)))
      (word : List (In₂ ⊕ In₁)) (th : ChainThread A),
      A.priority (chainFold A narrowed word th es).2.2 ≤
        A.priority th.2.2
  | [], _, _ => Nat.le_refl _
  | s :: rest, word, th => by
      show A.priority
          (chainFold A narrowed (word ++ [s.2])
            (chainThreadStep A th (narrowed word) s.2 s.1) rest).2.2 ≤ _
      refine Nat.le_trans (chainFold_snd_le narrowed rest _ _) ?_
      obtain ⟨mv, d⟩ := s
      rcases d with inputTwo | inputOne <;>
        rcases narrowed word with labL | labR <;>
        exact priority_minPriorityState_le_left _ _

/-- The sampled minimum of a composed thread never exceeds its
tracked state. -/
theorem chainFold_snd_le_fst
    (narrowed :
      LabeledTree (In₂ ⊕ In₁)
        (ChainLabel In₁ In₂ Out₁ Out₂ (A.State × A.State))) :
    ∀ (es : TreeNode ((In₁ × In₂) × (In₂ ⊕ In₁)))
      (word : List (In₂ ⊕ In₁)) (th : ChainThread A),
      A.priority th.2.2 ≤ A.priority th.2.1 ->
      A.priority (chainFold A narrowed word th es).2.2 ≤
        A.priority (chainFold A narrowed word th es).2.1
  | [], _, _ => fun h => h
  | s :: rest, word, th => fun _ => by
      show A.priority
          (chainFold A narrowed (word ++ [s.2])
            (chainThreadStep A th (narrowed word) s.2 s.1) rest).2.2 ≤ _
      refine chainFold_snd_le_fst narrowed rest _ _ ?_
      obtain ⟨mv, d⟩ := s
      rcases d with inputTwo | inputOne <;>
        rcases narrowed word with labL | labR <;>
        exact priority_minPriorityState_le_right _ _

/-! ### The composed-thread trace along a reversal chain -/

section Winner

variable (σ : StrategyPair In₁ In₂ Out₁ Out₂)
variable
  (τ :
    (uniformizationGame A σ).PositionalStrategy ParityPlayer.even)

/-- Every realized thread of a chain node is the composed-thread fold
of some sequence of chain rounds from a handoff thread. -/
theorem chainThread_trace
    (node₁ : TreeNode (GlobalJournalBranch (In₁ := In₁) A))
    (init : List In₂ ⊕ List In₁)
    (T₀ : Finset (ChainThread A))
    (hp : tauNodeState (In₂ := In₂) node₁ = revParse (A := A) init)
    (hrun₁ :
      globalRunIn CL CR CC (tauTree σ τ) (Sum.inl (A.initial, A.initial))
          node₁ =
        revModeState CL CR CC init (CC.start T₀) T₀) :
    ∀ (v : List (In₂ ⊕ In₁)) (c : CC.monitor.State)
      (threads : Finset (ChainThread A)),
      globalRunIn CL CR CC (tauTree σ τ)
          (Sum.inl (A.initial, A.initial))
          (node₁ ++ chainNode (A := A) v) =
        revModeState CL CR CC (chainWord init v) c threads ->
      ∀ qm ∈ threads,
        ∃ es : TreeNode ((In₁ × In₂) × (In₂ ⊕ In₁)),
          es.map Prod.snd = v ∧
            ∃ qm₀ ∈ T₀,
              chainFold A (chainNarrowed σ τ init) [] qm₀ es = qm := by
  intro v
  induction v using List.reverseRecOn with
  | nil =>
      intro c threads hrun qm hqm
      have hcomp : revModeState CL CR CC init (CC.start T₀) T₀ =
          revModeState CL CR CC init c threads := by
        rw [← hrun₁]
        rw [show node₁ ++ chainNode (A := A) ([] : List (In₂ ⊕ In₁)) =
          node₁ from by simp [chainNode]] at hrun
        exact hrun
      have hthreads : threads = T₀ := by
        rcases init with wordL | wordR
        · exact
            (congrArg Prod.snd
              (Sum.inl.inj
                (Sum.inr.inj (Sum.inr.inj (Sum.inr.inj hcomp))))).symm
        · exact
            (congrArg Prod.snd
              (Sum.inl.inj
                (Sum.inr.inj
                  (Sum.inr.inj
                    (Sum.inr.inj (Sum.inr.inj hcomp)))))).symm
      exact ⟨[], rfl, qm, by rw [← hthreads]; exact hqm, rfl⟩
  | append_singleton v d ih =>
      intro c threads hrun qm hqm
      obtain ⟨tp, htp⟩ :=
        globalRunIn_chain CL CR CC σ τ node₁ init T₀ hp hrun₁ v
      have htree := tauTree_chainNode σ τ node₁ init hp v
      have hnode :
          node₁ ++ chainNode (A := A) (v ++ [d]) =
            (node₁ ++ chainNode (A := A) v) ++ [Sum.inr d] := by
        simp [chainNode]
      rw [hnode, globalRunIn_append, htp, htree, chainWord_append]
        at hrun
      rcases hcw : chainWord init v with wordL | wordR <;>
        rw [hcw] at hrun <;> rcases d with inputTwo | inputOne
      · -- revL, continue
        have hthreads :
            threads =
              revLeftStepSubset tp (tauRevLeftLabel σ τ wordL)
                inputTwo :=
          (congrArg Prod.snd
            (Sum.inl.inj
              (Sum.inr.inj (Sum.inr.inj (Sum.inr.inj hrun))))).symm
        rw [hthreads] at hqm
        obtain ⟨base, inputOne, hbase, hstep⟩ :=
          mem_revLeftStepSubset hqm
        obtain ⟨es, hmap, qm₀, hqm₀, hfold⟩ :=
          ih _ tp (by rw [htp, hcw]) base hbase
        refine
          ⟨es ++ [((inputOne, default), Sum.inl inputTwo)], ?_, qm₀,
            hqm₀, ?_⟩
        · rw [List.map_append, hmap]
          rfl
        · rw [chainFold_snoc_nil, hfold, hmap,
            chainNarrowed_eq_left σ τ init v wordL hcw]
          exact hstep.symm
      · -- revL, reverse again
        have hthreads :
            threads =
              revLeftReverseSubset tp (tauRevLeftLabel σ τ wordL)
                inputOne :=
          (congrArg Prod.snd
            (Sum.inl.inj
              (Sum.inr.inj
                (Sum.inr.inj
                  (Sum.inr.inj (Sum.inr.inj hrun)))))).symm
        rw [hthreads] at hqm
        obtain ⟨base, inputTwo, hbase, hstep⟩ :=
          mem_revLeftReverseSubset hqm
        obtain ⟨es, hmap, qm₀, hqm₀, hfold⟩ :=
          ih _ tp (by rw [htp, hcw]) base hbase
        refine
          ⟨es ++ [((default, inputTwo), Sum.inr inputOne)], ?_, qm₀,
            hqm₀, ?_⟩
        · rw [List.map_append, hmap]
          rfl
        · rw [chainFold_snoc_nil, hfold, hmap,
            chainNarrowed_eq_left σ τ init v wordL hcw]
          exact hstep.symm
      · -- revR, reverse again
        have hthreads :
            threads =
              revRightReverseSubset tp (tauRevRightLabel σ τ wordR)
                inputTwo :=
          (congrArg Prod.snd
            (Sum.inl.inj
              (Sum.inr.inj (Sum.inr.inj (Sum.inr.inj hrun))))).symm
        rw [hthreads] at hqm
        obtain ⟨base, inputOne, hbase, hstep⟩ :=
          mem_revRightReverseSubset hqm
        obtain ⟨es, hmap, qm₀, hqm₀, hfold⟩ :=
          ih _ tp (by rw [htp, hcw]) base hbase
        refine
          ⟨es ++ [((inputOne, default), Sum.inl inputTwo)], ?_, qm₀,
            hqm₀, ?_⟩
        · rw [List.map_append, hmap]
          rfl
        · rw [chainFold_snoc_nil, hfold, hmap,
            chainNarrowed_eq_right σ τ init v wordR hcw]
          exact hstep.symm
      · -- revR, continue
        have hthreads :
            threads =
              revRightStepSubset tp (tauRevRightLabel σ τ wordR)
                inputOne :=
          (congrArg Prod.snd
            (Sum.inl.inj
              (Sum.inr.inj
                (Sum.inr.inj
                  (Sum.inr.inj (Sum.inr.inj hrun)))))).symm
        rw [hthreads] at hqm
        obtain ⟨base, inputTwo, hbase, hstep⟩ :=
          mem_revRightStepSubset hqm
        obtain ⟨es, hmap, qm₀, hqm₀, hfold⟩ :=
          ih _ tp (by rw [htp, hcw]) base hbase
        refine
          ⟨es ++ [((default, inputTwo), Sum.inr inputOne)], ?_, qm₀,
            hqm₀, ?_⟩
        · rw [List.map_append, hmap]
          rfl
        · rw [chainFold_snoc_nil, hfold, hmap,
            chainNarrowed_eq_right σ τ init v wordR hcw]
          exact hstep.symm

/-! ### Closing a reversal chain at a synchronizing round -/

/-- Unified thread-close of a reversal chain: dispatch on the final
reversed block's orientation.  Both close formulas coincide (a
synchronizing round is orientation-independent), so this reads the
appropriate mode-typed receive responses. -/
def chainThreadClose (th : ChainThread A)
    (label : ChainLabel In₁ In₂ Out₁ Out₂ (A.State × A.State))
    (mc : In₁ × In₂) : A.State × A.State :=
  match label with
  | Sum.inl labL => revLeftThreadClose A th labL mc.1 mc.2
  | Sum.inr labR => revRightThreadClose A th labR mc.1 mc.2

/-- The full move driving the synchronizing close round: both inputs
are real; the direction keeps the receiver's input. -/
def closeMv (W : List In₂ ⊕ List In₁) (mc : In₁ × In₂) :
    (In₁ × In₂) × (In₂ ⊕ In₁) :=
  match W with
  | Sum.inl _ => (mc, Sum.inl mc.2)
  | Sum.inr _ => (mc, Sum.inr mc.1)

theorem closeMv_gameMove (W : List In₂ ⊕ List In₁) (mc : In₁ × In₂) :
    gameMove (closeMv W mc) = mc := by
  cases W with
  | inl wordL => exact gameMove_left (closeMv (Sum.inl wordL) mc) mc.2 rfl
  | inr wordR => exact gameMove_right (closeMv (Sum.inr wordR) mc) mc.1 rfl

/-- The first close position (the reversal-table commit) of the
synchronizing round: one advance from the entry reversed block. -/
noncomputable def revClose1 (W : List In₂ ⊕ List In₁)
    (F : ChainThread A) (mc : In₁ × In₂) :
    UniformizationPosition (In₁ := In₁) A :=
  chainAdvance σ τ (closeMv W mc) (mkRevBlock σ τ W F)

/-- The second close position (the receive stage). -/
noncomputable def revClose2 (W : List In₂ ⊕ List In₁)
    (F : ChainThread A) (mc : In₁ × In₂) :
    UniformizationPosition (In₁ := In₁) A :=
  chainAdvance σ τ (closeMv W mc) (revClose1 σ τ W F mc)

/-- The third close position (the resolve stage). -/
noncomputable def revClose3 (W : List In₂ ⊕ List In₁)
    (F : ChainThread A) (mc : In₁ × In₂) :
    UniformizationPosition (In₁ := In₁) A :=
  chainAdvance σ τ (closeMv W mc) (revClose2 σ τ W F mc)

theorem revClose1_priority (W : List In₂ ⊕ List In₁)
    (F : ChainThread A) (mc : In₁ × In₂) :
    uniformizationPriority (revClose1 σ τ W F mc) = A.priority F.2.1 := by
  cases W with
  | inl wordL =>
      rw [revClose1,
        show chainAdvance σ τ (closeMv (Sum.inl wordL) mc)
            (mkRevBlock σ τ (Sum.inl wordL) F) =
          τ.move (mkRevBlock σ τ (Sum.inl wordL) F) from rfl,
        show mkRevBlock σ τ (Sum.inl wordL) F =
          .revBlockL (commitmentRevL σ τ [wordL.headD default] F.1.1 F.1.2)
            wordL F.1.1 F.1.2 F.2.1 F.2.2 from rfl,
        revSendTableL_spec σ τ _ wordL F.1.1 F.1.2 F.2.1 F.2.2]
      rfl
  | inr wordR =>
      rw [revClose1,
        show chainAdvance σ τ (closeMv (Sum.inr wordR) mc)
            (mkRevBlock σ τ (Sum.inr wordR) F) =
          τ.move (mkRevBlock σ τ (Sum.inr wordR) F) from rfl,
        show mkRevBlock σ τ (Sum.inr wordR) F =
          .revBlockR (commitmentRevR σ τ [wordR.headD default] F.1.1 F.1.2)
            wordR F.1.1 F.1.2 F.2.1 F.2.2 from rfl,
        revSendTableR_spec σ τ _ wordR F.1.1 F.1.2 F.2.1 F.2.2]
      rfl

theorem revClose2_priority (W : List In₂ ⊕ List In₁)
    (F : ChainThread A) (mc : In₁ × In₂) :
    uniformizationPriority (revClose2 σ τ W F mc) = A.priority F.2.1 := by
  cases W with
  | inl wordL =>
      rw [revClose2, revClose1,
        show chainAdvance σ τ (closeMv (Sum.inl wordL) mc)
            (mkRevBlock σ τ (Sum.inl wordL) F) =
          τ.move (mkRevBlock σ τ (Sum.inl wordL) F) from rfl,
        show mkRevBlock σ τ (Sum.inl wordL) F =
          .revBlockL (commitmentRevL σ τ [wordL.headD default] F.1.1 F.1.2)
            wordL F.1.1 F.1.2 F.2.1 F.2.2 from rfl,
        revSendTableL_spec σ τ _ wordL F.1.1 F.1.2 F.2.1 F.2.2]
      rfl
  | inr wordR =>
      rw [revClose2, revClose1,
        show chainAdvance σ τ (closeMv (Sum.inr wordR) mc)
            (mkRevBlock σ τ (Sum.inr wordR) F) =
          τ.move (mkRevBlock σ τ (Sum.inr wordR) F) from rfl,
        show mkRevBlock σ τ (Sum.inr wordR) F =
          .revBlockR (commitmentRevR σ τ [wordR.headD default] F.1.1 F.1.2)
            wordR F.1.1 F.1.2 F.2.1 F.2.2 from rfl,
        revSendTableR_spec σ τ _ wordR F.1.1 F.1.2 F.2.1 F.2.2]
      rfl

theorem revClose3_eq (W : List In₂ ⊕ List In₁)
    (F : ChainThread A) (mc : In₁ × In₂) :
    revClose3 σ τ W F mc =
      match W with
      | Sum.inl wordL =>
          .revResolveL (commitmentRevL σ τ [wordL.headD default] F.1.1 F.1.2)
            wordL F.1.1 F.1.2 F.2.1 F.2.2
            (revSendTableL σ τ
              (commitmentRevL σ τ [wordL.headD default] F.1.1 F.1.2)
              wordL F.1.1 F.1.2 F.2.1 F.2.2)
            mc
            (revRecvChoiceL σ τ
              (commitmentRevL σ τ [wordL.headD default] F.1.1 F.1.2)
              wordL F.1.1 F.1.2 F.2.1 F.2.2 mc).1
            (revRecvChoiceL σ τ
              (commitmentRevL σ τ [wordL.headD default] F.1.1 F.1.2)
              wordL F.1.1 F.1.2 F.2.1 F.2.2 mc).2
      | Sum.inr wordR =>
          .revResolveR (commitmentRevR σ τ [wordR.headD default] F.1.1 F.1.2)
            wordR F.1.1 F.1.2 F.2.1 F.2.2
            (revSendTableR σ τ
              (commitmentRevR σ τ [wordR.headD default] F.1.1 F.1.2)
              wordR F.1.1 F.1.2 F.2.1 F.2.2)
            mc
            (revRecvChoiceR σ τ
              (commitmentRevR σ τ [wordR.headD default] F.1.1 F.1.2)
              wordR F.1.1 F.1.2 F.2.1 F.2.2 mc).1
            (revRecvChoiceR σ τ
              (commitmentRevR σ τ [wordR.headD default] F.1.1 F.1.2)
              wordR F.1.1 F.1.2 F.2.1 F.2.2 mc).2 := by
  cases W with
  | inl wordL =>
      rw [revClose3, revClose2, revClose1,
        show mkRevBlock σ τ (Sum.inl wordL) F =
          .revBlockL (commitmentRevL σ τ [wordL.headD default] F.1.1 F.1.2)
            wordL F.1.1 F.1.2 F.2.1 F.2.2 from rfl,
        revBlockL_three σ τ (closeMv (Sum.inl wordL) mc) _ wordL
          F.1.1 F.1.2 F.2.1 F.2.2, closeMv_gameMove]
  | inr wordR =>
      rw [revClose3, revClose2, revClose1,
        show mkRevBlock σ τ (Sum.inr wordR) F =
          .revBlockR (commitmentRevR σ τ [wordR.headD default] F.1.1 F.1.2)
            wordR F.1.1 F.1.2 F.2.1 F.2.2 from rfl,
        revBlockR_three σ τ (closeMv (Sum.inr wordR) mc) _ wordR
          F.1.1 F.1.2 F.2.1 F.2.2, closeMv_gameMove]

theorem revClose3_priority (W : List In₂ ⊕ List In₁)
    (F : ChainThread A) (mc : In₁ × In₂) :
    uniformizationPriority (revClose3 σ τ W F mc) = A.priority F.2.1 := by
  rw [revClose3_eq]
  cases W <;> rfl

theorem revClose1_owner_odd (W : List In₂ ⊕ List In₁)
    (F : ChainThread A) (mc : In₁ × In₂)
    (howner :
      (uniformizationGame A σ).owner (revClose1 σ τ W F mc) =
        ParityPlayer.even) :
    False := by
  cases W with
  | inl wordL =>
      rw [revClose1,
        show chainAdvance σ τ (closeMv (Sum.inl wordL) mc)
            (mkRevBlock σ τ (Sum.inl wordL) F) =
          τ.move (mkRevBlock σ τ (Sum.inl wordL) F) from rfl,
        show mkRevBlock σ τ (Sum.inl wordL) F =
          .revBlockL (commitmentRevL σ τ [wordL.headD default] F.1.1 F.1.2)
            wordL F.1.1 F.1.2 F.2.1 F.2.2 from rfl,
        revSendTableL_spec σ τ _ wordL F.1.1 F.1.2 F.2.1 F.2.2] at howner
      simp [uniformizationGame, uniformizationOwner] at howner
  | inr wordR =>
      rw [revClose1,
        show chainAdvance σ τ (closeMv (Sum.inr wordR) mc)
            (mkRevBlock σ τ (Sum.inr wordR) F) =
          τ.move (mkRevBlock σ τ (Sum.inr wordR) F) from rfl,
        show mkRevBlock σ τ (Sum.inr wordR) F =
          .revBlockR (commitmentRevR σ τ [wordR.headD default] F.1.1 F.1.2)
            wordR F.1.1 F.1.2 F.2.1 F.2.2 from rfl,
        revSendTableR_spec σ τ _ wordR F.1.1 F.1.2 F.2.1 F.2.2] at howner
      simp [uniformizationGame, uniformizationOwner] at howner

theorem revClose2_move (W : List In₂ ⊕ List In₁)
    (F : ChainThread A) (mc : In₁ × In₂) :
    revClose3 σ τ W F mc = τ.move (revClose2 σ τ W F mc) := by
  rw [revClose3]
  refine chainAdvance_eq_tau_of_even σ τ (closeMv W mc) (revClose2 σ τ W F mc)
    ?_
  cases W with
  | inl wordL =>
      rw [revClose2, revClose1,
        show chainAdvance σ τ (closeMv (Sum.inl wordL) mc)
            (mkRevBlock σ τ (Sum.inl wordL) F) =
          τ.move (mkRevBlock σ τ (Sum.inl wordL) F) from rfl,
        show mkRevBlock σ τ (Sum.inl wordL) F =
          .revBlockL (commitmentRevL σ τ [wordL.headD default] F.1.1 F.1.2)
            wordL F.1.1 F.1.2 F.2.1 F.2.2 from rfl,
        revSendTableL_spec σ τ _ wordL F.1.1 F.1.2 F.2.1 F.2.2]
      rfl
  | inr wordR =>
      rw [revClose2, revClose1,
        show chainAdvance σ τ (closeMv (Sum.inr wordR) mc)
            (mkRevBlock σ τ (Sum.inr wordR) F) =
          τ.move (mkRevBlock σ τ (Sum.inr wordR) F) from rfl,
        show mkRevBlock σ τ (Sum.inr wordR) F =
          .revBlockR (commitmentRevR σ τ [wordR.headD default] F.1.1 F.1.2)
            wordR F.1.1 F.1.2 F.2.1 F.2.2 from rfl,
        revSendTableR_spec σ τ _ wordR F.1.1 F.1.2 F.2.1 F.2.2]
      rfl

theorem revClose3_owner_odd (W : List In₂ ⊕ List In₁)
    (F : ChainThread A) (mc : In₁ × In₂)
    (howner :
      (uniformizationGame A σ).owner (revClose3 σ τ W F mc) =
        ParityPlayer.even) :
    False := by
  rw [revClose3_eq] at howner
  cases W <;>
    simp [uniformizationGame, uniformizationOwner] at howner

/-- The synchronizing close of a reversal chain steps to the closed
boundary. -/
theorem revClose_step
    (init : List In₂ ⊕ List In₁)
    (v : List (In₂ ⊕ In₁)) (F : ChainThread A) (mc : In₁ × In₂)
    (a' : A.State × A.State)
    (ha' : a' = chainThreadClose F (chainNarrowed σ τ init v) mc) :
    (uniformizationGame A σ).step
      (revClose3 σ τ (chainWord init v) F mc) (.bnd a') := by
  rw [revClose3_eq]
  rcases hcw : chainWord init v with wordL | wordR
  · refine Or.inr (Or.inl ?_)
    rw [ha', chainNarrowed_eq_left σ τ init v wordL hcw]
    rfl
  · refine Or.inr (Or.inl ?_)
    rw [ha', chainNarrowed_eq_right σ τ init v wordR hcw]
    rfl

/-! ### From a reversal entry to a full segment -/

/--
A winner-consistent play piece from a boundary into the first
reversed block of a chain: the normal-block prefix and the handoff
round, ending at the entry reversed-block position.
-/
structure RevEntrySpec (a : A.State × A.State)
    (init : List In₂ ⊕ List In₁) (th₀ : ChainThread A) where
  len : Nat
  play : Nat -> UniformizationPosition (In₁ := In₁) A
  len_pos : 1 ≤ len
  play_zero : play 0 = .bnd a
  play_len : play len = mkRevBlock σ τ init th₀
  step : ∀ t, t < len ->
    (uniformizationGame A σ).step (play t) (play (t + 1))
  consistent :
    ∀ t, t < len ->
      (uniformizationGame A σ).owner (play t) = ParityPlayer.even ->
        play (t + 1) = τ.move (play t)
  bound :
    ∀ t, 0 < t -> t < len ->
      A.priority th₀.2.2 ≤ uniformizationPriority (play t)
  snd_le_fst : A.priority th₀.2.2 ≤ A.priority th₀.2.1

/-- Extending a reversal entry by the traced chain rounds and a
synchronizing close yields a winner-consistent segment. -/
theorem segmentSpec_of_revEntry
    {a : A.State × A.State} {init : List In₂ ⊕ List In₁}
    {th₀ : ChainThread A}
    (hinit : chainWordNonempty init)
    (E : RevEntrySpec σ τ a init th₀)
    (es : List ((In₁ × In₂) × (In₂ ⊕ In₁))) (mc : In₁ × In₂)
    (a' : A.State × A.State)
    (ha' :
      a' =
        chainThreadClose
          (chainFold A (chainNarrowed σ τ init) [] th₀ es)
          (chainNarrowed σ τ init (es.map Prod.snd)) mc) :
    Nonempty (SegmentSpec σ τ a a') := by
  have hbn :
      branchNode (fun j => es.getD j default) es.length = es := by
    rw [branchNode_getD es es.length (Nat.le_refl _), List.take_length]
  have hdirs :
      branchNode (fun n => ((fun j => es.getD j default) n).2)
          es.length =
        es.map Prod.snd := by
    rw [← branchNode_map_snd (fun j => es.getD j default) es.length,
      hbn]
  obtain ⟨tstar, hround, hreach⟩ :=
    chainRound_reach σ τ (fun j => es.getD j default) init th₀ hinit
      es.length
  rw [hdirs, hbn] at hreach
  have hqmk_le :
      A.priority
          (chainFold A (chainNarrowed σ τ init) [] th₀ es).2.2 ≤
        A.priority th₀.2.2 :=
    chainFold_snd_le _ es [] th₀
  have hqmk_fst :
      A.priority
          (chainFold A (chainNarrowed σ τ init) [] th₀ es).2.2 ≤
        A.priority
          (chainFold A (chainNarrowed σ τ init) [] th₀ es).2.1 :=
    chainFold_snd_le_fst _ es [] th₀ E.snd_le_fst
  have ha'2 :
      A.priority a'.2 =
        A.priority
          (chainFold A (chainNarrowed σ τ init) [] th₀ es).2.2 := by
    rw [ha']
    rcases chainNarrowed σ τ init (es.map Prod.snd) with labL | labR <;>
      rfl
  have htake :
      ∀ j,
        A.priority
            (chainFold A (chainNarrowed σ τ init) [] th₀ es).2.2 ≤
          A.priority
            (chainFold A (chainNarrowed σ τ init) [] th₀
              (es.take j)).2.1 := by
    intro j
    have hsplit :=
      chainFold_append (A := A) (chainNarrowed σ τ init) (es.take j)
        (es.drop j) [] th₀
    rw [List.take_append_drop] at hsplit
    refine
      Nat.le_trans ?_
        (chainFold_snd_le_fst _ (es.take j) [] th₀ E.snd_le_fst)
    rw [hsplit]
    exact chainFold_snd_le _ _ _ _
  have htakebn :
      ∀ j, j ≤ es.length ->
        branchNode (fun i => es.getD i default) j = es.take j := by
    intro j hj
    exact branchNode_getD es j hj
  refine ⟨⟨E.len + tstar + 4,
    fun t =>
      if t < E.len then E.play t
      else if t ≤ E.len + tstar then
        chainPlay σ τ (fun j => es.getD j default)
          (mkRevBlock σ τ init th₀) (t - E.len)
      else if t = E.len + tstar + 1 then
        revClose1 σ τ (chainWord init (es.map Prod.snd))
          (chainFold A (chainNarrowed σ τ init) [] th₀ es) mc
      else if t = E.len + tstar + 2 then
        revClose2 σ τ (chainWord init (es.map Prod.snd))
          (chainFold A (chainNarrowed σ τ init) [] th₀ es) mc
      else if t = E.len + tstar + 3 then
        revClose3 σ τ (chainWord init (es.map Prod.snd))
          (chainFold A (chainNarrowed σ τ init) [] th₀ es) mc
      else .bnd a',
    by omega, ?_, ?_, ?_, ?_, ?_⟩⟩
  · -- play_zero
    simp only []
    rw [if_pos (show 0 < E.len from E.len_pos)]
    exact E.play_zero
  · -- play_len
    simp only []
    rw [if_neg (show ¬ E.len + tstar + 4 < E.len by omega),
      if_neg (show ¬ E.len + tstar + 4 ≤ E.len + tstar by omega),
      if_neg (show ¬ E.len + tstar + 4 = E.len + tstar + 1 by omega),
      if_neg (show ¬ E.len + tstar + 4 = E.len + tstar + 2 by omega),
      if_neg (show ¬ E.len + tstar + 4 = E.len + tstar + 3 by omega)]
  · -- step
    intro t ht
    simp only []
    by_cases hc1 : t + 1 < E.len
    · rw [if_pos (show t < E.len by omega),
        if_pos (show t + 1 < E.len from hc1)]
      exact E.step t (by omega)
    · by_cases hc2 : t + 1 = E.len
      · rw [if_pos (show t < E.len by omega),
          if_neg (show ¬ t + 1 < E.len by omega),
          if_pos (show t + 1 ≤ E.len + tstar by omega),
          show t + 1 - E.len = 0 by omega]
        have hstep := E.step t (by omega)
        rw [hc2, E.play_len] at hstep
        rw [chainPlay_zero σ τ (fun j => es.getD j default)
          (mkRevBlock σ τ init th₀)]
        exact hstep
      · by_cases hc3 : t < E.len + tstar
        · rw [if_neg (show ¬ t < E.len by omega),
            if_pos (show t ≤ E.len + tstar by omega),
            if_neg (show ¬ t + 1 < E.len by omega),
            if_pos (show t + 1 ≤ E.len + tstar by omega),
            show t + 1 - E.len = t - E.len + 1 by omega]
          exact
            chainPlay_step σ τ (fun j => es.getD j default)
              (mkRevBlock σ τ init th₀) (t - E.len)
        · by_cases hc4 : t = E.len + tstar
          · rw [if_neg (show ¬ t < E.len by omega),
              if_pos (show t ≤ E.len + tstar by omega),
              if_neg (show ¬ t + 1 < E.len by omega),
              if_neg (show ¬ t + 1 ≤ E.len + tstar by omega),
              if_pos (show t + 1 = E.len + tstar + 1 by omega),
              show t - E.len = tstar by omega, hreach, revClose1]
            exact chainAdvance_step σ τ _ _
          · by_cases hc5 : t = E.len + tstar + 1
            · rw [if_neg (show ¬ t < E.len by omega),
                if_neg (show ¬ t ≤ E.len + tstar by omega),
                if_pos hc5,
                if_neg (show ¬ t + 1 < E.len by omega),
                if_neg (show ¬ t + 1 ≤ E.len + tstar by omega),
                if_neg (show ¬ t + 1 = E.len + tstar + 1 by omega),
                if_pos (show t + 1 = E.len + tstar + 2 by omega),
                revClose2]
              exact chainAdvance_step σ τ _ _
            · by_cases hc6 : t = E.len + tstar + 2
              · rw [if_neg (show ¬ t < E.len by omega),
                  if_neg (show ¬ t ≤ E.len + tstar by omega),
                  if_neg (show ¬ t = E.len + tstar + 1 by omega),
                  if_pos hc6,
                  if_neg (show ¬ t + 1 < E.len by omega),
                  if_neg (show ¬ t + 1 ≤ E.len + tstar by omega),
                  if_neg (show ¬ t + 1 = E.len + tstar + 1 by omega),
                  if_neg (show ¬ t + 1 = E.len + tstar + 2 by omega),
                  if_pos (show t + 1 = E.len + tstar + 3 by omega),
                  revClose3]
                exact chainAdvance_step σ τ _ _
              · have hc7 : t = E.len + tstar + 3 := by omega
                rw [if_neg (show ¬ t < E.len by omega),
                  if_neg (show ¬ t ≤ E.len + tstar by omega),
                  if_neg (show ¬ t = E.len + tstar + 1 by omega),
                  if_neg (show ¬ t = E.len + tstar + 2 by omega),
                  if_pos hc7,
                  if_neg (show ¬ t + 1 < E.len by omega),
                  if_neg (show ¬ t + 1 ≤ E.len + tstar by omega),
                  if_neg (show ¬ t + 1 = E.len + tstar + 1 by omega),
                  if_neg (show ¬ t + 1 = E.len + tstar + 2 by omega),
                  if_neg (show ¬ t + 1 = E.len + tstar + 3 by omega)]
                exact revClose_step σ τ init (es.map Prod.snd) _ mc a' ha'
  · -- consistent
    intro t ht howner
    simp only [] at howner ⊢
    by_cases hc1 : t + 1 < E.len
    · rw [if_pos (show t < E.len by omega)] at howner
      rw [if_pos (show t < E.len by omega),
        if_pos (show t + 1 < E.len from hc1)]
      exact E.consistent t (by omega) howner
    · by_cases hc2 : t + 1 = E.len
      · rw [if_pos (show t < E.len by omega)] at howner
        rw [if_pos (show t < E.len by omega),
          if_neg (show ¬ t + 1 < E.len by omega),
          if_pos (show t + 1 ≤ E.len + tstar by omega),
          show t + 1 - E.len = 0 by omega]
        have hcons := E.consistent t (by omega) howner
        rw [hc2, E.play_len] at hcons
        rw [chainPlay_zero σ τ (fun j => es.getD j default)
          (mkRevBlock σ τ init th₀)]
        exact hcons
      · by_cases hc3 : t < E.len + tstar
        · rw [if_neg (show ¬ t < E.len by omega),
            if_pos (show t ≤ E.len + tstar by omega)] at howner
          rw [if_neg (show ¬ t < E.len by omega),
            if_pos (show t ≤ E.len + tstar by omega),
            if_neg (show ¬ t + 1 < E.len by omega),
            if_pos (show t + 1 ≤ E.len + tstar by omega),
            show t + 1 - E.len = t - E.len + 1 by omega]
          exact
            chainPlay_consistent σ τ (fun j => es.getD j default)
              (mkRevBlock σ τ init th₀) (t - E.len) howner
        · by_cases hc4 : t = E.len + tstar
          · rw [if_neg (show ¬ t < E.len by omega),
              if_pos (show t ≤ E.len + tstar by omega),
              show t - E.len = tstar by omega, hreach] at howner
            rw [if_neg (show ¬ t < E.len by omega),
              if_pos (show t ≤ E.len + tstar by omega),
              if_neg (show ¬ t + 1 < E.len by omega),
              if_neg (show ¬ t + 1 ≤ E.len + tstar by omega),
              if_pos (show t + 1 = E.len + tstar + 1 by omega),
              show t - E.len = tstar by omega, hreach, revClose1]
            exact
              chainAdvance_eq_tau_of_even σ τ _
                (mkRevBlock σ τ (chainWord init (es.map Prod.snd))
                  (chainFold A (chainNarrowed σ τ init) [] th₀ es))
                howner
          · by_cases hc5 : t = E.len + tstar + 1
            · exfalso
              rw [if_neg (show ¬ t < E.len by omega),
                if_neg (show ¬ t ≤ E.len + tstar by omega),
                if_pos hc5] at howner
              exact revClose1_owner_odd σ τ _ _ mc howner
            · by_cases hc6 : t = E.len + tstar + 2
              · rw [if_neg (show ¬ t < E.len by omega),
                  if_neg (show ¬ t ≤ E.len + tstar by omega),
                  if_neg (show ¬ t = E.len + tstar + 1 by omega),
                  if_pos hc6,
                  if_neg (show ¬ t + 1 < E.len by omega),
                  if_neg (show ¬ t + 1 ≤ E.len + tstar by omega),
                  if_neg (show ¬ t + 1 = E.len + tstar + 1 by omega),
                  if_neg (show ¬ t + 1 = E.len + tstar + 2 by omega),
                  if_pos (show t + 1 = E.len + tstar + 3 by omega)]
                exact revClose2_move σ τ (chainWord init (es.map Prod.snd))
                  (chainFold A (chainNarrowed σ τ init) [] th₀ es) mc
              · have hc7 : t = E.len + tstar + 3 := by omega
                exfalso
                rw [if_neg (show ¬ t < E.len by omega),
                  if_neg (show ¬ t ≤ E.len + tstar by omega),
                  if_neg (show ¬ t = E.len + tstar + 1 by omega),
                  if_neg (show ¬ t = E.len + tstar + 2 by omega),
                  if_pos hc7] at howner
                exact revClose3_owner_odd σ τ _ _ mc howner
  · -- bound
    intro t ht0 htlen
    simp only []
    rw [ha'2]
    by_cases hc1 : t < E.len
    · rw [if_pos hc1]
      exact Nat.le_trans hqmk_le (E.bound t ht0 hc1)
    · by_cases hc2 : t ≤ E.len + tstar
      · rw [if_neg (show ¬ t < E.len by omega), if_pos hc2,
          chainPlay_hval σ τ (fun j => es.getD j default) init th₀
            hinit (t - E.len)]
        have hkle :
            roundAt σ τ (fun j => es.getD j default)
                (mkRevBlock σ τ init th₀) (t - E.len) ≤ es.length := by
          rw [← hround]
          exact
            roundAt_monotone σ τ (fun j => es.getD j default)
              (mkRevBlock σ τ init th₀) (by omega : t - E.len ≤ tstar)
        rw [htakebn _ hkle]
        exact htake _
      · by_cases hc3 : t = E.len + tstar + 1
        · rw [if_neg (show ¬ t < E.len by omega),
            if_neg (show ¬ t ≤ E.len + tstar by omega),
            if_pos hc3, revClose1_priority]
          exact hqmk_fst
        · by_cases hc4 : t = E.len + tstar + 2
          · rw [if_neg (show ¬ t < E.len by omega),
              if_neg (show ¬ t ≤ E.len + tstar by omega),
              if_neg (show ¬ t = E.len + tstar + 1 by omega),
              if_pos hc4, revClose2_priority]
            exact hqmk_fst
          · have hc5 : t = E.len + tstar + 3 := by omega
            rw [if_neg (show ¬ t < E.len by omega),
              if_neg (show ¬ t ≤ E.len + tstar by omega),
              if_neg (show ¬ t = E.len + tstar + 1 by omega),
              if_neg (show ¬ t = E.len + tstar + 2 by omega),
              if_pos hc5, revClose3_priority]
            exact hqmk_fst

/-! ### The reversal entries out of normal blocks -/

/-- The left-block reversal entry: drive the block play along the
traced thread, then reverse at the recorded handoff move. -/
theorem revEntryLeft_exists
    (node₀ : TreeNode (GlobalJournalBranch (In₁ := In₁) A))
    (a : A.State × A.State)
    (hp : tauNodeState (In₂ := In₂) node₀ = .atNode a)
    (w : List In₂) (ms : TreeNode (In₁ × In₂))
    (base : A.State × A.State) (mh : In₁ × In₂)
    (hne : ms ≠ [])
    (hsw : senderWord ms = w)
    (hctrl :
      narrowedControl (A.leftBlockMonitor a.1)
        (leftBlockNarrowed (tauTree σ τ) node₀) ms = base) :
    Nonempty
      (RevEntrySpec σ τ a (Sum.inr [mh.1])
        (leftThreadReverse base (tauLeftClose σ τ a w)
          (tauLeftRev σ τ a w) mh.1 mh.2)) := by
  obtain ⟨L, env, hL, hwL, hbnL, henvL⟩ :
      ∃ (L : Nat) (env : Nat -> In₁ × In₂),
        1 ≤ L ∧ w.length = L ∧ branchNode env L = ms ∧ env L = mh := by
    refine ⟨ms.length, fun j => (ms ++ [mh]).getD j default,
      List.length_pos_of_ne_nil hne, ?_, ?_, ?_⟩
    · rw [← hsw]
      simp [senderWord]
    · rw [branchNode_getD (ms ++ [mh]) ms.length
        (by rw [List.length_append]; omega), List.take_left]
    · show (ms ++ [mh]).getD ms.length default = mh
      rw [List.getD_append_right ms [mh] default ms.length
        (Nat.le_refl _)]
      simp
  have hnts :
      narrowedThreadState (A.leftBlockMonitor a.1)
          (leftBlockNarrowed (tauTree σ τ) node₀) env L =
        base := by
    show
      narrowedControl (A.leftBlockMonitor a.1)
          (leftBlockNarrowed (tauTree σ τ) node₀) (branchNode env L) =
        base
    rw [hbnL]
    exact hctrl
  set th : ChainThread A :=
    leftThreadReverse base (tauLeftClose σ τ a w) (tauLeftRev σ τ a w)
      mh.1 mh.2 with hth
  have h1 :
      blockLeftPlay σ τ a env (4 * L) =
        .blockL (commitmentOf σ τ a) w base.1 base.2 := by
    have h := blockLeftPlay_blockL σ τ a env node₀ hp (L - 1)
    rw [show L - 1 + 1 = L by omega] at h
    rw [show 4 * L = 4 * (L - 1) + 4 by omega, h, hbnL, hsw, hnts]
  have h2 :
      blockLeftPlay σ τ a env (4 * L + 2) =
        .recvL (commitmentOf σ τ a) w base.1 base.2
          (blockRevTableL σ τ a w base.1 base.2) mh := by
    rw [show 4 * L + 2 = (4 * L + 1) + 1 by omega,
      blockLeftPlay_succ σ τ a env (4 * L + 1),
      blockLeftPlay_succ σ τ a env (4 * L), h1,
      show advance σ τ env (.blockL (commitmentOf σ τ a) w base.1 base.2) =
          τ.move (.blockL (commitmentOf σ τ a) w base.1 base.2) from rfl,
      blockRevTableL_spec σ τ a w base.1 base.2]
    show
      UniformizationPosition.recvL (commitmentOf σ τ a) w base.1 base.2
          (blockRevTableL σ τ a w base.1 base.2) (env w.length) =
        _
    rw [hwL, henvL]
  have h3 :
      blockLeftPlay σ τ a env (4 * L + 3) =
        .resolveL (commitmentOf σ τ a) w base.1 base.2
          (blockRevTableL σ τ a w base.1 base.2) mh
          (recvChoiceL σ τ a w base.1 base.2 mh) := by
    rw [show 4 * L + 3 = (4 * L + 2) + 1 by omega,
      blockLeftPlay_succ σ τ a env (4 * L + 2), h2]
    exact recvChoiceL_spec σ τ a w base.1 base.2 mh
  have hq0 : A.priority th.2.2 ≤ A.priority base.2 :=
    priority_minPriorityState_le_left _ _
  have hfst : A.priority base.2 ≤ A.priority base.1 := by
    have h := leftThread_snd_le_fst a.1
      (leftBlockNarrowed (tauTree σ τ) node₀) env L
    rw [hnts] at h
    exact h
  refine ⟨⟨4 * L + 7,
    fun t =>
      if t ≤ 4 * L + 3 then blockLeftPlay σ τ a env t
      else if t = 4 * L + 4 then
        .closeL (commitmentOf σ τ a) w base.1 base.2
          (blockRevTableL σ τ a w base.1 base.2) mh
          (recvChoiceL σ τ a w base.1 base.2 mh)
      else if t = 4 * L + 5 then
        .closeResolveL (commitmentOf σ τ a) w base.1 base.2
          (blockRevTableL σ τ a w base.1 base.2) mh
          (recvChoiceL σ τ a w base.1 base.2 mh)
          (closeChoiceL σ τ a w base.1 base.2 mh)
      else if t = 4 * L + 6 then
        uRevReverseRTarget (A := A) base.1 base.2 mh
          (blockRevTableL σ τ a w base.1 base.2 mh.1)
          (closeChoiceL σ τ a w base.1 base.2 mh)
      else mkRevBlock σ τ (Sum.inr [mh.1]) th,
    by omega, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · -- play_zero
    simp only []
    rw [if_pos (show (0 : Nat) ≤ 4 * L + 3 by omega)]
    rfl
  · -- play_len
    simp only []
    rw [if_neg (show ¬ 4 * L + 7 ≤ 4 * L + 3 by omega),
      if_neg (show ¬ 4 * L + 7 = 4 * L + 4 by omega),
      if_neg (show ¬ 4 * L + 7 = 4 * L + 5 by omega),
      if_neg (show ¬ 4 * L + 7 = 4 * L + 6 by omega)]
  · -- step
    intro t ht
    simp only []
    by_cases hc1 : t ≤ 4 * L + 2
    · rw [if_pos (show t ≤ 4 * L + 3 by omega),
        if_pos (show t + 1 ≤ 4 * L + 3 by omega)]
      exact blockLeftPlay_step σ τ a env t
    · by_cases hc2 : t = 4 * L + 3
      · subst hc2
        rw [if_pos (show 4 * L + 3 ≤ 4 * L + 3 by omega),
          if_neg (show ¬ 4 * L + 3 + 1 ≤ 4 * L + 3 by omega),
          if_pos (show 4 * L + 3 + 1 = 4 * L + 4 by omega), h3]
        exact Or.inr rfl
      · by_cases hc3 : t = 4 * L + 4
        · subst hc3
          rw [if_neg (show ¬ 4 * L + 4 ≤ 4 * L + 3 by omega),
            if_pos (show (4 * L + 4 : Nat) = 4 * L + 4 from rfl),
            if_neg (show ¬ 4 * L + 4 + 1 ≤ 4 * L + 3 by omega),
            if_neg (show ¬ 4 * L + 4 + 1 = 4 * L + 4 by omega),
            if_pos (show 4 * L + 4 + 1 = 4 * L + 5 by omega)]
          exact ⟨closeChoiceL σ τ a w base.1 base.2 mh, rfl⟩
        · by_cases hc4 : t = 4 * L + 5
          · subst hc4
            rw [if_neg (show ¬ 4 * L + 5 ≤ 4 * L + 3 by omega),
              if_neg (show ¬ 4 * L + 5 = 4 * L + 4 by omega),
              if_pos rfl,
              if_neg (show ¬ 4 * L + 5 + 1 ≤ 4 * L + 3 by omega),
              if_neg (show ¬ 4 * L + 5 + 1 = 4 * L + 4 by omega),
              if_neg (show ¬ 4 * L + 5 + 1 = 4 * L + 5 by omega),
              if_pos (show 4 * L + 5 + 1 = 4 * L + 6 by omega)]
            exact Or.inr rfl
          · have hc5 : t = 4 * L + 6 := by omega
            subst hc5
            rw [if_neg (show ¬ 4 * L + 6 ≤ 4 * L + 3 by omega),
              if_neg (show ¬ 4 * L + 6 = 4 * L + 4 by omega),
              if_neg (show ¬ 4 * L + 6 = 4 * L + 5 by omega),
              if_pos rfl,
              if_neg (show ¬ 4 * L + 6 + 1 ≤ 4 * L + 3 by omega),
              if_neg (show ¬ 4 * L + 6 + 1 = 4 * L + 4 by omega),
              if_neg (show ¬ 4 * L + 6 + 1 = 4 * L + 5 by omega),
              if_neg (show ¬ 4 * L + 6 + 1 = 4 * L + 6 by omega)]
            exact ⟨_, rfl⟩
  · -- consistent
    intro t ht howner
    simp only [] at howner ⊢
    by_cases hc1 : t ≤ 4 * L + 2
    · rw [if_pos (show t ≤ 4 * L + 3 by omega)] at howner
      rw [if_pos (show t ≤ 4 * L + 3 by omega),
        if_pos (show t + 1 ≤ 4 * L + 3 by omega)]
      exact blockLeftPlay_consistent σ τ a env t howner
    · by_cases hc2 : t = 4 * L + 3
      · subst hc2
        rw [if_pos (show 4 * L + 3 ≤ 4 * L + 3 by omega), h3] at howner
        simp [uniformizationGame, uniformizationOwner] at howner
      · by_cases hc3 : t = 4 * L + 4
        · subst hc3
          rw [if_neg (show ¬ 4 * L + 4 ≤ 4 * L + 3 by omega),
            if_pos (show (4 * L + 4 : Nat) = 4 * L + 4 from rfl),
            if_neg (show ¬ 4 * L + 4 + 1 ≤ 4 * L + 3 by omega),
            if_neg (show ¬ 4 * L + 4 + 1 = 4 * L + 4 by omega),
            if_pos (show 4 * L + 4 + 1 = 4 * L + 5 by omega)]
          exact (closeChoiceL_spec σ τ a w base.1 base.2 mh).symm
        · by_cases hc4 : t = 4 * L + 5
          · subst hc4
            rw [if_neg (show ¬ 4 * L + 5 ≤ 4 * L + 3 by omega),
              if_neg (show ¬ 4 * L + 5 = 4 * L + 4 by omega),
              if_pos rfl] at howner
            simp [uniformizationGame, uniformizationOwner] at howner
          · have hc5 : t = 4 * L + 6 := by omega
            subst hc5
            rw [if_neg (show ¬ 4 * L + 6 ≤ 4 * L + 3 by omega),
              if_neg (show ¬ 4 * L + 6 = 4 * L + 4 by omega),
              if_neg (show ¬ 4 * L + 6 = 4 * L + 5 by omega),
              if_pos rfl,
              if_neg (show ¬ 4 * L + 6 + 1 ≤ 4 * L + 3 by omega),
              if_neg (show ¬ 4 * L + 6 + 1 = 4 * L + 4 by omega),
              if_neg (show ¬ 4 * L + 6 + 1 = 4 * L + 5 by omega),
              if_neg (show ¬ 4 * L + 6 + 1 = 4 * L + 6 by omega)]
            exact (commitmentRevR_spec σ τ [mh.1] th.1.1 th.1.2).symm
  · -- bound
    intro t ht0 htlen
    simp only []
    by_cases hc1 : t ≤ 4 * L + 3
    · rw [if_pos hc1]
      refine Nat.le_trans hq0 ?_
      by_cases hopen : t ≤ 3
      · have hbase : A.priority base.2 ≤ A.priority a.1 := by
          have hchain :=
            leftThread_snd_antitone a.1
              (leftBlockNarrowed (tauTree σ τ) node₀) env 0 L
          rw [show 0 + L = L by omega, hnts] at hchain
          exact
            Nat.le_trans hchain
              (leftThread_snd_le_fst a.1
                (leftBlockNarrowed (tauTree σ τ) node₀) env 0)
        interval_cases t
        · rw [blockLeftPlay_one]; exact hbase
        · rw [blockLeftPlay_two]; exact hbase
        · rw [blockLeftPlay_three]; exact hbase
      · obtain ⟨s, rfl⟩ : ∃ s, t = s + 4 := ⟨t - 4, by omega⟩
        rw [blockLeftPlay_priority σ τ a env node₀ hp s]
        have hchain :=
          leftThread_snd_antitone a.1
            (leftBlockNarrowed (tauTree σ τ) node₀) env (s / 4 + 1)
            (L - (s / 4 + 1))
        rw [show s / 4 + 1 + (L - (s / 4 + 1)) = L by omega, hnts]
          at hchain
        exact
          Nat.le_trans hchain
            (leftThread_snd_le_fst a.1
              (leftBlockNarrowed (tauTree σ τ) node₀) env (s / 4 + 1))
    · by_cases hc3 : t = 4 * L + 4
      · subst hc3
        rw [if_neg hc1, if_pos rfl]
        exact Nat.le_trans hq0 hfst
      · by_cases hc4 : t = 4 * L + 5
        · subst hc4
          rw [if_neg hc1,
            if_neg (show ¬ 4 * L + 5 = 4 * L + 4 by omega),
            if_pos rfl]
          exact Nat.le_trans hq0 hfst
        · have hc5 : t = 4 * L + 6 := by omega
          subst hc5
          rw [if_neg hc1,
            if_neg (show ¬ 4 * L + 6 = 4 * L + 4 by omega),
            if_neg (show ¬ 4 * L + 6 = 4 * L + 5 by omega),
            if_pos rfl]
          exact priority_minPriorityState_le_right _ _
  · -- snd_le_fst
    exact priority_minPriorityState_le_right _ _

/-- The right-block reversal entry: the orientation mirror. -/
theorem revEntryRight_exists
    (node₀ : TreeNode (GlobalJournalBranch (In₁ := In₁) A))
    (a : A.State × A.State)
    (hp : tauNodeState (In₂ := In₂) node₀ = .atNode a)
    (w : List In₁) (ms : TreeNode (In₂ × In₁))
    (base : A.State × A.State) (mh : In₂ × In₁)
    (hne : ms ≠ [])
    (hsw : senderWord ms = w)
    (hctrl :
      narrowedControl (A.rightBlockMonitor a.1)
        (rightBlockNarrowed (tauTree σ τ) node₀) ms = base) :
    Nonempty
      (RevEntrySpec σ τ a (Sum.inl [mh.1])
        (rightThreadReverse base (tauRightClose σ τ a w)
          (tauRightRev σ τ a w) mh.1 mh.2)) := by
  obtain ⟨L, renv, hL, hwL, hbnL, henvL⟩ :
      ∃ (L : Nat) (renv : Nat -> In₂ × In₁),
        1 ≤ L ∧ w.length = L ∧ branchNode renv L = ms ∧ renv L = mh := by
    refine ⟨ms.length, fun j => (ms ++ [mh]).getD j default,
      List.length_pos_of_ne_nil hne, ?_, ?_, ?_⟩
    · rw [← hsw]
      simp [senderWord]
    · rw [branchNode_getD (ms ++ [mh]) ms.length
        (by rw [List.length_append]; omega), List.take_left]
    · show (ms ++ [mh]).getD ms.length default = mh
      rw [List.getD_append_right ms [mh] default ms.length
        (Nat.le_refl _)]
      simp
  have hswap : swapEnv renv L = (mh.2, mh.1) := by
    show ((renv L).2, (renv L).1) = (mh.2, mh.1)
    rw [henvL]
  have hnts :
      narrowedThreadState (A.rightBlockMonitor a.1)
          (rightBlockNarrowed (tauTree σ τ) node₀) renv L =
        base := by
    show
      narrowedControl (A.rightBlockMonitor a.1)
          (rightBlockNarrowed (tauTree σ τ) node₀) (branchNode renv L) =
        base
    rw [hbnL]
    exact hctrl
  set th : ChainThread A :=
    rightThreadReverse base (tauRightClose σ τ a w) (tauRightRev σ τ a w)
      mh.1 mh.2 with hth
  have h1 :
      blockRightPlay σ τ a (swapEnv renv) (4 * L) =
        .blockR (commitmentOf σ τ a) w base.1 base.2 := by
    have h := blockRightPlay_blockR σ τ a renv node₀ hp (L - 1)
    rw [show L - 1 + 1 = L by omega] at h
    rw [show 4 * L = 4 * (L - 1) + 4 by omega, h, hbnL, hsw, hnts]
  have h2 :
      blockRightPlay σ τ a (swapEnv renv) (4 * L + 2) =
        .recvR (commitmentOf σ τ a) w base.1 base.2
          (blockRevTableR σ τ a w base.1 base.2) (mh.2, mh.1) := by
    rw [show 4 * L + 2 = (4 * L + 1) + 1 by omega,
      blockRightPlay_succ σ τ a (swapEnv renv) (4 * L + 1),
      blockRightPlay_succ σ τ a (swapEnv renv) (4 * L), h1,
      show advanceR σ τ (swapEnv renv)
          (.blockR (commitmentOf σ τ a) w base.1 base.2) =
          τ.move (.blockR (commitmentOf σ τ a) w base.1 base.2) from rfl,
      blockRevTableR_spec σ τ a w base.1 base.2]
    show
      UniformizationPosition.recvR (commitmentOf σ τ a) w base.1 base.2
          (blockRevTableR σ τ a w base.1 base.2) (swapEnv renv w.length) =
        _
    rw [hwL, hswap]
  have h3 :
      blockRightPlay σ τ a (swapEnv renv) (4 * L + 3) =
        .resolveR (commitmentOf σ τ a) w base.1 base.2
          (blockRevTableR σ τ a w base.1 base.2) (mh.2, mh.1)
          (recvChoiceR σ τ a w base.1 base.2 (mh.2, mh.1)) := by
    rw [show 4 * L + 3 = (4 * L + 2) + 1 by omega,
      blockRightPlay_succ σ τ a (swapEnv renv) (4 * L + 2), h2]
    exact recvChoiceR_spec σ τ a w base.1 base.2 (mh.2, mh.1)
  have hq0 : A.priority th.2.2 ≤ A.priority base.2 :=
    priority_minPriorityState_le_left _ _
  have hfst : A.priority base.2 ≤ A.priority base.1 := by
    have h := rightThread_snd_le_fst a.1
      (rightBlockNarrowed (tauTree σ τ) node₀) renv L
    rw [hnts] at h
    exact h
  refine ⟨⟨4 * L + 7,
    fun t =>
      if t ≤ 4 * L + 3 then blockRightPlay σ τ a (swapEnv renv) t
      else if t = 4 * L + 4 then
        .closeR (commitmentOf σ τ a) w base.1 base.2
          (blockRevTableR σ τ a w base.1 base.2) (mh.2, mh.1)
          (recvChoiceR σ τ a w base.1 base.2 (mh.2, mh.1))
      else if t = 4 * L + 5 then
        .closeResolveR (commitmentOf σ τ a) w base.1 base.2
          (blockRevTableR σ τ a w base.1 base.2) (mh.2, mh.1)
          (recvChoiceR σ τ a w base.1 base.2 (mh.2, mh.1))
          (closeChoiceR σ τ a w base.1 base.2 (mh.2, mh.1))
      else if t = 4 * L + 6 then
        uRevReverseLTarget (A := A) base.1 base.2 (mh.2, mh.1)
          (closeChoiceR σ τ a w base.1 base.2 (mh.2, mh.1))
          (blockRevTableR σ τ a w base.1 base.2 mh.1)
      else mkRevBlock σ τ (Sum.inl [mh.1]) th,
    by omega, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · -- play_zero
    simp only []
    rw [if_pos (show (0 : Nat) ≤ 4 * L + 3 by omega)]
    rfl
  · -- play_len
    simp only []
    rw [if_neg (show ¬ 4 * L + 7 ≤ 4 * L + 3 by omega),
      if_neg (show ¬ 4 * L + 7 = 4 * L + 4 by omega),
      if_neg (show ¬ 4 * L + 7 = 4 * L + 5 by omega),
      if_neg (show ¬ 4 * L + 7 = 4 * L + 6 by omega)]
  · -- step
    intro t ht
    simp only []
    by_cases hc1 : t ≤ 4 * L + 2
    · rw [if_pos (show t ≤ 4 * L + 3 by omega),
        if_pos (show t + 1 ≤ 4 * L + 3 by omega)]
      exact blockRightPlay_step σ τ a (swapEnv renv) t
    · by_cases hc2 : t = 4 * L + 3
      · subst hc2
        rw [if_pos (show 4 * L + 3 ≤ 4 * L + 3 by omega),
          if_neg (show ¬ 4 * L + 3 + 1 ≤ 4 * L + 3 by omega),
          if_pos (show 4 * L + 3 + 1 = 4 * L + 4 by omega), h3]
        exact Or.inr rfl
      · by_cases hc3 : t = 4 * L + 4
        · subst hc3
          rw [if_neg (show ¬ 4 * L + 4 ≤ 4 * L + 3 by omega),
            if_pos (show (4 * L + 4 : Nat) = 4 * L + 4 from rfl),
            if_neg (show ¬ 4 * L + 4 + 1 ≤ 4 * L + 3 by omega),
            if_neg (show ¬ 4 * L + 4 + 1 = 4 * L + 4 by omega),
            if_pos (show 4 * L + 4 + 1 = 4 * L + 5 by omega)]
          exact ⟨closeChoiceR σ τ a w base.1 base.2 (mh.2, mh.1), rfl⟩
        · by_cases hc4 : t = 4 * L + 5
          · subst hc4
            rw [if_neg (show ¬ 4 * L + 5 ≤ 4 * L + 3 by omega),
              if_neg (show ¬ 4 * L + 5 = 4 * L + 4 by omega),
              if_pos rfl,
              if_neg (show ¬ 4 * L + 5 + 1 ≤ 4 * L + 3 by omega),
              if_neg (show ¬ 4 * L + 5 + 1 = 4 * L + 4 by omega),
              if_neg (show ¬ 4 * L + 5 + 1 = 4 * L + 5 by omega),
              if_pos (show 4 * L + 5 + 1 = 4 * L + 6 by omega)]
            exact Or.inr rfl
          · have hc5 : t = 4 * L + 6 := by omega
            subst hc5
            rw [if_neg (show ¬ 4 * L + 6 ≤ 4 * L + 3 by omega),
              if_neg (show ¬ 4 * L + 6 = 4 * L + 4 by omega),
              if_neg (show ¬ 4 * L + 6 = 4 * L + 5 by omega),
              if_pos rfl,
              if_neg (show ¬ 4 * L + 6 + 1 ≤ 4 * L + 3 by omega),
              if_neg (show ¬ 4 * L + 6 + 1 = 4 * L + 4 by omega),
              if_neg (show ¬ 4 * L + 6 + 1 = 4 * L + 5 by omega),
              if_neg (show ¬ 4 * L + 6 + 1 = 4 * L + 6 by omega)]
            exact ⟨_, rfl⟩
  · -- consistent
    intro t ht howner
    simp only [] at howner ⊢
    by_cases hc1 : t ≤ 4 * L + 2
    · rw [if_pos (show t ≤ 4 * L + 3 by omega)] at howner
      rw [if_pos (show t ≤ 4 * L + 3 by omega),
        if_pos (show t + 1 ≤ 4 * L + 3 by omega)]
      exact blockRightPlay_consistent σ τ a (swapEnv renv) t howner
    · by_cases hc2 : t = 4 * L + 3
      · subst hc2
        rw [if_pos (show 4 * L + 3 ≤ 4 * L + 3 by omega), h3] at howner
        simp [uniformizationGame, uniformizationOwner] at howner
      · by_cases hc3 : t = 4 * L + 4
        · subst hc3
          rw [if_neg (show ¬ 4 * L + 4 ≤ 4 * L + 3 by omega),
            if_pos (show (4 * L + 4 : Nat) = 4 * L + 4 from rfl),
            if_neg (show ¬ 4 * L + 4 + 1 ≤ 4 * L + 3 by omega),
            if_neg (show ¬ 4 * L + 4 + 1 = 4 * L + 4 by omega),
            if_pos (show 4 * L + 4 + 1 = 4 * L + 5 by omega)]
          exact
            (closeChoiceR_spec σ τ a w base.1 base.2 (mh.2, mh.1)).symm
        · by_cases hc4 : t = 4 * L + 5
          · subst hc4
            rw [if_neg (show ¬ 4 * L + 5 ≤ 4 * L + 3 by omega),
              if_neg (show ¬ 4 * L + 5 = 4 * L + 4 by omega),
              if_pos rfl] at howner
            simp [uniformizationGame, uniformizationOwner] at howner
          · have hc5 : t = 4 * L + 6 := by omega
            subst hc5
            rw [if_neg (show ¬ 4 * L + 6 ≤ 4 * L + 3 by omega),
              if_neg (show ¬ 4 * L + 6 = 4 * L + 4 by omega),
              if_neg (show ¬ 4 * L + 6 = 4 * L + 5 by omega),
              if_pos rfl,
              if_neg (show ¬ 4 * L + 6 + 1 ≤ 4 * L + 3 by omega),
              if_neg (show ¬ 4 * L + 6 + 1 = 4 * L + 4 by omega),
              if_neg (show ¬ 4 * L + 6 + 1 = 4 * L + 5 by omega),
              if_neg (show ¬ 4 * L + 6 + 1 = 4 * L + 6 by omega)]
            exact (commitmentRevL_spec σ τ [mh.1] th.1.1 th.1.2).symm
  · -- bound
    intro t ht0 htlen
    simp only []
    by_cases hc1 : t ≤ 4 * L + 3
    · rw [if_pos hc1]
      refine Nat.le_trans hq0 ?_
      by_cases hopen : t ≤ 3
      · have hbase : A.priority base.2 ≤ A.priority a.1 := by
          have hchain :=
            rightThread_snd_antitone a.1
              (rightBlockNarrowed (tauTree σ τ) node₀) renv 0 L
          rw [show 0 + L = L by omega, hnts] at hchain
          exact
            Nat.le_trans hchain
              (rightThread_snd_le_fst a.1
                (rightBlockNarrowed (tauTree σ τ) node₀) renv 0)
        interval_cases t
        · rw [blockRightPlay_one]; exact hbase
        · rw [blockRightPlay_two]; exact hbase
        · rw [blockRightPlay_three]; exact hbase
      · obtain ⟨s, rfl⟩ : ∃ s, t = s + 4 := ⟨t - 4, by omega⟩
        rw [blockRightPlay_priority σ τ a renv node₀ hp s]
        have hchain :=
          rightThread_snd_antitone a.1
            (rightBlockNarrowed (tauTree σ τ) node₀) renv (s / 4 + 1)
            (L - (s / 4 + 1))
        rw [show s / 4 + 1 + (L - (s / 4 + 1)) = L by omega, hnts]
          at hchain
        exact
          Nat.le_trans hchain
            (rightThread_snd_le_fst a.1
              (rightBlockNarrowed (tauTree σ τ) node₀) renv (s / 4 + 1))
    · by_cases hc3 : t = 4 * L + 4
      · subst hc3
        rw [if_neg hc1, if_pos rfl]
        exact Nat.le_trans hq0 hfst
      · by_cases hc4 : t = 4 * L + 5
        · subst hc4
          rw [if_neg hc1,
            if_neg (show ¬ 4 * L + 5 = 4 * L + 4 by omega),
            if_pos rfl]
          exact Nat.le_trans hq0 hfst
        · have hc5 : t = 4 * L + 6 := by omega
          subst hc5
          rw [if_neg hc1,
            if_neg (show ¬ 4 * L + 6 = 4 * L + 4 by omega),
            if_neg (show ¬ 4 * L + 6 = 4 * L + 5 by omega),
            if_pos rfl]
          exact priority_minPriorityState_le_right _ _
  · -- snd_le_fst
    exact priority_minPriorityState_le_right _ _

/-! ### The segment extraction -/

/-- A sender direction never steps into an atom. -/
theorem globalJournalStep_inr_ne_inl
    (state : GlobalJournalState (In₁ := In₁) A CL CR CC)
    (label : GlobalJournalLabel (In₁ := In₁) A) (d : In₂ ⊕ In₁)
    (atom : A.State × A.State) :
    globalJournalStep A CL CR CC state label (Sum.inr d) ≠
      Sum.inl atom := by
  intro h
  rcases state with a | ⟨c, t⟩ | ⟨c, t⟩ | ⟨c, t⟩ | ⟨c, t⟩ | u <;>
    rcases d with x | x <;>
    simp [globalJournalStep] at h

/-- An atom direction steps into that atom or the sink. -/
theorem globalJournalStep_inl_or_sink
    (state : GlobalJournalState (In₁ := In₁) A CL CR CC)
    (label : GlobalJournalLabel (In₁ := In₁) A)
    (atom' : A.State × A.State) :
    globalJournalStep A CL CR CC state label (Sum.inl atom') =
        Sum.inl atom' ∨
      globalJournalStep A CL CR CC state label (Sum.inl atom') =
        Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr PUnit.unit)))) := by
  rcases state with a | ⟨c, t⟩ | ⟨c, t⟩ | ⟨c, t⟩ | ⟨c, t⟩ | u
  · simp only [globalJournalStep]
    split
    · exact Or.inl rfl
    · exact Or.inr rfl
  · simp only [globalJournalStep]
    split
    · exact Or.inl rfl
    · exact Or.inr rfl
  · simp only [globalJournalStep]
    split
    · exact Or.inl rfl
    · exact Or.inr rfl
  · simp only [globalJournalStep]
    split
    · exact Or.inl rfl
    · exact Or.inr rfl
  · simp only [globalJournalStep]
    split
    · exact Or.inl rfl
    · exact Or.inr rfl
  · exact Or.inr rfl

/--
Between a boundary and the next one the branch realizes a
winner-consistent segment: the sole branch direction is a
synchronizing round, the branch runs a block closed by an atom
direction, or the branch reverses out of the block and runs a
reversal chain closed by an atom direction.
-/
theorem exists_segmentSpec_of_boundary_pair
    (branch : Nat -> GlobalJournalBranch (In₁ := In₁) A)
    (hns :
      ∀ m, branchRun σ τ CL CR CC branch m ≠
        Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr PUnit.unit)))))
    (n n' : Nat) (a a' : A.State × A.State)
    (hrun : branchRun σ τ CL CR CC branch n = Sum.inl a)
    (hrun' : branchRun σ τ CL CR CC branch n' = Sum.inl a')
    (hlt : n < n')
    (hmid :
      ∀ m, n < m -> m < n' ->
        ∀ atom, branchRun σ τ CL CR CC branch m ≠ Sum.inl atom) :
    Nonempty (SegmentSpec σ τ a a') := by
  classical
  have hpa : tauNodeState (In₂ := In₂) (branchNode branch n) = .atNode a :=
    tauNodeState_atNode_of_run_inl CL CR CC σ τ (branchNode branch n) a
      hrun
  have htree :
      tauTree σ τ (branchNode branch n) = tauLabelOf σ τ (.atNode a) := by
    show tauLabelOf σ τ (tauNodeState (branchNode branch n)) = _
    rw [hpa]
  -- the chain-crossing continuation, shared by both block orientations
  have hchainClose :
      ∀ (p : Nat) (init : List In₂ ⊕ List In₁)
        (T₀ : Finset (ChainThread A)),
        n < p -> p + 1 < n' ->
        tauNodeState (In₂ := In₂) (branchNode branch (p + 1)) =
          revParse (A := A) init ->
        branchRun σ τ CL CR CC branch (p + 1) =
          revModeState CL CR CC init (CC.start T₀) T₀ ->
        ∃ (es : TreeNode ((In₁ × In₂) × (In₂ ⊕ In₁))) (mc : In₁ × In₂)
          (qm₀ : ChainThread A),
          qm₀ ∈ T₀ ∧
            a' =
              chainThreadClose
                (chainFold A (chainNarrowed σ τ init) [] qm₀ es)
                (chainNarrowed σ τ init (es.map Prod.snd)) mc := by
    intro p init T₀ hnp hpn' hp₁ hrun₁
    have hrun₁' :
        globalRunIn CL CR CC (tauTree σ τ)
            (Sum.inl (A.initial, A.initial))
            (branchNode branch (p + 1)) =
          revModeState CL CR CC init (CC.start T₀) T₀ := hrun₁
    have hdirC :
        ∀ u, ∃ dd : In₂ ⊕ In₁,
          p + 1 + u < n' - 1 -> branch (p + 1 + u) = Sum.inr dd := by
      intro u
      by_cases hu : p + 1 + u < n' - 1
      · rcases hb : branch (p + 1 + u) with ac | x2 | x1
        · exfalso
          have hsucc := branchRun_succ σ τ CL CR CC branch (p + 1 + u)
          rw [hb] at hsucc
          rcases
            globalJournalStep_inl_or_sink CL CR CC
              (branchRun σ τ CL CR CC branch (p + 1 + u))
              (tauTree σ τ (branchNode branch (p + 1 + u))) ac with
            hc | hc
          · rw [hc] at hsucc
            exact hmid (p + 1 + u + 1) (by omega) (by omega) ac hsucc
          · rw [hc] at hsucc
            exact hns (p + 1 + u + 1) hsucc
        · exact ⟨Sum.inl x2, fun _ => rfl⟩
        · exact ⟨Sum.inr x1, fun _ => rfl⟩
      · exact ⟨default, fun hc => absurd hc hu⟩
    choose dirs hdirs using hdirC
    have hnodeChain :
        ∀ u, u ≤ n' - 1 - (p + 1) ->
          branchNode branch (p + 1 + u) =
            branchNode branch (p + 1) ++
              chainNode (A := A) (branchNode dirs u) := by
      intro u
      induction u with
      | zero =>
          intro _
          rw [show branchNode dirs 0 = ([] : TreeNode (In₂ ⊕ In₁))
            from rfl]
          simp [chainNode]
      | succ u ih =>
          intro hu
          rw [show p + 1 + (u + 1) = p + 1 + u + 1 from rfl,
            show branchNode branch (p + 1 + u + 1) =
              branchNode branch (p + 1 + u) ++ [branch (p + 1 + u)]
              from rfl,
            ih (by omega), hdirs u (by omega),
            show branchNode dirs (u + 1) =
              branchNode dirs u ++ [dirs u] from rfl]
          simp [chainNode]
    obtain ⟨u, hu⟩ : ∃ u, n' - 1 = p + 1 + u :=
      ⟨n' - 1 - (p + 1), by omega⟩
    obtain ⟨tC, htC⟩ :=
      globalRunIn_chain CL CR CC σ τ (branchNode branch (p + 1)) init
        T₀ hp₁ hrun₁' (branchNode dirs u)
    have hrunC :
        branchRun σ τ CL CR CC branch (n' - 1) =
          revModeState CL CR CC
            (chainWord init (branchNode dirs u))
            (DeterministicBlockMonitor.controlIn CC.monitor
              (chainNarrowed σ τ init) (CC.start T₀)
              (branchNode dirs u)) tC := by
      show globalRunIn CL CR CC (tauTree σ τ)
          (Sum.inl (A.initial, A.initial))
          (branchNode branch (n' - 1)) = _
      rw [hu, hnodeChain u (by omega)]
      exact htC
    have htreeC :
        tauTree σ τ (branchNode branch (n' - 1)) =
          tauLabelOf σ τ
            (revParse (A := A)
              (chainWord init (branchNode dirs u))) := by
      rw [hu, hnodeChain u (by omega)]
      exact
        tauTree_chainNode σ τ (branchNode branch (p + 1)) init hp₁
          (branchNode dirs u)
    have hstepC := branchRun_succ σ τ CL CR CC branch (n' - 1)
    rw [show n' - 1 + 1 = n' by omega, hrun', hrunC, htreeC] at hstepC
    rcases hbrC : branch (n' - 1) with aa | x2 | x1
    · rw [hbrC] at hstepC
      rcases hcwC :
          chainWord init (branchNode dirs u) with
        wordL | wordR <;> rw [hcwC] at hstepC
      · simp only [revModeState, revParse, globalJournalStep,
          tauLabelOf, GlobalJournalLabel.revLeft,
          GlobalJournalLabel.revRight] at hstepC
        by_cases hmem :
            aa ∈ revLeftCloseSubset tC (tauRevLeftLabel σ τ wordL)
        · rw [if_pos hmem] at hstepC
          have haa : aa = a' := Sum.inl.inj hstepC.symm
          rw [haa] at hmem
          obtain ⟨qmk, mc, hqmk, hclose⟩ := mem_revLeftCloseSubset hmem
          obtain ⟨es, hmap, qm₀, hqm₀, hfold⟩ :=
            chainThread_trace CL CR CC σ τ (branchNode branch (p + 1))
              init T₀ hp₁ hrun₁' (branchNode dirs u) _ tC
              (by
                rw [show branchNode branch (p + 1) ++
                    chainNode (A := A) (branchNode dirs u) =
                    branchNode branch (n' - 1) from
                    (by rw [hu]; exact (hnodeChain u (by omega)).symm)]
                exact hrunC)
              qmk hqmk
          refine ⟨es, mc, qm₀, hqm₀, ?_⟩
          rw [hfold, hmap,
            chainNarrowed_eq_left σ τ init (branchNode dirs u) wordL
              hcwC]
          exact hclose
        · rw [if_neg hmem] at hstepC
          exact absurd hstepC.symm (by simp)
      · simp only [revModeState, revParse, globalJournalStep,
          tauLabelOf, GlobalJournalLabel.revLeft,
          GlobalJournalLabel.revRight] at hstepC
        by_cases hmem :
            aa ∈ revRightCloseSubset tC (tauRevRightLabel σ τ wordR)
        · rw [if_pos hmem] at hstepC
          have haa : aa = a' := Sum.inl.inj hstepC.symm
          rw [haa] at hmem
          obtain ⟨qmk, mc, hqmk, hclose⟩ :=
            mem_revRightCloseSubset hmem
          obtain ⟨es, hmap, qm₀, hqm₀, hfold⟩ :=
            chainThread_trace CL CR CC σ τ (branchNode branch (p + 1))
              init T₀ hp₁ hrun₁' (branchNode dirs u) _ tC
              (by
                rw [show branchNode branch (p + 1) ++
                    chainNode (A := A) (branchNode dirs u) =
                    branchNode branch (n' - 1) from
                    (by rw [hu]; exact (hnodeChain u (by omega)).symm)]
                exact hrunC)
              qmk hqmk
          refine ⟨es, mc, qm₀, hqm₀, ?_⟩
          rw [hfold, hmap,
            chainNarrowed_eq_right σ τ init (branchNode dirs u) wordR
              hcwC]
          exact hclose
        · rw [if_neg hmem] at hstepC
          exact absurd hstepC.symm (by simp)
    · rw [hbrC] at hstepC
      exact
        absurd hstepC.symm
          (globalJournalStep_inr_ne_inl CL CR CC _ _ (Sum.inl x2) a')
    · rw [hbrC] at hstepC
      exact
        absurd hstepC.symm
          (globalJournalStep_inr_ne_inl CL CR CC _ _ (Sum.inr x1) a')
  rcases hbr0 : branch n with a'' | x₀ | x₀
  · -- synchronizing round
    have hstep := branchRun_succ σ τ CL CR CC branch n
    rw [hrun, hbr0, htree] at hstep
    simp only [globalJournalStep, tauLabelOf,
      GlobalJournalLabel.leftNarrowed, GlobalJournalLabel.leftClose,
      GlobalJournalLabel.leftRev, GlobalJournalLabel.rightNarrowed,
      GlobalJournalLabel.rightClose, GlobalJournalLabel.rightRev,
      GlobalJournalLabel.revLeft, GlobalJournalLabel.revRight] at hstep
    by_cases hmem :
        a'' ∈
          bothAtomSubset a (tauOpeningLeftLabel σ τ a)
            (tauOpeningRightLabel σ τ a)
    · rw [if_pos hmem] at hstep
      have hn' : n' = n + 1 := by
        by_contra hne
        exact hmid (n + 1) (by omega) (by omega) a'' hstep
      rw [hn', hstep] at hrun'
      have ha'' : a'' = a' := Sum.inl.inj hrun'
      obtain ⟨move, hmove⟩ := mem_bothAtomSubset hmem
      exact ⟨segmentBoth σ τ a a' move (by rw [← ha'']; exact hmove)⟩
    · rw [if_neg hmem] at hstep
      exact absurd hstep (hns (n + 1))
  · -- left block
    have hstep1 := branchRun_succ σ τ CL CR CC branch n
    rw [hrun, hbr0, htree] at hstep1
    simp only [globalJournalStep, tauLabelOf,
      GlobalJournalLabel.leftNarrowed, GlobalJournalLabel.leftClose,
      GlobalJournalLabel.leftRev, GlobalJournalLabel.rightNarrowed,
      GlobalJournalLabel.rightClose, GlobalJournalLabel.rightRev,
      GlobalJournalLabel.revLeft, GlobalJournalLabel.revRight] at hstep1
    have hblock :
        ∀ j, 1 ≤ j -> n + j < n' ->
          (∀ i, 1 ≤ i -> i < j ->
            ∃ x : In₂, branch (n + i) = Sum.inr (Sum.inl x)) ->
          ∃ w : List In₂,
            w ≠ [] ∧
              branchNode branch (n + j) =
                branchNode branch n ++ senderLNode (A := A) w ∧
                tauNodeState (In₂ := In₂) (branchNode branch (n + j)) =
                  .inLeft a w ∧
                  ∃ (c : CL.monitor.State)
                    (t : Finset (A.State × A.State)),
                    branchRun σ τ CL CR CC branch (n + j) =
                      Sum.inr (Sum.inl (c, t)) := by
      intro j
      induction j with
      | zero => omega
      | succ j ih =>
          intro _ hjlt hdirsj
          rcases Nat.eq_zero_or_pos j with rfl | hj
          · refine ⟨[x₀], by simp, ?_, ?_, ?_⟩
            · rw [show branchNode branch (n + 1) =
                branchNode branch n ++ [branch n] from rfl, hbr0]
              rfl
            · rw [show branchNode branch (n + 1) =
                branchNode branch n ++ [branch n] from rfl, hbr0,
                tauNodeState_append, hpa]
              rfl
            · exact ⟨_, _, hstep1⟩
          · obtain ⟨w, hwne, hnode, hpar, c, t, hrunj⟩ :=
              ih (by omega) (by omega)
                (fun i h1 h2 => hdirsj i h1 (by omega))
            obtain ⟨x, hbr⟩ := hdirsj j (by omega) (by omega)
            have hstepj := branchRun_succ σ τ CL CR CC branch (n + j)
            rw [hrunj, hbr] at hstepj
            refine ⟨w ++ [x], by simp, ?_, ?_, ?_⟩
            · rw [show branchNode branch (n + (j + 1)) =
                branchNode branch (n + j) ++ [branch (n + j)] from rfl,
                hnode, hbr, senderLNode_append, List.append_assoc]
            · rw [show branchNode branch (n + (j + 1)) =
                branchNode branch (n + j) ++ [branch (n + j)] from rfl,
                tauNodeState_append, hpar, hbr]
              rfl
            · simp only [globalJournalStep] at hstepj
              exact ⟨_, _, by
                rw [show n + (j + 1) = n + j + 1 by omega]
                exact hstepj⟩
    have hn2 : n + 2 ≤ n' := by
      by_contra hcon
      have hn1 : n' = n + 1 := by omega
      rw [hn1, hstep1] at hrun'
      exact absurd hrun' (by simp)
    obtain ⟨j₀, ⟨⟨hj₀1, hj₀d⟩, hj₀not⟩, hj₀min⟩ :
        ∃ j₀,
          ((1 ≤ j₀ ∧ j₀ ≤ n' - n - 1) ∧
            ¬ ∃ x : In₂, branch (n + j₀) = Sum.inr (Sum.inl x)) ∧
            ∀ i, i < j₀ -> 1 ≤ i ->
              ∃ x : In₂, branch (n + i) = Sum.inr (Sum.inl x) := by
      have hexlast :
          ¬ ∃ x : In₂, branch (n + (n' - n - 1)) = Sum.inr (Sum.inl x) := by
        rintro ⟨x, hx⟩
        have hsucc := branchRun_succ σ τ CL CR CC branch (n + (n' - n - 1))
        rw [hx, show n + (n' - n - 1) + 1 = n' by omega, hrun']
          at hsucc
        exact
          globalJournalStep_inr_ne_inl CL CR CC _ _ (Sum.inl x) a'
            hsucc.symm
      have hex :
          ∃ j, (1 ≤ j ∧ j ≤ n' - n - 1) ∧
            ¬ ∃ x : In₂, branch (n + j) = Sum.inr (Sum.inl x) :=
        ⟨n' - n - 1, ⟨by omega, Nat.le_refl _⟩, hexlast⟩
      refine ⟨Nat.find hex, Nat.find_spec hex, ?_⟩
      intro i hi h1
      by_contra hcon
      have hspec := (Nat.find_spec hex).1.2
      exact absurd ⟨⟨h1, by omega⟩, hcon⟩ (Nat.find_min hex hi)
    obtain ⟨w, hwne, hnode, hpar, c, t, hrunL⟩ :=
      hblock j₀ hj₀1 (by omega) (fun i h1 h2 => hj₀min i h2 h1)
    have htreeL :
        tauTree σ τ (branchNode branch (n + j₀)) =
          tauLabelOf σ τ (.inLeft a w) := by
      show tauLabelOf σ τ (tauNodeState _) = _
      rw [hpar]
    have hstepL := branchRun_succ σ τ CL CR CC branch (n + j₀)
    rw [hrunL, htreeL] at hstepL
    rcases hbrL : branch (n + j₀) with ac | x | x
    · -- atom close out of the block
      rw [hbrL] at hstepL
      simp only [globalJournalStep, tauLabelOf,
      GlobalJournalLabel.leftNarrowed, GlobalJournalLabel.leftClose,
      GlobalJournalLabel.leftRev, GlobalJournalLabel.rightNarrowed,
      GlobalJournalLabel.rightClose, GlobalJournalLabel.rightRev,
      GlobalJournalLabel.revLeft, GlobalJournalLabel.revRight] at hstepL
      have hj₀last : n + j₀ + 1 = n' := by
        by_contra hne
        by_cases hmem :
            ac ∈
              leftCloseSubset t (tauLeftLabel σ τ a w)
                (tauLeftClose σ τ a w)
        · rw [if_pos hmem] at hstepL
          exact hmid (n + j₀ + 1) (by omega) (by omega) ac hstepL
        · rw [if_neg hmem] at hstepL
          exact hns (n + j₀ + 1) hstepL
      rw [hj₀last, hrun'] at hstepL
      by_cases hmem :
          ac ∈
            leftCloseSubset t (tauLeftLabel σ τ a w)
              (tauLeftClose σ τ a w)
      · rw [if_pos hmem] at hstepL
        have hac : ac = a' := Sum.inl.inj hstepL.symm
        rw [hac] at hmem
        obtain ⟨base, move, hbase, hmove⟩ := mem_leftCloseSubset hmem
        rcases List.eq_nil_or_concat w with rfl | ⟨w', xl, hwc⟩
        · exact absurd rfl hwne
        · rw [List.concat_eq_append] at hwc
          subst hwc
          obtain ⟨ms, hsw, hctrl⟩ :=
            leftThread_trace σ τ CL CR CC (branchNode branch n) a hrun
              w' xl c t (by rw [← hnode]; exact hrunL) base hbase
          exact
            segmentLeft_exists σ τ (branchNode branch n) a a' hpa
              (w' ++ [xl]) ms base move
              (by
                intro hmsnil
                rw [hmsnil] at hsw
                exact absurd hsw.symm (by simp [senderWord]))
              hsw hctrl hmove
      · rw [if_neg hmem] at hstepL
        exact absurd hstepL.symm (by simp)
    · exact absurd ⟨x, hbrL⟩ hj₀not
    · -- direct reversal out of the left block
      rw [hbrL] at hstepL
      have hp1lt : n + j₀ + 1 < n' := by
        by_contra hcon
        have : n + j₀ + 1 = n' := by omega
        rw [this, hrun'] at hstepL
        exact
          absurd hstepL.symm
            (globalJournalStep_inr_ne_inl CL CR CC _ _ (Sum.inr x) a')
      have hp₁ :
          tauNodeState (In₂ := In₂) (branchNode branch (n + j₀ + 1)) =
            revParse (A := A)
              (Sum.inr ([x] : List In₁)) := by
        rw [show branchNode branch (n + j₀ + 1) =
          branchNode branch (n + j₀) ++ [branch (n + j₀)] from rfl,
          tauNodeState_append, hpar, hbrL]
        rfl
      have hrun₁ :
          branchRun σ τ CL CR CC branch (n + j₀ + 1) =
            revModeState CL CR CC (Sum.inr ([x] : List In₁))
              (CC.start
                (leftReverseSubset t (tauLeftClose σ τ a w)
                  (tauLeftRev σ τ a w) x))
              (leftReverseSubset t (tauLeftClose σ τ a w)
                (tauLeftRev σ τ a w) x) := by
        rw [hstepL]
        rfl
      obtain ⟨es, mc, qm₀, hqm₀, hclose⟩ :=
        hchainClose (n + j₀) (Sum.inr [x]) _ (by omega) hp1lt hp₁
          hrun₁
      obtain ⟨base, i2, hbase, hqm₀eq⟩ := mem_leftReverseSubset hqm₀
      rcases List.eq_nil_or_concat w with rfl | ⟨w', xl, hwc⟩
      · exact absurd rfl hwne
      · rw [List.concat_eq_append] at hwc
        subst hwc
        obtain ⟨ms, hsw, hctrl⟩ :=
          leftThread_trace σ τ CL CR CC (branchNode branch n) a hrun
            w' xl c t (by rw [← hnode]; exact hrunL) base hbase
        obtain ⟨E⟩ :=
          revEntryLeft_exists σ τ (branchNode branch n) a hpa
            (w' ++ [xl]) ms base (x, i2)
            (by
              intro hmsnil
              rw [hmsnil] at hsw
              exact absurd hsw.symm (by simp [senderWord]))
            hsw hctrl
        refine
          segmentSpec_of_revEntry σ τ (by simp [chainWordNonempty]) E es mc
            a' ?_
        rw [hqm₀eq] at hclose
        exact hclose
  · -- right block
    have hstep1 := branchRun_succ σ τ CL CR CC branch n
    rw [hrun, hbr0, htree] at hstep1
    simp only [globalJournalStep, tauLabelOf,
      GlobalJournalLabel.leftNarrowed, GlobalJournalLabel.leftClose,
      GlobalJournalLabel.leftRev, GlobalJournalLabel.rightNarrowed,
      GlobalJournalLabel.rightClose, GlobalJournalLabel.rightRev,
      GlobalJournalLabel.revLeft, GlobalJournalLabel.revRight] at hstep1
    have hblock :
        ∀ j, 1 ≤ j -> n + j < n' ->
          (∀ i, 1 ≤ i -> i < j ->
            ∃ x : In₁, branch (n + i) = Sum.inr (Sum.inr x)) ->
          ∃ w : List In₁,
            w ≠ [] ∧
              branchNode branch (n + j) =
                branchNode branch n ++ senderRNode (A := A) w ∧
                tauNodeState (In₂ := In₂) (branchNode branch (n + j)) =
                  .inRight a w ∧
                  ∃ (c : CR.monitor.State)
                    (t : Finset (A.State × A.State)),
                    branchRun σ τ CL CR CC branch (n + j) =
                      Sum.inr (Sum.inr (Sum.inl (c, t))) := by
      intro j
      induction j with
      | zero => omega
      | succ j ih =>
          intro _ hjlt hdirsj
          rcases Nat.eq_zero_or_pos j with rfl | hj
          · refine ⟨[x₀], by simp, ?_, ?_, ?_⟩
            · rw [show branchNode branch (n + 1) =
                branchNode branch n ++ [branch n] from rfl, hbr0]
              rfl
            · rw [show branchNode branch (n + 1) =
                branchNode branch n ++ [branch n] from rfl, hbr0,
                tauNodeState_append, hpa]
              rfl
            · exact ⟨_, _, hstep1⟩
          · obtain ⟨w, hwne, hnode, hpar, c, t, hrunj⟩ :=
              ih (by omega) (by omega)
                (fun i h1 h2 => hdirsj i h1 (by omega))
            obtain ⟨x, hbr⟩ := hdirsj j (by omega) (by omega)
            have hstepj := branchRun_succ σ τ CL CR CC branch (n + j)
            rw [hrunj, hbr] at hstepj
            refine ⟨w ++ [x], by simp, ?_, ?_, ?_⟩
            · rw [show branchNode branch (n + (j + 1)) =
                branchNode branch (n + j) ++ [branch (n + j)] from rfl,
                hnode, hbr, senderRNode_append, List.append_assoc]
            · rw [show branchNode branch (n + (j + 1)) =
                branchNode branch (n + j) ++ [branch (n + j)] from rfl,
                tauNodeState_append, hpar, hbr]
              rfl
            · simp only [globalJournalStep] at hstepj
              exact ⟨_, _, by
                rw [show n + (j + 1) = n + j + 1 by omega]
                exact hstepj⟩
    have hn2 : n + 2 ≤ n' := by
      by_contra hcon
      have hn1 : n' = n + 1 := by omega
      rw [hn1, hstep1] at hrun'
      exact absurd hrun' (by simp)
    obtain ⟨j₀, ⟨⟨hj₀1, hj₀d⟩, hj₀not⟩, hj₀min⟩ :
        ∃ j₀,
          ((1 ≤ j₀ ∧ j₀ ≤ n' - n - 1) ∧
            ¬ ∃ x : In₁, branch (n + j₀) = Sum.inr (Sum.inr x)) ∧
            ∀ i, i < j₀ -> 1 ≤ i ->
              ∃ x : In₁, branch (n + i) = Sum.inr (Sum.inr x) := by
      have hexlast :
          ¬ ∃ x : In₁, branch (n + (n' - n - 1)) = Sum.inr (Sum.inr x) := by
        rintro ⟨x, hx⟩
        have hsucc := branchRun_succ σ τ CL CR CC branch (n + (n' - n - 1))
        rw [hx, show n + (n' - n - 1) + 1 = n' by omega, hrun']
          at hsucc
        exact
          globalJournalStep_inr_ne_inl CL CR CC _ _ (Sum.inr x) a'
            hsucc.symm
      have hex :
          ∃ j, (1 ≤ j ∧ j ≤ n' - n - 1) ∧
            ¬ ∃ x : In₁, branch (n + j) = Sum.inr (Sum.inr x) :=
        ⟨n' - n - 1, ⟨by omega, Nat.le_refl _⟩, hexlast⟩
      refine ⟨Nat.find hex, Nat.find_spec hex, ?_⟩
      intro i hi h1
      by_contra hcon
      have hspec := (Nat.find_spec hex).1.2
      exact absurd ⟨⟨h1, by omega⟩, hcon⟩ (Nat.find_min hex hi)
    obtain ⟨w, hwne, hnode, hpar, c, t, hrunL⟩ :=
      hblock j₀ hj₀1 (by omega) (fun i h1 h2 => hj₀min i h2 h1)
    have htreeL :
        tauTree σ τ (branchNode branch (n + j₀)) =
          tauLabelOf σ τ (.inRight a w) := by
      show tauLabelOf σ τ (tauNodeState _) = _
      rw [hpar]
    have hstepL := branchRun_succ σ τ CL CR CC branch (n + j₀)
    rw [hrunL, htreeL] at hstepL
    rcases hbrL : branch (n + j₀) with ac | x | x
    · -- atom close out of the block
      rw [hbrL] at hstepL
      simp only [globalJournalStep, tauLabelOf,
      GlobalJournalLabel.leftNarrowed, GlobalJournalLabel.leftClose,
      GlobalJournalLabel.leftRev, GlobalJournalLabel.rightNarrowed,
      GlobalJournalLabel.rightClose, GlobalJournalLabel.rightRev,
      GlobalJournalLabel.revLeft, GlobalJournalLabel.revRight] at hstepL
      have hj₀last : n + j₀ + 1 = n' := by
        by_contra hne
        by_cases hmem :
            ac ∈
              rightCloseSubset t (tauRightLabel σ τ a w)
                (tauRightClose σ τ a w)
        · rw [if_pos hmem] at hstepL
          exact hmid (n + j₀ + 1) (by omega) (by omega) ac hstepL
        · rw [if_neg hmem] at hstepL
          exact hns (n + j₀ + 1) hstepL
      rw [hj₀last, hrun'] at hstepL
      by_cases hmem :
          ac ∈
            rightCloseSubset t (tauRightLabel σ τ a w)
              (tauRightClose σ τ a w)
      · rw [if_pos hmem] at hstepL
        have hac : ac = a' := Sum.inl.inj hstepL.symm
        rw [hac] at hmem
        obtain ⟨base, move, hbase, hmove⟩ := mem_rightCloseSubset hmem
        rcases List.eq_nil_or_concat w with rfl | ⟨w', xl, hwc⟩
        · exact absurd rfl hwne
        · rw [List.concat_eq_append] at hwc
          subst hwc
          obtain ⟨ms, hsw, hctrl⟩ :=
            rightThread_trace σ τ CL CR CC (branchNode branch n) a hrun
              w' xl c t (by rw [← hnode]; exact hrunL) base hbase
          exact
            segmentRight_exists σ τ (branchNode branch n) a a' hpa
              (w' ++ [xl]) ms base move
              (by
                intro hmsnil
                rw [hmsnil] at hsw
                exact absurd hsw.symm (by simp [senderWord]))
              hsw hctrl hmove
      · rw [if_neg hmem] at hstepL
        exact absurd hstepL.symm (by simp)
    · -- direct reversal out of the right block
      rw [hbrL] at hstepL
      have hp1lt : n + j₀ + 1 < n' := by
        by_contra hcon
        have : n + j₀ + 1 = n' := by omega
        rw [this, hrun'] at hstepL
        exact
          absurd hstepL.symm
            (globalJournalStep_inr_ne_inl CL CR CC _ _ (Sum.inl x) a')
      have hp₁ :
          tauNodeState (In₂ := In₂) (branchNode branch (n + j₀ + 1)) =
            revParse (A := A)
              (Sum.inl ([x] : List In₂)) := by
        rw [show branchNode branch (n + j₀ + 1) =
          branchNode branch (n + j₀) ++ [branch (n + j₀)] from rfl,
          tauNodeState_append, hpar, hbrL]
        rfl
      have hrun₁ :
          branchRun σ τ CL CR CC branch (n + j₀ + 1) =
            revModeState CL CR CC (Sum.inl ([x] : List In₂))
              (CC.start
                (rightReverseSubset t (tauRightClose σ τ a w)
                  (tauRightRev σ τ a w) x))
              (rightReverseSubset t (tauRightClose σ τ a w)
                (tauRightRev σ τ a w) x) := by
        rw [hstepL]
        rfl
      obtain ⟨es, mc, qm₀, hqm₀, hclose⟩ :=
        hchainClose (n + j₀) (Sum.inl [x]) _ (by omega) hp1lt hp₁
          hrun₁
      obtain ⟨base, i1, hbase, hqm₀eq⟩ := mem_rightReverseSubset hqm₀
      rcases List.eq_nil_or_concat w with rfl | ⟨w', xl, hwc⟩
      · exact absurd rfl hwne
      · rw [List.concat_eq_append] at hwc
        subst hwc
        obtain ⟨ms, hsw, hctrl⟩ :=
          rightThread_trace σ τ CL CR CC (branchNode branch n) a hrun
            w' xl c t (by rw [← hnode]; exact hrunL) base hbase
        obtain ⟨E⟩ :=
          revEntryRight_exists σ τ (branchNode branch n) a hpa
            (w' ++ [xl]) ms base (x, i1)
            (by
              intro hmsnil
              rw [hmsnil] at hsw
              exact absurd hsw.symm (by simp [senderWord]))
            hsw hctrl
        refine
          segmentSpec_of_revEntry σ τ (by simp [chainWordNonempty]) E es mc
            a' ?_
        rw [hqm₀eq] at hclose
        exact hclose
    · exact absurd ⟨x, hbrL⟩ hj₀not

end Winner

end DetParityAutomaton

end DistributedSynthesis
