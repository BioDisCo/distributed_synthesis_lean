/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmTauTreeRealization
import DistributedSynthesis.Formalizations.Theorem.ThmGlobalTreeTracking

/-!
# The global journal automaton accepts the winner's tree

The subset-membership inversions of the automaton transitions and the
run/parse correspondence: along the deterministic run over the
winner's journal tree, a non-sink state matches the node's parse and
every realized atom or thread is reached by a consistent play of the
uniformization game.  Direct reversals are genuine transitions: the
handoff thread sets and the reversed-block thread sets are realized
at the reversed-block positions of the game.  This is the
reachability backbone for the parity regimes of the acceptance proof.
-/

set_option linter.unusedSectionVars false

namespace DistributedSynthesis

universe u v x y s

namespace DetParityAutomaton

open GlobalJournalLabel

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}

variable
  {A :
    DetParityAutomaton.{max u v x y, s}
      (RoundRecord In₁ In₂ Graph Out₁ Out₂)}

variable [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
variable [DecidableEq In₁] [DecidableEq In₂] [DecidableEq A.State]

/-! ### Subset-membership inversions -/

theorem mem_bothAtomSubset {atom atom' : A.State × A.State}
    {labelL : NarrowedBlockLabel In₁ In₂ Out₁ Out₂ (A.State × A.State)}
    {labelR : NarrowedBlockLabel In₂ In₁ Out₂ Out₁ (A.State × A.State)}
    (h : atom' ∈ bothAtomSubset atom labelL labelR) :
    ∃ move : In₁ × In₂,
      atom' = bothThreadAtom atom labelL labelR move.1 move.2 := by
  obtain ⟨move, -, hmove⟩ := Finset.mem_image.mp h
  exact ⟨move, hmove.symm⟩

theorem mem_leftOpenSubset {atom qm : A.State × A.State}
    {label : NarrowedBlockLabel In₁ In₂ Out₁ Out₂ (A.State × A.State)}
    {inputTwo : In₂} (h : qm ∈ leftOpenSubset atom label inputTwo) :
    ∃ inputOne : In₁,
      qm = leftThreadOpen atom label inputOne inputTwo := by
  obtain ⟨inputOne, -, hio⟩ := Finset.mem_image.mp h
  exact ⟨inputOne, hio.symm⟩

theorem mem_leftStepSubset {qm : A.State × A.State}
    {threads : Finset (A.State × A.State)}
    {label : NarrowedBlockLabel In₁ In₂ Out₁ Out₂ (A.State × A.State)}
    {inputTwo : In₂} (h : qm ∈ leftStepSubset threads label inputTwo) :
    ∃ (base : A.State × A.State) (inputOne : In₁),
      base ∈ threads ∧ qm = leftThreadStep base label inputOne inputTwo := by
  obtain ⟨base, hbase, hmem⟩ := Finset.mem_biUnion.mp h
  obtain ⟨inputOne, -, hio⟩ := Finset.mem_image.mp hmem
  exact ⟨base, inputOne, hbase, hio.symm⟩

theorem mem_leftCloseSubset {atom' : A.State × A.State}
    {threads : Finset (A.State × A.State)}
    {label : NarrowedBlockLabel In₁ In₂ Out₁ Out₂ (A.State × A.State)}
    {close : (A.State × A.State) -> In₁ × In₂ -> Out₂}
    (h : atom' ∈ leftCloseSubset threads label close) :
    ∃ (base : A.State × A.State) (move : In₁ × In₂),
      base ∈ threads ∧
        atom' = leftThreadClose base label close move.1 move.2 := by
  obtain ⟨base, hbase, hmem⟩ := Finset.mem_biUnion.mp h
  obtain ⟨move, -, hmove⟩ := Finset.mem_image.mp hmem
  exact ⟨base, move, hbase, hmove.symm⟩

theorem mem_rightOpenSubset {atom qm : A.State × A.State}
    {label : NarrowedBlockLabel In₂ In₁ Out₂ Out₁ (A.State × A.State)}
    {inputOne : In₁} (h : qm ∈ rightOpenSubset atom label inputOne) :
    ∃ inputTwo : In₂,
      qm = rightThreadOpen atom label inputTwo inputOne := by
  obtain ⟨inputTwo, -, hit⟩ := Finset.mem_image.mp h
  exact ⟨inputTwo, hit.symm⟩

theorem mem_rightStepSubset {qm : A.State × A.State}
    {threads : Finset (A.State × A.State)}
    {label : NarrowedBlockLabel In₂ In₁ Out₂ Out₁ (A.State × A.State)}
    {inputOne : In₁} (h : qm ∈ rightStepSubset threads label inputOne) :
    ∃ (base : A.State × A.State) (inputTwo : In₂),
      base ∈ threads ∧
        qm = rightThreadStep base label inputTwo inputOne := by
  obtain ⟨base, hbase, hmem⟩ := Finset.mem_biUnion.mp h
  obtain ⟨inputTwo, -, hit⟩ := Finset.mem_image.mp hmem
  exact ⟨base, inputTwo, hbase, hit.symm⟩

theorem mem_rightCloseSubset {atom' : A.State × A.State}
    {threads : Finset (A.State × A.State)}
    {label : NarrowedBlockLabel In₂ In₁ Out₂ Out₁ (A.State × A.State)}
    {close : (A.State × A.State) -> In₂ × In₁ -> Out₁}
    (h : atom' ∈ rightCloseSubset threads label close) :
    ∃ (base : A.State × A.State) (move : In₂ × In₁),
      base ∈ threads ∧
        atom' = rightThreadClose base label close move.1 move.2 := by
  obtain ⟨base, hbase, hmem⟩ := Finset.mem_biUnion.mp h
  obtain ⟨move, -, hmove⟩ := Finset.mem_image.mp hmem
  exact ⟨base, move, hbase, hmove.symm⟩

theorem mem_leftReverseSubset {qm : ChainThread A}
    {threads : Finset (A.State × A.State)}
    {close : (A.State × A.State) -> In₁ × In₂ -> Out₂}
    {rev : (A.State × A.State) -> In₁ -> Out₁}
    {inputOne : In₁}
    (h : qm ∈ leftReverseSubset threads close rev inputOne) :
    ∃ (base : A.State × A.State) (inputTwo : In₂),
      base ∈ threads ∧
        qm = leftThreadReverse base close rev inputOne inputTwo := by
  obtain ⟨base, hbase, hmem⟩ := Finset.mem_biUnion.mp h
  obtain ⟨inputTwo, -, hit⟩ := Finset.mem_image.mp hmem
  exact ⟨base, inputTwo, hbase, hit.symm⟩

theorem mem_rightReverseSubset {qm : ChainThread A}
    {threads : Finset (A.State × A.State)}
    {close : (A.State × A.State) -> In₂ × In₁ -> Out₁}
    {rev : (A.State × A.State) -> In₂ -> Out₂}
    {inputTwo : In₂}
    (h : qm ∈ rightReverseSubset threads close rev inputTwo) :
    ∃ (base : A.State × A.State) (inputOne : In₁),
      base ∈ threads ∧
        qm = rightThreadReverse base close rev inputTwo inputOne := by
  obtain ⟨base, hbase, hmem⟩ := Finset.mem_biUnion.mp h
  obtain ⟨inputOne, -, hit⟩ := Finset.mem_image.mp hmem
  exact ⟨base, inputOne, hbase, hit.symm⟩

theorem mem_revLeftStepSubset {qm : ChainThread A}
    {threads : Finset (ChainThread A)}
    {label :
      RevLeftBlockLabel (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁)
        (Out₂ := Out₂) (A.State × A.State)}
    {inputTwo : In₂}
    (h : qm ∈ revLeftStepSubset threads label inputTwo) :
    ∃ (base : ChainThread A) (inputOne : In₁),
      base ∈ threads ∧
        qm = revLeftThreadStep A base label inputOne inputTwo := by
  obtain ⟨base, hbase, hmem⟩ := Finset.mem_biUnion.mp h
  obtain ⟨inputOne, -, hio⟩ := Finset.mem_image.mp hmem
  exact ⟨base, inputOne, hbase, hio.symm⟩

theorem mem_revLeftCloseSubset {atom' : A.State × A.State}
    {threads : Finset (ChainThread A)}
    {label :
      RevLeftBlockLabel (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁)
        (Out₂ := Out₂) (A.State × A.State)}
    (h : atom' ∈ revLeftCloseSubset threads label) :
    ∃ (base : ChainThread A) (move : In₁ × In₂),
      base ∈ threads ∧
        atom' = revLeftThreadClose A base label move.1 move.2 := by
  obtain ⟨base, hbase, hmem⟩ := Finset.mem_biUnion.mp h
  obtain ⟨move, -, hmove⟩ := Finset.mem_image.mp hmem
  exact ⟨base, move, hbase, hmove.symm⟩

theorem mem_revLeftReverseSubset {qm : ChainThread A}
    {threads : Finset (ChainThread A)}
    {label :
      RevLeftBlockLabel (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁)
        (Out₂ := Out₂) (A.State × A.State)}
    {inputOne : In₁}
    (h : qm ∈ revLeftReverseSubset threads label inputOne) :
    ∃ (base : ChainThread A) (inputTwo : In₂),
      base ∈ threads ∧
        qm = revLeftThreadReverse A base label inputOne inputTwo := by
  obtain ⟨base, hbase, hmem⟩ := Finset.mem_biUnion.mp h
  obtain ⟨inputTwo, -, hit⟩ := Finset.mem_image.mp hmem
  exact ⟨base, inputTwo, hbase, hit.symm⟩

theorem mem_revRightStepSubset {qm : ChainThread A}
    {threads : Finset (ChainThread A)}
    {label :
      RevRightBlockLabel (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁)
        (Out₂ := Out₂) (A.State × A.State)}
    {inputOne : In₁}
    (h : qm ∈ revRightStepSubset threads label inputOne) :
    ∃ (base : ChainThread A) (inputTwo : In₂),
      base ∈ threads ∧
        qm = revRightThreadStep A base label inputOne inputTwo := by
  obtain ⟨base, hbase, hmem⟩ := Finset.mem_biUnion.mp h
  obtain ⟨inputTwo, -, hit⟩ := Finset.mem_image.mp hmem
  exact ⟨base, inputTwo, hbase, hit.symm⟩

theorem mem_revRightCloseSubset {atom' : A.State × A.State}
    {threads : Finset (ChainThread A)}
    {label :
      RevRightBlockLabel (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁)
        (Out₂ := Out₂) (A.State × A.State)}
    (h : atom' ∈ revRightCloseSubset threads label) :
    ∃ (base : ChainThread A) (move : In₁ × In₂),
      base ∈ threads ∧
        atom' = revRightThreadClose A base label move.1 move.2 := by
  obtain ⟨base, hbase, hmem⟩ := Finset.mem_biUnion.mp h
  obtain ⟨move, -, hmove⟩ := Finset.mem_image.mp hmem
  exact ⟨base, move, hbase, hmove.symm⟩

theorem mem_revRightReverseSubset {qm : ChainThread A}
    {threads : Finset (ChainThread A)}
    {label :
      RevRightBlockLabel (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁)
        (Out₂ := Out₂) (A.State × A.State)}
    {inputTwo : In₂}
    (h : qm ∈ revRightReverseSubset threads label inputTwo) :
    ∃ (base : ChainThread A) (inputOne : In₁),
      base ∈ threads ∧
        qm = revRightThreadReverse A base label inputOne inputTwo := by
  obtain ⟨base, hbase, hmem⟩ := Finset.mem_biUnion.mp h
  obtain ⟨inputOne, -, hio⟩ := Finset.mem_image.mp hmem
  exact ⟨base, inputOne, hbase, hio.symm⟩

/-! ### The run/parse correspondence -/

variable [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]
variable [Countable In₁] [Countable In₂] [Countable Out₁] [Countable Out₂]

variable (σ : StrategyPair In₁ In₂ Out₁ Out₂)
variable
  (τ :
    (uniformizationGame A σ).PositionalStrategy ParityPlayer.even)
variable (CL : LeftThreadChecker (In₁ := In₁) A)
variable (CR : RightThreadChecker (In₁ := In₁) A)
variable (CC : ChainThreadChecker (In₁ := In₁) (A := A))

/--
Along the deterministic run over the winner's journal tree, every node
is either sink, or matches its parse with every realized atom and
thread reachable by a consistent play of the uniformization game;
reversed-block threads are realized at the reversed-block positions.
-/
theorem runGood
    (node : TreeNode (GlobalJournalBranch (In₁ := In₁) A)) :
    globalRunIn CL CR CC (tauTree σ τ)
        (Sum.inl (A.initial, A.initial)) node =
      Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr PUnit.unit)))) ∨
    (∃ atom : A.State × A.State,
      tauNodeState (In₂ := In₂) node = .atNode atom ∧
        globalRunIn CL CR CC (tauTree σ τ)
            (Sum.inl (A.initial, A.initial)) node = Sum.inl atom ∧
          Reaches σ τ (.bnd atom)) ∨
    (∃ (atom : A.State × A.State) (word : List In₂)
        (checker : CL.monitor.State)
        (threads : Finset (A.State × A.State)),
      tauNodeState (In₂ := In₂) node = .inLeft atom word ∧
        globalRunIn CL CR CC (tauTree σ τ)
            (Sum.inl (A.initial, A.initial)) node =
          Sum.inr (Sum.inl (checker, threads)) ∧
          ∀ qm ∈ threads,
            Reaches σ τ
              (.blockL (commitmentOf σ τ atom) word qm.1 qm.2)) ∨
    (∃ (atom : A.State × A.State) (word : List In₁)
        (checker : CR.monitor.State)
        (threads : Finset (A.State × A.State)),
      tauNodeState (In₂ := In₂) node = .inRight atom word ∧
        globalRunIn CL CR CC (tauTree σ τ)
            (Sum.inl (A.initial, A.initial)) node =
          Sum.inr (Sum.inr (Sum.inl (checker, threads))) ∧
          ∀ qm ∈ threads,
            Reaches σ τ
              (.blockR (commitmentOf σ τ atom) word qm.1 qm.2)) ∨
    (∃ (word : List In₂) (checker : CC.monitor.State)
        (threads : Finset (ChainThread A)),
      tauNodeState (In₂ := In₂) node = .inRevLeft word ∧
        globalRunIn CL CR CC (tauTree σ τ)
            (Sum.inl (A.initial, A.initial)) node =
          Sum.inr (Sum.inr (Sum.inr (Sum.inl (checker, threads)))) ∧
          word ≠ [] ∧
          ∀ qm ∈ threads,
            Reaches σ τ
              (.revBlockL
                (commitmentRevL σ τ [word.headD default] qm.1.1 qm.1.2)
                word qm.1.1 qm.1.2 qm.2.1 qm.2.2)) ∨
    (∃ (word : List In₁) (checker : CC.monitor.State)
        (threads : Finset (ChainThread A)),
      tauNodeState (In₂ := In₂) node = .inRevRight word ∧
        globalRunIn CL CR CC (tauTree σ τ)
            (Sum.inl (A.initial, A.initial)) node =
          Sum.inr
            (Sum.inr (Sum.inr (Sum.inr (Sum.inl (checker, threads))))) ∧
          word ≠ [] ∧
          ∀ qm ∈ threads,
            Reaches σ τ
              (.revBlockR
                (commitmentRevR σ τ [word.headD default] qm.1.1 qm.1.2)
                word qm.1.1 qm.1.2 qm.2.1 qm.2.2)) := by
  induction node using List.reverseRecOn with
  | nil =>
      exact
        Or.inr (Or.inl
          ⟨(A.initial, A.initial), rfl, rfl, reaches_initial σ τ⟩)
  | append_singleton node branch ih =>
      have hrapp :=
        globalRunIn_append CL CR CC (tauTree σ τ)
          (Sum.inl (A.initial, A.initial)) node branch
      have hpapp := tauNodeState_append (In₂ := In₂) node branch
      rcases ih with hsink | ⟨atom, hpar, hrun, hreach⟩ |
        ⟨atom, word, checker, threads, hpar, hrun, hreach⟩ |
        ⟨atom, word, checker, threads, hpar, hrun, hreach⟩ |
        ⟨word, checker, threads, hpar, hrun, hne, hreach⟩ |
        ⟨word, checker, threads, hpar, hrun, hne, hreach⟩
      · -- sink absorbs
        refine Or.inl ?_
        rw [hrapp, hsink]
        simp only [globalJournalStep]
      · -- at an atom node
        have htree :
            tauTree σ τ node = tauLabelOf σ τ (.atNode atom) := by
          show tauLabelOf σ τ (tauNodeState node) = _
          rw [hpar]
        rcases branch with atom' | inputTwo | inputOne
        · -- synchronizing round
          by_cases hmem :
              atom' ∈
                bothAtomSubset atom (tauOpeningLeftLabel σ τ atom)
                  (tauOpeningRightLabel σ τ atom)
          · refine Or.inr (Or.inl ⟨atom', ?_, ?_, ?_⟩)
            · simp only [hpapp, tauNodeStep]
            · rw [hrapp, hrun, htree]
              show
                globalJournalStep A CL CR CC (Sum.inl atom)
                    (tauLabelOf σ τ (.atNode atom)) (Sum.inl atom') =
                  Sum.inl atom'
              simp only [globalJournalStep, tauLabelOf, leftNarrowed,
                rightNarrowed]
              rw [if_pos hmem]
            · obtain ⟨move, hmove⟩ := mem_bothAtomSubset hmem
              rw [hmove]
              exact reaches_both_target σ τ atom move hreach
          · refine Or.inl ?_
            rw [hrapp, hrun, htree]
            show
              globalJournalStep A CL CR CC (Sum.inl atom)
                  (tauLabelOf σ τ (.atNode atom)) (Sum.inl atom') =
                Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr PUnit.unit))))
            simp only [globalJournalStep, tauLabelOf, leftNarrowed,
              rightNarrowed]
            rw [if_neg hmem]
        · -- left-block opening
          refine Or.inr (Or.inr (Or.inl
            ⟨atom, [inputTwo],
              CL.monitor.step (CL.start atom.1)
                (tauOpeningLeftLabel σ τ atom) inputTwo,
              leftOpenSubset atom (tauOpeningLeftLabel σ τ atom) inputTwo,
              ?_, ?_, ?_⟩))
          · simp only [hpapp, hpar, tauNodeStep]
          · rw [hrapp, hrun, htree]
            simp only [globalJournalStep, tauLabelOf, leftNarrowed]
          · intro qm hqm
            obtain ⟨inputOne, hqm'⟩ := mem_leftOpenSubset hqm
            rw [hqm']
            exact reaches_open_left σ τ atom (inputOne, inputTwo) hreach
        · -- right-block opening
          refine Or.inr (Or.inr (Or.inr (Or.inl
            ⟨atom, [inputOne],
              CR.monitor.step (CR.start atom.1)
                (tauOpeningRightLabel σ τ atom) inputOne,
              rightOpenSubset atom (tauOpeningRightLabel σ τ atom)
                inputOne,
              ?_, ?_, ?_⟩)))
          · simp only [hpapp, hpar, tauNodeStep]
          · rw [hrapp, hrun, htree]
            simp only [globalJournalStep, tauLabelOf, rightNarrowed]
          · intro qm hqm
            obtain ⟨inputTwo, hqm'⟩ := mem_rightOpenSubset hqm
            rw [hqm']
            exact
              reaches_open_right σ τ atom (inputOne, inputTwo) hreach
      · -- inside a left block
        have htree :
            tauTree σ τ node = tauLabelOf σ τ (.inLeft atom word) := by
          show tauLabelOf σ τ (tauNodeState node) = _
          rw [hpar]
        rcases branch with atom' | inputTwo | inputOne
        · -- closing round
          by_cases hmem :
              atom' ∈
                leftCloseSubset threads (tauLeftLabel σ τ atom word)
                  (tauLeftClose σ τ atom word)
          · refine Or.inr (Or.inl ⟨atom', ?_, ?_, ?_⟩)
            · simp only [hpapp, tauNodeStep]
            · rw [hrapp, hrun, htree]
              show
                globalJournalStep A CL CR CC
                    (Sum.inr (Sum.inl (checker, threads)))
                    (tauLabelOf σ τ (.inLeft atom word)) (Sum.inl atom') =
                  Sum.inl atom'
              simp only [globalJournalStep, tauLabelOf, leftNarrowed,
                leftClose]
              rw [if_pos hmem]
            · obtain ⟨base, move, hbase, hmove⟩ := mem_leftCloseSubset hmem
              rw [hmove]
              exact
                reaches_close_left σ τ atom word base.1 base.2 move
                  (hreach base hbase)
          · refine Or.inl ?_
            rw [hrapp, hrun, htree]
            show
              globalJournalStep A CL CR CC
                  (Sum.inr (Sum.inl (checker, threads)))
                  (tauLabelOf σ τ (.inLeft atom word)) (Sum.inl atom') =
                Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr PUnit.unit))))
            simp only [globalJournalStep, tauLabelOf, leftNarrowed,
              leftClose]
            rw [if_neg hmem]
        · -- continuation round
          refine Or.inr (Or.inr (Or.inl
            ⟨atom, word ++ [inputTwo],
              CL.monitor.step checker (tauLeftLabel σ τ atom word)
                inputTwo,
              leftStepSubset threads (tauLeftLabel σ τ atom word)
                inputTwo,
              ?_, ?_, ?_⟩))
          · simp only [hpapp, hpar, tauNodeStep]
          · rw [hrapp, hrun, htree]
            simp only [globalJournalStep, tauLabelOf, leftNarrowed]
          · intro qm hqm
            obtain ⟨base, inputOne, hbase, hqm'⟩ :=
              mem_leftStepSubset hqm
            rw [hqm']
            exact
              reaches_continue_left σ τ atom word base.1 base.2
                (inputOne, inputTwo) (hreach base hbase)
        · -- direct reversal into a reversed right block
          refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
            ⟨[inputOne],
              CC.start
                (leftReverseSubset threads (tauLeftClose σ τ atom word)
                  (tauLeftRev σ τ atom word) inputOne),
              leftReverseSubset threads (tauLeftClose σ τ atom word)
                (tauLeftRev σ τ atom word) inputOne,
              ?_, ?_, by simp, ?_⟩))))
          · simp only [hpapp, hpar, tauNodeStep]
          · rw [hrapp, hrun, htree]
            simp only [globalJournalStep, tauLabelOf, leftClose,
              leftRev]
          · intro qm hqm
            obtain ⟨base, inputTwo, hbase, hqm'⟩ :=
              mem_leftReverseSubset hqm
            rw [hqm']
            exact
              reaches_revBlockR σ τ [inputOne]
                (leftThreadReverse base (tauLeftClose σ τ atom word)
                    (tauLeftRev σ τ atom word) inputOne
                    inputTwo).1.1
                (leftThreadReverse base (tauLeftClose σ τ atom word)
                    (tauLeftRev σ τ atom word) inputOne
                    inputTwo).1.2
                (reaches_reverse_right σ τ atom word base.1 base.2
                  (inputOne, inputTwo) (hreach base hbase))
      · -- inside a right block
        have htree :
            tauTree σ τ node = tauLabelOf σ τ (.inRight atom word) := by
          show tauLabelOf σ τ (tauNodeState node) = _
          rw [hpar]
        rcases branch with atom' | inputTwo | inputOne
        · -- closing round
          by_cases hmem :
              atom' ∈
                rightCloseSubset threads (tauRightLabel σ τ atom word)
                  (tauRightClose σ τ atom word)
          · refine Or.inr (Or.inl ⟨atom', ?_, ?_, ?_⟩)
            · simp only [hpapp, tauNodeStep]
            · rw [hrapp, hrun, htree]
              show
                globalJournalStep A CL CR CC
                    (Sum.inr (Sum.inr (Sum.inl (checker, threads))))
                    (tauLabelOf σ τ (.inRight atom word))
                    (Sum.inl atom') =
                  Sum.inl atom'
              simp only [globalJournalStep, tauLabelOf, rightNarrowed,
                rightClose]
              rw [if_pos hmem]
            · obtain ⟨base, move, hbase, hmove⟩ :=
                mem_rightCloseSubset hmem
              rw [hmove]
              exact
                reaches_close_right σ τ atom word base.1 base.2
                  (move.2, move.1) (hreach base hbase)
          · refine Or.inl ?_
            rw [hrapp, hrun, htree]
            show
              globalJournalStep A CL CR CC
                  (Sum.inr (Sum.inr (Sum.inl (checker, threads))))
                  (tauLabelOf σ τ (.inRight atom word)) (Sum.inl atom') =
                Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr PUnit.unit))))
            simp only [globalJournalStep, tauLabelOf, rightNarrowed,
              rightClose]
            rw [if_neg hmem]
        · -- direct reversal into a reversed left block
          refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
            ⟨[inputTwo],
              CC.start
                (rightReverseSubset threads
                  (tauRightClose σ τ atom word)
                  (tauRightRev σ τ atom word) inputTwo),
              rightReverseSubset threads (tauRightClose σ τ atom word)
                (tauRightRev σ τ atom word) inputTwo,
              ?_, ?_, by simp, ?_⟩))))
          · simp only [hpapp, hpar, tauNodeStep]
          · rw [hrapp, hrun, htree]
            simp only [globalJournalStep, tauLabelOf, rightClose,
              rightRev]
          · intro qm hqm
            obtain ⟨base, inputOne, hbase, hqm'⟩ :=
              mem_rightReverseSubset hqm
            rw [hqm']
            exact
              reaches_revBlockL σ τ [inputTwo]
                (rightThreadReverse base (tauRightClose σ τ atom word)
                    (tauRightRev σ τ atom word) inputTwo
                    inputOne).1.1
                (rightThreadReverse base (tauRightClose σ τ atom word)
                    (tauRightRev σ τ atom word) inputTwo
                    inputOne).1.2
                (reaches_reverse_left σ τ atom word base.1 base.2
                  (inputOne, inputTwo) (hreach base hbase))
        · -- continuation round
          refine Or.inr (Or.inr (Or.inr (Or.inl
            ⟨atom, word ++ [inputOne],
              CR.monitor.step checker (tauRightLabel σ τ atom word)
                inputOne,
              rightStepSubset threads (tauRightLabel σ τ atom word)
                inputOne,
              ?_, ?_, ?_⟩)))
          · simp only [hpapp, hpar, tauNodeStep]
          · rw [hrapp, hrun, htree]
            simp only [globalJournalStep, tauLabelOf, rightNarrowed]
          · intro qm hqm
            obtain ⟨base, inputTwo, hbase, hqm'⟩ :=
              mem_rightStepSubset hqm
            rw [hqm']
            exact
              reaches_continue_right σ τ atom word base.1 base.2
                (inputOne, inputTwo) (hreach base hbase)
      · -- inside a reversed left block
        have htree :
            tauTree σ τ node = tauLabelOf σ τ (.inRevLeft word) := by
          show tauLabelOf σ τ (tauNodeState node) = _
          rw [hpar]
        have hhead : ∀ b : In₂,
            (word ++ [b]).headD default = word.headD default := by
          obtain ⟨a, t, rfl⟩ := List.exists_cons_of_ne_nil hne
          intro _; rfl
        rcases branch with atom' | inputTwo | inputOne
        · -- closing round
          by_cases hmem :
              atom' ∈
                revLeftCloseSubset threads (tauRevLeftLabel σ τ word)
          · refine Or.inr (Or.inl ⟨atom', ?_, ?_, ?_⟩)
            · simp only [hpapp, tauNodeStep]
            · rw [hrapp, hrun, htree]
              show
                globalJournalStep A CL CR CC
                    (Sum.inr (Sum.inr (Sum.inr (Sum.inl
                      (checker, threads)))))
                    (tauLabelOf σ τ (.inRevLeft word)) (Sum.inl atom') =
                  Sum.inl atom'
              simp only [globalJournalStep, tauLabelOf, revLeft]
              rw [if_pos hmem]
            · obtain ⟨base, move, hbase, hmove⟩ :=
                mem_revLeftCloseSubset hmem
              rw [hmove]
              exact
                reaches_revClose_left σ τ
                  (commitmentRevL σ τ [word.headD default] base.1.1
                    base.1.2)
                  word base.1.1 base.1.2 base.2.1 base.2.2 move
                  (hreach base hbase)
          · refine Or.inl ?_
            rw [hrapp, hrun, htree]
            show
              globalJournalStep A CL CR CC
                  (Sum.inr (Sum.inr (Sum.inr (Sum.inl
                    (checker, threads)))))
                  (tauLabelOf σ τ (.inRevLeft word)) (Sum.inl atom') =
                Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr PUnit.unit))))
            simp only [globalJournalStep, tauLabelOf, revLeft]
            rw [if_neg hmem]
        · -- continuation round
          refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
            ⟨word ++ [inputTwo],
              CC.monitor.step checker (Sum.inl (tauRevLeftLabel σ τ word))
                (Sum.inl inputTwo),
              revLeftStepSubset threads (tauRevLeftLabel σ τ word)
                inputTwo,
              ?_, ?_, by simp, ?_⟩))))
          · simp only [hpapp, hpar, tauNodeStep]
          · rw [hrapp, hrun, htree]
            simp only [globalJournalStep, tauLabelOf, revLeft]
          · intro qm hqm
            obtain ⟨base, inputOne, hbase, hqm'⟩ :=
              mem_revLeftStepSubset hqm
            rw [hqm', hhead]
            exact
              reaches_revContinue_left σ τ
                (commitmentRevL σ τ [word.headD default] base.1.1
                  base.1.2)
                word base.1.1 base.1.2 base.2.1 base.2.2
                (inputOne, inputTwo) (hreach base hbase)
        · -- reversing again into a reversed right block
          refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
            ⟨[inputOne],
              CC.monitor.step checker (Sum.inl (tauRevLeftLabel σ τ word))
                (Sum.inr inputOne),
              revLeftReverseSubset threads (tauRevLeftLabel σ τ word)
                inputOne,
              ?_, ?_, by simp, ?_⟩))))
          · simp only [hpapp, hpar, tauNodeStep]
          · rw [hrapp, hrun, htree]
            simp only [globalJournalStep, tauLabelOf, revLeft]
          · intro qm hqm
            obtain ⟨base, inputTwo, hbase, hqm'⟩ :=
              mem_revLeftReverseSubset hqm
            rw [hqm']
            exact
              reaches_revBlockR σ τ [inputOne]
                (revLeftThreadReverse A base (tauRevLeftLabel σ τ word)
                    inputOne inputTwo).1.1
                (revLeftThreadReverse A base (tauRevLeftLabel σ τ word)
                    inputOne inputTwo).1.2
                (reaches_revReverse_right σ τ
                  (commitmentRevL σ τ [word.headD default] base.1.1
                    base.1.2)
                  word base.1.1 base.1.2 base.2.1 base.2.2
                  (inputOne, inputTwo) (hreach base hbase))
      · -- inside a reversed right block
        have htree :
            tauTree σ τ node = tauLabelOf σ τ (.inRevRight word) := by
          show tauLabelOf σ τ (tauNodeState node) = _
          rw [hpar]
        have hhead : ∀ b : In₁,
            (word ++ [b]).headD default = word.headD default := by
          obtain ⟨a, t, rfl⟩ := List.exists_cons_of_ne_nil hne
          intro _; rfl
        rcases branch with atom' | inputTwo | inputOne
        · -- closing round
          by_cases hmem :
              atom' ∈
                revRightCloseSubset threads (tauRevRightLabel σ τ word)
          · refine Or.inr (Or.inl ⟨atom', ?_, ?_, ?_⟩)
            · simp only [hpapp, tauNodeStep]
            · rw [hrapp, hrun, htree]
              show
                globalJournalStep A CL CR CC
                    (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl
                      (checker, threads))))))
                    (tauLabelOf σ τ (.inRevRight word)) (Sum.inl atom') =
                  Sum.inl atom'
              simp only [globalJournalStep, tauLabelOf, revRight]
              rw [if_pos hmem]
            · obtain ⟨base, move, hbase, hmove⟩ :=
                mem_revRightCloseSubset hmem
              rw [hmove]
              exact
                reaches_revClose_right σ τ
                  (commitmentRevR σ τ [word.headD default] base.1.1
                    base.1.2)
                  word base.1.1 base.1.2 base.2.1 base.2.2 move
                  (hreach base hbase)
          · refine Or.inl ?_
            rw [hrapp, hrun, htree]
            show
              globalJournalStep A CL CR CC
                  (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl
                    (checker, threads))))))
                  (tauLabelOf σ τ (.inRevRight word)) (Sum.inl atom') =
                Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr PUnit.unit))))
            simp only [globalJournalStep, tauLabelOf, revRight]
            rw [if_neg hmem]
        · -- reversing again into a reversed left block
          refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
            ⟨[inputTwo],
              CC.monitor.step checker (Sum.inr (tauRevRightLabel σ τ word))
                (Sum.inl inputTwo),
              revRightReverseSubset threads (tauRevRightLabel σ τ word)
                inputTwo,
              ?_, ?_, by simp, ?_⟩))))
          · simp only [hpapp, hpar, tauNodeStep]
          · rw [hrapp, hrun, htree]
            simp only [globalJournalStep, tauLabelOf, revRight]
          · intro qm hqm
            obtain ⟨base, inputOne, hbase, hqm'⟩ :=
              mem_revRightReverseSubset hqm
            rw [hqm']
            exact
              reaches_revBlockL σ τ [inputTwo]
                (revRightThreadReverse A base (tauRevRightLabel σ τ word)
                    inputOne inputTwo).1.1
                (revRightThreadReverse A base (tauRevRightLabel σ τ word)
                    inputOne inputTwo).1.2
                (reaches_revReverse_left σ τ
                  (commitmentRevR σ τ [word.headD default] base.1.1
                    base.1.2)
                  word base.1.1 base.1.2 base.2.1 base.2.2
                  (inputOne, inputTwo) (hreach base hbase))
        · -- continuation round
          refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
            ⟨word ++ [inputOne],
              CC.monitor.step checker (Sum.inr (tauRevRightLabel σ τ word))
                (Sum.inr inputOne),
              revRightStepSubset threads (tauRevRightLabel σ τ word)
                inputOne,
              ?_, ?_, by simp, ?_⟩))))
          · simp only [hpapp, hpar, tauNodeStep]
          · rw [hrapp, hrun, htree]
            simp only [globalJournalStep, tauLabelOf, revRight]
          · intro qm hqm
            obtain ⟨base, inputTwo, hbase, hqm'⟩ :=
              mem_revRightStepSubset hqm
            rw [hqm', hhead]
            exact
              reaches_revContinue_right σ τ
                (commitmentRevR σ τ [word.headD default] base.1.1
                  base.1.2)
                word base.1.1 base.1.2 base.2.1 base.2.2
                (inputOne, inputTwo) (hreach base hbase)

/-! ### The sink regime and the reduction to never-sink branches -/

/-- An eventually-constant priority sequence with an even value is
min-even. -/
theorem natSeqMinEvenParity_of_eventually_const {s : Nat -> Nat}
    {c N : Nat} (hconst : ∀ n, N ≤ n -> s n = c)
    (hc : NatEven c) : NatSeqMinEvenParity s := by
  refine ⟨c, hc, ?_, ?_⟩
  · intro n
    exact ⟨max n N, le_max_left _ _, hconst _ (le_max_right _ _)⟩
  · intro q hq
    obtain ⟨k, hk, hsk⟩ := hq N
    rw [hconst k hk] at hsk
    omega

/-- Once the run sinks it stays sunk. -/
theorem runSink_absorb
    (node : TreeNode (GlobalJournalBranch (In₁ := In₁) A))
    (b : GlobalJournalBranch (In₁ := In₁) A)
    (h :
      globalRunIn CL CR CC (tauTree σ τ)
          (Sum.inl (A.initial, A.initial)) node =
        Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr PUnit.unit))))) :
    globalRunIn CL CR CC (tauTree σ τ)
        (Sum.inl (A.initial, A.initial)) (node ++ [b]) =
      Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr PUnit.unit)))) := by
  rw [globalRunIn_append, h, globalJournalStep_sink]

/-- The sink persists along a branch. -/
theorem runSink_branch
    (branch : Nat -> GlobalJournalBranch (In₁ := In₁) A)
    {n m : Nat} (hnm : n ≤ m)
    (h :
      globalRunIn CL CR CC (tauTree σ τ)
          (Sum.inl (A.initial, A.initial)) (branchNode branch n) =
        Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr PUnit.unit))))) :
    globalRunIn CL CR CC (tauTree σ τ)
        (Sum.inl (A.initial, A.initial)) (branchNode branch m) =
      Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr PUnit.unit)))) := by
  induction m, hnm using Nat.le_induction with
  | base => exact h
  | succ m _ ih =>
      exact
        runSink_absorb σ τ CL CR CC (branchNode branch m)
          (branch m) ih

/-- A branch whose run sinks has min-even priorities. -/
theorem branch_min_even_of_sinks
    (branch : Nat -> GlobalJournalBranch (In₁ := In₁) A)
    (N : Nat)
    (h :
      globalRunIn CL CR CC (tauTree σ τ)
          (Sum.inl (A.initial, A.initial)) (branchNode branch N) =
        Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr PUnit.unit))))) :
    NatSeqMinEvenParity
      (fun n =>
        globalJournalPriority A CL CR CC
          (globalRunIn CL CR CC (tauTree σ τ)
            (Sum.inl (A.initial, A.initial)) (branchNode branch n))) := by
  refine
    natSeqMinEvenParity_of_eventually_const
      (c := globalShift (In₁ := In₁) A) (N := N) ?_ (globalShift_even A)
  intro n hn
  rw [runSink_branch σ τ CL CR CC branch hn h]
  rfl

/-- The deterministic fold is a run of the automaton. -/
theorem tauTree_isRun :
    (globalJournalAutomaton A CL CR CC).IsRun (tauTree σ τ)
      (globalRunIn CL CR CC (tauTree σ τ)
        (Sum.inl (A.initial, A.initial))) := by
  refine ⟨rfl, fun node => ?_⟩
  intro b
  exact
    globalRunIn_append CL CR CC (tauTree σ τ)
      (Sum.inl (A.initial, A.initial)) node b

/--
The global journal automaton accepts the winner's tree, provided every
never-sinking branch has min-even run priorities.  This reduces the
acceptance to the parity regimes over realized branches.
-/
theorem tauTree_acceptsTree_of_neverSink
    (hns :
      ∀ branch : Nat -> GlobalJournalBranch (In₁ := In₁) A,
        (∀ n : Nat,
          globalRunIn CL CR CC (tauTree σ τ)
              (Sum.inl (A.initial, A.initial)) (branchNode branch n) ≠
            Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr PUnit.unit))))) ->
          NatSeqMinEvenParity
            (fun n =>
              globalJournalPriority A CL CR CC
                (globalRunIn CL CR CC (tauTree σ τ)
                  (Sum.inl (A.initial, A.initial))
                  (branchNode branch n)))) :
    (globalJournalAutomaton A CL CR CC).acceptsTree (tauTree σ τ) := by
  refine
    ⟨globalRunIn CL CR CC (tauTree σ τ)
        (Sum.inl (A.initial, A.initial)),
      tauTree_isRun σ τ CL CR CC, fun branch => ?_⟩
  by_cases hsink :
      ∃ N : Nat,
        globalRunIn CL CR CC (tauTree σ τ)
            (Sum.inl (A.initial, A.initial)) (branchNode branch N) =
          Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr PUnit.unit))))
  · obtain ⟨N, hN⟩ := hsink
    exact branch_min_even_of_sinks σ τ CL CR CC branch N hN
  · exact hns branch (not_exists.mp hsink)

end DetParityAutomaton

end DistributedSynthesis
