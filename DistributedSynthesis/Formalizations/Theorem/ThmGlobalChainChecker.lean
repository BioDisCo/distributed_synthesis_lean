/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmRevJournalChecker
import DistributedSynthesis.Formalizations.Theorem.ThmTauTreeChainSegment

/-!
# The set-started chain checker

The chain checker instantiation (the last checker instance of the
journal automaton).  The universal composed-thread condition over a
handoff thread SET reduces to an ordinary single-monitor universal
thread condition by making the start choice part of the thread
nondeterminism: a guarded pre-start state consumes a guessed start
thread carried in the receiver-input slot at the first round; guesses
outside the set die into an absorbing even sink, so exactly the
composed threads from the set (and vacuous dead threads) appear.  The
generic narrowed-thread determinization then yields a deterministic
per-set checker monitor, and the disjoint union over handoff sets is
the `ChainThreadChecker` instance.
-/

set_option linter.unusedSectionVars false

-- The chain-label alphabet is a sum of four-tuples of function types over
-- product domains; its `Fintype` synthesis exceeds the default search size.
set_option synthInstance.maxSize 512

namespace DistributedSynthesis

universe u v x y s

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}

namespace DetParityAutomaton

variable
  (A :
    DetParityAutomaton.{max u v x y, s}
      (RoundRecord In₁ In₂ Graph Out₁ Out₂))

variable [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
variable [DecidableEq In₁] [DecidableEq In₂] [DecidableEq A.State]

/-- The composed-thread step on a realized guessed round: the
direction sorts the round type, and the packed mode bit (left- versus
right-mode block) decides whether the entry thread is kept (a
continuation) or doubled (a re-reversal). -/
def chainGuessStep (th : ChainThread A)
    (round :
      RealizedBlockRound ((In₁ × In₂) × (ChainThread A))
        (In₂ ⊕ In₁) ((Out₁ × Out₁ × Out₂ × Out₂) × Bool) PUnit) :
    ChainThread A :=
  match round.1.2 with
  | Sum.inl inputTwo =>
      let next :=
        A.step th.2.1
          (leftRoundRecord (round.1.1.1.1, inputTwo)
            round.2.1.1.1 round.2.1.1.2.2.1)
      let m := A.minPriorityState th.2.2 next
      if round.2.1.2 then (th.1, next, m) else ((next, m), next, m)
  | Sum.inr inputOne =>
      let next :=
        A.step th.2.1
          (rightRoundRecord (round.1.1.1.2, inputOne)
            round.2.1.1.2.1 round.2.1.1.2.2.2)
      let m := A.minPriorityState th.2.2 next
      if round.2.1.2 then ((next, m), next, m) else (th.1, next, m)

/--
The set-started chain monitor: `none` is the pre-start state, the
first round starts the composed thread at the guessed handoff thread
carried in the receiver input (guesses outside the set die into the
absorbing even sink `some none`), and active threads step as composed
chain threads.
-/
def chainSetMonitor (T : Finset (ChainThread A)) :
    BlockRecordMonitor.{max u v s, max u v, max x y, y, s}
      ((In₁ × In₂) × (ChainThread A)) (In₂ ⊕ In₁)
      ((Out₁ × Out₁ × Out₂ × Out₂) × Bool) PUnit where
  State := Option (Option (ChainThread A))
  stateFinite := inferInstance
  initial := none
  step := fun st round =>
    match st with
    | some none => some none
    | some (some th) => some (some (chainGuessStep A th round))
    | none =>
        if round.1.1.2 ∈ T then
          some (some (chainGuessStep A round.1.1.2 round))
        else some none
  priority := fun st =>
    match st with
    | some (some th) => A.priority th.2.1
    | _ => 0

variable {A}

/-- The realized outputs of a chain label at a composed thread and
move, tagged with the mode bit (`true` for a reversed-left-mode
block): process one's receive and no-receive responses and process
two's no-receive and receive responses. -/
def chainLabelOutputs
    (label : ChainLabel In₁ In₂ Out₁ Out₂ (A.State × A.State))
    (th : ChainThread A) (move : In₁ × In₂) :
    (Out₁ × Out₁ × Out₂ × Out₂) × Bool :=
  match label with
  | Sum.inl labL =>
      ((labL.oneRecv th move, labL.oneSend th move.1,
          labL.twoSend th.1 move.2, labL.twoRecv th move), true)
  | Sum.inr labR =>
      ((labR.oneRecv th move, labR.oneSend th.1 move.1,
          labR.twoSend th move.2, labR.twoRecv th move), false)

/-- Pack a chain label for the set monitor: the receiver values are
looked up at the active thread, or at the guessed start at the
pre-start state. -/
def packChainSetLabel
    (label : ChainLabel In₁ In₂ Out₁ Out₂ (A.State × A.State))
    [Inhabited Out₁] [Inhabited Out₂] :
    NarrowedBlockLabel ((In₁ × In₂) × (ChainThread A)) (In₂ ⊕ In₁)
      ((Out₁ × Out₁ × Out₂ × Out₂) × Bool) PUnit
      (Option (Option (ChainThread A))) :=
  (fun _ => PUnit.unit,
    fun st move =>
      match st with
      | none =>
          chainLabelOutputs label move.1.2
            (composedChainMove (move.1.1, move.2))
      | some none => default
      | some (some th) =>
          chainLabelOutputs label th
            (composedChainMove (move.1.1, move.2)))

variable [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]

/-! ### Step laws of the packed set monitor -/

theorem chainSetMonitor_step_active
    (T : Finset (ChainThread A)) (qm : ChainThread A)
    (label : ChainLabel In₁ In₂ Out₁ Out₂ (A.State × A.State))
    (move : ((In₁ × In₂) × (ChainThread A)) × (In₂ ⊕ In₁)) :
    (chainSetMonitor A T).step (some (some qm))
        (narrowedRecord (chainSetMonitor A T) (packChainSetLabel label)
          (some (some qm)) move) =
      some (some (chainThreadStep A qm label move.2 move.1.1)) := by
  obtain ⟨⟨mv, g⟩, d⟩ := move
  rcases label with labL | labR <;> cases d <;> rfl

theorem chainSetMonitor_step_dead
    (T : Finset (ChainThread A))
    (label : ChainLabel In₁ In₂ Out₁ Out₂ (A.State × A.State))
    (move : ((In₁ × In₂) × (ChainThread A)) × (In₂ ⊕ In₁)) :
    (chainSetMonitor A T).step (some none)
        (narrowedRecord (chainSetMonitor A T) (packChainSetLabel label)
          (some none) move) =
      some none :=
  rfl

theorem chainSetMonitor_step_start_mem
    (T : Finset (ChainThread A))
    (label : ChainLabel In₁ In₂ Out₁ Out₂ (A.State × A.State))
    (move : ((In₁ × In₂) × (ChainThread A)) × (In₂ ⊕ In₁))
    (h : move.1.2 ∈ T) :
    (chainSetMonitor A T).step none
        (narrowedRecord (chainSetMonitor A T) (packChainSetLabel label)
          none move) =
      some (some (chainThreadStep A move.1.2 label move.2 move.1.1)) := by
  obtain ⟨⟨mv, g⟩, d⟩ := move
  rcases label with labL | labR <;>
    cases d <;>
    · show (if g ∈ T then _ else _) = _
      rw [if_pos h]
      rfl

theorem chainSetMonitor_step_start_notMem
    (T : Finset (ChainThread A))
    (label : ChainLabel In₁ In₂ Out₁ Out₂ (A.State × A.State))
    (move : ((In₁ × In₂) × (ChainThread A)) × (In₂ ⊕ In₁))
    (h : move.1.2 ∉ T) :
    (chainSetMonitor A T).step none
        (narrowedRecord (chainSetMonitor A T) (packChainSetLabel label)
          none move) =
      some none := by
  obtain ⟨⟨mv, g⟩, d⟩ := move
  rcases label with labL | labR <;>
    cases d <;>
    · show (if g ∈ T then _ else _) = _
      rw [if_neg h]

/-! ### Thread-state correspondence -/

section Correspondence

variable (T : Finset (ChainThread A))
variable
  (narrowed :
    LabeledTree (In₂ ⊕ In₁)
      (ChainLabel In₁ In₂ Out₁ Out₂ (A.State × A.State)))

/-- The set-monitor thread state of a started thread is the composed
fold from the round-zero guess. -/
theorem chainSetThreadState_succ
    (env' :
      Nat -> (((In₁ × In₂) × (ChainThread A)) × (In₂ ⊕ In₁)))
    (hg : (env' 0).1.2 ∈ T) :
    ∀ n : Nat,
      narrowedThreadState (chainSetMonitor A T)
          (fun w => packChainSetLabel (narrowed w)) env' (n + 1) =
        some (some
          (chainFold A narrowed [] ((env' 0).1.2)
            (branchNode (fun k => ((env' k).1.1, (env' k).2))
              (n + 1)))) := by
  intro n
  induction n with
  | zero =>
      show narrowedControl (chainSetMonitor A T)
          (fun w => packChainSetLabel (narrowed w))
          ([] ++ [env' 0]) = _
      rw [narrowedControl_append]
      show (chainSetMonitor A T).step none
          (narrowedRecord (chainSetMonitor A T)
            (packChainSetLabel (narrowed [])) none (env' 0)) = _
      rw [chainSetMonitor_step_start_mem T (narrowed []) (env' 0) hg]
      rfl
  | succ n ih =>
      show narrowedControl (chainSetMonitor A T)
          (fun w => packChainSetLabel (narrowed w))
          (branchNode env' (n + 1) ++ [env' (n + 1)]) = _
      rw [narrowedControl_append]
      have hstate :
          narrowedControl (chainSetMonitor A T)
              (fun w => packChainSetLabel (narrowed w))
              (branchNode env' (n + 1)) =
            some (some
              (chainFold A narrowed [] ((env' 0).1.2)
                (branchNode (fun k => ((env' k).1.1, (env' k).2))
                  (n + 1)))) := ih
      rw [hstate]
      have hsw :
          senderWord (branchNode env' (n + 1)) =
            (branchNode (fun k => ((env' k).1.1, (env' k).2))
                (n + 1)).map Prod.snd := by
        rw [BlockRecordMonitor.senderWord_branchNode env'
            (fun k => (env' k).2) (fun _ => rfl),
          branchNode_map_snd (fun k => ((env' k).1.1, (env' k).2))
            (n + 1)]
      rw [hsw, chainSetMonitor_step_active T _ (narrowed _) (env' (n + 1)),
        show branchNode (fun k => ((env' k).1.1, (env' k).2)) (n + 2) =
          branchNode (fun k => ((env' k).1.1, (env' k).2)) (n + 1) ++
            [((env' (n + 1)).1.1, (env' (n + 1)).2)] from rfl,
        chainFold_snoc_nil]

/-- The set-monitor thread state of a dead thread stays dead. -/
theorem chainSetThreadState_dead
    (env' :
      Nat -> (((In₁ × In₂) × (ChainThread A)) × (In₂ ⊕ In₁)))
    (hg : (env' 0).1.2 ∉ T) :
    ∀ n : Nat,
      narrowedThreadState (chainSetMonitor A T)
          (fun w => packChainSetLabel (narrowed w)) env' (n + 1) =
        some none := by
  intro n
  induction n with
  | zero =>
      show narrowedControl (chainSetMonitor A T)
          (fun w => packChainSetLabel (narrowed w))
          ([] ++ [env' 0]) = _
      rw [narrowedControl_append]
      exact
        chainSetMonitor_step_start_notMem T (narrowed []) (env' 0) hg
  | succ n ih =>
      show narrowedControl (chainSetMonitor A T)
          (fun w => packChainSetLabel (narrowed w))
          (branchNode env' (n + 1) ++ [env' (n + 1)]) = _
      rw [narrowedControl_append]
      have hstate :
          narrowedControl (chainSetMonitor A T)
              (fun w => packChainSetLabel (narrowed w))
              (branchNode env' (n + 1)) =
            some none := ih
      rw [hstate]
      exact chainSetMonitor_step_dead T _ (env' (n + 1))

/-! ### The set semantics -/

/-- The universal thread condition of the set monitor is the
composed-thread condition over every thread of the set. -/
theorem chainSetAllThreadsWin_iff :
    NarrowedAllThreadsWin (chainSetMonitor A T)
        (fun w => packChainSetLabel (narrowed w)) ↔
      ∀ qm ∈ T, ChainAllThreadsWin A narrowed qm := by
  constructor
  · intro h qm hqm env
    have henv :=
      h (fun k => (((env k).1, qm), (env k).2))
    have hshift :=
      (natSeqMinEvenParity_shift
        (fun n =>
          (chainSetMonitor A T).priority
            (narrowedThreadState (chainSetMonitor A T)
              (fun w => packChainSetLabel (narrowed w))
              (fun k => (((env k).1, qm), (env k).2)) n))
        1).mpr henv
    have hfun :
        (fun n =>
            (chainSetMonitor A T).priority
              (narrowedThreadState (chainSetMonitor A T)
                (fun w => packChainSetLabel (narrowed w))
                (fun k => (((env k).1, qm), (env k).2)) (1 + n))) =
          fun n =>
            A.priority
              (chainFold A narrowed [] qm (branchNode env (1 + n))).2.1 := by
      funext n
      rw [show 1 + n = n + 1 by omega,
        chainSetThreadState_succ T narrowed
          (fun k => (((env k).1, qm), (env k).2)) hqm n]
      rfl
    rw [hfun] at hshift
    have htarget :=
      (natSeqMinEvenParity_shift
        (fun n =>
          A.priority
            (chainFold A narrowed [] qm (branchNode env n)).2.1)
        1).mp hshift
    exact htarget
  · intro h env'
    by_cases hg : (env' 0).1.2 ∈ T
    · have hwin :=
        h ((env' 0).1.2) hg
          (fun k => ((env' k).1.1, (env' k).2))
      have hshift :=
        (natSeqMinEvenParity_shift
          (fun n =>
            A.priority
              (chainFold A narrowed [] ((env' 0).1.2)
                (branchNode (fun k => ((env' k).1.1, (env' k).2))
                  n)).2.1)
          1).mpr hwin
      refine
        (natSeqMinEvenParity_shift
          (fun n =>
            (chainSetMonitor A T).priority
              (narrowedThreadState (chainSetMonitor A T)
                (fun w => packChainSetLabel (narrowed w)) env' n))
          1).mp ?_
      have hfun :
          (fun n =>
              (chainSetMonitor A T).priority
                (narrowedThreadState (chainSetMonitor A T)
                  (fun w => packChainSetLabel (narrowed w)) env'
                  (1 + n))) =
            fun n =>
              A.priority
                (chainFold A narrowed [] ((env' 0).1.2)
                  (branchNode (fun k => ((env' k).1.1, (env' k).2))
                    (1 + n))).2.1 := by
        funext n
        rw [show 1 + n = n + 1 by omega,
          chainSetThreadState_succ T narrowed env' hg n]
        rfl
      rw [hfun]
      exact hshift
    · refine
        (natSeqMinEvenParity_shift
          (fun n =>
            (chainSetMonitor A T).priority
              (narrowedThreadState (chainSetMonitor A T)
                (fun w => packChainSetLabel (narrowed w)) env' n))
          1).mp ?_
      have hfun :
          (fun n =>
              (chainSetMonitor A T).priority
                (narrowedThreadState (chainSetMonitor A T)
                  (fun w => packChainSetLabel (narrowed w)) env'
                  (1 + n))) =
            fun _ => 0 := by
        funext n
        rw [show 1 + n = n + 1 by omega,
          chainSetThreadState_dead T narrowed env' hg n]
        rfl
      rw [hfun]
      exact
        ⟨0, ⟨0, rfl⟩, fun n => ⟨n, Nat.le_refl _, rfl⟩,
          fun q hq => by
            obtain ⟨k, -, hk⟩ := hq 0
            omega⟩

end Correspondence

/-! ### The per-set checker monitor and the checker instance -/

variable (A)

/-- The per-set chain checker monitor: the narrowed-thread
determinization of the set monitor, reading reversed-block labels and
mixed directions through the set packing. -/
noncomputable def chainSetPerMonitor (T : Finset (ChainThread A)) :
    DeterministicBlockMonitor.{max u v, max u v x y s, s}
      (In₂ ⊕ In₁)
      (ChainLabel In₁ In₂ Out₁ Out₂ (A.State × A.State)) where
  branchFinite := inferInstance
  alphabetFinite := inferInstance
  State := ((chainSetMonitor A T).threadBlockMonitor).State
  stateFinite := ((chainSetMonitor A T).threadBlockMonitor).stateFinite
  initial := ((chainSetMonitor A T).threadBlockMonitor).initial
  step := fun st label branch =>
    ((chainSetMonitor A T).threadBlockMonitor).step st
      (packChainSetLabel label) branch
  priority := fun st =>
    ((chainSetMonitor A T).threadBlockMonitor).priority st

variable {A}

theorem chainSetPerMonitor_control (T : Finset (ChainThread A))
    (narrowed :
      LabeledTree (In₂ ⊕ In₁)
        (ChainLabel In₁ In₂ Out₁ Out₂ (A.State × A.State))) :
    ∀ node : TreeNode (In₂ ⊕ In₁),
      (chainSetPerMonitor A T).control narrowed node =
        ((chainSetMonitor A T).threadBlockMonitor).control
          (fun w => packChainSetLabel (narrowed w)) node := by
  intro node
  induction node using List.reverseRecOn with
  | nil => rfl
  | append_singleton node b ih =>
      rw [DeterministicBlockMonitor.control_append,
        DeterministicBlockMonitor.control_append, ih]
      rfl

/-- The per-set chain checker is sound and complete for the
composed-thread condition over the set. -/
theorem chainSetPerMonitor_winningTree_iff
    (T : Finset (ChainThread A))
    (narrowed :
      LabeledTree (In₂ ⊕ In₁)
        (ChainLabel In₁ In₂ Out₁ Out₂ (A.State × A.State))) :
    (chainSetPerMonitor A T).WinningTree narrowed ↔
      ∀ qm ∈ T, ChainAllThreadsWin A narrowed qm := by
  rw [← chainSetAllThreadsWin_iff T narrowed,
    ← BlockRecordMonitor.threadBlockMonitor_winningTree_iff
      (chainSetMonitor A T)
      (fun w => packChainSetLabel (narrowed w))]
  have heq :
      ∀ branch : Nat -> In₂ ⊕ In₁,
        (fun n =>
            (chainSetPerMonitor A T).priority
              ((chainSetPerMonitor A T).control narrowed
                (branchNode branch n))) =
          fun n =>
            ((chainSetMonitor A T).threadBlockMonitor).priority
              (((chainSetMonitor A T).threadBlockMonitor).control
                (fun w => packChainSetLabel (narrowed w))
                (branchNode branch n)) := by
    intro branch
    funext n
    rw [chainSetPerMonitor_control T narrowed (branchNode branch n)]
    rfl
  constructor
  · intro hwin branch
    have hb := hwin branch
    rwa [heq branch] at hb
  · intro hwin branch
    have hb := hwin branch
    rw [heq branch]
    exact hb

variable (A)

/-- The chain checker monitor: the disjoint union of the per-set
determinizations, threaded fiberwise. -/
noncomputable def chainCheckerMonitor :
    DeterministicBlockMonitor.{max u v, max u v x y s, s}
      (In₂ ⊕ In₁)
      (ChainLabel In₁ In₂ Out₁ Out₂ (A.State × A.State)) where
  branchFinite := inferInstance
  alphabetFinite := by
    classical
    infer_instance
  State :=
    Σ T : Finset (ChainThread A), (chainSetPerMonitor A T).State
  stateFinite := by
    letI :
        ∀ T : Finset (ChainThread A),
          Fintype (chainSetPerMonitor A T).State :=
      fun T => (chainSetPerMonitor A T).stateFinite
    infer_instance
  initial := ⟨∅, (chainSetPerMonitor A ∅).initial⟩
  step := fun state label branch =>
    ⟨state.1, (chainSetPerMonitor A state.1).step state.2 label branch⟩
  priority := fun state =>
    (chainSetPerMonitor A state.1).priority state.2

/-- Fiberwise threading of the chain checker monitor. -/
theorem chainCheckerMonitor_controlIn (T : Finset (ChainThread A)) :
    ∀ node : TreeNode (In₂ ⊕ In₁),
      ∀ tree' :
        LabeledTree (In₂ ⊕ In₁)
          (ChainLabel In₁ In₂ Out₁ Out₂ (A.State × A.State)),
      ∀ state' : (chainSetPerMonitor A T).State,
        (chainCheckerMonitor A).controlIn tree' ⟨T, state'⟩ node =
          ⟨T, (chainSetPerMonitor A T).controlIn tree' state' node⟩ := by
  intro node
  induction node with
  | nil =>
      intro tree' state'
      rfl
  | cons dir rest ih =>
      intro tree' state'
      show
        (chainCheckerMonitor A).controlIn (fun node => tree' (dir :: node))
            ⟨T, (chainSetPerMonitor A T).step state' (tree' []) dir⟩
            rest =
          _
      rw [ih]
      rfl

/-- The chain thread checker of the global journal automaton. -/
noncomputable def chainThreadCheckerInstance :
    ChainThreadChecker (In₁ := In₁) (A := A) where
  monitor := chainCheckerMonitor A
  start := fun T => ⟨T, (chainSetPerMonitor A T).initial⟩
  winning_iff := by
    intro T narrowed
    rw [← chainSetPerMonitor_winningTree_iff (A := A) T narrowed]
    have hcontrol :
        ∀ node : TreeNode (In₂ ⊕ In₁),
          ({ chainCheckerMonitor A with
              initial := ⟨T, (chainSetPerMonitor A T).initial⟩ } :
            DeterministicBlockMonitor (In₂ ⊕ In₁)
              (ChainLabel In₁ In₂ Out₁ Out₂ (A.State × A.State))).control narrowed
              node =
            ⟨T, (chainSetPerMonitor A T).control narrowed node⟩ := by
      intro node
      show
        ({ chainCheckerMonitor A with
            initial := ⟨T, (chainSetPerMonitor A T).initial⟩ } :
          DeterministicBlockMonitor (In₂ ⊕ In₁)
            (ChainLabel In₁ In₂ Out₁ Out₂ (A.State × A.State))).controlIn narrowed
            ⟨T, (chainSetPerMonitor A T).initial⟩ node =
          _
      rw [DeterministicBlockMonitor.controlIn_update_initial]
      exact
        chainCheckerMonitor_controlIn A T node narrowed
          (chainSetPerMonitor A T).initial
    have heq :
        ∀ branch : Nat -> In₂ ⊕ In₁,
          (fun n =>
            ({ chainCheckerMonitor A with
                initial := ⟨T, (chainSetPerMonitor A T).initial⟩ } :
              DeterministicBlockMonitor (In₂ ⊕ In₁)
                (ChainLabel In₁ In₂ Out₁ Out₂ (A.State × A.State))).priority
              (DeterministicBlockMonitor.control _ narrowed
                (branchNode branch n))) =
            fun n =>
              (chainSetPerMonitor A T).priority
                ((chainSetPerMonitor A T).control narrowed
                  (branchNode branch n)) := by
      intro branch
      funext n
      rw [hcontrol (branchNode branch n)]
      rfl
    constructor
    · intro hwin branch
      have hb := hwin branch
      rwa [heq branch] at hb
    · intro hwin branch
      have hb := hwin branch
      rw [heq branch]
      exact hb

end DetParityAutomaton

end DistributedSynthesis
