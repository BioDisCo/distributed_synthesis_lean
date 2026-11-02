/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemObservableThreadTreeRationalization

/-!
# Hidden code continuity below a public family tree

A public family controller may remember a finite family of possible codes,
but it must not reselect an unrelated code at every level when parity is
checked.  This module keeps the actual code proof-side in a hidden thread.
The hidden state also carries the literal control of a deterministic parity
automaton on successive codes.  Thus every live transition has the form

```
(code, control) -> (nextCode, D.step control nextCode).
```

The public letter is `(move, nextFamily)`.  A model-specific relation `Edge`
says which `nextCode` is an exact successor of the current code under that
letter.  Incoherent resolutions enter an accepting priority-zero sink.
Consequently the universal-run DPA accepts a public word exactly when every
one coherent hidden code thread has the original code-DPA parity.  In
particular, sibling nodes cannot be pasted into a parity mosaic by repeatedly
reselecting a member of the public family.

The final section couples this bundle to the existing observable-tree
monitor.  Rationalization then sees only the public family code and the
simultaneous family move; the actual code and objective control remain hidden.
-/

namespace DistributedSynthesis

universe u v w x

section HiddenCodeContinuity

variable {Code : Type u} {Move : Type v} {Family : Type w}
variable [Fintype Code]

/-- A live exact code and its literal objective control, or the harmless
destination of an incoherent hidden resolution. -/
inductive HiddenCodeContinuityState
    (D : DetParityAutomaton.{u, x} Code) where
  | live (code : Code) (control : D.State)
  | dead

namespace HiddenCodeContinuityState

variable (D : DetParityAutomaton.{u, x} Code)

noncomputable instance : Fintype (HiddenCodeContinuityState D) := by
  classical
  let Rep := (Code × D.State) ⊕ Unit
  let e : HiddenCodeContinuityState D ≃ Rep :=
    { toFun := fun state =>
        match state with
        | .live code control => .inl (code, control)
        | .dead => .inr ()
      invFun := fun state =>
        match state with
        | .inl pair => .live pair.1 pair.2
        | .inr _ => .dead
      left_inv := by intro state; cases state <;> rfl
      right_inv := by
        intro state
        cases state with
        | inl pair => rcases pair with ⟨code, control⟩; rfl
        | inr value => cases value; rfl }
  exact Fintype.ofEquiv Rep e.symm

end HiddenCodeContinuityState

/-- Hidden exact-code threads below public `(move, nextFamily)` letters.
The objective control is advanced definitionally on the selected next code.
`Edge` is the only model-specific ingredient. -/
noncomputable def hiddenCodeContinuitySystem
    (D : DetParityAutomaton.{u, x} Code)
    (initialCode : Code)
    (Edge : Code → Move → Family → Code → Prop) :
    FiniteThreadSystem.{max v w, max u x, u} (Move × Family) := by
  classical
  exact {
    State := HiddenCodeContinuityState D
    stateFinite := inferInstance
    initial := .live initialCode D.initial
    Resolution := Code
    step := fun source letter nextCode =>
      match source with
      | .dead => .dead
      | .live code control =>
          if Edge code letter.1 letter.2 nextCode then
            .live nextCode (D.step control nextCode)
          else .dead
    priority := fun state =>
      match state with
      | .dead => 0
      | .live _ control => D.priority control
  }

@[simp] theorem hiddenCodeContinuitySystem_step_dead
    (D : DetParityAutomaton.{u, x} Code)
    (initialCode : Code)
    (Edge : Code → Move → Family → Code → Prop)
    (letter : Move × Family) (nextCode : Code) :
    (hiddenCodeContinuitySystem D initialCode Edge).step .dead letter nextCode =
      .dead :=
  rfl

@[simp] theorem hiddenCodeContinuitySystem_step_live_of
    (D : DetParityAutomaton.{u, x} Code)
    (initialCode code nextCode : Code)
    (Edge : Code → Move → Family → Code → Prop)
    (letter : Move × Family)
    (control : D.State)
    (hedge : Edge code letter.1 letter.2 nextCode) :
    (hiddenCodeContinuitySystem D initialCode Edge).step
        (.live code control) letter nextCode =
      .live nextCode (D.step control nextCode) := by
  simp [hiddenCodeContinuitySystem, hedge]

@[simp] theorem hiddenCodeContinuitySystem_step_live_dead_of
    (D : DetParityAutomaton.{u, x} Code)
    (initialCode code nextCode : Code)
    (Edge : Code → Move → Family → Code → Prop)
    (letter : Move × Family)
    (control : D.State)
    (hedge : ¬ Edge code letter.1 letter.2 nextCode) :
    (hiddenCodeContinuitySystem D initialCode Edge).step
        (.live code control) letter nextCode = .dead := by
  simp [hiddenCodeContinuitySystem, hedge]

/-- One persistent exact-code trajectory below a fixed public word. -/
structure HiddenCodeContinuityThread
    (initialCode : Code)
    (Edge : Code → Move → Family → Code → Prop)
    (word : OmegaWord (Move × Family)) where
  code : Nat → Code
  initial : code 0 = initialCode
  edge : ∀ n, Edge (code n) (word n).1 (word n).2 (code (n + 1))

namespace HiddenCodeContinuityThread

variable
  (D : DetParityAutomaton.{u, x} Code)
  (initialCode : Code)
  (Edge : Code → Move → Family → Code → Prop)
  (word : OmegaWord (Move × Family))
  (thread : HiddenCodeContinuityThread initialCode Edge word)

/-- The code word seen by the objective is the positive-time tail of the
persistent hidden trajectory. -/
def childCodeWord : OmegaWord Code := fun n => thread.code (n + 1)

/-- Literal hidden state at depth `n`. -/
def stateAt (n : Nat) : HiddenCodeContinuityState D :=
  .live (thread.code n) (D.run thread.childCodeWord n)

omit [Fintype Code] in
@[simp] theorem stateAt_zero :
    stateAt D initialCode Edge word thread 0 =
      .live initialCode D.initial := by
  simp [stateAt, thread.initial]

/-- Every coherent exact-code trajectory is literally a run of the hidden
system.  No family member is reselected between consecutive depths. -/
theorem isRun :
    (hiddenCodeContinuitySystem D initialCode Edge).IsRun word
      (stateAt D initialCode Edge word thread) := by
  constructor
  · exact stateAt_zero D initialCode Edge word thread
  · intro n
    refine ⟨thread.code (n + 1), ?_⟩
    change HiddenCodeContinuityState.live (thread.code (n + 1))
        (D.run thread.childCodeWord (n + 1)) =
      (hiddenCodeContinuitySystem D initialCode Edge).step
        (.live (thread.code n) (D.run thread.childCodeWord n))
        (word n) (thread.code (n + 1))
    rw [hiddenCodeContinuitySystem_step_live_of D initialCode
      (thread.code n) (thread.code (n + 1)) Edge (word n)
      (D.run thread.childCodeWord n) (thread.edge n)]
    rw [D.run_succ]
    rfl

end HiddenCodeContinuityThread

private theorem hiddenCode_minEven_of_eventually_zero
    (priorities : Nat → Nat) (n : Nat)
    (hzero : ∀ k, priorities (n + k) = 0) :
    NatSeqMinEvenParity priorities := by
  refine ⟨0, ⟨0, rfl⟩, ?_, ?_⟩
  · intro base
    exact ⟨n + base, by omega, hzero base⟩
  · intro q _
    exact Nat.zero_le q

/-- Once an incoherent resolution reaches `dead`, the run stays there. -/
theorem hiddenCodeContinuity_isRun_dead_persists
    (D : DetParityAutomaton.{u, x} Code)
    (initialCode : Code)
    (Edge : Code → Move → Family → Code → Prop)
    (word : OmegaWord (Move × Family))
    (run : Nat → HiddenCodeContinuityState D)
    (hrun : (hiddenCodeContinuitySystem D initialCode Edge).IsRun word run)
    {n : Nat} (hdead : run n = .dead) :
    ∀ k, run (n + k) = .dead := by
  intro k
  induction k with
  | zero => simpa using hdead
  | succ k ih =>
      rcases hrun.2 (n + k) with ⟨nextCode, hnext⟩
      rw [Nat.add_succ, hnext, ih]
      rfl

/-- Exact semantic characterization of the universal hidden bundle.

The forward implication prevents mosaics: acceptance of the public word
certifies the original code-DPA objective for every persistent exact thread.
The reverse implication says these are the only live obligations; incoherent
resolutions are absorbed by the even sink. -/
theorem hiddenCodeContinuitySystem_universalRunDPA_accepts_iff
    (D : DetParityAutomaton.{u, x} Code)
    (initialCode : Code)
    (Edge : Code → Move → Family → Code → Prop)
    (word : OmegaWord (Move × Family)) :
    (hiddenCodeContinuitySystem D initialCode Edge).universalRunDPA.Accepts
        word ↔
      ∀ thread : HiddenCodeContinuityThread initialCode Edge word,
        D.Accepts thread.childCodeWord := by
  classical
  constructor
  · intro haccepts thread
    have hall :=
      ((hiddenCodeContinuitySystem D initialCode Edge)
        |>.universalRunDPA_accepts_iff word).mp haccepts
    have hparity := hall
      (HiddenCodeContinuityThread.stateAt D initialCode Edge word thread)
      (HiddenCodeContinuityThread.isRun D initialCode Edge word thread)
    rw [D.accepts_iff_natSeqMinEvenParity]
    simpa [HiddenCodeContinuityThread.stateAt,
      hiddenCodeContinuitySystem] using hparity
  · intro hthreads
    rw [(hiddenCodeContinuitySystem D initialCode Edge)
      |>.universalRunDPA_accepts_iff]
    intro run hrun
    by_cases hever : ∃ n, run n = .dead
    · rcases hever with ⟨n, hdead⟩
      apply hiddenCode_minEven_of_eventually_zero _ n
      intro k
      rw [hiddenCodeContinuity_isRun_dead_persists D initialCode Edge word run
        hrun hdead k]
      rfl
    · let code : Nat → Code := fun n =>
        match run n with
        | .live code _ => code
        | .dead => initialCode
      let control : Nat → D.State := fun n =>
        match run n with
        | .live _ control => control
        | .dead => D.initial
      have hlive : ∀ n, run n = .live (code n) (control n) := by
        intro n
        cases hstate : run n with
        | live actualCode actualControl => simp [code, control, hstate]
        | dead => exact False.elim (hever ⟨n, hstate⟩)
      have hinitialCode : code 0 = initialCode := by
        have h := (hlive 0).symm.trans hrun.1
        exact HiddenCodeContinuityState.live.inj h |>.1
      have hinitialControl : control 0 = D.initial := by
        have h := (hlive 0).symm.trans hrun.1
        exact HiddenCodeContinuityState.live.inj h |>.2
      have hedge : ∀ n,
          Edge (code n) (word n).1 (word n).2 (code (n + 1)) := by
        intro n
        rcases hrun.2 n with ⟨nextCode, hnext⟩
        by_cases hexact : Edge (code n) (word n).1 (word n).2 nextCode
        · have htarget : code (n + 1) = nextCode := by
            have h := (hlive (n + 1)).symm.trans hnext
            rw [hlive n,
              hiddenCodeContinuitySystem_step_live_of D initialCode
                (code n) nextCode Edge (word n) (control n) hexact] at h
            exact (HiddenCodeContinuityState.live.inj h).1
          simpa [htarget] using hexact
        · have hdead : run (n + 1) = .dead := by
            rw [hnext, hlive n,
              hiddenCodeContinuitySystem_step_live_dead_of D initialCode
                (code n) nextCode Edge (word n) (control n) hexact]
          exact False.elim (hever ⟨n + 1, hdead⟩)
      let thread : HiddenCodeContinuityThread initialCode Edge word := {
        code := code
        initial := hinitialCode
        edge := hedge }
      have hcontrol : ∀ n,
          control n = D.run thread.childCodeWord n := by
        intro n
        induction n with
        | zero => simpa using hinitialControl
        | succ n ih =>
            rcases hrun.2 n with ⟨nextCode, hnext⟩
            have hexact : Edge (code n) (word n).1 (word n).2 nextCode := by
              by_contra hnot
              have hdead : run (n + 1) = .dead := by
                rw [hnext, hlive n,
                  hiddenCodeContinuitySystem_step_live_dead_of D initialCode
                    (code n) nextCode Edge (word n) (control n) hnot]
              exact hever ⟨n + 1, hdead⟩
            have h := (hlive (n + 1)).symm.trans hnext
            rw [hlive n,
              hiddenCodeContinuitySystem_step_live_of D initialCode
                (code n) nextCode Edge (word n) (control n) hexact] at h
            have hcode : code (n + 1) = nextCode :=
              (HiddenCodeContinuityState.live.inj h).1
            have hnextControl : control (n + 1) = D.step (control n) nextCode :=
              (HiddenCodeContinuityState.live.inj h).2
            rw [hnextControl, ih, D.run_succ]
            change D.step _ nextCode = D.step _ (code (n + 1))
            rw [hcode]
      have haccepts := hthreads thread
      have hparity := (D.accepts_iff_natSeqMinEvenParity
        thread.childCodeWord).mp haccepts
      have hpriority :
          (fun n => (hiddenCodeContinuitySystem D initialCode Edge).priority
            (run n)) =
          fun n => D.priority (D.run thread.childCodeWord n) := by
        funext n
        rw [hlive n]
        change D.priority (control n) = _
        rw [hcontrol n]
      rw [hpriority]
      exact hparity

/-! ## Coupling to a public family-move tree -/

variable [Fintype Family] [Fintype Move] [Inhabited Family]

/-- The public monitor sees a family code and chooses one simultaneous family
move.  Its parity component universally checks persistent hidden codes. -/
noncomputable def hiddenCodeContinuityTreeMonitor
    (D : DetParityAutomaton.{u, x} Code)
    (initialCode : Code)
    (Edge : Code → Move → Family → Code → Prop)
    (initialFamily : Family)
    (Valid : Family → Move → Prop) [DecidableRel Valid] :=
  observableThreadTreeMonitor
    (hiddenCodeContinuitySystem D initialCode Edge)
    initialFamily Valid

/-- Exact winning condition of the coupled public-family/hidden-code tree. -/
theorem hiddenCodeContinuityTreeMonitor_winning_iff
    (D : DetParityAutomaton.{u, x} Code)
    (initialCode : Code)
    (Edge : Code → Move → Family → Code → Prop)
    (initialFamily : Family)
    (Valid : Family → Move → Prop) [DecidableRel Valid]
    (tree : LabeledTree Family Move) :
    (hiddenCodeContinuityTreeMonitor D initialCode Edge initialFamily Valid).WinningTree
        tree ↔
      ObservableMovesValid initialFamily Valid tree ∧
        ∀ branch : Nat → Family,
          ∀ thread : HiddenCodeContinuityThread initialCode Edge
            (observableThreadWord tree branch),
            D.Accepts thread.childCodeWord := by
  rw [hiddenCodeContinuityTreeMonitor,
    observableThreadTreeMonitor_winning_iff]
  constructor
  · rintro ⟨hvalid, hbundle⟩
    refine ⟨hvalid, ?_⟩
    intro branch
    exact (hiddenCodeContinuitySystem_universalRunDPA_accepts_iff
      D initialCode Edge (observableThreadWord tree branch)).mp
        (hbundle branch)
  · rintro ⟨hvalid, hthreads⟩
    refine ⟨hvalid, ?_⟩
    intro branch
    exact (hiddenCodeContinuitySystem_universalRunDPA_accepts_iff
      D initialCode Edge (observableThreadWord tree branch)).mpr
        (hthreads branch)

/-- A semantic public tree satisfying the family law and every persistent
hidden-code objective admits one checked finite public controller. -/
theorem exists_stateControlled_hiddenCodeContinuityTree
    (D : DetParityAutomaton.{u, x} Code)
    (initialCode : Code)
    (Edge : Code → Move → Family → Code → Prop)
    (initialFamily : Family)
    (Valid : Family → Move → Prop) [DecidableRel Valid]
    (tree : LabeledTree Family Move)
    (hvalid : ObservableMovesValid initialFamily Valid tree)
    (hthreads : ∀ branch : Nat → Family,
      ∀ thread : HiddenCodeContinuityThread initialCode Edge
        (observableThreadWord tree branch),
        D.Accepts thread.childCodeWord) :
    ∃ table : RunParityTreeAutomaton.StateControlledTreeTable
        (hiddenCodeContinuityTreeMonitor D initialCode Edge initialFamily Valid
          |>.toRunAutomaton),
      (hiddenCodeContinuityTreeMonitor D initialCode Edge initialFamily Valid).WinningTree
        table.toTransitionRationalTree.labeledTree := by
  apply exists_stateControlled_observableThreadTree_of_winning
    (hiddenCodeContinuitySystem D initialCode Edge)
    initialFamily Valid tree
  exact (hiddenCodeContinuityTreeMonitor_winning_iff D initialCode Edge
    initialFamily Valid tree).mpr ⟨hvalid, hthreads⟩

end HiddenCodeContinuity

end DistributedSynthesis
