/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemFiniteSemanticFibreImage

/-!
# Control-aware hidden descriptor continuity

The code-only bundle is sufficient when one public move component is
determined by the current code.  In the staged family construction the same
code may occur with a different objective control or old finite table.  The
smallest safe finite descriptor therefore stores

```
((code, code-DPA control), move identity).
```

This module keeps that whole descriptor in one hidden thread.  A live edge is
both a model `ExactEdge` and the literal deterministic update
`q' = D.step q code'`.  Pairwise edge witnesses are not claimed to provide a
semantic path lift; the concrete adapter retains that as a separate premise.
-/

namespace DistributedSynthesis

universe u v m b f x

section

variable {Code : Type u} {MoveIdentity : Type v}
variable (D : DetParityAutomaton.{u, x} Code)

/-- Finite hidden identity used by staged family extraction. -/
abbrev HiddenCodeControlDescriptor := (Code × D.State) × MoveIdentity

namespace HiddenCodeControlDescriptor

variable {D}

def code (descriptor : HiddenCodeControlDescriptor D (MoveIdentity := MoveIdentity)) :
    Code :=
  descriptor.1.1

def control
    (descriptor : HiddenCodeControlDescriptor D (MoveIdentity := MoveIdentity)) :
    D.State :=
  descriptor.1.2

def moveIdentity
    (descriptor : HiddenCodeControlDescriptor D (MoveIdentity := MoveIdentity)) :
    MoveIdentity :=
  descriptor.2

@[simp] theorem code_mk (code : Code) (control : D.State)
    (moveIdentity : MoveIdentity) :
    HiddenCodeControlDescriptor.code ((code, control), moveIdentity) = code :=
  rfl

@[simp] theorem control_mk (code : Code) (control : D.State)
    (moveIdentity : MoveIdentity) :
    HiddenCodeControlDescriptor.control ((code, control), moveIdentity) =
      control :=
  rfl

@[simp] theorem moveIdentity_mk (code : Code) (control : D.State)
    (moveIdentity : MoveIdentity) :
    HiddenCodeControlDescriptor.moveIdentity ((code, control), moveIdentity) =
      moveIdentity :=
  rfl

end HiddenCodeControlDescriptor

variable {D}
variable {FamilyMove : Type m} {Direction : Type b} {FamilyCode : Type f}
variable [Fintype Code] [Fintype MoveIdentity]

/-- Public letter read at one family transition: the simultaneous family
move, Nature's finite direction, and the computed next public family code. -/
abbrev HiddenDescriptorFamilyLetter :=
  FamilyMove × (Direction × FamilyCode)

/-- Live hidden descriptor, or the harmless accepting destination of an
incoherent resolution. -/
inductive HiddenDescriptorContinuityState
    (D : DetParityAutomaton.{u, x} Code) (MoveIdentity : Type v) where
  | live (descriptor : HiddenCodeControlDescriptor D
      (MoveIdentity := MoveIdentity))
  | dead

namespace HiddenDescriptorContinuityState

noncomputable instance : Fintype
    (HiddenDescriptorContinuityState D MoveIdentity) := by
  classical
  let Descriptor := HiddenCodeControlDescriptor D
    (MoveIdentity := MoveIdentity)
  let Rep := Descriptor ⊕ Unit
  let e : HiddenDescriptorContinuityState D MoveIdentity ≃ Rep :=
    { toFun := fun state =>
        match state with
        | .live descriptor => .inl descriptor
        | .dead => .inr ()
      invFun := fun state =>
        match state with
        | .inl descriptor => .live descriptor
        | .inr _ => .dead
      left_inv := by intro state; cases state <;> rfl
      right_inv := by
        intro state
        cases state with
        | inl descriptor => rfl
        | inr value => cases value; rfl }
  exact Fintype.ofEquiv Rep e.symm

end HiddenDescriptorContinuityState

/-- Control-aware persistent-descriptor system.  `ExactEdge` may inspect the
old move identity, current code-DPA control, public family move, finite
direction, and computed next family. -/
noncomputable def hiddenDescriptorContinuitySystem
    (D : DetParityAutomaton.{u, x} Code)
    (initialDescriptor : HiddenCodeControlDescriptor D
      (MoveIdentity := MoveIdentity))
    (ExactEdge : HiddenCodeControlDescriptor D
        (MoveIdentity := MoveIdentity) →
      FamilyMove → Direction → FamilyCode →
        HiddenCodeControlDescriptor D (MoveIdentity := MoveIdentity) → Prop) :
    FiniteThreadSystem
      (HiddenDescriptorFamilyLetter
        (FamilyMove := FamilyMove) (Direction := Direction)
        (FamilyCode := FamilyCode)) := by
  classical
  exact {
    State := HiddenDescriptorContinuityState D MoveIdentity
    stateFinite := inferInstance
    initial := .live initialDescriptor
    Resolution := HiddenCodeControlDescriptor D
      (MoveIdentity := MoveIdentity)
    step := fun source letter target =>
      match source with
      | .dead => .dead
      | .live current =>
          if ExactEdge current letter.1 letter.2.1 letter.2.2 target ∧
              target.control = D.step current.control target.code then
            .live target
          else .dead
    priority := fun state =>
      match state with
      | .dead => 0
      | .live descriptor => D.priority descriptor.control
  }

@[simp] theorem hiddenDescriptorContinuitySystem_step_dead
    (D : DetParityAutomaton.{u, x} Code)
    (initialDescriptor : HiddenCodeControlDescriptor D
      (MoveIdentity := MoveIdentity))
    (ExactEdge : HiddenCodeControlDescriptor D
        (MoveIdentity := MoveIdentity) →
      FamilyMove → Direction → FamilyCode →
        HiddenCodeControlDescriptor D (MoveIdentity := MoveIdentity) → Prop)
    (letter : HiddenDescriptorFamilyLetter
      (FamilyMove := FamilyMove) (Direction := Direction)
      (FamilyCode := FamilyCode))
    (target : HiddenCodeControlDescriptor D (MoveIdentity := MoveIdentity)) :
    (hiddenDescriptorContinuitySystem D initialDescriptor ExactEdge).step
      .dead letter target = .dead :=
  rfl

@[simp] theorem hiddenDescriptorContinuitySystem_step_live_of
    (D : DetParityAutomaton.{u, x} Code)
    (initialDescriptor current target : HiddenCodeControlDescriptor D
      (MoveIdentity := MoveIdentity))
    (ExactEdge : HiddenCodeControlDescriptor D
        (MoveIdentity := MoveIdentity) →
      FamilyMove → Direction → FamilyCode →
        HiddenCodeControlDescriptor D (MoveIdentity := MoveIdentity) → Prop)
    (letter : HiddenDescriptorFamilyLetter
      (FamilyMove := FamilyMove) (Direction := Direction)
      (FamilyCode := FamilyCode))
    (hedge : ExactEdge current letter.1 letter.2.1 letter.2.2 target)
    (hcontrol : target.control = D.step current.control target.code) :
    (hiddenDescriptorContinuitySystem D initialDescriptor ExactEdge).step
        (.live current) letter target = .live target := by
  simp [hiddenDescriptorContinuitySystem, hedge, hcontrol]

@[simp] theorem hiddenDescriptorContinuitySystem_step_live_dead_of
    (D : DetParityAutomaton.{u, x} Code)
    (initialDescriptor current target : HiddenCodeControlDescriptor D
      (MoveIdentity := MoveIdentity))
    (ExactEdge : HiddenCodeControlDescriptor D
        (MoveIdentity := MoveIdentity) →
      FamilyMove → Direction → FamilyCode →
        HiddenCodeControlDescriptor D (MoveIdentity := MoveIdentity) → Prop)
    (letter : HiddenDescriptorFamilyLetter
      (FamilyMove := FamilyMove) (Direction := Direction)
      (FamilyCode := FamilyCode))
    (hbad : ¬ (ExactEdge current letter.1 letter.2.1 letter.2.2 target ∧
      target.control = D.step current.control target.code)) :
    (hiddenDescriptorContinuitySystem D initialDescriptor ExactEdge).step
        (.live current) letter target = .dead := by
  simp [hiddenDescriptorContinuitySystem, hbad]

/-- One persistent descriptor trajectory.  The model edge and objective
control step are separate fields so downstream proofs cannot silently use a
pairwise semantic witness as a path-lifting theorem. -/
structure HiddenDescriptorContinuityThread
    (D : DetParityAutomaton.{u, x} Code)
    (initialDescriptor : HiddenCodeControlDescriptor D
      (MoveIdentity := MoveIdentity))
    (ExactEdge : HiddenCodeControlDescriptor D
        (MoveIdentity := MoveIdentity) →
      FamilyMove → Direction → FamilyCode →
        HiddenCodeControlDescriptor D (MoveIdentity := MoveIdentity) → Prop)
    (word : OmegaWord (HiddenDescriptorFamilyLetter
      (FamilyMove := FamilyMove) (Direction := Direction)
      (FamilyCode := FamilyCode))) where
  descriptor : Nat → HiddenCodeControlDescriptor D
    (MoveIdentity := MoveIdentity)
  initial : descriptor 0 = initialDescriptor
  exactEdge : ∀ n, ExactEdge (descriptor n) (word n).1 (word n).2.1
    (word n).2.2 (descriptor (n + 1))
  controlStep : ∀ n, (descriptor (n + 1)).control =
    D.step (descriptor n).control (descriptor (n + 1)).code

namespace HiddenDescriptorContinuityThread

variable
  (D : DetParityAutomaton.{u, x} Code)
  (initialDescriptor : HiddenCodeControlDescriptor D
    (MoveIdentity := MoveIdentity))
  (ExactEdge : HiddenCodeControlDescriptor D
      (MoveIdentity := MoveIdentity) →
    FamilyMove → Direction → FamilyCode →
      HiddenCodeControlDescriptor D (MoveIdentity := MoveIdentity) → Prop)
  (word : OmegaWord (HiddenDescriptorFamilyLetter
    (FamilyMove := FamilyMove) (Direction := Direction)
    (FamilyCode := FamilyCode)))
  (thread : HiddenDescriptorContinuityThread D initialDescriptor ExactEdge word)

def childCodeWord : OmegaWord Code :=
  fun n => (thread.descriptor (n + 1)).code

def stateAt (n : Nat) : HiddenDescriptorContinuityState D
    MoveIdentity :=
  .live (thread.descriptor n)

omit [Fintype Code] [Fintype MoveIdentity] in
theorem control_eq_run
    (hinitialControl : initialDescriptor.control = D.initial) : ∀ n,
    (thread.descriptor n).control = D.run thread.childCodeWord n := by
  intro n
  induction n with
  | zero => simpa [thread.initial] using hinitialControl
  | succ n ih =>
      rw [thread.controlStep n, D.run_succ, ih]
      rfl

theorem isRun :
    (hiddenDescriptorContinuitySystem D initialDescriptor ExactEdge).IsRun
      word thread.stateAt := by
  constructor
  · change HiddenDescriptorContinuityState.live (thread.descriptor 0) =
      HiddenDescriptorContinuityState.live initialDescriptor
    rw [thread.initial]
  · intro n
    refine ⟨thread.descriptor (n + 1), ?_⟩
    change HiddenDescriptorContinuityState.live (thread.descriptor (n + 1)) =
      (hiddenDescriptorContinuitySystem D initialDescriptor ExactEdge).step
        (.live (thread.descriptor n)) (word n) (thread.descriptor (n + 1))
    rw [hiddenDescriptorContinuitySystem_step_live_of D initialDescriptor
      (thread.descriptor n) (thread.descriptor (n + 1)) ExactEdge (word n)
      (thread.exactEdge n) (thread.controlStep n)]

end HiddenDescriptorContinuityThread

private theorem hiddenDescriptor_minEven_of_eventually_zero
    (priorities : Nat → Nat) (n : Nat)
    (hzero : ∀ k, priorities (n + k) = 0) :
    NatSeqMinEvenParity priorities := by
  refine ⟨0, ⟨0, rfl⟩, ?_, ?_⟩
  · intro base
    exact ⟨n + base, by omega, hzero base⟩
  · intro q _
    exact Nat.zero_le q

theorem hiddenDescriptorContinuity_isRun_dead_persists
    (D : DetParityAutomaton.{u, x} Code)
    (initialDescriptor : HiddenCodeControlDescriptor D
      (MoveIdentity := MoveIdentity))
    (ExactEdge : HiddenCodeControlDescriptor D
        (MoveIdentity := MoveIdentity) →
      FamilyMove → Direction → FamilyCode →
        HiddenCodeControlDescriptor D (MoveIdentity := MoveIdentity) → Prop)
    (word : OmegaWord (HiddenDescriptorFamilyLetter
      (FamilyMove := FamilyMove) (Direction := Direction)
      (FamilyCode := FamilyCode)))
    (run : Nat → HiddenDescriptorContinuityState D MoveIdentity)
    (hrun : (hiddenDescriptorContinuitySystem D initialDescriptor ExactEdge)
      |>.IsRun word run)
    {n : Nat} (hdead : run n = .dead) :
    ∀ k, run (n + k) = .dead := by
  intro k
  induction k with
  | zero => simpa using hdead
  | succ k ih =>
      rcases hrun.2 (n + k) with ⟨target, hnext⟩
      rw [Nat.add_succ, hnext, ih]
      rfl

/-- Universal acceptance is exactly parity of every persistent full
descriptor thread.  This theorem guarantees code/control continuity; a
concrete semantic construction still owes a whole-path lift for each thread. -/
theorem hiddenDescriptorContinuitySystem_universalRunDPA_accepts_iff
    (D : DetParityAutomaton.{u, x} Code)
    (initialDescriptor : HiddenCodeControlDescriptor D
      (MoveIdentity := MoveIdentity))
    (hinitialControl : initialDescriptor.control = D.initial)
    (ExactEdge : HiddenCodeControlDescriptor D
        (MoveIdentity := MoveIdentity) →
      FamilyMove → Direction → FamilyCode →
        HiddenCodeControlDescriptor D (MoveIdentity := MoveIdentity) → Prop)
    (word : OmegaWord (HiddenDescriptorFamilyLetter
      (FamilyMove := FamilyMove) (Direction := Direction)
      (FamilyCode := FamilyCode))) :
    (hiddenDescriptorContinuitySystem D initialDescriptor ExactEdge).universalRunDPA.Accepts
        word ↔
      ∀ thread : HiddenDescriptorContinuityThread D initialDescriptor ExactEdge
          word,
        D.Accepts thread.childCodeWord := by
  classical
  constructor
  · intro haccepts thread
    have hall :=
      ((hiddenDescriptorContinuitySystem D initialDescriptor ExactEdge)
        |>.universalRunDPA_accepts_iff word).mp haccepts
    let threadState := HiddenDescriptorContinuityThread.stateAt D
      initialDescriptor ExactEdge word thread
    have hparity := hall threadState
      (HiddenDescriptorContinuityThread.isRun D initialDescriptor ExactEdge
        word thread)
    rw [D.accepts_iff_natSeqMinEvenParity]
    have hpriority :
        (fun n => (hiddenDescriptorContinuitySystem D initialDescriptor
          ExactEdge).priority (threadState n)) =
        fun n => D.priority (D.run thread.childCodeWord n) := by
      funext n
      change D.priority (thread.descriptor n).control = _
      rw [thread.control_eq_run D initialDescriptor ExactEdge word
        hinitialControl n]
    rw [hpriority] at hparity
    exact hparity
  · intro hthreads
    rw [(hiddenDescriptorContinuitySystem D initialDescriptor ExactEdge)
      |>.universalRunDPA_accepts_iff]
    intro run hrun
    by_cases hever : ∃ n, run n = .dead
    · rcases hever with ⟨n, hdead⟩
      apply hiddenDescriptor_minEven_of_eventually_zero _ n
      intro k
      rw [hiddenDescriptorContinuity_isRun_dead_persists D initialDescriptor
        ExactEdge word run hrun hdead k]
      rfl
    · let descriptor : Nat → HiddenCodeControlDescriptor D
          (MoveIdentity := MoveIdentity) := fun n =>
        match run n with
        | .live descriptor => descriptor
        | .dead => initialDescriptor
      have hlive : ∀ n, run n = .live (descriptor n) := by
        intro n
        cases hstate : run n with
        | live actual => simp [descriptor, hstate]
        | dead => exact False.elim (hever ⟨n, hstate⟩)
      have hinitial : descriptor 0 = initialDescriptor := by
        have h := (hlive 0).symm.trans hrun.1
        exact HiddenDescriptorContinuityState.live.inj h
      have hstep : ∀ n,
          ExactEdge (descriptor n) (word n).1 (word n).2.1 (word n).2.2
              (descriptor (n + 1)) ∧
            (descriptor (n + 1)).control =
              D.step (descriptor n).control (descriptor (n + 1)).code := by
        intro n
        rcases hrun.2 n with ⟨target, hnext⟩
        by_cases hgood :
            ExactEdge (descriptor n) (word n).1 (word n).2.1 (word n).2.2
                target ∧
              target.control = D.step (descriptor n).control target.code
        · have htarget : descriptor (n + 1) = target := by
            have h := (hlive (n + 1)).symm.trans hnext
            rw [hlive n,
              hiddenDescriptorContinuitySystem_step_live_of D
                initialDescriptor (descriptor n) target ExactEdge (word n)
                hgood.1 hgood.2] at h
            exact HiddenDescriptorContinuityState.live.inj h
          simpa [htarget] using hgood
        · have hdead : run (n + 1) = .dead := by
            rw [hnext, hlive n,
              hiddenDescriptorContinuitySystem_step_live_dead_of D
                initialDescriptor (descriptor n) target ExactEdge (word n)
                hgood]
          exact False.elim (hever ⟨n + 1, hdead⟩)
      let thread : HiddenDescriptorContinuityThread D initialDescriptor
          ExactEdge word := {
        descriptor := descriptor
        initial := hinitial
        exactEdge := fun n => (hstep n).1
        controlStep := fun n => (hstep n).2 }
      have haccepts := hthreads thread
      have hparity := (D.accepts_iff_natSeqMinEvenParity
        thread.childCodeWord).mp haccepts
      have hpriority :
          (fun n => (hiddenDescriptorContinuitySystem D initialDescriptor
            ExactEdge).priority (run n)) =
          fun n => D.priority (D.run thread.childCodeWord n) := by
        funext n
        rw [hlive n]
        change D.priority (descriptor n).control = _
        rw [thread.control_eq_run D initialDescriptor ExactEdge word
          hinitialControl n]
      rw [hpriority]
      exact hparity

end

end DistributedSynthesis
