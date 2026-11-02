/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledEndToEndRecurrentPolicyBank
import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledPolicyBank

/-!
# Finite recurrent handoff below common-policy children

This is the finite assembly boundary after the exceptional first block.  The
originating guarded child is retained as a finite bank index.  Both recurrent
orientations then use the single ordinary policy obtained below that child.
Certificate handoff changes only the orientation and reachable live state;
the origin and policy are definitionally unchanged.
-/

namespace DistributedSynthesis

universe u v x y s

namespace DetParityAutomaton

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable
  (A : DetParityAutomaton.{max u v x y, s}
    (RoundRecord In₁ In₂ Graph Out₁ Out₂))

noncomputable section

variable [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]
variable [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
variable [DecidableEq In₁] [DecidableEq In₂]

/-! ## A bank below a process-one guarded root -/

variable {rightTarget : PairedProfiledTreeState A}
variable {rightOverlap : ProcOneEntryOverlapProfile
  (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁)}
variable {rightGuarded :
  (rightProfiledGuardedAutomaton A rightTarget rightOverlap).RationalTransitionPolicy}

/-- Process-one recurrent macros indexed by the finite child at which the
ordinary common policy began. -/
abbrev EndToEndGuardedRightRecurrentRightMacro :=
  Σ child : EndToEndGuardedRightChild A rightTarget rightOverlap rightGuarded,
    ProfiledPolicyRightMacro A (child.policy A)

/-- Process-two recurrent mirror, under exactly the same child policy. -/
abbrev EndToEndGuardedRightRecurrentLeftMacro :=
  Σ child : EndToEndGuardedRightChild A rightTarget rightOverlap rightGuarded,
    ProfiledPolicyLeftMacro A (child.policy A)

noncomputable instance :
    Fintype (EndToEndGuardedRightRecurrentRightMacro A
      (rightGuarded := rightGuarded)) := by
  classical
  infer_instance

noncomputable instance :
    Fintype (EndToEndGuardedRightRecurrentLeftMacro A
      (rightGuarded := rightGuarded)) := by
  classical
  infer_instance

noncomputable def endToEndGuardedRightRecurrentRightController
    (source : EndToEndGuardedRightRecurrentRightMacro A
      (rightGuarded := rightGuarded)) :=
  profiledPolicyRightController A (source.1.policy A) source.2

noncomputable abbrev endToEndGuardedRightRecurrentRightMonitor
    (source : EndToEndGuardedRightRecurrentRightMacro A
      (rightGuarded := rightGuarded)) :=
  profiledPolicyRightMonitor A (source.1.policy A) source.2

theorem endToEndGuardedRightRecurrentRightController_wins
    (source : EndToEndGuardedRightRecurrentRightMacro A
      (rightGuarded := rightGuarded)) :
    NarrowedAllThreadsWin
      (endToEndGuardedRightRecurrentRightMonitor A source)
      (endToEndGuardedRightRecurrentRightController A source).labeledTree :=
  profiledPolicyRightController_wins A (source.1.policy A) source.2

noncomputable def endToEndGuardedRightRecurrentLeftController
    (source : EndToEndGuardedRightRecurrentLeftMacro A
      (rightGuarded := rightGuarded)) :=
  profiledPolicyLeftController A (source.1.policy A) source.2

noncomputable abbrev endToEndGuardedRightRecurrentLeftMonitor
    (source : EndToEndGuardedRightRecurrentLeftMacro A
      (rightGuarded := rightGuarded)) :=
  profiledPolicyLeftMonitor A (source.1.policy A) source.2

theorem endToEndGuardedRightRecurrentLeftController_wins
    (source : EndToEndGuardedRightRecurrentLeftMacro A
      (rightGuarded := rightGuarded)) :
    NarrowedAllThreadsWin
      (endToEndGuardedRightRecurrentLeftMonitor A source)
      (endToEndGuardedRightRecurrentLeftController A source).labeledTree :=
  profiledPolicyLeftController_wins A (source.1.policy A) source.2

/-- The first checked right close installs the left-oriented root of the
child's restricted policy. -/
def EndToEndGuardedRightChild.recurrentLeftMacroOfClose
    (child : EndToEndGuardedRightChild A rightTarget rightOverlap rightGuarded)
    (scan : PairedRightScanState A) (row : PairedEntryRow)
    (letter : PairedRightBlockLetter
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (herase : erasePairedProfiledState A child.1 =
      pairedRightCloseTarget A scan row letter) :
    EndToEndGuardedRightRecurrentLeftMacro A
      (rightGuarded := rightGuarded) := by
  cases hchild : child.1 with
  | inl trivial =>
      rw [hchild] at herase
      cases row <;>
        simp [erasePairedProfiledState, pairedRightCloseTarget] at herase
  | inr live =>
      cases live with
      | inl rightLive =>
          rw [hchild] at herase
          cases row <;>
            simp [erasePairedProfiledState, pairedRightCloseTarget] at herase
      | inr leftLive =>
          refine ⟨child, leftLive, ?_⟩
          rw [← hchild]
          exact child.reachable A

section
omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] [DecidableEq In₁]
    [DecidableEq In₂]

/-- Re-embedding the first recurrent-left macro recovers the guarded child
at which its ordinary policy starts. -/
theorem EndToEndGuardedRightChild.recurrentLeftMacroOfClose_state
    (child : EndToEndGuardedRightChild A rightTarget rightOverlap rightGuarded)
    (scan : PairedRightScanState A) (row : PairedEntryRow)
    (letter : PairedRightBlockLetter
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (herase : erasePairedProfiledState A child.1 =
      pairedRightCloseTarget A scan row letter) :
    (.inr (.inr
      (child.recurrentLeftMacroOfClose A scan row letter herase).2.1) :
        PairedProfiledTreeState A) = child.1 := by
  rcases child with ⟨childState, hallowed⟩
  cases childState with
  | inl trivial =>
      cases row <;>
        simp [erasePairedProfiledState, pairedRightCloseTarget] at herase
  | inr live =>
      cases live with
      | inl rightLive =>
          cases row <;>
            simp [erasePairedProfiledState, pairedRightCloseTarget] at herase
      | inr leftLive =>
          rfl

/-- The first recurrent macro retains the very same guarded-child index.
This dependent equality is useful when rewriting its restricted policy. -/
theorem EndToEndGuardedRightChild.recurrentLeftMacroOfClose_child
    (child : EndToEndGuardedRightChild A rightTarget rightOverlap rightGuarded)
    (scan : PairedRightScanState A) (row : PairedEntryRow)
    (letter : PairedRightBlockLetter
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (herase : erasePairedProfiledState A child.1 =
      pairedRightCloseTarget A scan row letter) :
    (child.recurrentLeftMacroOfClose A scan row letter herase).1 = child := by
  rcases child with ⟨childState, hallowed⟩
  cases childState with
  | inl trivial =>
      cases row <;>
        simp [erasePairedProfiledState, pairedRightCloseTarget] at herase
  | inr live =>
      cases live with
      | inl rightLive =>
          cases row <;>
            simp [erasePairedProfiledState, pairedRightCloseTarget] at herase
      | inr leftLive =>
          rfl

/-- The staged first recurrent-left macro is the initial root of the policy
indexed by that macro itself.  Stating the result this way avoids any
dependent transport of its child-indexed payload. -/
theorem EndToEndGuardedRightChild.recurrentLeftMacroOfClose_initial
    (child : EndToEndGuardedRightChild A rightTarget rightOverlap rightGuarded)
    (scan : PairedRightScanState A) (row : PairedEntryRow)
    (letter : PairedRightBlockLetter
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (herase : erasePairedProfiledState A child.1 =
      pairedRightCloseTarget A scan row letter) :
    let staged := child.recurrentLeftMacroOfClose A scan row letter herase
    (.inr (.inr staged.2.1) : PairedProfiledTreeState A) =
      (staged.1.policy A).run [] := by
  rcases child with ⟨childState, hallowed⟩
  cases childState with
  | inl trivial =>
      cases row <;>
        simp [erasePairedProfiledState, pairedRightCloseTarget] at herase
  | inr live =>
      cases live with
      | inl rightLive =>
          cases row <;>
            simp [erasePairedProfiledState, pairedRightCloseTarget] at herase
      | inr leftLive =>
          simpa [EndToEndGuardedRightChild.recurrentLeftMacroOfClose] using
            (EndToEndGuardedRightChild.policy A
              (⟨.inr (.inr leftLive), hallowed⟩ :
                EndToEndGuardedRightChild A rightTarget rightOverlap
                  rightGuarded)).accepts.1.1.symm

/-- The first right close preserves the live left root profile carried by
the checked child. -/
theorem EndToEndGuardedRightChild.recurrentLeftMacroOfClose_profile_of_eq
    (child : EndToEndGuardedRightChild A rightTarget rightOverlap rightGuarded)
    (live : (((A.State × A.State) × A.State) ×
      LeftInitialActionProfile
        (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁)))
    (scan : PairedRightScanState A) (row : PairedEntryRow)
    (letter : PairedRightBlockLetter
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (htarget : child.1 = .inr (.inr live))
    (herase : erasePairedProfiledState A child.1 =
      pairedRightCloseTarget A scan row letter) :
    (child.recurrentLeftMacroOfClose A scan row letter herase).2.1.2 =
      live.2 := by
  rcases child with ⟨target, allowed⟩
  change target = .inr (.inr live) at htarget
  subst target
  rfl

end

/-- A later right close stays below the same finite child and common policy. -/
def endToEndGuardedRightRecurrentLeftOfRightCertificate
    (source : EndToEndGuardedRightRecurrentRightMacro A
      (rightGuarded := rightGuarded))
    (target : PairedProfiledTreeState A)
    (scan : PairedRightScanState A) (row : PairedEntryRow)
    (letter : PairedRightBlockLetter
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (herase : erasePairedProfiledState A target =
      pairedRightCloseTarget A scan row letter)
    (hallowed : PairedProfiledRationalPolicy.Allowed A (source.1.policy A)
      (.inr (.inl source.2.1)) target) :
    EndToEndGuardedRightRecurrentLeftMacro A
      (rightGuarded := rightGuarded) :=
  ⟨source.1, profiledPolicyLeftMacroOfRightCertificate A
    (source.1.policy A) source.2 target scan row letter herase hallowed⟩

/-- A later left close stays below the same finite child and common policy. -/
def endToEndGuardedRightRecurrentRightOfLeftCertificate
    (source : EndToEndGuardedRightRecurrentLeftMacro A
      (rightGuarded := rightGuarded))
    (target : PairedProfiledTreeState A)
    (scan : PairedLeftScanState A) (row : PairedEntryRow)
    (letter : PairedLeftBlockLetter
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (herase : erasePairedProfiledState A target =
      pairedLeftCloseTarget A scan row letter)
    (hallowed : PairedProfiledRationalPolicy.Allowed A (source.1.policy A)
      (.inr (.inr source.2.1)) target) :
    EndToEndGuardedRightRecurrentRightMacro A
      (rightGuarded := rightGuarded) :=
  ⟨source.1, profiledPolicyRightMacroOfLeftCertificate A
    (source.1.policy A) source.2 target scan row letter herase hallowed⟩

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] [DecidableEq In₁]
    [DecidableEq In₂] in
@[simp] theorem endToEndGuardedRightRecurrentLeftOfRightCertificate_child
    (source : EndToEndGuardedRightRecurrentRightMacro A
      (rightGuarded := rightGuarded))
    (target : PairedProfiledTreeState A)
    (scan : PairedRightScanState A) (row : PairedEntryRow)
    (letter : PairedRightBlockLetter
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (herase : erasePairedProfiledState A target =
      pairedRightCloseTarget A scan row letter)
    (hallowed : PairedProfiledRationalPolicy.Allowed A (source.1.policy A)
      (.inr (.inl source.2.1)) target) :
    (endToEndGuardedRightRecurrentLeftOfRightCertificate A source target scan
      row letter herase hallowed).1 = source.1 := rfl

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] [DecidableEq In₁]
    [DecidableEq In₂] in
@[simp] theorem endToEndGuardedRightRecurrentRightOfLeftCertificate_child
    (source : EndToEndGuardedRightRecurrentLeftMacro A
      (rightGuarded := rightGuarded))
    (target : PairedProfiledTreeState A)
    (scan : PairedLeftScanState A) (row : PairedEntryRow)
    (letter : PairedLeftBlockLetter
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (herase : erasePairedProfiledState A target =
      pairedLeftCloseTarget A scan row letter)
    (hallowed : PairedProfiledRationalPolicy.Allowed A (source.1.policy A)
      (.inr (.inr source.2.1)) target) :
    (endToEndGuardedRightRecurrentRightOfLeftCertificate A source target scan
      row letter herase hallowed).1 = source.1 := rfl

/-! ## Mirror bank below a process-two guarded root -/

variable {leftTarget : PairedProfiledTreeState A}
variable {leftOverlap : ProcTwoEntryOverlapProfile
  (In₁ := In₁) (In₂ := In₂) (Out₂ := Out₂)}
variable {leftGuarded :
  (leftProfiledGuardedAutomaton A leftTarget leftOverlap).RationalTransitionPolicy}

abbrev EndToEndGuardedLeftRecurrentRightMacro :=
  Σ child : EndToEndGuardedLeftChild A leftTarget leftOverlap leftGuarded,
    ProfiledPolicyRightMacro A (child.policy A)

abbrev EndToEndGuardedLeftRecurrentLeftMacro :=
  Σ child : EndToEndGuardedLeftChild A leftTarget leftOverlap leftGuarded,
    ProfiledPolicyLeftMacro A (child.policy A)

noncomputable instance :
    Fintype (EndToEndGuardedLeftRecurrentRightMacro A
      (leftGuarded := leftGuarded)) := by
  classical
  infer_instance

noncomputable instance :
    Fintype (EndToEndGuardedLeftRecurrentLeftMacro A
      (leftGuarded := leftGuarded)) := by
  classical
  infer_instance

noncomputable def endToEndGuardedLeftRecurrentRightController
    (source : EndToEndGuardedLeftRecurrentRightMacro A
      (leftGuarded := leftGuarded)) :=
  profiledPolicyRightController A (source.1.policy A) source.2

noncomputable abbrev endToEndGuardedLeftRecurrentRightMonitor
    (source : EndToEndGuardedLeftRecurrentRightMacro A
      (leftGuarded := leftGuarded)) :=
  profiledPolicyRightMonitor A (source.1.policy A) source.2

theorem endToEndGuardedLeftRecurrentRightController_wins
    (source : EndToEndGuardedLeftRecurrentRightMacro A
      (leftGuarded := leftGuarded)) :
    NarrowedAllThreadsWin
      (endToEndGuardedLeftRecurrentRightMonitor A source)
      (endToEndGuardedLeftRecurrentRightController A source).labeledTree :=
  profiledPolicyRightController_wins A (source.1.policy A) source.2

noncomputable def endToEndGuardedLeftRecurrentLeftController
    (source : EndToEndGuardedLeftRecurrentLeftMacro A
      (leftGuarded := leftGuarded)) :=
  profiledPolicyLeftController A (source.1.policy A) source.2

noncomputable abbrev endToEndGuardedLeftRecurrentLeftMonitor
    (source : EndToEndGuardedLeftRecurrentLeftMacro A
      (leftGuarded := leftGuarded)) :=
  profiledPolicyLeftMonitor A (source.1.policy A) source.2

theorem endToEndGuardedLeftRecurrentLeftController_wins
    (source : EndToEndGuardedLeftRecurrentLeftMacro A
      (leftGuarded := leftGuarded)) :
    NarrowedAllThreadsWin
      (endToEndGuardedLeftRecurrentLeftMonitor A source)
      (endToEndGuardedLeftRecurrentLeftController A source).labeledTree :=
  profiledPolicyLeftController_wins A (source.1.policy A) source.2

/-- The first checked left close installs the right-oriented root of the
child's restricted policy. -/
def EndToEndGuardedLeftChild.recurrentRightMacroOfClose
    (child : EndToEndGuardedLeftChild A leftTarget leftOverlap leftGuarded)
    (scan : PairedLeftScanState A) (row : PairedEntryRow)
    (letter : PairedLeftBlockLetter
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (herase : erasePairedProfiledState A child.1 =
      pairedLeftCloseTarget A scan row letter) :
    EndToEndGuardedLeftRecurrentRightMacro A
      (leftGuarded := leftGuarded) := by
  cases hchild : child.1 with
  | inl trivial =>
      rw [hchild] at herase
      cases row <;>
        simp [erasePairedProfiledState, pairedLeftCloseTarget] at herase
  | inr live =>
      cases live with
      | inl rightLive =>
          refine ⟨child, rightLive, ?_⟩
          rw [← hchild]
          exact child.reachable A
      | inr leftLive =>
          rw [hchild] at herase
          cases row <;>
            simp [erasePairedProfiledState, pairedLeftCloseTarget] at herase

section
omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] [DecidableEq In₁]
    [DecidableEq In₂]

/-- Process-swapped initial-state identity for the first recurrent-right
macro below a guarded child. -/
theorem EndToEndGuardedLeftChild.recurrentRightMacroOfClose_state
    (child : EndToEndGuardedLeftChild A leftTarget leftOverlap leftGuarded)
    (scan : PairedLeftScanState A) (row : PairedEntryRow)
    (letter : PairedLeftBlockLetter
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (herase : erasePairedProfiledState A child.1 =
      pairedLeftCloseTarget A scan row letter) :
    (.inr (.inl
      (child.recurrentRightMacroOfClose A scan row letter herase).2.1) :
        PairedProfiledTreeState A) = child.1 := by
  rcases child with ⟨childState, hallowed⟩
  cases childState with
  | inl trivial =>
      cases row <;>
        simp [erasePairedProfiledState, pairedLeftCloseTarget] at herase
  | inr live =>
      cases live with
      | inl rightLive =>
          rfl
      | inr leftLive =>
          cases row <;>
            simp [erasePairedProfiledState, pairedLeftCloseTarget] at herase

/-- Process-swapped guarded-child index preservation. -/
theorem EndToEndGuardedLeftChild.recurrentRightMacroOfClose_child
    (child : EndToEndGuardedLeftChild A leftTarget leftOverlap leftGuarded)
    (scan : PairedLeftScanState A) (row : PairedEntryRow)
    (letter : PairedLeftBlockLetter
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (herase : erasePairedProfiledState A child.1 =
      pairedLeftCloseTarget A scan row letter) :
    (child.recurrentRightMacroOfClose A scan row letter herase).1 = child := by
  rcases child with ⟨childState, hallowed⟩
  cases childState with
  | inl trivial =>
      cases row <;>
        simp [erasePairedProfiledState, pairedLeftCloseTarget] at herase
  | inr live =>
      cases live with
      | inl rightLive =>
          rfl
      | inr leftLive =>
          cases row <;>
            simp [erasePairedProfiledState, pairedLeftCloseTarget] at herase

/-- Process-swapped initial-root identity, indexed by the staged macro. -/
theorem EndToEndGuardedLeftChild.recurrentRightMacroOfClose_initial
    (child : EndToEndGuardedLeftChild A leftTarget leftOverlap leftGuarded)
    (scan : PairedLeftScanState A) (row : PairedEntryRow)
    (letter : PairedLeftBlockLetter
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (herase : erasePairedProfiledState A child.1 =
      pairedLeftCloseTarget A scan row letter) :
    let staged := child.recurrentRightMacroOfClose A scan row letter herase
    (.inr (.inl staged.2.1) : PairedProfiledTreeState A) =
      (staged.1.policy A).run [] := by
  rcases child with ⟨childState, hallowed⟩
  cases childState with
  | inl trivial =>
      cases row <;>
        simp [erasePairedProfiledState, pairedLeftCloseTarget] at herase
  | inr live =>
      cases live with
      | inl rightLive =>
          simpa [EndToEndGuardedLeftChild.recurrentRightMacroOfClose] using
            (EndToEndGuardedLeftChild.policy A
              (⟨.inr (.inl rightLive), hallowed⟩ :
                EndToEndGuardedLeftChild A leftTarget leftOverlap
                  leftGuarded)).accepts.1.1.symm
      | inr leftLive =>
          cases row <;>
            simp [erasePairedProfiledState, pairedLeftCloseTarget] at herase

/-- Process-swapped profile preservation at the first left close. -/
theorem EndToEndGuardedLeftChild.recurrentRightMacroOfClose_profile_of_eq
    (child : EndToEndGuardedLeftChild A leftTarget leftOverlap leftGuarded)
    (live : (((A.State × A.State) × A.State) ×
      RightInitialActionProfile
        (In₁ := In₁) (In₂ := In₂) (Out₂ := Out₂)))
    (scan : PairedLeftScanState A) (row : PairedEntryRow)
    (letter : PairedLeftBlockLetter
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (htarget : child.1 = .inr (.inl live))
    (herase : erasePairedProfiledState A child.1 =
      pairedLeftCloseTarget A scan row letter) :
    (child.recurrentRightMacroOfClose A scan row letter herase).2.1.2 =
      live.2 := by
  rcases child with ⟨target, allowed⟩
  change target = .inr (.inl live) at htarget
  subst target
  rfl

end

def endToEndGuardedLeftRecurrentLeftOfRightCertificate
    (source : EndToEndGuardedLeftRecurrentRightMacro A
      (leftGuarded := leftGuarded))
    (target : PairedProfiledTreeState A)
    (scan : PairedRightScanState A) (row : PairedEntryRow)
    (letter : PairedRightBlockLetter
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (herase : erasePairedProfiledState A target =
      pairedRightCloseTarget A scan row letter)
    (hallowed : PairedProfiledRationalPolicy.Allowed A (source.1.policy A)
      (.inr (.inl source.2.1)) target) :
    EndToEndGuardedLeftRecurrentLeftMacro A
      (leftGuarded := leftGuarded) :=
  ⟨source.1, profiledPolicyLeftMacroOfRightCertificate A
    (source.1.policy A) source.2 target scan row letter herase hallowed⟩

def endToEndGuardedLeftRecurrentRightOfLeftCertificate
    (source : EndToEndGuardedLeftRecurrentLeftMacro A
      (leftGuarded := leftGuarded))
    (target : PairedProfiledTreeState A)
    (scan : PairedLeftScanState A) (row : PairedEntryRow)
    (letter : PairedLeftBlockLetter
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (herase : erasePairedProfiledState A target =
      pairedLeftCloseTarget A scan row letter)
    (hallowed : PairedProfiledRationalPolicy.Allowed A (source.1.policy A)
      (.inr (.inr source.2.1)) target) :
    EndToEndGuardedLeftRecurrentRightMacro A
      (leftGuarded := leftGuarded) :=
  ⟨source.1, profiledPolicyRightMacroOfLeftCertificate A
    (source.1.policy A) source.2 target scan row letter herase hallowed⟩

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] [DecidableEq In₁]
    [DecidableEq In₂] in
@[simp] theorem endToEndGuardedLeftRecurrentLeftOfRightCertificate_child
    (source : EndToEndGuardedLeftRecurrentRightMacro A
      (leftGuarded := leftGuarded))
    (target : PairedProfiledTreeState A)
    (scan : PairedRightScanState A) (row : PairedEntryRow)
    (letter : PairedRightBlockLetter
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (herase : erasePairedProfiledState A target =
      pairedRightCloseTarget A scan row letter)
    (hallowed : PairedProfiledRationalPolicy.Allowed A (source.1.policy A)
      (.inr (.inl source.2.1)) target) :
    (endToEndGuardedLeftRecurrentLeftOfRightCertificate A source target scan
      row letter herase hallowed).1 = source.1 := rfl

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] [DecidableEq In₁]
    [DecidableEq In₂] in
@[simp] theorem endToEndGuardedLeftRecurrentRightOfLeftCertificate_child
    (source : EndToEndGuardedLeftRecurrentLeftMacro A
      (leftGuarded := leftGuarded))
    (target : PairedProfiledTreeState A)
    (scan : PairedLeftScanState A) (row : PairedEntryRow)
    (letter : PairedLeftBlockLetter
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (herase : erasePairedProfiledState A target =
      pairedLeftCloseTarget A scan row letter)
    (hallowed : PairedProfiledRationalPolicy.Allowed A (source.1.policy A)
      (.inr (.inr source.2.1)) target) :
    (endToEndGuardedLeftRecurrentRightOfLeftCertificate A source target scan
      row letter herase hallowed).1 = source.1 := rfl

end


end DetParityAutomaton

end DistributedSynthesis
