/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridRootPinnedMacroControl
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridMegaFrontPhase

/-!
# Honest finite front state for the root-pinned hybrid carrier

The generic carrier starts from a `Unit` root control.  On the first physical
simultaneous receive, each process learns the first input pair, but there is
not yet a second pair from which to form a
`ProfiledRawJointInitialCommonBothKey = (first, current)`.

There are two exact intermediate controls.  A process that receives retains
the initial local shadow, which contains the common candidate indexed by
`first` and the old strict-root cross.  A process that is blind in the first
strict round cannot yet know the full input pair, so it retains the old
initial owner control instead.  This file inserts both finite phases into the
root-pinned control shape.  Its exceptional state is

```
  OldInitial ⊕ (InitialShadow ⊕ (first, current)).
```

The maps below are constructors and projections only.  They do not define a
complete kernel transition table, and none takes a graph, orientation, or
leader signal.  In particular, the old blind summand has no total projection
to a full first input pair; the corresponding observation below returns
`none` rather than inserting a default partner input.
-/

namespace DistributedSynthesis

universe u v x y s

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
  (controllers : ProfiledRawJointRootCompatibleInitialControllers A strategy)
  (initialBank : ProfiledRawJointInitialControllerBank A strategy)

/-! ## The missing finite exceptional phase -/

/-- Process one's exact post-root shadow, followed by the already-existing
two-pair ambiguity key after the next receive. -/
abbrev ProfiledRawJointHybridRootPinnedFrontExceptionalOne :=
  ProfiledRawJointHybridMegaOldInitialOne A strategy hwin controllers
      initialBank ⊕
    (ProfiledRawJointHybridInitialOneShadow A strategy hwin controllers ⊕
      ProfiledRawJointHybridRootPinnedExceptionalOne
        (In₁ := In₁) (In₂ := In₂))

/-- Process-two mirror. -/
abbrev ProfiledRawJointHybridRootPinnedFrontExceptionalTwo :=
  ProfiledRawJointHybridMegaOldInitialTwo A strategy hwin controllers
      initialBank ⊕
    (ProfiledRawJointHybridInitialTwoShadow A strategy hwin controllers ⊕
      ProfiledRawJointHybridRootPinnedExceptionalTwo
        (In₁ := In₁) (In₂ := In₂))

noncomputable instance
    profiledRawJointHybridRootPinnedFrontExceptionalOneFintype :
    Fintype
      (ProfiledRawJointHybridRootPinnedFrontExceptionalOne A strategy hwin
        controllers initialBank) := by
  classical
  infer_instance

noncomputable instance
    profiledRawJointHybridRootPinnedFrontExceptionalTwoFintype :
    Fintype
      (ProfiledRawJointHybridRootPinnedFrontExceptionalTwo A strategy hwin
        controllers initialBank) := by
  classical
  infer_instance

/-- Root-pinned process-one control with the honest shadow phase inserted. -/
abbrev ProfiledRawJointHybridRootPinnedFrontOneControl :=
  ProfiledRawJointLeaderFreeOneControl
    (ProfiledRawJointHybridRootPinnedInitialOne)
    (ProfiledRawJointHybridRootPinnedFrontExceptionalOne A strategy hwin
      controllers initialBank)
    (ProfiledRawJointHybridRootPinnedChildCode A strategy hwin)
    (ProfiledRawJointHybridRootPinnedRightMacro A strategy hwin)
    (ProfiledRawJointHybridRootPinnedLeftMacro A strategy hwin)

/-- Process-two mirror. -/
abbrev ProfiledRawJointHybridRootPinnedFrontTwoControl :=
  ProfiledRawJointLeaderFreeTwoControl
    (ProfiledRawJointHybridRootPinnedInitialTwo)
    (ProfiledRawJointHybridRootPinnedFrontExceptionalTwo A strategy hwin
      controllers initialBank)
    (ProfiledRawJointHybridRootPinnedChildCode A strategy hwin)
    (ProfiledRawJointHybridRootPinnedRightMacro A strategy hwin)
    (ProfiledRawJointHybridRootPinnedLeftMacro A strategy hwin)

noncomputable instance profiledRawJointHybridRootPinnedFrontOneControlFintype :
    Fintype
      (ProfiledRawJointHybridRootPinnedFrontOneControl A strategy hwin
        controllers initialBank) := by
  classical
  infer_instance

noncomputable instance profiledRawJointHybridRootPinnedFrontTwoControlFintype :
    Fintype
      (ProfiledRawJointHybridRootPinnedFrontTwoControl A strategy hwin
        controllers initialBank) := by
  classical
  infer_instance

/-! ## Named injections -/

def profiledRawJointHybridRootPinnedFrontInitialOneControl :
    ProfiledRawJointHybridRootPinnedFrontOneControl A strategy hwin
      controllers initialBank :=
  .initial ()

def profiledRawJointHybridRootPinnedFrontInitialTwoControl :
    ProfiledRawJointHybridRootPinnedFrontTwoControl A strategy hwin
      controllers initialBank :=
  .initial ()

/-- Embed an honest old process-one initial control.  This is the branch used
when process one is blind in the first strict round. -/
def profiledRawJointHybridRootPinnedFrontExceptionalOneOfOld
    (old : ProfiledRawJointHybridMegaOldInitialOne A strategy hwin controllers
      initialBank) :
    ProfiledRawJointHybridRootPinnedFrontExceptionalOne A strategy hwin
      controllers initialBank :=
  .inl old

/-- Process-two mirror. -/
def profiledRawJointHybridRootPinnedFrontExceptionalTwoOfOld
    (old : ProfiledRawJointHybridMegaOldInitialTwo A strategy hwin controllers
      initialBank) :
    ProfiledRawJointHybridRootPinnedFrontExceptionalTwo A strategy hwin
      controllers initialBank :=
  .inl old

def profiledRawJointHybridRootPinnedFrontExceptionalOneOfShadow
    (shadow : ProfiledRawJointHybridInitialOneShadow A strategy hwin
      controllers) :
    ProfiledRawJointHybridRootPinnedFrontExceptionalOne A strategy hwin
      controllers initialBank :=
  .inr (.inl shadow)

def profiledRawJointHybridRootPinnedFrontExceptionalTwoOfShadow
    (shadow : ProfiledRawJointHybridInitialTwoShadow A strategy hwin
      controllers) :
    ProfiledRawJointHybridRootPinnedFrontExceptionalTwo A strategy hwin
      controllers initialBank :=
  .inr (.inl shadow)

def profiledRawJointHybridRootPinnedFrontExceptionalOneOfKey
    (key : ProfiledRawJointHybridRootPinnedExceptionalOne
      (In₁ := In₁) (In₂ := In₂)) :
    ProfiledRawJointHybridRootPinnedFrontExceptionalOne A strategy hwin
      controllers initialBank :=
  .inr (.inr key)

def profiledRawJointHybridRootPinnedFrontExceptionalTwoOfKey
    (key : ProfiledRawJointHybridRootPinnedExceptionalTwo
      (In₁ := In₁) (In₂ := In₂)) :
    ProfiledRawJointHybridRootPinnedFrontExceptionalTwo A strategy hwin
      controllers initialBank :=
  .inr (.inr key)

/-- Embed an old process-one initial control in the complete front control. -/
def profiledRawJointHybridRootPinnedFrontOneOldControl
    (old : ProfiledRawJointHybridMegaOldInitialOne A strategy hwin controllers
      initialBank) :
    ProfiledRawJointHybridRootPinnedFrontOneControl A strategy hwin controllers
      initialBank :=
  .exceptional
    (profiledRawJointHybridRootPinnedFrontExceptionalOneOfOld A strategy hwin
      controllers initialBank old)

/-- Process-two mirror. -/
def profiledRawJointHybridRootPinnedFrontTwoOldControl
    (old : ProfiledRawJointHybridMegaOldInitialTwo A strategy hwin controllers
      initialBank) :
    ProfiledRawJointHybridRootPinnedFrontTwoControl A strategy hwin controllers
      initialBank :=
  .exceptional
    (profiledRawJointHybridRootPinnedFrontExceptionalTwoOfOld A strategy hwin
      controllers initialBank old)

def profiledRawJointHybridRootPinnedFrontOneShadowControl
    (shadow : ProfiledRawJointHybridInitialOneShadow A strategy hwin
      controllers) :
    ProfiledRawJointHybridRootPinnedFrontOneControl A strategy hwin
      controllers initialBank :=
  .exceptional
    (profiledRawJointHybridRootPinnedFrontExceptionalOneOfShadow A strategy
      hwin controllers initialBank shadow)

def profiledRawJointHybridRootPinnedFrontTwoShadowControl
    (shadow : ProfiledRawJointHybridInitialTwoShadow A strategy hwin
      controllers) :
    ProfiledRawJointHybridRootPinnedFrontTwoControl A strategy hwin
      controllers initialBank :=
  .exceptional
    (profiledRawJointHybridRootPinnedFrontExceptionalTwoOfShadow A strategy
      hwin controllers initialBank shadow)

def profiledRawJointHybridRootPinnedFrontOneKeyControl
    (key : ProfiledRawJointHybridRootPinnedExceptionalOne
      (In₁ := In₁) (In₂ := In₂)) :
    ProfiledRawJointHybridRootPinnedFrontOneControl A strategy hwin
      controllers initialBank :=
  .exceptional
    (profiledRawJointHybridRootPinnedFrontExceptionalOneOfKey A strategy hwin
      controllers initialBank key)

def profiledRawJointHybridRootPinnedFrontTwoKeyControl
    (key : ProfiledRawJointHybridRootPinnedExceptionalTwo
      (In₁ := In₁) (In₂ := In₂)) :
    ProfiledRawJointHybridRootPinnedFrontTwoControl A strategy hwin
      controllers initialBank :=
  .exceptional
    (profiledRawJointHybridRootPinnedFrontExceptionalTwoOfKey A strategy hwin
      controllers initialBank key)

/-! ## Exact first physical receive -/

/-- Process one's root non-receive uses only its own input and retains the
actual blind initial-right owner control.  In particular, it does not choose
a full outer first-input index. -/
noncomputable def profiledRawJointHybridRootPinnedFrontRootNoRecvOne
    (input : In₁) :
    Out₁ ×
      ProfiledRawJointHybridRootPinnedFrontOneControl A strategy hwin
        controllers initialBank :=
  let next := stepProfiledRawJointRootRightOwner A strategy controllers
    (profiledRawJointInitialRightOwnerInitial A strategy controllers) input
  (next.1,
    profiledRawJointHybridRootPinnedFrontOneOldControl A strategy hwin
      controllers initialBank (.inl next.2))

/-- Process-two mirror: the blind initial-left owner is the second summand of
the old process-two front. -/
noncomputable def profiledRawJointHybridRootPinnedFrontRootNoRecvTwo
    (input : In₂) :
    Out₂ ×
      ProfiledRawJointHybridRootPinnedFrontTwoControl A strategy hwin
        controllers initialBank :=
  let next := stepProfiledRawJointRootLeftOwner A strategy controllers
    (profiledRawJointInitialLeftOwnerInitial A strategy controllers) input
  (next.1,
    profiledRawJointHybridRootPinnedFrontTwoOldControl A strategy hwin
      controllers initialBank (.inr (.inl next.2)))

section
omit [Inhabited Out₁] [Inhabited Out₂]

@[simp] theorem profiledRawJointHybridRootPinnedFrontRootNoRecvOne_control
    (input : In₁) :
    (profiledRawJointHybridRootPinnedFrontRootNoRecvOne A strategy hwin
      controllers initialBank input).2 =
      profiledRawJointHybridRootPinnedFrontOneOldControl A strategy hwin
        controllers initialBank
        (.inl
          (stepProfiledRawJointRootRightOwner A strategy controllers
            (profiledRawJointInitialRightOwnerInitial A strategy controllers)
            input).2) :=
  rfl

@[simp] theorem profiledRawJointHybridRootPinnedFrontRootNoRecvTwo_control
    (input : In₂) :
    (profiledRawJointHybridRootPinnedFrontRootNoRecvTwo A strategy hwin
      controllers initialBank input).2 =
      profiledRawJointHybridRootPinnedFrontTwoOldControl A strategy hwin
        controllers initialBank
        (.inr
          (.inl
            (stepProfiledRawJointRootLeftOwner A strategy controllers
              (profiledRawJointInitialLeftOwnerInitial A strategy controllers)
              input).2)) :=
  rfl

@[simp] theorem profiledRawJointHybridRootPinnedFrontRootNoRecvOne_output
    (input : In₁) :
    (profiledRawJointHybridRootPinnedFrontRootNoRecvOne A strategy hwin
      controllers initialBank input).1 =
      (stepProfiledRawJointRootRightOwner A strategy controllers
        (profiledRawJointInitialRightOwnerInitial A strategy controllers)
        input).1 :=
  rfl

@[simp] theorem profiledRawJointHybridRootPinnedFrontRootNoRecvTwo_output
    (input : In₂) :
    (profiledRawJointHybridRootPinnedFrontRootNoRecvTwo A strategy hwin
      controllers initialBank input).1 =
      (stepProfiledRawJointRootLeftOwner A strategy controllers
        (profiledRawJointInitialLeftOwnerInitial A strategy controllers)
        input).1 :=
  rfl

end

/-- Process one's root receive retains the exact existing local shadow.  Its
arguments are precisely its own input and the delivered partner input. -/
noncomputable def profiledRawJointHybridRootPinnedFrontRootRecvOne
    (own : In₁) (delivered : In₂) :
    Out₁ ×
      ProfiledRawJointHybridRootPinnedFrontOneControl A strategy hwin
        controllers initialBank :=
  let next := profiledRawJointHybridInitialRootRecvOne A strategy hwin
    controllers (own, delivered)
  (next.1,
    profiledRawJointHybridRootPinnedFrontOneShadowControl A strategy hwin
      controllers initialBank next.2)

/-- Process-two mirror, with the delivered process-one input restored to the
first coordinate of the common pair. -/
noncomputable def profiledRawJointHybridRootPinnedFrontRootRecvTwo
    (own : In₂) (delivered : In₁) :
    Out₂ ×
      ProfiledRawJointHybridRootPinnedFrontTwoControl A strategy hwin
        controllers initialBank :=
  let next := profiledRawJointHybridInitialRootRecvTwo A strategy hwin
    controllers (delivered, own)
  (next.1,
    profiledRawJointHybridRootPinnedFrontTwoShadowControl A strategy hwin
      controllers initialBank next.2)

section
omit [Inhabited Out₁] [Inhabited Out₂]

@[simp] theorem profiledRawJointHybridRootPinnedFrontRootRecvOne_control
    (own : In₁) (delivered : In₂) :
    (profiledRawJointHybridRootPinnedFrontRootRecvOne A strategy hwin
      controllers initialBank own delivered).2 =
      profiledRawJointHybridRootPinnedFrontOneShadowControl A strategy hwin
        controllers initialBank
        (profiledRawJointHybridInitialRootRecvOne A strategy hwin controllers
          (own, delivered)).2 :=
  rfl

@[simp] theorem profiledRawJointHybridRootPinnedFrontRootRecvTwo_control
    (own : In₂) (delivered : In₁) :
    (profiledRawJointHybridRootPinnedFrontRootRecvTwo A strategy hwin
      controllers initialBank own delivered).2 =
      profiledRawJointHybridRootPinnedFrontTwoShadowControl A strategy hwin
        controllers initialBank
        (profiledRawJointHybridInitialRootRecvTwo A strategy hwin controllers
          (delivered, own)).2 :=
  rfl

@[simp] theorem profiledRawJointHybridRootPinnedFrontRootRecvOne_output
    (own : In₁) (delivered : In₂) :
    (profiledRawJointHybridRootPinnedFrontRootRecvOne A strategy hwin
      controllers initialBank own delivered).1 =
      (profiledRawJointHybridInitialRootRecvOne A strategy hwin controllers
        (own, delivered)).1 :=
  rfl

@[simp] theorem profiledRawJointHybridRootPinnedFrontRootRecvTwo_output
    (own : In₂) (delivered : In₁) :
    (profiledRawJointHybridRootPinnedFrontRootRecvTwo A strategy hwin
      controllers initialBank own delivered).1 =
      (profiledRawJointHybridInitialRootRecvTwo A strategy hwin controllers
        (delivered, own)).1 :=
  rfl

/-- The paired root receives retain the literal first-round output. -/
theorem profiledRawJointHybridRootPinnedFrontRootRecv_outputs_eq_literalBoth
    (first : In₁ × In₂) :
    ((profiledRawJointHybridRootPinnedFrontRootRecvOne A strategy hwin
        controllers initialBank first.1 first.2).1,
      (profiledRawJointHybridRootPinnedFrontRootRecvTwo A strategy hwin
        controllers initialBank first.2 first.1).1) =
      let round := nextRound strategy []
        ⟨first.1, first.2, Graph.both⟩
      (round.outputOne, round.outputTwo) := by
  exact profiledRawJointHybridInitialRootRecv_outputs_eq_literalBoth A strategy
    hwin controllers first

end

/-! ## Retained first pair and the next local receive -/

/-- Observe the exact first pair only after it has genuinely become locally
available.  The old blind-owner branch returns `none`; no default partner
input is inserted. -/
def profiledRawJointHybridRootPinnedFrontExceptionalOneFirst :
    ProfiledRawJointHybridRootPinnedFrontExceptionalOne A strategy hwin
        controllers initialBank →
      Option (In₁ × In₂)
  | .inl _ => none
  | .inr (.inl shadow) => some shadow.common.1
  | .inr (.inr key) => some key.1

/-- Process-two mirror. -/
def profiledRawJointHybridRootPinnedFrontExceptionalTwoFirst :
    ProfiledRawJointHybridRootPinnedFrontExceptionalTwo A strategy hwin
        controllers initialBank →
      Option (In₁ × In₂)
  | .inl _ => none
  | .inr (.inl shadow) => some shadow.common.1
  | .inr (.inr key) => some key.1

section
omit [Inhabited Out₁] [Inhabited Out₂]

@[simp] theorem
    profiledRawJointHybridRootPinnedFrontExceptionalOneFirst_old
    (old : ProfiledRawJointHybridMegaOldInitialOne A strategy hwin controllers
      initialBank) :
    profiledRawJointHybridRootPinnedFrontExceptionalOneFirst A strategy hwin
        controllers initialBank (.inl old) =
      none :=
  rfl

@[simp] theorem
    profiledRawJointHybridRootPinnedFrontExceptionalTwoFirst_old
    (old : ProfiledRawJointHybridMegaOldInitialTwo A strategy hwin controllers
      initialBank) :
    profiledRawJointHybridRootPinnedFrontExceptionalTwoFirst A strategy hwin
        controllers initialBank (.inl old) =
      none :=
  rfl

@[simp] theorem
    profiledRawJointHybridRootPinnedFrontExceptionalOneFirst_shadow
    (shadow : ProfiledRawJointHybridInitialOneShadow A strategy hwin
      controllers) :
    profiledRawJointHybridRootPinnedFrontExceptionalOneFirst A strategy hwin
        controllers initialBank (.inr (.inl shadow)) =
      some shadow.common.1 :=
  rfl

@[simp] theorem
    profiledRawJointHybridRootPinnedFrontExceptionalTwoFirst_shadow
    (shadow : ProfiledRawJointHybridInitialTwoShadow A strategy hwin
      controllers) :
    profiledRawJointHybridRootPinnedFrontExceptionalTwoFirst A strategy hwin
        controllers initialBank (.inr (.inl shadow)) =
      some shadow.common.1 :=
  rfl

@[simp] theorem
    profiledRawJointHybridRootPinnedFrontExceptionalOneFirst_key
    (key : ProfiledRawJointHybridRootPinnedExceptionalOne
      (In₁ := In₁) (In₂ := In₂)) :
    profiledRawJointHybridRootPinnedFrontExceptionalOneFirst A strategy hwin
        controllers initialBank (.inr (.inr key)) =
      some key.1 :=
  rfl

@[simp] theorem
    profiledRawJointHybridRootPinnedFrontExceptionalTwoFirst_key
    (key : ProfiledRawJointHybridRootPinnedExceptionalTwo
      (In₁ := In₁) (In₂ := In₂)) :
    profiledRawJointHybridRootPinnedFrontExceptionalTwoFirst A strategy hwin
        controllers initialBank (.inr (.inr key)) =
      some key.1 :=
  rfl

end

/-- Process one forms the honest two-pair key only at its following receive. -/
def profiledRawJointHybridRootPinnedFrontOneKeyOfReceive
    (shadow : ProfiledRawJointHybridInitialOneShadow A strategy hwin
      controllers)
    (own : In₁) (delivered : In₂) :
    ProfiledRawJointHybridRootPinnedExceptionalOne
      (In₁ := In₁) (In₂ := In₂) :=
  profiledRawJointInitialCommonBothKeyOfOneReceive shadow.common.1 own delivered

/-- Process-two mirror. -/
def profiledRawJointHybridRootPinnedFrontTwoKeyOfReceive
    (shadow : ProfiledRawJointHybridInitialTwoShadow A strategy hwin
      controllers)
    (own : In₂) (delivered : In₁) :
    ProfiledRawJointHybridRootPinnedExceptionalTwo
      (In₁ := In₁) (In₂ := In₂) :=
  profiledRawJointInitialCommonBothKeyOfTwoReceive shadow.common.1 own delivered

section
omit [Inhabited Out₁] [Inhabited Out₂]

@[simp] theorem profiledRawJointHybridRootPinnedFrontRootRecvOne_retains_first
    (first : In₁ × In₂) :
    let shadow :=
      (profiledRawJointHybridInitialRootRecvOne A strategy hwin controllers
        first).2
    shadow.common.1 = first :=
  rfl

@[simp] theorem profiledRawJointHybridRootPinnedFrontRootRecvTwo_retains_first
    (first : In₁ × In₂) :
    let shadow :=
      (profiledRawJointHybridInitialRootRecvTwo A strategy hwin controllers
        first).2
    shadow.common.1 = first :=
  rfl

/-- After two simultaneous receives, both local reconstructions produce the
same literal `(first, current)` key. -/
@[simp] theorem
    profiledRawJointHybridRootPinnedFront_localKeys_agree_after_root
    (first current : In₁ × In₂) :
    profiledRawJointHybridRootPinnedFrontOneKeyOfReceive A strategy hwin
        controllers
        (profiledRawJointHybridInitialRootRecvOne A strategy hwin controllers
          first).2 current.1 current.2 =
      profiledRawJointHybridRootPinnedFrontTwoKeyOfReceive A strategy hwin
        controllers
        (profiledRawJointHybridInitialRootRecvTwo A strategy hwin controllers
          first).2 current.2 current.1 :=
  rfl

@[simp] theorem
    profiledRawJointHybridRootPinnedFront_oneKey_after_root
    (first current : In₁ × In₂) :
    profiledRawJointHybridRootPinnedFrontOneKeyOfReceive A strategy hwin
        controllers
        (profiledRawJointHybridInitialRootRecvOne A strategy hwin controllers
          first).2 current.1 current.2 =
      (first, current) :=
  rfl

@[simp] theorem
    profiledRawJointHybridRootPinnedFront_twoKey_after_root
    (first current : In₁ × In₂) :
    profiledRawJointHybridRootPinnedFrontTwoKeyOfReceive A strategy hwin
        controllers
        (profiledRawJointHybridInitialRootRecvTwo A strategy hwin controllers
          first).2 current.2 current.1 =
      (first, current) :=
  rfl

end

end

end DetParityAutomaton

end DistributedSynthesis
