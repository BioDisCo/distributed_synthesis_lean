/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonLiteralHeterogeneousSeam
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonLiteralCrossPreselection
import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledRawJointGuardedFirstPolicyRootHandoff

/-!
# Finite tagged children of the guarded-common heterogeneous seam

The unconditional heterogeneous seam keeps the exact root-pinned first block.
Its first record must not be erased to a bare incidence code: two literal
children with the same code may be assigned different ordinary policies.

This file gives the guarded-common occurrence route the same honest finite
tag used by the older exact hybrid family.  A tag contains

* the finite decorated-policy state,
* the finite input pair selecting the literal child occurrence, and
* the dependent exact literal-child witness emitted by that occurrence's
  root-pinned first block.

For every fixed finite key, the proof-side semantic representative and its
root-pinned package are chosen once.  The dependent sum over all keys is
therefore finite.  Runtime code may retain this tag and recover the exact
ordinary policy root; it never receives a graph, orientation, leader bit, or
history.
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

private abbrev CommonPoint :=
  ProfiledRawJointGuardedCommonSemanticPoint A strategy

private abbrev CrossValid :=
  ProfiledRawJointGuardedCommonLiteralCrossExtraValid A strategy hwin

namespace ProfiledRawJointGuardedCommonDecoratedPolicyPackage

variable {initial : CommonPoint A strategy}

private abbrev DecoratedState :=
  ProfiledRawJointGuardedCommonDecoratedPolicyState A strategy hwin initial
    (CrossValid A strategy hwin)

private abbrev DecoratedReachable
    (package : ProfiledRawJointGuardedCommonDecoratedPolicyPackage A strategy
      hwin initial (CrossValid A strategy hwin))
    (state : DecoratedState A strategy hwin (initial := initial)) :=
  ProfiledRawJointGuardedCommonDecoratedPolicyReachable A strategy hwin
    initial (CrossValid A strategy hwin) package.policy state

/-! ## One fixed representative at every finite decorated state -/

/-- Choose the occurrence witness already carried by `extraAt_valid` at a
reachable state.  Unreachable states use the initial occurrence only to make
the finite lookup total; no correctness theorem consumes that branch. -/
noncomputable def literalRightSeamPointAt
    (package : ProfiledRawJointGuardedCommonDecoratedPolicyPackage A strategy
      hwin initial (CrossValid A strategy hwin))
    (state : DecoratedState A strategy hwin (initial := initial)) :
    CommonPoint A strategy := by
  classical
  if h : DecoratedReachable A strategy hwin package state then
    exact Classical.choose (package.extraAt_valid A strategy hwin state h)
  else
    exact initial

/-- At a reachable state the total representative has the selected code,
guarded pair, and literal annotation. -/
theorem literalRightSeamPointAt_spec
    (package : ProfiledRawJointGuardedCommonDecoratedPolicyPackage A strategy
      hwin initial (CrossValid A strategy hwin))
    (state : DecoratedState A strategy hwin (initial := initial))
    (hreachable : DecoratedReachable A strategy hwin package state) :
    let point := package.literalRightSeamPointAt A strategy hwin state
    point.code A strategy = state.1 ∧
      point.move A strategy hwin = package.pairAt A strategy hwin state ∧
      profiledRawJointGuardedCommonLiteralCrossExtraOfPoint A strategy hwin
          point = package.extraAt A strategy hwin state := by
  classical
  rw [literalRightSeamPointAt, dif_pos hreachable]
  exact Classical.choose_spec
    (package.extraAt_valid A strategy hwin state hreachable)

/-! ## A finite key and its exact root-pinned source -/

/-- The finite identity of one right/`both` seam table. -/
abbrev ProfiledRawJointGuardedCommonLiteralRightSeamKey
    (package : ProfiledRawJointGuardedCommonDecoratedPolicyPackage A strategy
      hwin initial (CrossValid A strategy hwin)) :=
  DecoratedState A strategy hwin (initial := initial) × (In₁ × In₂)

noncomputable instance literalRightSeamKeyFintype
    (package : ProfiledRawJointGuardedCommonDecoratedPolicyPackage A strategy
      hwin initial (CrossValid A strategy hwin)) :
    Fintype
      (ProfiledRawJointGuardedCommonLiteralRightSeamKey A strategy hwin
        package) := by
  infer_instance

/-- Literal common child occurrence selected by the finite seam key. -/
def literalRightSeamChildPoint
    (package : ProfiledRawJointGuardedCommonDecoratedPolicyPackage A strategy
      hwin initial (CrossValid A strategy hwin))
    (key : ProfiledRawJointGuardedCommonLiteralRightSeamKey A strategy hwin
      package) : CommonPoint A strategy :=
  (package.literalRightSeamPointAt A strategy hwin key.1).step A strategy key.2

/-- Policy-free installed data of the selected child occurrence. -/
def literalRightSeamInstalled
    (package : ProfiledRawJointGuardedCommonDecoratedPolicyPackage A strategy
      hwin initial (CrossValid A strategy hwin))
    (key : ProfiledRawJointGuardedCommonLiteralRightSeamKey A strategy hwin
      package) : ProfiledRawJointHybridCommonMoveData A strategy :=
  profiledRawJointGuardedCommonPointInstalled A strategy
    (package.literalRightSeamChildPoint A strategy hwin key)

/-- Exact semantic source selected by the root-pinned left first block at one
finite seam key. -/
noncomputable abbrev ProfiledRawJointGuardedCommonLiteralRightSeamSelectedSource
  (package : ProfiledRawJointGuardedCommonDecoratedPolicyPackage A strategy
      hwin initial (CrossValid A strategy hwin))
    (key : ProfiledRawJointGuardedCommonLiteralRightSeamKey A strategy hwin
      package) :=
  profiledRawJointRootPinnedSelectedSource A strategy
    ((package.literalRightSeamInstalled A strategy hwin key).world
      |>.oneSidedState A .left)
    (profiledRawJointHybridExactLeftRootPredicate A
      (package.literalRightSeamInstalled A strategy hwin key))
    (profiledRawJointHybridExactLeftPolicy A hwin
      (package.literalRightSeamInstalled A strategy hwin key))

/-! ## The honest finite dependent child tag -/

/-- The exact tagged target alphabet of all right/`both` seam first blocks.
The incidence code is only the first projection of the dependent child; it is
not used as the handoff key. -/
abbrev ProfiledRawJointGuardedCommonLiteralRightSeamTaggedChildCode
    (package : ProfiledRawJointGuardedCommonDecoratedPolicyPackage A strategy
      hwin initial (CrossValid A strategy hwin)) :=
  Σ key : ProfiledRawJointGuardedCommonLiteralRightSeamKey A strategy hwin
      package,
    ProfiledRawJointOneSidedLiteralChildCode A strategy
      (ProfiledRawJointGuardedCommonLiteralRightSeamSelectedSource A strategy
        hwin package key)

noncomputable instance literalRightSeamTaggedChildCodeFintype
    (package : ProfiledRawJointGuardedCommonDecoratedPolicyPackage A strategy
      hwin initial (CrossValid A strategy hwin)) :
    Fintype
      (ProfiledRawJointGuardedCommonLiteralRightSeamTaggedChildCode A strategy
        hwin package) := by
  classical
  infer_instance

/-- Recover the exact literal semantic child from its finite dependent tag. -/
noncomputable def literalRightSeamTaggedChildSource
    (package : ProfiledRawJointGuardedCommonDecoratedPolicyPackage A strategy
      hwin initial (CrossValid A strategy hwin))
    (child :
      ProfiledRawJointGuardedCommonLiteralRightSeamTaggedChildCode A strategy
        hwin package) :
    ProfiledRawJointOneSidedSemanticState A strategy (I := Unit) :=
  profiledRawJointOneSidedLiteralChildSource A strategy
    (ProfiledRawJointGuardedCommonLiteralRightSeamSelectedSource A strategy
      hwin package child.1) child.2

@[simp] theorem literalRightSeamTaggedChildSource_code
    (package : ProfiledRawJointGuardedCommonDecoratedPolicyPackage A strategy
      hwin initial (CrossValid A strategy hwin))
    (child :
      ProfiledRawJointGuardedCommonLiteralRightSeamTaggedChildCode A strategy
        hwin package) :
    (package.literalRightSeamTaggedChildSource A strategy hwin child).code A =
      child.2.1 :=
  profiledRawJointOneSidedLiteralChildSource_code A strategy
    (ProfiledRawJointGuardedCommonLiteralRightSeamSelectedSource A strategy
      hwin package child.1) child.2

/-- Recover the exact ordinary policy bank member belonging to the full
dependent child, rather than choosing by incidence code. -/
noncomputable def literalRightSeamTaggedChildPolicy
    (package : ProfiledRawJointGuardedCommonDecoratedPolicyPackage A strategy
      hwin initial (CrossValid A strategy hwin))
    (child :
      ProfiledRawJointGuardedCommonLiteralRightSeamTaggedChildCode A strategy
        hwin package) :
    ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
      ((package.literalRightSeamTaggedChildSource A strategy hwin child).code
        A) := by
  let installed := package.literalRightSeamInstalled A strategy hwin child.1
  let policy := profiledRawJointRootPinnedLiteralChildPolicyBank A strategy
    hwin (installed.world.oneSidedState A .left)
      (profiledRawJointHybridExactLeftRootPredicate A installed)
      (profiledRawJointHybridExactLeftPolicy A hwin installed) child.2
  simpa only [literalRightSeamTaggedChildSource,
    profiledRawJointOneSidedLiteralChildSource_code] using policy

/-! ## Exact tagged target and ordinary root handoff -/

/-- Add the finite seam key to the exact target emitted by its root-pinned
left first block. -/
def literalRightSeamTaggedTarget
    (package : ProfiledRawJointGuardedCommonDecoratedPolicyPackage A strategy
      hwin initial (CrossValid A strategy hwin))
    (key : ProfiledRawJointGuardedCommonLiteralRightSeamKey A strategy hwin
      package)
    (row : PairedEntryRow) (past : List (In₁ × In₂))
    (input : In₁ × In₂) :
    ProfiledRawJointGuardedCommonLiteralRightSeamTaggedChildCode A strategy
      hwin package :=
  let installed := package.literalRightSeamInstalled A strategy hwin key
  ⟨key,
    profiledRawJointGuardedFirstLeftTarget A strategy
      (installed.world.oneSidedState A .left)
      (profiledRawJointHybridExactLeftRootPredicate A installed)
      (profiledRawJointHybridExactLeftPolicy A hwin installed)
      row past input⟩

/-- The full finite seam tag recovers the ordinary right-policy root selected
by the exact root-pinned first block. -/
noncomputable def literalRightSeamTaggedChildRootMacro
    (package : ProfiledRawJointGuardedCommonDecoratedPolicyPackage A strategy
      hwin initial (CrossValid A strategy hwin))
    (key : ProfiledRawJointGuardedCommonLiteralRightSeamKey A strategy hwin
      package)
    (row : PairedEntryRow) (past : List (In₁ × In₂))
    (input : In₁ × In₂) :
    let child := package.literalRightSeamTaggedTarget A strategy hwin key row
      past input
    ProfiledRawJointUnitRightPolicyMacro A strategy
      ((package.literalRightSeamTaggedChildSource A strategy hwin child).code
        A)
      (package.literalRightSeamTaggedChildPolicy A strategy hwin child) := by
  let installed := package.literalRightSeamInstalled A strategy hwin key
  let literal := profiledRawJointGuardedFirstLeftTarget A strategy
    (installed.world.oneSidedState A .left)
    (profiledRawJointHybridExactLeftRootPredicate A installed)
    (profiledRawJointHybridExactLeftPolicy A hwin installed) row past input
  let child := package.literalRightSeamTaggedTarget A strategy hwin key row
    past input
  let policy := package.literalRightSeamTaggedChildPolicy A strategy hwin child
  let activation := profiledRawJointHybridExactLeftActivation A hwin installed
  let slot := profiledRawLeftChildSlot A (installed.world.procTwoSlot A)
    activation.lambda row past input
  have hliteral : literal.1.family.right () = some slot := by
    exact activation.target_active_slot row past input
  have hsource :
      (package.literalRightSeamTaggedChildSource A strategy hwin child).code A =
        literal.1 := by
    exact package.literalRightSeamTaggedChildSource_code A strategy hwin child
  have hrootCode :
      (policy.run []).1 =
        (package.literalRightSeamTaggedChildSource A strategy hwin child).code
          A := by
    have hroot := congrArg Prod.fst policy.accepts.1.1
    simpa [sourceFreeBeliefCodeParityRunAutomaton] using hroot
  exact {
    state := policy.run []
    reachable := ⟨[], rfl⟩
    slot := slot
    active_slot := by
      rw [hrootCode, hsource]
      exact hliteral }

@[simp] theorem literalRightSeamTaggedChildRootMacro_state
    (package : ProfiledRawJointGuardedCommonDecoratedPolicyPackage A strategy
      hwin initial (CrossValid A strategy hwin))
    (key : ProfiledRawJointGuardedCommonLiteralRightSeamKey A strategy hwin
      package)
    (row : PairedEntryRow) (past : List (In₁ × In₂))
    (input : In₁ × In₂) :
    (package.literalRightSeamTaggedChildRootMacro A strategy hwin key row past
      input).state =
      (package.literalRightSeamTaggedChildPolicy A strategy hwin
        (package.literalRightSeamTaggedTarget A strategy hwin key row past
      input)).run [] :=
  rfl

@[simp] theorem literalRightSeamTaggedChildRootMacro_slot
    (package : ProfiledRawJointGuardedCommonDecoratedPolicyPackage A strategy
      hwin initial (CrossValid A strategy hwin))
    (key : ProfiledRawJointGuardedCommonLiteralRightSeamKey A strategy hwin
      package)
    (row : PairedEntryRow) (past : List (In₁ × In₂))
    (input : In₁ × In₂) :
    (package.literalRightSeamTaggedChildRootMacro A strategy hwin key row past
      input).slot =
      let installed := package.literalRightSeamInstalled A strategy hwin key
      let activation := profiledRawJointHybridExactLeftActivation A hwin
        installed
      profiledRawLeftChildSlot A (installed.world.procTwoSlot A)
        activation.lambda row past input :=
  rfl

end ProfiledRawJointGuardedCommonDecoratedPolicyPackage

end

end DetParityAutomaton

end DistributedSynthesis
