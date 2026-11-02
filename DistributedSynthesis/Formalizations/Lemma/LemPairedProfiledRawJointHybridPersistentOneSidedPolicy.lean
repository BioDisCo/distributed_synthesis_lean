/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridCommonInstalledMove

/-!
# One persistent hybrid policy below the strict exit

The common/one-sided hybrid rational policy already contains all strict
descendants of each reachable common state.  Selecting a fresh ordinary
one-sided policy at every exceptional close loses that fact and permits two
local shadows to enter unrelated policy trees.  This file records the
alternative invariant directly.

A reachable hybrid state tagged `oneSided` has one literal one-sided semantic
source and one installed raw move.  Every strict physical direction then
lands in another `oneSided` state of the *same* rational policy.  The policy
object and its initial bank index do not change.  The strict side remains a
proof-tree direction; no graph, orientation, or leader bit is made available
to a process.
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

/-! ## Inverting a reachable one-sided hybrid state -/

/-- The literal one-sided source and raw move installed at a reachable
one-sided state of one fixed hybrid policy. -/
structure ProfiledRawJointHybridOneSidedInstalledMove
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (initialCode : ProfiledRawJointHybridCode A)
    (policy : ProfiledRawJointHybridProvenanceRationalPolicy A strategy
      initialCode)
    (key : ProfiledRawJointHybridOneSidedPolicyKey A strategy initialCode
      policy) where
  rawMove : ProfiledRawJointLambdaFamilyMove A (I := Unit)
  source : ProfiledRawJointOneSidedSemanticState A strategy (I := Unit)
  realizes : ProfiledRawJointHybridProvenanceMoveRealizesAt A strategy
    initialCode policy key.state (some rawMove)
  incidence_eq : source.code A = key.incidenceCode
  move_eq : source.move A = rawMove

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- Provenance at a reachable `oneSided` key cannot be common or dead, and
therefore supplies the exact literal one-sided source. -/
theorem nonempty_profiledRawJointHybridOneSidedInstalledMove
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (initialCode : ProfiledRawJointHybridCode A)
    (policy : ProfiledRawJointHybridProvenanceRationalPolicy A strategy
      initialCode)
    (key : ProfiledRawJointHybridOneSidedPolicyKey A strategy initialCode
      policy) :
    Nonempty (ProfiledRawJointHybridOneSidedInstalledMove A strategy
      initialCode policy key) := by
  rcases exists_profiledRawJointHybridProvenanceInstalledSemanticSource A
      strategy initialCode policy key.state key.reachable with
    ⟨move, semantic, hmove, hsourceCode, hsourceMove⟩
  rw [key.state_code] at hsourceCode
  cases semantic with
  | common world =>
      simp [ProfiledRawJointHybridSemanticState.code] at hsourceCode
  | oneSided source =>
      simp only [ProfiledRawJointHybridSemanticState.code,
        ProfiledRawJointHybridSemanticState.move] at hsourceCode hsourceMove
      cases move with
      | none => simp at hsourceMove
      | some rawMove =>
          exact ⟨⟨rawMove, source, hmove,
            ProfiledRawJointHybridCode.oneSided.inj hsourceCode,
            Option.some.inj hsourceMove⟩⟩
  | dead =>
      simp [ProfiledRawJointHybridSemanticState.code] at hsourceCode

namespace ProfiledRawJointHybridOneSidedInstalledMove

variable {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
variable {initialCode : ProfiledRawJointHybridCode A}
variable {policy : ProfiledRawJointHybridProvenanceRationalPolicy A strategy
  initialCode}
variable {key : ProfiledRawJointHybridOneSidedPolicyKey A strategy initialCode
  policy}

section
omit [Inhabited Out₁] [Inhabited Out₂]

/-- Reassembling the stored source as a hybrid state gives exactly the
complete public code of the policy state. -/
theorem semanticSource_code
    (installed : ProfiledRawJointHybridOneSidedInstalledMove A strategy
      initialCode policy key) :
    (ProfiledRawJointHybridSemanticState.oneSided installed.source).code A =
      key.state.1 := by
  rw [key.state_code]
  exact congrArg ProfiledRawJointHybridCode.oneSided installed.incidence_eq

/-- The semantic source exposes the installed hybrid move. -/
theorem semanticSource_move
    (installed : ProfiledRawJointHybridOneSidedInstalledMove A strategy
      initialCode policy key) :
    (ProfiledRawJointHybridSemanticState.oneSided installed.source).move A =
      some installed.rawMove := by
  exact congrArg some installed.move_eq

/-- The incidence code itself, rather than a separately selected semantic
representative, determines which live right slot is stored at this key. -/
theorem right_slot_iff
    (installed : ProfiledRawJointHybridOneSidedInstalledMove A strategy
      initialCode policy key)
    (slot : ProfiledRawRightSlot A) :
    key.incidenceCode.family.right () = some slot ↔
      (installed.source.code A).family.right () = some slot := by
  rw [installed.incidence_eq]

/-- Left-slot mirror. -/
theorem left_slot_iff
    (installed : ProfiledRawJointHybridOneSidedInstalledMove A strategy
      initialCode policy key)
    (slot : ProfiledRawLeftSlot A) :
    key.incidenceCode.family.left () = some slot ↔
      (installed.source.code A).family.left () = some slot := by
  rw [installed.incidence_eq]

end

/-! ## Strict successors stay inside the same policy -/

/-- Tagged hybrid child code of one later strict physical direction. -/
def strictChildCode
    (installed : ProfiledRawJointHybridOneSidedInstalledMove A strategy
      initialCode policy key)
    (actual : ProfiledRawJointActualDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂)) :
    ProfiledRawJointHybridCode A :=
  .oneSided (profiledRawJointOneSidedNext A key.incidenceCode
    installed.rawMove actual)

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- The raw hybrid transition on a one-sided state is exactly the tagged
ordinary strict child. -/
theorem hybridNext_strict
    (installed : ProfiledRawJointHybridOneSidedInstalledMove A strategy
      initialCode policy key)
    (actual : ProfiledRawJointActualDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂)) :
    profiledRawJointHybridNext A key.state.1 (some installed.rawMove)
        (.strict actual) =
      installed.strictChildCode A actual := by
  rw [key.state_code]
  rfl

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- On a literal strict child tag, the successor table of the one fixed
hybrid policy performs exactly the hybrid code-DPA step. -/
theorem successor_eq_strict
    (installed : ProfiledRawJointHybridOneSidedInstalledMove A strategy
      initialCode policy key)
    (actual : ProfiledRawJointActualDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂)) :
    policy.successor key.state (installed.strictChildCode A actual) =
      (installed.strictChildCode A actual,
        (profiledRawJointHybridCodeParityDPA A initialCode).step key.state.2
          (installed.strictChildCode A actual)) := by
  have hsuccessor := installed.realizes.2
    (installed.strictChildCode A actual)
  have hraw := installed.hybridNext_strict A actual
  have hfinite :
      profiledRawJointHybridFiniteCodeNext A key.state.1
          (some installed.rawMove) (installed.strictChildCode A actual) =
        installed.strictChildCode A actual := by
    rw [← hraw]
    exact sourceFreeBeliefFiniteCodeNext_of_direction
      (profiledRawJointHybridNext A) key.state.1 (some installed.rawMove)
        (.strict actual)
  rw [hfinite] at hsuccessor
  exact hsuccessor

/-- Package a strict child as another reachable one-sided key of the very
same hybrid policy.  In particular no new rational policy is selected here. -/
noncomputable def strictSuccessorKey
    (installed : ProfiledRawJointHybridOneSidedInstalledMove A strategy
      initialCode policy key)
    (actual : ProfiledRawJointActualDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂)) :
    ProfiledRawJointHybridOneSidedPolicyKey A strategy initialCode policy where
  incidenceCode := profiledRawJointOneSidedNext A key.incidenceCode
    installed.rawMove actual
  state := policy.successor key.state (installed.strictChildCode A actual)
  reachable := profiledRawJointHybridProvenancePolicy_successor_reachable A
    strategy initialCode policy key.state key.reachable
      (installed.strictChildCode A actual)
  state_code := by
    exact congrArg Prod.fst (installed.successor_eq_strict A actual)

omit [Inhabited Out₁] [Inhabited Out₂] in
@[simp] theorem strictSuccessorKey_state
    (installed : ProfiledRawJointHybridOneSidedInstalledMove A strategy
      initialCode policy key)
    (actual : ProfiledRawJointActualDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂)) :
    (installed.strictSuccessorKey A actual).state =
      policy.successor key.state (installed.strictChildCode A actual) :=
  rfl

omit [Inhabited Out₁] [Inhabited Out₂] in
@[simp] theorem strictSuccessorKey_incidenceCode
    (installed : ProfiledRawJointHybridOneSidedInstalledMove A strategy
      initialCode policy key)
    (actual : ProfiledRawJointActualDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂)) :
    (installed.strictSuccessorKey A actual).incidenceCode =
      profiledRawJointOneSidedNext A key.incidenceCode installed.rawMove
        actual :=
  rfl

end ProfiledRawJointHybridOneSidedInstalledMove

/-! ## The strict exit from a common key uses the same policy -/

namespace ProfiledRawJointHybridCommonInstalledMove

variable {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
variable {initialCode : ProfiledRawJointHybridCode A}
variable {policy : ProfiledRawJointHybridProvenanceRationalPolicy A strategy
  initialCode}
variable {key : ProfiledRawJointHybridCommonPolicyKey A strategy initialCode
  policy}

/-- Tagged one-sided child selected by a strict exit from this common key. -/
def strictChildCode
    (installed : ProfiledRawJointHybridCommonInstalledMove A strategy
      initialCode policy key)
    (actual : ProfiledRawJointActualDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂)) :
    ProfiledRawJointHybridCode A :=
  .oneSided (profiledRawJointOneSidedNext A key.incidenceCode
    installed.rawMove (profiledRawJointCommonActualDirection actual))

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- The raw hybrid transition is exactly the explicit strict-exit code. -/
theorem hybridNext_strict
    (installed : ProfiledRawJointHybridCommonInstalledMove A strategy
      initialCode policy key)
    (actual : ProfiledRawJointActualDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂)) :
    profiledRawJointHybridNext A key.state.1 (some installed.rawMove)
        (.strict actual) =
      installed.strictChildCode A actual := by
  rw [key.state_code]
  rfl

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- The strict exit follows the successor table of the already selected
hybrid policy; no ordinary child policy is chosen. -/
theorem successor_eq_strict
    (installed : ProfiledRawJointHybridCommonInstalledMove A strategy
      initialCode policy key)
    (actual : ProfiledRawJointActualDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂)) :
    policy.successor key.state (installed.strictChildCode A actual) =
      (installed.strictChildCode A actual,
        (profiledRawJointHybridCodeParityDPA A initialCode).step key.state.2
          (installed.strictChildCode A actual)) := by
  have hsuccessor := installed.realizes.2
    (installed.strictChildCode A actual)
  have hraw := installed.hybridNext_strict A actual
  have hfinite :
      profiledRawJointHybridFiniteCodeNext A key.state.1
          (some installed.rawMove) (installed.strictChildCode A actual) =
        installed.strictChildCode A actual := by
    rw [← hraw]
    exact sourceFreeBeliefFiniteCodeNext_of_direction
      (profiledRawJointHybridNext A) key.state.1 (some installed.rawMove)
        (.strict actual)
  rw [hfinite] at hsuccessor
  exact hsuccessor

/-- Package the strict exit as a reachable one-sided key of the same hybrid
policy. -/
noncomputable def strictSuccessorKey
    (installed : ProfiledRawJointHybridCommonInstalledMove A strategy
      initialCode policy key)
    (actual : ProfiledRawJointActualDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂)) :
    ProfiledRawJointHybridOneSidedPolicyKey A strategy initialCode policy where
  incidenceCode := profiledRawJointOneSidedNext A key.incidenceCode
    installed.rawMove (profiledRawJointCommonActualDirection actual)
  state := policy.successor key.state (installed.strictChildCode A actual)
  reachable := profiledRawJointHybridProvenancePolicy_successor_reachable A
    strategy initialCode policy key.state key.reachable
      (installed.strictChildCode A actual)
  state_code := by
    exact congrArg Prod.fst (installed.successor_eq_strict A actual)

omit [Inhabited Out₁] [Inhabited Out₂] in
@[simp] theorem strictSuccessorKey_state
    (installed : ProfiledRawJointHybridCommonInstalledMove A strategy
      initialCode policy key)
    (actual : ProfiledRawJointActualDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂)) :
    (installed.strictSuccessorKey A actual).state =
      policy.successor key.state (installed.strictChildCode A actual) :=
  rfl

end ProfiledRawJointHybridCommonInstalledMove

end

end DetParityAutomaton

end DistributedSynthesis
