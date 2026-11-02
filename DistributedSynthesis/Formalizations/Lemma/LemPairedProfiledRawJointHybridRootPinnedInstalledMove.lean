/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridRootPinnedSharedTail
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridCommonMoveData

/-!
# Installed moves below the exact guarded hybrid root

Every reachable false-bit state of the one root-pinned policy has an ordinary
hybrid move installed by the shared tail table.  Provenance then recovers the
literal common or one-sided semantic source named by the state's public tag.

The successor keys in this file remain states of that same guarded policy.
No `ordinaryBelow` policy is stored, and no child is independently
rationalized.
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

variable
  (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
  (hwin : ∀ env : EnvironmentSequence In₁ In₂,
    A.Accepts (execution strategy env))

/-! ## Move realization by the shared false-state table -/

/-- One hybrid move realizes the complete shared tail table at an underlying
ordinary state of the guarded policy. -/
def ProfiledRawJointHybridInitialRootPinnedFalseMoveRealizesAt
    (first : In₁ × In₂)
    (state :
      (ProfiledRawJointHybridInitialRootPinnedRunAutomaton A strategy
        first).State)
    (move : ProfiledRawJointHybridMove A) : Prop :=
  ProfiledRawJointHybridProvenanceValid A strategy state.1 move ∧
    ∀ childCode : ProfiledRawJointHybridCode A,
      let nextCode := profiledRawJointHybridFiniteCodeNext A state.1 move
        childCode
      profiledRawJointHybridInitialRootPinnedTailSuccessor A strategy hwin
          first state childCode =
        (nextCode,
          (profiledRawJointHybridCodeParityDPA A
            (ProfiledRawJointHybridInitialRootPinnedCode A strategy first)
            ).step state.2 nextCode)

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- Legality at a reachable false-bit guarded state exposes one installed
move and its literal semantic provenance source. -/
theorem
    exists_profiledRawJointHybridInitialRootPinnedFalseInstalledSemanticSource
    (first : In₁ × In₂)
    (state : ProfiledRawJointHybridInitialRootPinnedGuardedState A strategy
      first)
    (hreachable :
      ProfiledRawJointHybridInitialRootPinnedReachable A strategy hwin first
        state)
    (hfresh : state.1 = false) :
    ∃ move : ProfiledRawJointHybridMove A,
      ∃ source : ProfiledRawJointHybridSemanticState A strategy,
        ProfiledRawJointHybridInitialRootPinnedFalseMoveRealizesAt A strategy
            hwin first state.2 move ∧
          source.code A = state.2.1 ∧ source.move A = move := by
  let package :=
    profiledRawJointHybridInitialRootPinnedPolicy A strategy hwin first
  rcases hreachable with ⟨node, hnode⟩
  have hlegal := package.policy.legal_at node
  rw [hnode] at hlegal
  have hstate : state = (false, state.2) := by
    apply Prod.ext
    · exact hfresh
    · rfl
  rw [hstate] at hlegal
  change ∃ next : ProfiledRawJointHybridCode A →
      (ProfiledRawJointHybridInitialRootPinnedRunAutomaton A strategy
        first).State,
    (∃ move : ProfiledRawJointHybridMove A,
      ProfiledRawJointHybridProvenanceValid A strategy state.2.1 move ∧
        ∀ childCode : ProfiledRawJointHybridCode A,
          let nextCode := profiledRawJointHybridFiniteCodeNext A state.2.1
            move childCode
          next childCode =
            (nextCode,
              (profiledRawJointHybridCodeParityDPA A
                (ProfiledRawJointHybridInitialRootPinnedCode A strategy first)
                ).step state.2.2 nextCode)) ∧
      package.policy.successor (false, state.2) =
        fun childCode ↦ (false, next childCode) at hlegal
  rcases hlegal with ⟨next, ⟨move, hvalid, hnext⟩, htable⟩
  rcases hvalid with ⟨source, hsourceCode, hsourceMove⟩
  refine ⟨move, source, ⟨⟨⟨source, hsourceCode, hsourceMove⟩, ?_⟩,
    hsourceCode, hsourceMove⟩⟩
  intro childCode
  change (package.policy.successor (false, state.2) childCode).2 = _
  rw [htable]
  exact hnext childCode

/-! ## Common and one-sided provenance inversion -/

/-- The literal common source installed at a reachable false/common key. -/
structure ProfiledRawJointHybridInitialRootPinnedFalseCommonInstalledMove
    (first : In₁ × In₂)
    (key : ProfiledRawJointHybridInitialRootPinnedFalseCommonKey A strategy
      hwin first) where
  rawMove : ProfiledRawJointLambdaFamilyMove A (I := Unit)
  world : ProfiledRawJointCommonBaseWorld A strategy
  realizes :
    ProfiledRawJointHybridInitialRootPinnedFalseMoveRealizesAt A strategy hwin
      first key.state.2 (some rawMove)
  incidence_eq :
    (profiledRawJointCommonWorldFamily A world).incidenceCode A =
      key.incidenceCode
  move_eq : (profiledRawJointCommonWorldFamily A world).move A = rawMove

/-- Forget the guarded-policy realization while retaining exactly the common
move data consumed by local exact-root guards. -/
def
    ProfiledRawJointHybridInitialRootPinnedFalseCommonInstalledMove.toCommonMoveData
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    {hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env)}
    {first : In₁ × In₂}
    {key : ProfiledRawJointHybridInitialRootPinnedFalseCommonKey A strategy
      hwin first}
    (installed :
      ProfiledRawJointHybridInitialRootPinnedFalseCommonInstalledMove A
        strategy hwin first key) :
    ProfiledRawJointHybridCommonMoveData A strategy where
  incidenceCode := key.incidenceCode
  rawMove := installed.rawMove
  world := installed.world
  incidence_eq := installed.incidence_eq
  move_eq := installed.move_eq

/-- Root-pinned false/common installed moves have the same policy-free view
as ordinary common installed moves. -/
noncomputable instance
    profiledRawJointHybridInitialRootPinnedFalseCommonInstalledMoveCoeCommonMoveData
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    {hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env)}
    {first : In₁ × In₂}
    {key : ProfiledRawJointHybridInitialRootPinnedFalseCommonKey A strategy
      hwin first} :
    CoeOut
      (ProfiledRawJointHybridInitialRootPinnedFalseCommonInstalledMove A
        strategy hwin first key)
      (ProfiledRawJointHybridCommonMoveData A strategy) where
  coe :=
    ProfiledRawJointHybridInitialRootPinnedFalseCommonInstalledMove.toCommonMoveData
      A

/-- The literal one-sided source installed at a reachable false/one-sided
key. -/
structure ProfiledRawJointHybridInitialRootPinnedFalseOneSidedInstalledMove
    (first : In₁ × In₂)
    (key : ProfiledRawJointHybridInitialRootPinnedFalseOneSidedKey A strategy
      hwin first) where
  rawMove : ProfiledRawJointLambdaFamilyMove A (I := Unit)
  source : ProfiledRawJointOneSidedSemanticState A strategy (I := Unit)
  realizes :
    ProfiledRawJointHybridInitialRootPinnedFalseMoveRealizesAt A strategy hwin
      first key.state.2 (some rawMove)
  incidence_eq : source.code A = key.incidenceCode
  move_eq : source.move A = rawMove

omit [Inhabited Out₁] [Inhabited Out₂] in
theorem
    nonempty_profiledRawJointHybridInitialRootPinnedFalseCommonInstalledMove
    (first : In₁ × In₂)
    (key : ProfiledRawJointHybridInitialRootPinnedFalseCommonKey A strategy
      hwin first) :
    Nonempty
      (ProfiledRawJointHybridInitialRootPinnedFalseCommonInstalledMove A
        strategy hwin first key) := by
  rcases
      exists_profiledRawJointHybridInitialRootPinnedFalseInstalledSemanticSource
        A strategy hwin first key.state key.reachable key.fresh_false with
    ⟨move, source, hmove, hsourceCode, hsourceMove⟩
  rw [key.state_code] at hsourceCode
  cases source with
  | common world =>
      simp only [ProfiledRawJointHybridSemanticState.code,
        ProfiledRawJointHybridSemanticState.move] at hsourceCode hsourceMove
      cases move with
      | none => simp at hsourceMove
      | some rawMove =>
          exact ⟨⟨rawMove, world, hmove,
            ProfiledRawJointHybridCode.common.inj hsourceCode,
            Option.some.inj hsourceMove⟩⟩
  | oneSided source =>
      simp [ProfiledRawJointHybridSemanticState.code] at hsourceCode
  | dead =>
      simp [ProfiledRawJointHybridSemanticState.code] at hsourceCode

omit [Inhabited Out₁] [Inhabited Out₂] in
theorem
    nonempty_profiledRawJointHybridInitialRootPinnedFalseOneSidedInstalledMove
    (first : In₁ × In₂)
    (key : ProfiledRawJointHybridInitialRootPinnedFalseOneSidedKey A strategy
      hwin first) :
    Nonempty
      (ProfiledRawJointHybridInitialRootPinnedFalseOneSidedInstalledMove A
        strategy hwin first key) := by
  rcases
      exists_profiledRawJointHybridInitialRootPinnedFalseInstalledSemanticSource
        A strategy hwin first key.state key.reachable key.fresh_false with
    ⟨move, source, hmove, hsourceCode, hsourceMove⟩
  rw [key.state_code] at hsourceCode
  cases source with
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

/-! ## Same-policy successors from a common key -/

namespace ProfiledRawJointHybridInitialRootPinnedFalseCommonInstalledMove

variable {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
variable {hwin : ∀ env : EnvironmentSequence In₁ In₂,
  A.Accepts (execution strategy env)}
variable {first : In₁ × In₂}
variable {key : ProfiledRawJointHybridInitialRootPinnedFalseCommonKey A
  strategy hwin first}

def simultaneousChildCode
    (installed :
      ProfiledRawJointHybridInitialRootPinnedFalseCommonInstalledMove A
        strategy hwin first key)
    (input : In₁ × In₂) : ProfiledRawJointHybridCode A :=
  .common (profiledRawJointIncidenceNext A key.incidenceCode.family
    installed.rawMove (profiledRawJointBothRestartDirection input))

def strictChildCode
    (installed :
      ProfiledRawJointHybridInitialRootPinnedFalseCommonInstalledMove A
        strategy hwin first key)
    (actual : ProfiledRawJointActualDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂)) :
    ProfiledRawJointHybridCode A :=
  .oneSided (profiledRawJointOneSidedNext A key.incidenceCode
    installed.rawMove (profiledRawJointCommonActualDirection actual))

section
omit [Inhabited Out₁] [Inhabited Out₂]

theorem hybridNext_simultaneous
    (installed :
      ProfiledRawJointHybridInitialRootPinnedFalseCommonInstalledMove A
        strategy hwin first key)
    (input : In₁ × In₂) :
    profiledRawJointHybridNext A key.state.2.1 (some installed.rawMove)
        (.simultaneous input) = installed.simultaneousChildCode A input := by
  rw [key.state_code]
  rfl

theorem hybridNext_strict
    (installed :
      ProfiledRawJointHybridInitialRootPinnedFalseCommonInstalledMove A
        strategy hwin first key)
    (actual : ProfiledRawJointActualDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂)) :
    profiledRawJointHybridNext A key.state.2.1 (some installed.rawMove)
        (.strict actual) = installed.strictChildCode A actual := by
  rw [key.state_code]
  rfl

theorem tailSuccessor_eq_simultaneous
    (installed :
      ProfiledRawJointHybridInitialRootPinnedFalseCommonInstalledMove A
        strategy hwin first key)
    (input : In₁ × In₂) :
    profiledRawJointHybridInitialRootPinnedTailSuccessor A strategy hwin first
        key.state.2 (installed.simultaneousChildCode A input) =
      (installed.simultaneousChildCode A input,
        (profiledRawJointHybridCodeParityDPA A
          (ProfiledRawJointHybridInitialRootPinnedCode A strategy first)).step
          key.state.2.2 (installed.simultaneousChildCode A input)) := by
  have hnext := installed.realizes.2
    (installed.simultaneousChildCode A input)
  have hfinite :
      profiledRawJointHybridFiniteCodeNext A key.state.2.1
          (some installed.rawMove) (installed.simultaneousChildCode A input) =
        installed.simultaneousChildCode A input := by
    rw [← installed.hybridNext_simultaneous A input]
    exact sourceFreeBeliefFiniteCodeNext_of_direction
      (profiledRawJointHybridNext A) key.state.2.1
        (some installed.rawMove) (.simultaneous input)
  rw [hfinite] at hnext
  exact hnext

theorem tailSuccessor_eq_strict
    (installed :
      ProfiledRawJointHybridInitialRootPinnedFalseCommonInstalledMove A
        strategy hwin first key)
    (actual : ProfiledRawJointActualDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂)) :
    profiledRawJointHybridInitialRootPinnedTailSuccessor A strategy hwin first
        key.state.2 (installed.strictChildCode A actual) =
      (installed.strictChildCode A actual,
        (profiledRawJointHybridCodeParityDPA A
          (ProfiledRawJointHybridInitialRootPinnedCode A strategy first)).step
          key.state.2.2 (installed.strictChildCode A actual)) := by
  have hnext := installed.realizes.2 (installed.strictChildCode A actual)
  have hfinite :
      profiledRawJointHybridFiniteCodeNext A key.state.2.1
          (some installed.rawMove) (installed.strictChildCode A actual) =
        installed.strictChildCode A actual := by
    rw [← installed.hybridNext_strict A actual]
    exact sourceFreeBeliefFiniteCodeNext_of_direction
      (profiledRawJointHybridNext A) key.state.2.1
        (some installed.rawMove) (.strict actual)
  rw [hfinite] at hnext
  exact hnext

theorem successor_eq_simultaneous
    (installed :
      ProfiledRawJointHybridInitialRootPinnedFalseCommonInstalledMove A
        strategy hwin first key)
    (input : In₁ × In₂) :
    (profiledRawJointHybridInitialRootPinnedPolicy A strategy hwin first
      ).policy.successor key.state (installed.simultaneousChildCode A input) =
      (false,
        (installed.simultaneousChildCode A input,
          (profiledRawJointHybridCodeParityDPA A
            (ProfiledRawJointHybridInitialRootPinnedCode A strategy first)
            ).step key.state.2.2
              (installed.simultaneousChildCode A input))) := by
  rw [key.successor_eq_tail A strategy hwin]
  rw [installed.tailSuccessor_eq_simultaneous A input]
  rfl

theorem successor_eq_strict
    (installed :
      ProfiledRawJointHybridInitialRootPinnedFalseCommonInstalledMove A
        strategy hwin first key)
    (actual : ProfiledRawJointActualDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂)) :
    (profiledRawJointHybridInitialRootPinnedPolicy A strategy hwin first
      ).policy.successor key.state (installed.strictChildCode A actual) =
      (false,
        (installed.strictChildCode A actual,
          (profiledRawJointHybridCodeParityDPA A
            (ProfiledRawJointHybridInitialRootPinnedCode A strategy first)
            ).step key.state.2.2 (installed.strictChildCode A actual))) := by
  rw [key.successor_eq_tail A strategy hwin]
  rw [installed.tailSuccessor_eq_strict A actual]
  rfl

end

noncomputable def simultaneousSuccessorKey
    (installed :
      ProfiledRawJointHybridInitialRootPinnedFalseCommonInstalledMove A
        strategy hwin first key)
    (input : In₁ × In₂) :
    ProfiledRawJointHybridInitialRootPinnedFalseCommonKey A strategy hwin
      first where
  incidenceCode := profiledRawJointIncidenceNext A key.incidenceCode.family
    installed.rawMove (profiledRawJointBothRestartDirection input)
  state :=
    (profiledRawJointHybridInitialRootPinnedPolicy A strategy hwin first
      ).policy.successor key.state (installed.simultaneousChildCode A input)
  reachable := by
    rcases key.reachable with ⟨node, hnode⟩
    refine ⟨node ++ [installed.simultaneousChildCode A input], ?_⟩
    rw [← (profiledRawJointHybridInitialRootPinnedPolicy A strategy hwin
      first).policy.successor_at node
        (installed.simultaneousChildCode A input), hnode]
  fresh_false := by
    exact congrArg Prod.fst (installed.successor_eq_simultaneous A input)
  state_code := by
    exact congrArg (fun state ↦ state.2.1)
      (installed.successor_eq_simultaneous A input)

noncomputable def strictSuccessorKey
    (installed :
      ProfiledRawJointHybridInitialRootPinnedFalseCommonInstalledMove A
        strategy hwin first key)
    (actual : ProfiledRawJointActualDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂)) :
    ProfiledRawJointHybridInitialRootPinnedFalseOneSidedKey A strategy hwin
      first where
  incidenceCode := profiledRawJointOneSidedNext A key.incidenceCode
    installed.rawMove (profiledRawJointCommonActualDirection actual)
  state :=
    (profiledRawJointHybridInitialRootPinnedPolicy A strategy hwin first
      ).policy.successor key.state (installed.strictChildCode A actual)
  reachable := by
    rcases key.reachable with ⟨node, hnode⟩
    refine ⟨node ++ [installed.strictChildCode A actual], ?_⟩
    rw [← (profiledRawJointHybridInitialRootPinnedPolicy A strategy hwin
      first).policy.successor_at node (installed.strictChildCode A actual),
      hnode]
  fresh_false := by
    exact congrArg Prod.fst (installed.successor_eq_strict A actual)
  state_code := by
    exact congrArg (fun state ↦ state.2.1)
      (installed.successor_eq_strict A actual)

end ProfiledRawJointHybridInitialRootPinnedFalseCommonInstalledMove

/-! ## Same-policy strict successors from a one-sided key -/

namespace ProfiledRawJointHybridInitialRootPinnedFalseOneSidedInstalledMove

variable {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
variable {hwin : ∀ env : EnvironmentSequence In₁ In₂,
  A.Accepts (execution strategy env)}
variable {first : In₁ × In₂}
variable {key : ProfiledRawJointHybridInitialRootPinnedFalseOneSidedKey A
  strategy hwin first}

def strictChildCode
    (installed :
      ProfiledRawJointHybridInitialRootPinnedFalseOneSidedInstalledMove A
        strategy hwin first key)
    (actual : ProfiledRawJointActualDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂)) :
    ProfiledRawJointHybridCode A :=
  .oneSided (profiledRawJointOneSidedNext A key.incidenceCode
    installed.rawMove actual)

section
omit [Inhabited Out₁] [Inhabited Out₂]

theorem hybridNext_strict
    (installed :
      ProfiledRawJointHybridInitialRootPinnedFalseOneSidedInstalledMove A
        strategy hwin first key)
    (actual : ProfiledRawJointActualDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂)) :
    profiledRawJointHybridNext A key.state.2.1 (some installed.rawMove)
        (.strict actual) = installed.strictChildCode A actual := by
  rw [key.state_code]
  rfl

theorem tailSuccessor_eq_strict
    (installed :
      ProfiledRawJointHybridInitialRootPinnedFalseOneSidedInstalledMove A
        strategy hwin first key)
    (actual : ProfiledRawJointActualDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂)) :
    profiledRawJointHybridInitialRootPinnedTailSuccessor A strategy hwin first
        key.state.2 (installed.strictChildCode A actual) =
      (installed.strictChildCode A actual,
        (profiledRawJointHybridCodeParityDPA A
          (ProfiledRawJointHybridInitialRootPinnedCode A strategy first)).step
          key.state.2.2 (installed.strictChildCode A actual)) := by
  have hnext := installed.realizes.2 (installed.strictChildCode A actual)
  have hfinite :
      profiledRawJointHybridFiniteCodeNext A key.state.2.1
          (some installed.rawMove) (installed.strictChildCode A actual) =
        installed.strictChildCode A actual := by
    rw [← installed.hybridNext_strict A actual]
    exact sourceFreeBeliefFiniteCodeNext_of_direction
      (profiledRawJointHybridNext A) key.state.2.1
        (some installed.rawMove) (.strict actual)
  rw [hfinite] at hnext
  exact hnext

theorem successor_eq_strict
    (installed :
      ProfiledRawJointHybridInitialRootPinnedFalseOneSidedInstalledMove A
        strategy hwin first key)
    (actual : ProfiledRawJointActualDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂)) :
    (profiledRawJointHybridInitialRootPinnedPolicy A strategy hwin first
      ).policy.successor key.state (installed.strictChildCode A actual) =
      (false,
        (installed.strictChildCode A actual,
          (profiledRawJointHybridCodeParityDPA A
            (ProfiledRawJointHybridInitialRootPinnedCode A strategy first)
            ).step key.state.2.2 (installed.strictChildCode A actual))) := by
  rw [key.successor_eq_tail A strategy hwin]
  rw [installed.tailSuccessor_eq_strict A actual]
  rfl

end

noncomputable def strictSuccessorKey
    (installed :
      ProfiledRawJointHybridInitialRootPinnedFalseOneSidedInstalledMove A
        strategy hwin first key)
    (actual : ProfiledRawJointActualDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂)) :
    ProfiledRawJointHybridInitialRootPinnedFalseOneSidedKey A strategy hwin
      first where
  incidenceCode := profiledRawJointOneSidedNext A key.incidenceCode
    installed.rawMove actual
  state :=
    (profiledRawJointHybridInitialRootPinnedPolicy A strategy hwin first
      ).policy.successor key.state (installed.strictChildCode A actual)
  reachable := by
    rcases key.reachable with ⟨node, hnode⟩
    refine ⟨node ++ [installed.strictChildCode A actual], ?_⟩
    rw [← (profiledRawJointHybridInitialRootPinnedPolicy A strategy hwin
      first).policy.successor_at node (installed.strictChildCode A actual),
      hnode]
  fresh_false := by
    exact congrArg Prod.fst (installed.successor_eq_strict A actual)
  state_code := by
    exact congrArg (fun state ↦ state.2.1)
      (installed.successor_eq_strict A actual)

end ProfiledRawJointHybridInitialRootPinnedFalseOneSidedInstalledMove

end


end DetParityAutomaton

end DistributedSynthesis
