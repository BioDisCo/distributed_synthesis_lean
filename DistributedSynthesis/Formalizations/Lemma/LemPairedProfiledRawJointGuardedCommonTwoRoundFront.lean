/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonTailFront
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridInitialShadow
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointInitialCommonBothOneShot

/-!
# The local two-round entrance to the guarded common tail

This file isolates the genuinely local `both`/`both` entrance to the guarded
common tail.  The bare root has a one-point local control.  On its first
receive, each process enters the already verified hybrid initial shadow; that
shadow retains the exact first input pair together with the strict
contingencies required by indistinguishability.  On its next receive, each
process reconstructs the same two-pair seed, emits its projection of the
literal common `both` output, and installs the root of the selected guarded
occurrence-sensitive common policy.

Every executable map below accepts only a local state, the process's own
input, and the partner input delivered by an actual receive.  In particular,
no map accepts a graph, orientation, hierarchy side, leader bit, semantic
world, or history.
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

/-! ## Finite local phases -/

/-- The bare process-one root carries no orientation or semantic data. -/
abbrev ProfiledRawJointGuardedCommonTwoRoundInitialOne := Unit

/-- Process-two mirror. -/
abbrev ProfiledRawJointGuardedCommonTwoRoundInitialTwo := Unit

/-- Process one's exact local shadow after its first receive. -/
abbrev ProfiledRawJointGuardedCommonTwoRoundSeedOne :=
  ProfiledRawJointHybridInitialOneShadow A strategy hwin controllers

/-- Process-two mirror. -/
abbrev ProfiledRawJointGuardedCommonTwoRoundSeedTwo :=
  ProfiledRawJointHybridInitialTwoShadow A strategy hwin controllers

noncomputable instance profiledRawJointGuardedCommonTwoRoundSeedOneFintype :
    Fintype
      (ProfiledRawJointGuardedCommonTwoRoundSeedOne A strategy hwin
        controllers) := by
  classical
  infer_instance

noncomputable instance profiledRawJointGuardedCommonTwoRoundSeedTwoFintype :
    Fintype
      (ProfiledRawJointGuardedCommonTwoRoundSeedTwo A strategy hwin
        controllers) := by
  classical
  infer_instance

/-! ## First physical receive -/

/-- Process one's first receive.  The root state is intentionally trivial;
the only informative arguments are its own input and the delivered input. -/
noncomputable def profiledRawJointGuardedCommonTwoRoundFirstRecvOne
    (_state : ProfiledRawJointGuardedCommonTwoRoundInitialOne)
    (own : In₁) (delivered : In₂) :
    Out₁ ×
      ProfiledRawJointGuardedCommonTwoRoundSeedOne A strategy hwin
        controllers :=
  profiledRawJointHybridInitialRootRecvOne A strategy hwin controllers
    (own, delivered)

/-- Process-two first receive mirror. -/
noncomputable def profiledRawJointGuardedCommonTwoRoundFirstRecvTwo
    (_state : ProfiledRawJointGuardedCommonTwoRoundInitialTwo)
    (own : In₂) (delivered : In₁) :
    Out₂ ×
      ProfiledRawJointGuardedCommonTwoRoundSeedTwo A strategy hwin
        controllers :=
  profiledRawJointHybridInitialRootRecvTwo A strategy hwin controllers
    (delivered, own)

section
omit [Inhabited Out₁] [Inhabited Out₂]

/-- On an actual simultaneous first round, the two local receive tables emit
exactly the literal output of the original strategy. -/
theorem profiledRawJointGuardedCommonTwoRoundFirstRecv_outputs_eq_literalBoth
    (first : In₁ × In₂) :
    ((profiledRawJointGuardedCommonTwoRoundFirstRecvOne A strategy hwin
        controllers () first.1 first.2).1,
      (profiledRawJointGuardedCommonTwoRoundFirstRecvTwo A strategy hwin
        controllers () first.2 first.1).1) =
      let round := nextRound strategy []
        ⟨first.1, first.2, Graph.both⟩
      (round.outputOne, round.outputTwo) := by
  exact profiledRawJointHybridInitialRootRecv_outputs_eq_literalBoth A strategy
    hwin controllers first

@[simp] theorem
    profiledRawJointGuardedCommonTwoRoundFirstRecvOne_retains_first
    (first : In₁ × In₂) :
    (profiledRawJointGuardedCommonTwoRoundFirstRecvOne A strategy hwin
      controllers () first.1 first.2).2.common.1 = first :=
  rfl

@[simp] theorem
    profiledRawJointGuardedCommonTwoRoundFirstRecvTwo_retains_first
    (first : In₁ × In₂) :
    (profiledRawJointGuardedCommonTwoRoundFirstRecvTwo A strategy hwin
      controllers () first.2 first.1).2.common.1 = first :=
  rfl

end

/-! ## Second physical receive and guarded-tail installation -/

/-- Process one's second receive.  The output and guarded-tail control are
both reconstructed from its retained first pair and the currently delivered
input. -/
noncomputable def profiledRawJointGuardedCommonTwoRoundSecondRecvOne
    (state : ProfiledRawJointGuardedCommonTwoRoundSeedOne A strategy hwin
      controllers)
    (own : In₁) (delivered : In₂) :
    Out₁ ×
      ProfiledRawJointGuardedCommonTailInitialOne A strategy hwin :=
  let seed := (state.common.1, (own, delivered))
  (profiledRawJointInitialCommonBothOutputOneOfReceive A strategy
      state.common.1 own delivered,
    profiledRawJointGuardedInitialCommonControlRoot A strategy hwin seed)

/-- Process-two second receive mirror. -/
noncomputable def profiledRawJointGuardedCommonTwoRoundSecondRecvTwo
    (state : ProfiledRawJointGuardedCommonTwoRoundSeedTwo A strategy hwin
      controllers)
    (own : In₂) (delivered : In₁) :
    Out₂ ×
      ProfiledRawJointGuardedCommonTailInitialTwo A strategy hwin :=
  let seed := (state.common.1, (delivered, own))
  (profiledRawJointInitialCommonBothOutputTwoOfReceive A strategy
      state.common.1 own delivered,
    profiledRawJointGuardedInitialCommonControlRoot A strategy hwin seed)

/-- On a physical second simultaneous round, the two local output
projections are exactly the literal common one-shot output. -/
@[simp] theorem
    profiledRawJointGuardedCommonTwoRoundSecondRecv_outputs_eq_literalBoth
    (first current : In₁ × In₂) :
    ((profiledRawJointGuardedCommonTwoRoundSecondRecvOne A strategy hwin
        controllers
        (profiledRawJointGuardedCommonTwoRoundFirstRecvOne A strategy hwin
          controllers () first.1 first.2).2 current.1 current.2).1,
      (profiledRawJointGuardedCommonTwoRoundSecondRecvTwo A strategy hwin
        controllers
        (profiledRawJointGuardedCommonTwoRoundFirstRecvTwo A strategy hwin
          controllers () first.2 first.1).2 current.2 current.1).1) =
      profiledRawJointInitialCommonBothOutput A strategy (first, current) :=
  rfl

/-- Expanded literal form of the second-round output theorem. -/
theorem
    profiledRawJointGuardedCommonTwoRoundSecondRecv_outputs_eq_nextRound
    (first current : In₁ × In₂) :
    ((profiledRawJointGuardedCommonTwoRoundSecondRecvOne A strategy hwin
        controllers
        (profiledRawJointGuardedCommonTwoRoundFirstRecvOne A strategy hwin
          controllers () first.1 first.2).2 current.1 current.2).1,
      (profiledRawJointGuardedCommonTwoRoundSecondRecvTwo A strategy hwin
        controllers
        (profiledRawJointGuardedCommonTwoRoundFirstRecvTwo A strategy hwin
          controllers () first.2 first.1).2 current.2 current.1).1) =
      let world := profiledRawJointInitialCommonBothWorld A strategy
        (first, current)
      let round := nextRound strategy (world.procOne A).bothHistory
        ⟨current.1, current.2, Graph.both⟩
      (round.outputOne, round.outputTwo) := by
  rfl

/-- Process one installs exactly the guarded policy root indexed by the two
literal input pairs. -/
@[simp] theorem
    profiledRawJointGuardedCommonTwoRoundSecondRecvOne_installs_root
    (first current : In₁ × In₂) :
    (profiledRawJointGuardedCommonTwoRoundSecondRecvOne A strategy hwin
      controllers
      (profiledRawJointGuardedCommonTwoRoundFirstRecvOne A strategy hwin
        controllers () first.1 first.2).2 current.1 current.2).2 =
      profiledRawJointGuardedInitialCommonControlRoot A strategy hwin
        (first, current) :=
  rfl

/-- Process-two mirror. -/
@[simp] theorem
    profiledRawJointGuardedCommonTwoRoundSecondRecvTwo_installs_root
    (first current : In₁ × In₂) :
    (profiledRawJointGuardedCommonTwoRoundSecondRecvTwo A strategy hwin
      controllers
      (profiledRawJointGuardedCommonTwoRoundFirstRecvTwo A strategy hwin
        controllers () first.2 first.1).2 current.2 current.1).2 =
      profiledRawJointGuardedInitialCommonControlRoot A strategy hwin
        (first, current) :=
  rfl

/-- Hence both local receive maps install definitionally equal tail controls.
This equality uses only the fact that an actual simultaneous receive delivers
the complementary current input to each process. -/
@[simp] theorem
    profiledRawJointGuardedCommonTwoRoundSecondRecv_controls_agree
    (first current : In₁ × In₂) :
    (profiledRawJointGuardedCommonTwoRoundSecondRecvOne A strategy hwin
      controllers
      (profiledRawJointGuardedCommonTwoRoundFirstRecvOne A strategy hwin
        controllers () first.1 first.2).2 current.1 current.2).2 =
    (profiledRawJointGuardedCommonTwoRoundSecondRecvTwo A strategy hwin
      controllers
      (profiledRawJointGuardedCommonTwoRoundFirstRecvTwo A strategy hwin
        controllers () first.2 first.1).2 current.2 current.1).2 :=
  rfl

end

end DetParityAutomaton

end DistributedSynthesis
