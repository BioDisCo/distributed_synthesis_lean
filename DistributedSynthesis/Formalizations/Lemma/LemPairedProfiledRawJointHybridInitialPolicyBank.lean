/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridCommonInstalledMove
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointOneSidedInitialState

/-!
# The finite bank of common-prefix hybrid policies

The hybrid semantic root depends on the first input pair.  That pair is not
known after a strict initial round, but after an actual simultaneous receive
both processes know it.  Since the input alphabets are finite, we select one
unconditional hybrid policy for every first input pair and collect their
reachable common states in one finite dependent sum.

The local receive projections below take only the stored common control, the
process's own input, and the input delivered by the receive.  They contain no
graph, orientation, or strict-leader argument.
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

variable (strategy : StrategyPair In₁ In₂ Out₁ Out₂)

/-! ## One selected policy at every first input pair -/

/-- Literal common semantic root selected after the initial simultaneous
round with the indicated input pair. -/
abbrev ProfiledRawJointHybridInitialWorld
    (input : In₁ × In₂) :=
  profiledRawJointInitialCommonBaseWorld A strategy input.1 input.2

/-- Tagged finite root code for that input pair. -/
abbrev ProfiledRawJointHybridInitialCode
    (input : In₁ × In₂) : ProfiledRawJointHybridCode A :=
  .common ((profiledRawJointCommonWorldFamily A
    (ProfiledRawJointHybridInitialWorld A strategy input)).incidenceCode A)

/-- Select the unconditional finite-child-code hybrid policy once for this
first input pair. -/
noncomputable def profiledRawJointHybridInitialPolicy
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (input : In₁ × In₂) :
    ProfiledRawJointHybridProvenanceRationalPolicy A strategy
      (ProfiledRawJointHybridInitialCode A strategy input) :=
  Classical.choice
    (nonempty_profiledRawJointHybridProvenanceRationalPolicy A strategy hwin
      (ProfiledRawJointHybridInitialWorld A strategy input))

/-- The selected policy's reachable root, packaged as a common macro. -/
def profiledRawJointHybridInitialCommonKey
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (input : In₁ × In₂) :
    ProfiledRawJointHybridCommonPolicyKey A strategy
      (ProfiledRawJointHybridInitialCode A strategy input)
      (profiledRawJointHybridInitialPolicy A strategy hwin input) where
  incidenceCode :=
    (profiledRawJointCommonWorldFamily A
      (ProfiledRawJointHybridInitialWorld A strategy input)).incidenceCode A
  state := (profiledRawJointHybridInitialPolicy A strategy hwin input).run []
  reachable :=
    profiledRawJointHybridProvenancePolicy_initial_reachable A strategy
      (ProfiledRawJointHybridInitialCode A strategy input)
      (profiledRawJointHybridInitialPolicy A strategy hwin input)
  state_code := by
    have hroot :=
      (profiledRawJointHybridInitialPolicy A strategy hwin input).accepts.1.1
    exact congrArg Prod.fst hroot

/-! ## One finite common-control alphabet -/

/-- A runtime common control remembers the first-pair policy bank index and
one reachable common state of that fixed policy. -/
abbrev ProfiledRawJointHybridCommonControl
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env)) :=
  Σ input : In₁ × In₂,
    ProfiledRawJointHybridCommonPolicyKey A strategy
      (ProfiledRawJointHybridInitialCode A strategy input)
      (profiledRawJointHybridInitialPolicy A strategy hwin input)

noncomputable instance profiledRawJointHybridCommonControlFintype
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env)) :
    Fintype (ProfiledRawJointHybridCommonControl A strategy hwin) := by
  classical
  infer_instance

/-- Enter the common bank after the actual initial simultaneous receive. -/
def profiledRawJointHybridInitialCommonControl
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (input : In₁ × In₂) :
    ProfiledRawJointHybridCommonControl A strategy hwin :=
  ⟨input, profiledRawJointHybridInitialCommonKey A strategy hwin input⟩

noncomputable instance profiledRawJointHybridCommonControlInhabited
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env)) :
    Inhabited (ProfiledRawJointHybridCommonControl A strategy hwin) :=
  ⟨profiledRawJointHybridInitialCommonControl A strategy hwin
    (default, default)⟩

/-! ## Once-selected installed moves and local receive tables -/

/-- Select the provenance package once at each finite common control. -/
noncomputable def profiledRawJointHybridCommonControlInstalled
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (control : ProfiledRawJointHybridCommonControl A strategy hwin) :
    ProfiledRawJointHybridCommonInstalledMove A strategy
      (ProfiledRawJointHybridInitialCode A strategy control.1)
      (profiledRawJointHybridInitialPolicy A strategy hwin control.1)
      control.2 :=
  Classical.choice
    (nonempty_profiledRawJointHybridCommonInstalledMove A strategy
      (ProfiledRawJointHybridInitialCode A strategy control.1)
      (profiledRawJointHybridInitialPolicy A strategy hwin control.1)
      control.2)

/-- Common successor on a genuine simultaneous receive. -/
noncomputable def profiledRawJointHybridCommonControlNext
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (control : ProfiledRawJointHybridCommonControl A strategy hwin)
    (current : In₁ × In₂) :
    ProfiledRawJointHybridCommonControl A strategy hwin :=
  ⟨control.1,
    (profiledRawJointHybridCommonControlInstalled A strategy hwin control
      ).simultaneousSuccessorKey A current⟩

/-- Process one's executable common receive table. -/
noncomputable def profiledRawJointHybridCommonRecvOne
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (control : ProfiledRawJointHybridCommonControl A strategy hwin)
    (own : In₁) (delivered : In₂) :
    Out₁ × ProfiledRawJointHybridCommonControl A strategy hwin :=
  let current := (own, delivered)
  let installed :=
    profiledRawJointHybridCommonControlInstalled A strategy hwin control
  (installed.bothOutputOne A current,
    profiledRawJointHybridCommonControlNext A strategy hwin control current)

/-- Process-two mirror. -/
noncomputable def profiledRawJointHybridCommonRecvTwo
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (control : ProfiledRawJointHybridCommonControl A strategy hwin)
    (own : In₂) (delivered : In₁) :
    Out₂ × ProfiledRawJointHybridCommonControl A strategy hwin :=
  let current := (delivered, own)
  let installed :=
    profiledRawJointHybridCommonControlInstalled A strategy hwin control
  (installed.bothOutputTwo A current,
    profiledRawJointHybridCommonControlNext A strategy hwin control current)

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- On an actual simultaneous receive the two local tables install exactly
the same finite common successor. -/
@[simp] theorem profiledRawJointHybridCommonRecv_controls_agree
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (control : ProfiledRawJointHybridCommonControl A strategy hwin)
    (current : In₁ × In₂) :
    (profiledRawJointHybridCommonRecvOne A strategy hwin control current.1
        current.2).2 =
      (profiledRawJointHybridCommonRecvTwo A strategy hwin control current.2
        current.1).2 :=
  rfl

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- Their physical outputs are the literal common-world simultaneous output
of the one installed move. -/
@[simp] theorem profiledRawJointHybridCommonRecv_outputs
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (control : ProfiledRawJointHybridCommonControl A strategy hwin)
    (current : In₁ × In₂) :
    ((profiledRawJointHybridCommonRecvOne A strategy hwin control current.1
        current.2).1,
      (profiledRawJointHybridCommonRecvTwo A strategy hwin control current.2
        current.1).1) =
      (profiledRawJointHybridCommonControlInstalled A strategy hwin control
        ).literalBothOutput A current := by
  exact (profiledRawJointHybridCommonControlInstalled A strategy hwin control
    ).bothOutputs_eq_literal A current

end

end DetParityAutomaton

end DistributedSynthesis
