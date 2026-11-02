/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemFiniteAcknowledgedExactClosingRelationalInvariant
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonLiteralHeterogeneousSeamTaggedStagedFront

/-!
# Arbitrary-depth output coherence of the right seam fork

The right heterogeneous table has two proof-side members but one shared
blind sender control.  This module makes the resulting delayed fork explicit.
Its open candidate is tagged `false`, its closed candidate is tagged `true`,
and both carry the same dependent table key and sender control.

The table's sender-label and sender-step equalities prove two facts required
by the acknowledged relay:

* both unresolved candidates emit the same no-receive output for every input;
* after a no-receive, they again carry one shared next control, so the same
  fact holds at arbitrary depth.

The Boolean below is stored inside the proof-side delayed fork.  It is never
an input to a runtime transition and is not a graph, orientation, hierarchy,
leader, strict-leader, history, or view signal.
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

private abbrev Package (initial : CommonPoint A strategy) :=
  ProfiledRawJointGuardedCommonDecoratedPolicyPackage A strategy hwin initial
    (CrossValid A strategy hwin)

private abbrev Key
    (package : Package A strategy hwin initial) :=
  ProfiledRawJointGuardedCommonLiteralRightSeamKey A strategy hwin package

private abbrev Installed
    (package : Package A strategy hwin initial)
    (key : Key A strategy hwin package) :=
  package.literalRightSeamInstalled A strategy hwin key

private abbrev SenderControl
    (package : Package A strategy hwin initial)
    (key : Key A strategy hwin package) :=
  ProfiledRawJointLiteralRightBothExactSenderState A strategy hwin
    (Installed A strategy hwin package key)

/-! ## Member-tagged sender candidates -/

/-- One proof-side member of the right seam sender.  The member bit changes
which table controller is used to read the semantic label; the concrete
control is the table's literally shared sender control. -/
abbrev ProfiledRawJointGuardedCommonLiteralRightSeamMemberSenderCandidate
    (package : Package A strategy hwin initial) :=
  Σ key : Key A strategy hwin package,
    Bool × SenderControl A strategy hwin package key

noncomputable instance literalRightSeamMemberSenderCandidateFintype
    (package : Package A strategy hwin initial) :
    Fintype
      (ProfiledRawJointGuardedCommonLiteralRightSeamMemberSenderCandidate A
        strategy hwin package) := by
  classical
  infer_instance

/-- Forget the proof-side member tag and recover the executable table sender
state. -/
def literalRightSeamMemberSenderForget
    (package : Package A strategy hwin initial)
    (candidate :
      ProfiledRawJointGuardedCommonLiteralRightSeamMemberSenderCandidate A
        strategy hwin package) :
    ProfiledRawJointGuardedCommonLiteralRightSeamStagedSenderState A strategy
      hwin package :=
  ⟨candidate.1, candidate.2.2⟩

/-- State-first no-receive for one proof-side member.  Both label and step are
read through that member of the same finite table. -/
noncomputable def literalRightSeamMemberSenderNoRecv
    (package : Package A strategy hwin initial)
    (candidate :
      ProfiledRawJointGuardedCommonLiteralRightSeamMemberSenderCandidate A
        strategy hwin package)
    (input : In₂) :
    ProfiledRawJointGuardedCommonLiteralRightSeamMemberSenderCandidate A
        strategy hwin package × Out₂ :=
  let table :=
    profiledRawJointLiteralRightBothExactHeterogeneousLeftTable A strategy hwin
      (Installed A strategy hwin package candidate.1)
  let controller := table.memberController candidate.2.1
  (⟨candidate.1, candidate.2.1,
      controller.step candidate.2.2 input⟩,
    (controller.labelOf candidate.2.2).1 input)

/-- The member-specific transition forgets to the executable shared sender
step, in both its next control and physical output. -/
theorem literalRightSeamMemberSenderNoRecv_forget
    (package : Package A strategy hwin initial)
    (candidate :
      ProfiledRawJointGuardedCommonLiteralRightSeamMemberSenderCandidate A
        strategy hwin package)
    (input : In₂) :
    package.literalRightSeamMemberSenderForget A strategy hwin
        (package.literalRightSeamMemberSenderNoRecv A strategy hwin candidate
          input).1 =
        (package.literalRightSeamStagedSenderNoRecv A strategy hwin
          (package.literalRightSeamMemberSenderForget A strategy hwin
            candidate) input).2 ∧
      (package.literalRightSeamMemberSenderNoRecv A strategy hwin candidate
        input).2 =
        (package.literalRightSeamStagedSenderNoRecv A strategy hwin
          (package.literalRightSeamMemberSenderForget A strategy hwin
            candidate) input).1 := by
  rcases candidate with ⟨key, member, control⟩
  cases member <;> constructor <;> rfl

/-! ## The canonical unresolved member fork -/

/-- The two seam interpretations at one literally shared table control. -/
def literalRightSeamMemberSenderFork
    (package : Package A strategy hwin initial)
    (key : Key A strategy hwin package)
    (control : SenderControl A strategy hwin package key) :
    FiniteDelayedFork
      (ProfiledRawJointGuardedCommonLiteralRightSeamMemberSenderCandidate A
        strategy hwin package) :=
  ⟨⟨key, false, control⟩, ⟨key, true, control⟩⟩

/-- At every shared control and every private input, the unresolved false/true
fork has one physical sender output. -/
theorem literalRightSeamMemberSenderFork_noRecvOutputCoherent
    (package : Package A strategy hwin initial)
    (key : Key A strategy hwin package)
    (control : SenderControl A strategy hwin package key)
    (input : In₂) :
    (package.literalRightSeamMemberSenderFork A strategy hwin key control
      ).NoRecvMealyOutputCoherent
        (package.literalRightSeamMemberSenderNoRecv A strategy hwin) input := by
  change
    (((profiledRawJointLiteralRightBothExactHeterogeneousLeftTable A strategy
      hwin (Installed A strategy hwin package key)).memberController false
      ).labelOf control).1 input =
    (((profiledRawJointLiteralRightBothExactHeterogeneousLeftTable A strategy
      hwin (Installed A strategy hwin package key)).memberController true
      ).labelOf control).1 input
  exact congrFun
    ((profiledRawJointLiteralRightBothExactHeterogeneousLeftTable A strategy
      hwin (Installed A strategy hwin package key)
      ).memberController_senderLabel_eq false true control) input

/-- One blind step again produces the canonical member fork, now at the one
shared next table control.  This is the replace-not-accumulate equation behind
arbitrary-depth coherence. -/
theorem literalRightSeamMemberSenderFork_noRecvMealy
    (package : Package A strategy hwin initial)
    (key : Key A strategy hwin package)
    (control : SenderControl A strategy hwin package key)
    (input : In₂) :
    let table :=
      profiledRawJointLiteralRightBothExactHeterogeneousLeftTable A strategy
        hwin (Installed A strategy hwin package key)
    (package.literalRightSeamMemberSenderFork A strategy hwin key control
      ).noRecvMealy
        (package.literalRightSeamMemberSenderNoRecv A strategy hwin) input =
      (package.literalRightSeamMemberSenderFork A strategy hwin key
          ((table.memberController false).step control input),
        ((table.memberController false).labelOf control).1 input) := by
  dsimp only
  let table :=
    profiledRawJointLiteralRightBothExactHeterogeneousLeftTable A strategy hwin
      (Installed A strategy hwin package key)
  have hstep :
      (table.memberController false).step control input =
        (table.memberController true).step control input :=
    profiledRawJointLiteralRightBothExactHeterogeneousLeftTable_noRecv_step_eq
      A strategy hwin (Installed A strategy hwin package key) control input
  change
    (FiniteDelayedFork.mk
        (⟨key, false, (table.memberController false).step control input⟩ :
          ProfiledRawJointGuardedCommonLiteralRightSeamMemberSenderCandidate A
            strategy hwin package)
        (⟨key, true, (table.memberController true).step control input⟩ :
          ProfiledRawJointGuardedCommonLiteralRightSeamMemberSenderCandidate A
            strategy hwin package),
      ((table.memberController false).labelOf control).1 input) =
      (FiniteDelayedFork.mk
        (⟨key, false, (table.memberController false).step control input⟩ :
          ProfiledRawJointGuardedCommonLiteralRightSeamMemberSenderCandidate A
            strategy hwin package)
        (⟨key, true, (table.memberController false).step control input⟩ :
          ProfiledRawJointGuardedCommonLiteralRightSeamMemberSenderCandidate A
            strategy hwin package),
      ((table.memberController false).labelOf control).1 input)
  rw [hstep]

/-- Hence coherence is available again for every next input after an
arbitrary current no-receive. -/
theorem literalRightSeamMemberSenderFork_noRecv_preserves_coherent
    (package : Package A strategy hwin initial)
    (key : Key A strategy hwin package)
    (control : SenderControl A strategy hwin package key)
    (input nextInput : In₂) :
    ((package.literalRightSeamMemberSenderFork A strategy hwin key control
      ).noRecvMealy
        (package.literalRightSeamMemberSenderNoRecv A strategy hwin) input).1
      |>.NoRecvMealyOutputCoherent
        (package.literalRightSeamMemberSenderNoRecv A strategy hwin)
        nextInput := by
  rw [package.literalRightSeamMemberSenderFork_noRecvMealy A strategy hwin key
    control input]
  exact package.literalRightSeamMemberSenderFork_noRecvOutputCoherent A strategy
    hwin key _ nextInput

/-! ## Direct acknowledged-relay statements -/

/-- A relay whose current value is the canonical member fork satisfies the
exact `NoRecvOutputCoherent` field consumed by `ExactClosingRelayInvariant`. -/
theorem literalRightSeamMemberSenderRelay_noRecvOutputCoherent
    (package : Package A strategy hwin initial)
    (id : Fin 5) (ack : Option (Fin 5 × Bool))
    (key : Key A strategy hwin package)
    (control : SenderControl A strategy hwin package key)
    (input : In₂) :
    FiniteAcknowledgedDelayedCarrier.NoRecvOutputCoherent
      (package.literalRightSeamMemberSenderNoRecv A strategy hwin)
      (⟨.fork id
          (package.literalRightSeamMemberSenderFork A strategy hwin key
            control), ack⟩ :
        FiniteAcknowledgedDelayedCarrier (Fin 5)
          (ProfiledRawJointGuardedCommonLiteralRightSeamMemberSenderCandidate A
            strategy hwin package))
      input :=
  package.literalRightSeamMemberSenderFork_noRecvOutputCoherent A strategy hwin
    key control input

/-- The acknowledged no-receive advances both member candidates and preserves
coherence for every subsequent input. -/
theorem literalRightSeamMemberSenderRelay_noRecv_preserves_coherent
    (package : Package A strategy hwin initial)
    (id : Fin 5) (ack : Option (Fin 5 × Bool))
    (key : Key A strategy hwin package)
    (control : SenderControl A strategy hwin package key)
    (input nextInput : In₂) :
    FiniteAcknowledgedDelayedCarrier.NoRecvOutputCoherent
      (package.literalRightSeamMemberSenderNoRecv A strategy hwin)
      (FiniteAcknowledgedDelayedCarrier.noRecvMealy
        (package.literalRightSeamMemberSenderNoRecv A strategy hwin)
        (⟨.fork id
            (package.literalRightSeamMemberSenderFork A strategy hwin key
              control), ack⟩ :
          FiniteAcknowledgedDelayedCarrier (Fin 5)
            (ProfiledRawJointGuardedCommonLiteralRightSeamMemberSenderCandidate
              A strategy hwin package)) input).1
      nextInput := by
  exact package.literalRightSeamMemberSenderFork_noRecv_preserves_coherent A
    strategy hwin key control input nextInput

end ProfiledRawJointGuardedCommonDecoratedPolicyPackage

end

end DetParityAutomaton

end DistributedSynthesis
