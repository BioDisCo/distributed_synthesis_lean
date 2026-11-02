/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointUnitPhysicalDirection
import DistributedSynthesis.Formalizations.Lemma.LemSourceFreeBeliefFiniteCodePolicyImage

/-!
# Reachable singleton-code shape and physical policy closes

The recurrent raw-joint construction uses the unique lineage `Unit`.  A
reachable state of the provenance-strengthened policy has a literal semantic
source with exactly its advertised code.  Therefore every live singleton slot
is related to itself by the appropriate stored row pattern.  This is the
finite code-shape fact needed to materialize a physical close at either row.

For an installed move, the concrete right/left physical direction then names
a literal raw one-sided child.  Tagging the finite policy transition by that
child code installs the corresponding target in the finite image of the one
fixed rational policy.  No strict-leader or orientation bit is supplied to a
process; the side remains proof-tree data.
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

/-! ## Semantic reflexivity of every live singleton slot -/

omit [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁] [Fintype In₂] [Fintype Out₁]
    [Fintype Out₂] in
/-- A live process-one slot in a literal singleton semantic state is
reflexive at either physical row in the stored right pattern. -/
theorem ProfiledRawJointOneSidedSemanticState.rightPattern_self_of_currentSlot
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (semantic : ProfiledRawJointOneSidedSemanticState A strategy (I := Unit))
    (root : ProfiledRawJointThreadRoot A)
    (hslot : profiledRawJointOneSidedCurrentSlots A .right
      (semantic.code A) () = some root)
    (row : PairedEntryRow) :
    (semantic.code A).family.rightPattern ((), row) ((), row) = true := by
  cases hmember : semantic.family.right () with
  | none =>
      simp [profiledRawJointOneSidedCurrentSlots,
        ProfiledRawJointOneSidedSemanticState.code,
        ProfiledRawJointSemanticFamily.incidenceCode,
        ProfiledRawJointSemanticFamily.code, hmember] at hslot
  | some member =>
      simp [ProfiledRawJointOneSidedSemanticState.code,
        ProfiledRawJointSemanticFamily.incidenceCode,
        ProfiledRawJointSemanticFamily.code,
        ProfiledRawJointSemanticFamily.rightPattern, hmember]

omit [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁] [Fintype In₂] [Fintype Out₁]
    [Fintype Out₂] in
/-- Process-two/left-pattern mirror. -/
theorem ProfiledRawJointOneSidedSemanticState.leftPattern_self_of_currentSlot
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (semantic : ProfiledRawJointOneSidedSemanticState A strategy (I := Unit))
    (root : ProfiledRawJointThreadRoot A)
    (hslot : profiledRawJointOneSidedCurrentSlots A .left
      (semantic.code A) () = some root)
    (row : PairedEntryRow) :
    (semantic.code A).family.leftPattern ((), row) ((), row) = true := by
  cases hmember : semantic.family.left () with
  | none =>
      simp [profiledRawJointOneSidedCurrentSlots,
        ProfiledRawJointOneSidedSemanticState.code,
        ProfiledRawJointSemanticFamily.incidenceCode,
        ProfiledRawJointSemanticFamily.code, hmember] at hslot
  | some member =>
      simp [ProfiledRawJointOneSidedSemanticState.code,
        ProfiledRawJointSemanticFamily.incidenceCode,
        ProfiledRawJointSemanticFamily.code,
        ProfiledRawJointSemanticFamily.leftPattern, hmember]

/-! ## Reachable policy codes inherit the semantic shape -/

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- Every reachable live right slot of the singleton provenance policy is
reflexive at either row. -/
theorem profiledRawJointOneSidedProvenance_reachable_rightPattern_self
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (initial : ProfiledRawJointOneSidedSemanticState A strategy (I := Unit))
    (policy : ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
      (initial.code A))
    (state : ProfiledRawJointOneSidedProvenancePolicyState A strategy
      (initial.code A))
    (hreachable : SourceFreeBeliefCodeParityRationalPolicy.Reachable
      (profiledRawJointOneSidedCodeParityDPA A (initial.code A))
      (initial.code A)
      (ProfiledRawJointOneSidedProvenanceValid A strategy)
      (profiledRawJointOneSidedFiniteCodeNext A)
      policy state)
    (root : ProfiledRawJointThreadRoot A)
    (hslot : profiledRawJointOneSidedCurrentSlots A .right state.1 () =
      some root)
    (row : PairedEntryRow) :
    state.1.family.rightPattern ((), row) ((), row) = true := by
  obtain ⟨move, semantic, _hmove, hcode, _hsemanticMove⟩ :=
    exists_profiledRawJointOneSidedProvenanceInstalledMove A strategy
      (initial.code A) policy state hreachable
  rw [← hcode] at hslot ⊢
  exact semantic.rightPattern_self_of_currentSlot A root hslot row

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- Reachable live left-slot mirror. -/
theorem profiledRawJointOneSidedProvenance_reachable_leftPattern_self
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (initial : ProfiledRawJointOneSidedSemanticState A strategy (I := Unit))
    (policy : ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
      (initial.code A))
    (state : ProfiledRawJointOneSidedProvenancePolicyState A strategy
      (initial.code A))
    (hreachable : SourceFreeBeliefCodeParityRationalPolicy.Reachable
      (profiledRawJointOneSidedCodeParityDPA A (initial.code A))
      (initial.code A)
      (ProfiledRawJointOneSidedProvenanceValid A strategy)
      (profiledRawJointOneSidedFiniteCodeNext A)
      policy state)
    (root : ProfiledRawJointThreadRoot A)
    (hslot : profiledRawJointOneSidedCurrentSlots A .left state.1 () =
      some root)
    (row : PairedEntryRow) :
    state.1.family.leftPattern ((), row) ((), row) = true := by
  obtain ⟨move, semantic, _hmove, hcode, _hsemanticMove⟩ :=
    exists_profiledRawJointOneSidedProvenanceInstalledMove A strategy
      (initial.code A) policy state hreachable
  rw [← hcode] at hslot ⊢
  exact semantic.leftPattern_self_of_currentSlot A root hslot row

/-! ## Literal physical children are finite-image edges -/

/-- Concrete specialization of the generic finite policy-image relation. -/
abbrev ProfiledRawJointOneSidedProvenanceAllowedTarget
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (initialCode : ProfiledRawJointIncidenceCode A (I := Unit))
    (policy : ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
      initialCode)
    (source target : ProfiledRawJointOneSidedProvenancePolicyState A strategy
      initialCode) : Prop :=
  SourceFreeBeliefFiniteCodePolicyImage.AllowedTarget
    (profiledRawJointOneSidedCodeParityDPA A initialCode)
    initialCode
    (ProfiledRawJointOneSidedProvenanceValid A strategy)
    (profiledRawJointOneSidedNext A)
    policy source target

/-- Complete finite/semantic payload consumed by a right physical-close
monitor.  The chosen lambda remains proof-side package data; neither the side
nor the semantic provenance witness is made observable to a process. -/
structure ProfiledRawJointUnitRightPhysicalClosePackage
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (initialCode : ProfiledRawJointIncidenceCode A (I := Unit))
    (policy : ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
      initialCode)
    (state : ProfiledRawJointOneSidedProvenancePolicyState A strategy
      initialCode)
    (move : ProfiledRawJointLambdaFamilyMove A (I := Unit))
    (source : ProfiledRawRightSlot A)
    (row : PairedEntryRow) (past : List (In₂ × In₁))
    (input : In₂ × In₁) where
  lambda : ProcOnePairedRightLambda
    (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)
  lambda_selected : move.rightLambda () = some lambda
  initial_profile : rightInitialFirstProfile lambda = source.2
  forever : PairedRightForeverAccepts A source.1.1 lambda
  row_functional : state.1.family.rightPattern.RowFunctionalAt ((), row)
  row_reflexive :
    state.1.family.rightPattern ((), row) ((), row) = true
  target : ProfiledRawJointOneSidedProvenancePolicyState A strategy initialCode
  target_eq :
    target =
      let actual := profiledRawJointUnitRightActualDirection
        (In₁ := In₁) (In₂ := In₂) row past input
      let childCode := profiledRawJointOneSidedNext A state.1 move actual
      (childCode,
        (profiledRawJointOneSidedCodeParityDPA A initialCode).step state.2
          childCode)
  allowed : ProfiledRawJointOneSidedProvenanceAllowedTarget A strategy
    initialCode policy state target
  active_slot : target.1.family.left () =
    some (profiledRawRightChildSlot A source lambda row past input)

/-- Complete left-close mirror package. -/
structure ProfiledRawJointUnitLeftPhysicalClosePackage
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (initialCode : ProfiledRawJointIncidenceCode A (I := Unit))
    (policy : ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
      initialCode)
    (state : ProfiledRawJointOneSidedProvenancePolicyState A strategy
      initialCode)
    (move : ProfiledRawJointLambdaFamilyMove A (I := Unit))
    (source : ProfiledRawLeftSlot A)
    (row : PairedEntryRow) (past : List (In₁ × In₂))
    (input : In₁ × In₂) where
  lambda : ProcTwoPairedLeftLambda
    (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)
  lambda_selected : move.leftLambda () = some lambda
  initial_profile : leftInitialFirstProfile lambda = source.2
  forever : PairedLeftForeverAccepts A source.1.1 lambda
  row_functional : state.1.family.leftPattern.RowFunctionalAt ((), row)
  row_reflexive :
    state.1.family.leftPattern ((), row) ((), row) = true
  target : ProfiledRawJointOneSidedProvenancePolicyState A strategy initialCode
  target_eq :
    target =
      let actual := profiledRawJointUnitLeftActualDirection
        (In₁ := In₁) (In₂ := In₂) row past input
      let childCode := profiledRawJointOneSidedNext A state.1 move actual
      (childCode,
        (profiledRawJointOneSidedCodeParityDPA A initialCode).step state.2
          childCode)
  allowed : ProfiledRawJointOneSidedProvenanceAllowedTarget A strategy
    initialCode policy state target
  active_slot : target.1.family.right () =
    some (profiledRawLeftChildSlot A source lambda row past input)

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- A literal right physical close is an edge of the one finite rational
policy, and its target code is exactly the raw one-sided child. -/
theorem ProfiledRawJointOneSidedProvenanceMoveRealizesAt.unitRight_allowedTarget
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (initialCode : ProfiledRawJointIncidenceCode A (I := Unit))
    (policy : ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
      initialCode)
    (state : ProfiledRawJointOneSidedProvenancePolicyState A strategy
      initialCode)
    (move : ProfiledRawJointLambdaFamilyMove A (I := Unit))
    (hmove : ProfiledRawJointOneSidedProvenanceMoveRealizesAt A strategy
      initialCode policy state move)
    (row : PairedEntryRow) (past : List (In₂ × In₁))
    (input : In₂ × In₁) :
    let actual := profiledRawJointUnitRightActualDirection
      (In₁ := In₁) (In₂ := In₂) row past input
    let childCode := profiledRawJointOneSidedNext A state.1 move actual
    ProfiledRawJointOneSidedProvenanceAllowedTarget A strategy initialCode
      policy state
        (childCode,
          (profiledRawJointOneSidedCodeParityDPA A initialCode).step state.2
            childCode) := by
  dsimp only
  refine ⟨profiledRawJointOneSidedNext A state.1 move
    (profiledRawJointUnitRightActualDirection
      (In₁ := In₁) (In₂ := In₂) row past input), ?_⟩
  exact ProfiledRawJointOneSidedProvenanceMoveRealizesAt.successor_eq_raw
    A strategy initialCode policy state move hmove
    (profiledRawJointUnitRightActualDirection
      (In₁ := In₁) (In₂ := In₂) row past input)

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- Left physical-close mirror. -/
theorem ProfiledRawJointOneSidedProvenanceMoveRealizesAt.unitLeft_allowedTarget
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (initialCode : ProfiledRawJointIncidenceCode A (I := Unit))
    (policy : ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
      initialCode)
    (state : ProfiledRawJointOneSidedProvenancePolicyState A strategy
      initialCode)
    (move : ProfiledRawJointLambdaFamilyMove A (I := Unit))
    (hmove : ProfiledRawJointOneSidedProvenanceMoveRealizesAt A strategy
      initialCode policy state move)
    (row : PairedEntryRow) (past : List (In₁ × In₂))
    (input : In₁ × In₂) :
    let actual := profiledRawJointUnitLeftActualDirection
      (In₁ := In₁) (In₂ := In₂) row past input
    let childCode := profiledRawJointOneSidedNext A state.1 move actual
    ProfiledRawJointOneSidedProvenanceAllowedTarget A strategy initialCode
      policy state
        (childCode,
          (profiledRawJointOneSidedCodeParityDPA A initialCode).step state.2
            childCode) := by
  dsimp only
  refine ⟨profiledRawJointOneSidedNext A state.1 move
    (profiledRawJointUnitLeftActualDirection
      (In₁ := In₁) (In₂ := In₂) row past input), ?_⟩
  exact ProfiledRawJointOneSidedProvenanceMoveRealizesAt.successor_eq_raw
    A strategy initialCode policy state move hmove
    (profiledRawJointUnitLeftActualDirection
      (In₁ := In₁) (In₂ := In₂) row past input)

/-! ## Reachable active closes install the literal physical slot -/

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- At a reachable live process-one state, the installed joint move contains
one right lambda.  A concrete physical right close simultaneously installs
its literal child slot and follows an edge of the one rational policy. -/
theorem ProfiledRawJointOneSidedProvenanceMoveRealizesAt.unitRight_physicalClose
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (initial : ProfiledRawJointOneSidedSemanticState A strategy (I := Unit))
    (policy : ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
      (initial.code A))
    (state : ProfiledRawJointOneSidedProvenancePolicyState A strategy
      (initial.code A))
    (hreachable : SourceFreeBeliefCodeParityRationalPolicy.Reachable
      (profiledRawJointOneSidedCodeParityDPA A (initial.code A))
      (initial.code A)
      (ProfiledRawJointOneSidedProvenanceValid A strategy)
      (profiledRawJointOneSidedFiniteCodeNext A)
      policy state)
    (move : ProfiledRawJointLambdaFamilyMove A (I := Unit))
    (hmove : ProfiledRawJointOneSidedProvenanceMoveRealizesAt A strategy
      (initial.code A) policy state move)
    (source : ProfiledRawRightSlot A)
    (hsource : state.1.family.right () = some source)
    (row : PairedEntryRow) (past : List (In₂ × In₁))
    (input : In₂ × In₁) :
    ∃ lambda : ProcOnePairedRightLambda
        (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂),
      move.rightLambda () = some lambda ∧
        let actual := profiledRawJointUnitRightActualDirection
          (In₁ := In₁) (In₂ := In₂) row past input
        let childCode := profiledRawJointOneSidedNext A state.1 move actual
        childCode.family.left () =
            some (profiledRawRightChildSlot A source lambda row past input) ∧
          ProfiledRawJointOneSidedProvenanceAllowedTarget A strategy
            (initial.code A) policy state
              (childCode,
                (profiledRawJointOneSidedCodeParityDPA A (initial.code A)).step
                  state.2 childCode) := by
  have hvalid : move.Valid A state.1.family := hmove.1.1
  rcases hvalid.2.2.2.1 () source hsource with
    ⟨lambda, hlambda, _hprofile, _hforever⟩
  have hcurrent : profiledRawJointOneSidedCurrentSlots A .right state.1 () =
      some (.inl source) := by
    simp [profiledRawJointOneSidedCurrentSlots, hsource]
  have hreflexive :=
    profiledRawJointOneSidedProvenance_reachable_rightPattern_self A strategy
      initial policy state hreachable (.inl source) hcurrent row
  have hfunctional := hvalid.2.1 ((), row)
  refine ⟨lambda, hlambda, ?_, ?_⟩
  · exact profiledRawJointOneSidedNext_unitRight_leftSlot A state.1 move row
      past input source lambda hsource hlambda hfunctional hreflexive
  · exact
      ProfiledRawJointOneSidedProvenanceMoveRealizesAt.unitRight_allowedTarget
        A strategy (initial.code A) policy state move hmove row past input

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- Reachable process-two/left-close mirror. -/
theorem ProfiledRawJointOneSidedProvenanceMoveRealizesAt.unitLeft_physicalClose
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (initial : ProfiledRawJointOneSidedSemanticState A strategy (I := Unit))
    (policy : ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
      (initial.code A))
    (state : ProfiledRawJointOneSidedProvenancePolicyState A strategy
      (initial.code A))
    (hreachable : SourceFreeBeliefCodeParityRationalPolicy.Reachable
      (profiledRawJointOneSidedCodeParityDPA A (initial.code A))
      (initial.code A)
      (ProfiledRawJointOneSidedProvenanceValid A strategy)
      (profiledRawJointOneSidedFiniteCodeNext A)
      policy state)
    (move : ProfiledRawJointLambdaFamilyMove A (I := Unit))
    (hmove : ProfiledRawJointOneSidedProvenanceMoveRealizesAt A strategy
      (initial.code A) policy state move)
    (source : ProfiledRawLeftSlot A)
    (hsource : state.1.family.left () = some source)
    (row : PairedEntryRow) (past : List (In₁ × In₂))
    (input : In₁ × In₂) :
    ∃ lambda : ProcTwoPairedLeftLambda
        (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂),
      move.leftLambda () = some lambda ∧
        let actual := profiledRawJointUnitLeftActualDirection
          (In₁ := In₁) (In₂ := In₂) row past input
        let childCode := profiledRawJointOneSidedNext A state.1 move actual
        childCode.family.right () =
            some (profiledRawLeftChildSlot A source lambda row past input) ∧
          ProfiledRawJointOneSidedProvenanceAllowedTarget A strategy
            (initial.code A) policy state
              (childCode,
                (profiledRawJointOneSidedCodeParityDPA A (initial.code A)).step
                  state.2 childCode) := by
  have hvalid : move.Valid A state.1.family := hmove.1.1
  rcases hvalid.2.2.2.2.2.1 () source hsource with
    ⟨lambda, hlambda, _hprofile, _hforever⟩
  have hcurrent : profiledRawJointOneSidedCurrentSlots A .left state.1 () =
      some (.inr source) := by
    simp [profiledRawJointOneSidedCurrentSlots, hsource]
  have hreflexive :=
    profiledRawJointOneSidedProvenance_reachable_leftPattern_self A strategy
      initial policy state hreachable (.inr source) hcurrent row
  have hfunctional := hvalid.2.2.1 ((), row)
  refine ⟨lambda, hlambda, ?_, ?_⟩
  · exact profiledRawJointOneSidedNext_unitLeft_rightSlot A state.1 move row
      past input source lambda hsource hlambda hfunctional hreflexive
  · exact
      ProfiledRawJointOneSidedProvenanceMoveRealizesAt.unitLeft_allowedTarget
        A strategy (initial.code A) policy state move hmove row past input

/-! ## Monitor-facing close packages -/

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- Package all right-close facts in the form consumed by a finite block
monitor.  In particular, `target` is an exact state of the one fixed policy,
not an independently selected same-code representative. -/
theorem nonempty_profiledRawJointUnitRightPhysicalClosePackage
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (initial : ProfiledRawJointOneSidedSemanticState A strategy (I := Unit))
    (policy : ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
      (initial.code A))
    (state : ProfiledRawJointOneSidedProvenancePolicyState A strategy
      (initial.code A))
    (hreachable : SourceFreeBeliefCodeParityRationalPolicy.Reachable
      (profiledRawJointOneSidedCodeParityDPA A (initial.code A))
      (initial.code A)
      (ProfiledRawJointOneSidedProvenanceValid A strategy)
      (profiledRawJointOneSidedFiniteCodeNext A)
      policy state)
    (move : ProfiledRawJointLambdaFamilyMove A (I := Unit))
    (hmove : ProfiledRawJointOneSidedProvenanceMoveRealizesAt A strategy
      (initial.code A) policy state move)
    (source : ProfiledRawRightSlot A)
    (hsource : state.1.family.right () = some source)
    (row : PairedEntryRow) (past : List (In₂ × In₁))
    (input : In₂ × In₁) :
    Nonempty (ProfiledRawJointUnitRightPhysicalClosePackage A strategy
      (initial.code A) policy state move source row past input) := by
  have hvalid : move.Valid A state.1.family := hmove.1.1
  rcases hvalid.2.2.2.1 () source hsource with
    ⟨lambda, hlambda, hprofile, hforever⟩
  have hcurrent : profiledRawJointOneSidedCurrentSlots A .right state.1 () =
      some (.inl source) := by
    simp [profiledRawJointOneSidedCurrentSlots, hsource]
  have hreflexive :=
    profiledRawJointOneSidedProvenance_reachable_rightPattern_self A strategy
      initial policy state hreachable (.inl source) hcurrent row
  have hfunctional := hvalid.2.1 ((), row)
  let actual := profiledRawJointUnitRightActualDirection
    (In₁ := In₁) (In₂ := In₂) row past input
  let childCode := profiledRawJointOneSidedNext A state.1 move actual
  let target : ProfiledRawJointOneSidedProvenancePolicyState A strategy
      (initial.code A) :=
    (childCode,
      (profiledRawJointOneSidedCodeParityDPA A (initial.code A)).step state.2
        childCode)
  have hallowed : ProfiledRawJointOneSidedProvenanceAllowedTarget A strategy
      (initial.code A) policy state target := by
    simpa [actual, childCode, target] using
      ProfiledRawJointOneSidedProvenanceMoveRealizesAt.unitRight_allowedTarget
        A strategy (initial.code A) policy state move hmove row past input
  have hslot : target.1.family.left () =
      some (profiledRawRightChildSlot A source lambda row past input) := by
    simpa [actual, childCode, target] using
      profiledRawJointOneSidedNext_unitRight_leftSlot A state.1 move row past
        input source lambda hsource hlambda hfunctional hreflexive
  exact ⟨{
    lambda := lambda
    lambda_selected := hlambda
    initial_profile := hprofile
    forever := hforever
    row_functional := hfunctional
    row_reflexive := hreflexive
    target := target
    target_eq := by simp [target, childCode, actual]
    allowed := hallowed
    active_slot := hslot }⟩

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- Left monitor-facing close package. -/
theorem nonempty_profiledRawJointUnitLeftPhysicalClosePackage
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (initial : ProfiledRawJointOneSidedSemanticState A strategy (I := Unit))
    (policy : ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
      (initial.code A))
    (state : ProfiledRawJointOneSidedProvenancePolicyState A strategy
      (initial.code A))
    (hreachable : SourceFreeBeliefCodeParityRationalPolicy.Reachable
      (profiledRawJointOneSidedCodeParityDPA A (initial.code A))
      (initial.code A)
      (ProfiledRawJointOneSidedProvenanceValid A strategy)
      (profiledRawJointOneSidedFiniteCodeNext A)
      policy state)
    (move : ProfiledRawJointLambdaFamilyMove A (I := Unit))
    (hmove : ProfiledRawJointOneSidedProvenanceMoveRealizesAt A strategy
      (initial.code A) policy state move)
    (source : ProfiledRawLeftSlot A)
    (hsource : state.1.family.left () = some source)
    (row : PairedEntryRow) (past : List (In₁ × In₂))
    (input : In₁ × In₂) :
    Nonempty (ProfiledRawJointUnitLeftPhysicalClosePackage A strategy
      (initial.code A) policy state move source row past input) := by
  have hvalid : move.Valid A state.1.family := hmove.1.1
  rcases hvalid.2.2.2.2.2.1 () source hsource with
    ⟨lambda, hlambda, hprofile, hforever⟩
  have hcurrent : profiledRawJointOneSidedCurrentSlots A .left state.1 () =
      some (.inr source) := by
    simp [profiledRawJointOneSidedCurrentSlots, hsource]
  have hreflexive :=
    profiledRawJointOneSidedProvenance_reachable_leftPattern_self A strategy
      initial policy state hreachable (.inr source) hcurrent row
  have hfunctional := hvalid.2.2.1 ((), row)
  let actual := profiledRawJointUnitLeftActualDirection
    (In₁ := In₁) (In₂ := In₂) row past input
  let childCode := profiledRawJointOneSidedNext A state.1 move actual
  let target : ProfiledRawJointOneSidedProvenancePolicyState A strategy
      (initial.code A) :=
    (childCode,
      (profiledRawJointOneSidedCodeParityDPA A (initial.code A)).step state.2
        childCode)
  have hallowed : ProfiledRawJointOneSidedProvenanceAllowedTarget A strategy
      (initial.code A) policy state target := by
    simpa [actual, childCode, target] using
      ProfiledRawJointOneSidedProvenanceMoveRealizesAt.unitLeft_allowedTarget
        A strategy (initial.code A) policy state move hmove row past input
  have hslot : target.1.family.right () =
      some (profiledRawLeftChildSlot A source lambda row past input) := by
    simpa [actual, childCode, target] using
      profiledRawJointOneSidedNext_unitLeft_rightSlot A state.1 move row past
        input source lambda hsource hlambda hfunctional hreflexive
  exact ⟨{
    lambda := lambda
    lambda_selected := hlambda
    initial_profile := hprofile
    forever := hforever
    row_functional := hfunctional
    row_reflexive := hreflexive
    target := target
    target_eq := by simp [target, childCode, actual]
    allowed := hallowed
    active_slot := hslot }⟩

end

end DetParityAutomaton

end DistributedSynthesis
