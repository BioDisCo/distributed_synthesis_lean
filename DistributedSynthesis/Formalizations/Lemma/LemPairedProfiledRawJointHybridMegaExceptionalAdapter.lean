/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridMegaFrontPhase
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridMegaRootStaging

/-!
# The finite exceptional adapter for the hybrid mega carrier

This module is the local transition table above the already completed indexed
recurrent kernel.  Its cases inspect only the process's current finite local
control and, on a receive, the delivered partner control and inputs.  In
particular no case is supplied a graph, orientation, or strict-leader bit.

The optional branches below totalize malformed finite controls whose preceding
guarded output contained no live lane.  Reachable guarded plays use the exact
staged child/root branch; the corresponding safety equations are proved in the
guarded-controller modules.
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

local notation "ExceptionalOne" =>
  ProfiledRawJointHybridMegaExceptionalOne A strategy hwin controllers
    initialBank
local notation "ExceptionalTwo" =>
  ProfiledRawJointHybridMegaExceptionalTwo A strategy hwin controllers
    initialBank
local notation "OneControl" =>
  ProfiledRawJointHybridMegaOneControl A strategy hwin initialBank Unit
    ExceptionalOne
local notation "TwoControl" =>
  ProfiledRawJointHybridMegaTwoControl A strategy hwin initialBank Unit
    ExceptionalTwo

/-! ## Exact staged-root installation -/

/-- Install and execute a right owner at an exact mega root. -/
noncomputable def profiledRawJointHybridMegaStartRightOwner
    (child : ProfiledRawJointHybridMegaChildCode A strategy hwin initialBank)
    (root : ProfiledRawJointHybridMegaRightMacro A strategy hwin initialBank
      child)
    (input : In₁) : Out₁ × OneControl :=
  let source := profiledRawJointHybridMegaChildSource A strategy hwin
    initialBank child
  let policy := profiledRawJointHybridMegaChildPolicy A strategy hwin
    initialBank child
  let bank := profiledRawJointHybridMegaChildControllerBank A strategy hwin
    initialBank child
  let owner := initialProfiledRawJointUnitRightPolicyOwner A strategy source
    policy bank root
  let next := stepProfiledRawJointUnitRightPolicyOwner A strategy source policy
    bank owner input
  (next.1, .rightOwner child next.2)

/-- Install and execute a left owner at an exact mega root. -/
noncomputable def profiledRawJointHybridMegaStartLeftOwner
    (child : ProfiledRawJointHybridMegaChildCode A strategy hwin initialBank)
    (root : ProfiledRawJointHybridMegaLeftMacro A strategy hwin initialBank
      child)
    (input : In₂) : Out₂ × TwoControl :=
  let source := profiledRawJointHybridMegaChildSource A strategy hwin
    initialBank child
  let policy := profiledRawJointHybridMegaChildPolicy A strategy hwin
    initialBank child
  let bank := profiledRawJointHybridMegaChildControllerBank A strategy hwin
    initialBank child
  let owner := initialProfiledRawJointUnitLeftPolicyOwner A strategy source
    policy bank root
  let next := stepProfiledRawJointUnitLeftPolicyOwner A strategy source policy
    bank owner input
  (next.1, .leftOwner child next.2)

/-- Install a left receiver at an exact mega root and execute the current
receive.  The row is carried by the delivered closing receiver. -/
noncomputable def profiledRawJointHybridMegaStartLeftReceiver
    (child : ProfiledRawJointHybridMegaChildCode A strategy hwin initialBank)
    (root : ProfiledRawJointHybridMegaLeftMacro A strategy hwin initialBank
      child)
    (row : PairedEntryRow) (ownInput : In₁) (deliveredInput : In₂) :
    Out₁ × OneControl :=
  let source := profiledRawJointHybridMegaChildSource A strategy hwin
    initialBank child
  let policy := profiledRawJointHybridMegaChildPolicy A strategy hwin
    initialBank child
  let bank := profiledRawJointHybridMegaChildControllerBank A strategy hwin
    initialBank child
  let restart := profiledRawJointUnitRestartLeft A strategy source policy bank
    root row
  let next := continueProfiledRawJointUnitLeftPolicyReceiver A strategy source
    policy bank restart.2 restart.1 (ownInput, deliveredInput)
  (next.1, .leftReceiver child next.2)

/-- Right-receiver mirror. -/
noncomputable def profiledRawJointHybridMegaStartRightReceiver
    (child : ProfiledRawJointHybridMegaChildCode A strategy hwin initialBank)
    (root : ProfiledRawJointHybridMegaRightMacro A strategy hwin initialBank
      child)
    (row : PairedEntryRow) (ownInput : In₂) (deliveredInput : In₁) :
    Out₂ × TwoControl :=
  let source := profiledRawJointHybridMegaChildSource A strategy hwin
    initialBank child
  let policy := profiledRawJointHybridMegaChildPolicy A strategy hwin
    initialBank child
  let bank := profiledRawJointHybridMegaChildControllerBank A strategy hwin
    initialBank child
  let restart := profiledRawJointUnitRestartRight A strategy source policy bank
    root row
  let next := continueProfiledRawJointUnitRightPolicyReceiver A strategy source
    policy bank restart.2 restart.1 (ownInput, deliveredInput)
  (next.1, .rightReceiver child next.2)

/-! ## Checked finite-sibling close installation -/

/-- The deterministic checked key and literal left macro selected by an
installed right sibling target. -/
abbrev ProfiledRawJointHybridMegaInitialRightTargetRoot :=
  Σ checked : ProfiledRawJointHybridInitialSiblingTargetChildCode A strategy,
    ProfiledRawJointHybridMegaLeftMacro A strategy hwin initialBank
      (profiledRawJointHybridMegaChildOfInitialSiblingTarget A strategy hwin
        initialBank checked)

/-- Left-target mirror, carrying a literal right macro. -/
abbrev ProfiledRawJointHybridMegaInitialLeftTargetRoot :=
  Σ checked : ProfiledRawJointHybridInitialSiblingTargetChildCode A strategy,
    ProfiledRawJointHybridMegaRightMacro A strategy hwin initialBank
      (profiledRawJointHybridMegaChildOfInitialSiblingTarget A strategy hwin
        initialBank checked)

/-- Total checked-root lookup for a finite right sibling target. -/
noncomputable def profiledRawJointHybridMegaInitialRightTargetRoot?
    (installation : ProfiledRawJointHybridInitialSiblingInstallation
      (In₁ := In₁) (In₂ := In₂))
    (target : ProfiledRawJointUnitTarget A) :
    Option
      (ProfiledRawJointHybridMegaInitialRightTargetRoot A strategy hwin
        initialBank) :=
  match profiledRawJointHybridMegaInitialRightTargetChild? A strategy
      installation target with
  | none => none
  | some checked =>
      let child :=
        profiledRawJointHybridMegaChildOfInitialSiblingTarget A strategy hwin
          initialBank checked
      match profiledRawJointHybridMegaLeftRoot? A strategy hwin initialBank
          child with
      | none => none
      | some root => some ⟨checked, root⟩

/-- Total checked-root lookup for a finite left sibling target. -/
noncomputable def profiledRawJointHybridMegaInitialLeftTargetRoot?
    (installation : ProfiledRawJointHybridInitialSiblingInstallation
      (In₁ := In₁) (In₂ := In₂))
    (target : ProfiledRawJointUnitTarget A) :
    Option
      (ProfiledRawJointHybridMegaInitialLeftTargetRoot A strategy hwin
        initialBank) :=
  match profiledRawJointHybridMegaInitialLeftTargetChild? A strategy
      installation target with
  | none => none
  | some checked =>
      let child :=
        profiledRawJointHybridMegaChildOfInitialSiblingTarget A strategy hwin
          initialBank checked
      match profiledRawJointHybridMegaRightRoot? A strategy hwin initialBank
          child with
      | none => none
      | some root => some ⟨checked, root⟩

/-- A non-receive closes an installed left sibling receiver into the sixth
mega family.  Malformed states without a checked target are retained only to
totalize the finite local table. -/
noncomputable def
    profiledRawJointHybridMegaInitialLeftReceiverNoRecvOne
    (state : ProfiledRawJointHybridInitialLeftInstalledReceiver A strategy
      hwin)
    (input : In₁) : Out₁ × OneControl := by
  classical
  cases htarget : state.2.2.2 with
  | none =>
      exact (default, .exceptional
        (profiledRawJointHybridMegaExceptionalOneOfPinnedInitial A strategy
          hwin controllers initialBank (.inr (.inr (.inr state)))))
  | some target =>
      cases hchecked :
          profiledRawJointHybridMegaInitialLeftTargetChild? A strategy
            state.1 target with
      | none =>
          exact (default, .exceptional
            (profiledRawJointHybridMegaExceptionalOneOfPinnedInitial A strategy
              hwin controllers initialBank (.inr (.inr (.inr state)))))
      | some checked =>
          let child :=
            profiledRawJointHybridMegaChildOfInitialSiblingTarget A strategy
              hwin initialBank checked
          cases hroot : profiledRawJointHybridMegaRightRoot? A strategy hwin
              initialBank child with
          | none =>
              exact (default, .exceptional
                (profiledRawJointHybridMegaExceptionalOneOfPinnedInitial A
                  strategy hwin controllers initialBank
                    (.inr (.inr (.inr state)))))
          | some root =>
              exact profiledRawJointHybridMegaStartRightOwner A strategy hwin
                controllers initialBank child root input

/-- Right-receiver mirror: a non-receive starts the checked left owner. -/
noncomputable def
    profiledRawJointHybridMegaInitialRightReceiverNoRecvTwo
    (state : ProfiledRawJointHybridInitialRightInstalledReceiver A strategy
      hwin)
    (input : In₂) : Out₂ × TwoControl := by
  classical
  cases htarget : state.2.2.2 with
  | none =>
      exact (default, .exceptional
        (profiledRawJointHybridMegaExceptionalTwoOfPinnedInitial A strategy
          hwin controllers initialBank (.inr (.inr (.inl state)))))
  | some target =>
      cases hchecked :
          profiledRawJointHybridMegaInitialRightTargetChild? A strategy
            state.1 target with
      | none =>
          exact (default, .exceptional
            (profiledRawJointHybridMegaExceptionalTwoOfPinnedInitial A strategy
              hwin controllers initialBank (.inr (.inr (.inl state)))))
      | some checked =>
          let child :=
            profiledRawJointHybridMegaChildOfInitialSiblingTarget A strategy
              hwin initialBank checked
          cases hroot : profiledRawJointHybridMegaLeftRoot? A strategy hwin
              initialBank child with
          | none =>
              exact (default, .exceptional
                (profiledRawJointHybridMegaExceptionalTwoOfPinnedInitial A
                  strategy hwin controllers initialBank
                    (.inr (.inr (.inl state)))))
          | some root =>
              exact profiledRawJointHybridMegaStartLeftOwner A strategy hwin
                controllers initialBank child root input

/-! ## No-receive table -/

/-- Every process-one exceptional no-receive transition. -/
noncomputable def profiledRawJointHybridMegaExceptionalNoRecvOne
    (state : ExceptionalOne) (input : In₁) : Out₁ × OneControl := by
  classical
  rcases state with old | rest
  · rcases old with rootRightOwner | rest
    · let next := stepProfiledRawJointRootRightOwner A strategy controllers
        rootRightOwner input
      exact (next.1, .exceptional (.inl (.inl next.2)))
    · rcases rest with rootLeftReceiver | rest
      · let next := startProfiledRawJointInitialLeftExceptionalOwner A
          strategy initialBank rootLeftReceiver input
        exact match next.2 with
        | none => (next.1, .exceptional (.inl (.inr (.inl rootLeftReceiver))))
        | some owner =>
            (next.1, .exceptional (.inl (.inr (.inr (.inl owner)))))
      · rcases rest with initialLeftOwner | initialRightReceiver
        · let next := stepProfiledRawJointInitialLeftOwner A strategy
            initialBank initialLeftOwner input
          exact (next.1,
            .exceptional (.inl (.inr (.inr (.inl next.2)))))
        · cases hpending : initialRightReceiver.receiver.pending with
          | none =>
              exact (default,
                .exceptional (.inl (.inr (.inr (.inr initialRightReceiver)))))
          | some pending =>
              let tagged : ProfiledRawJointInitialTaggedChildCode A strategy
                  initialBank :=
                .inr ⟨initialRightReceiver.receiver.base.1, pending.1⟩
              let child := profiledRawJointHybridMegaChildOfInitial A strategy
                hwin initialBank tagged
              exact match profiledRawJointHybridMegaRightRoot? A strategy hwin
                  initialBank child with
                | none => (default, .exceptional
                    (.inl (.inr (.inr (.inr initialRightReceiver)))))
                | some root =>
                    profiledRawJointHybridMegaStartRightOwner A strategy hwin
                      controllers initialBank child root input
  · rcases rest with initialShadow | rest
    · let next := profiledRawJointHybridInitialOneShadowNoRecv A strategy
        hwin controllers initialShadow input
      exact (next.1, .exceptional
        (profiledRawJointHybridMegaExceptionalOneOfPinnedInitial A strategy
          hwin controllers initialBank (.inl (.inl next.2))))
    · rcases rest with common | pinned
      · rcases common with commonControl | rest
        · let next := profiledRawJointHybridCommonNoRecvOne A strategy hwin
            commonControl input
          exact (next.1, .exceptional
            (profiledRawJointHybridMegaExceptionalOneOfCommon A strategy hwin
              controllers initialBank (.inr (.inr (.inl next.2)))))
        · rcases rest with shadow | rest
          · let next := profiledRawJointHybridOneShadowNoRecv A strategy hwin
                shadow input
            let recurrent :=
              profiledRawJointHybridOneReplacementOwnerToMega A strategy hwin
                initialBank next.2
            exact (next.1, .rightOwner recurrent.1 recurrent.2)
          · rcases rest with guardOwner | strictReceiver
            · let controller :=
                profiledRawJointHybridShadowRightController A strategy hwin
                  guardOwner.origin
              let label := controller.labelOf guardOwner.owner
              exact (label.1 input, .exceptional
                (profiledRawJointHybridMegaExceptionalOneOfCommon A strategy
                  hwin controllers initialBank
                  (.inr (.inr (.inl
                    ⟨guardOwner.origin,
                      controller.step guardOwner.owner input⟩)))))
            · cases hpending : strictReceiver.receiver.pending with
              | none =>
                  exact (default, .exceptional
                    (profiledRawJointHybridMegaExceptionalOneOfCommon A
                      strategy hwin controllers initialBank
                      (.inr (.inr (.inr strictReceiver)))))
              | some pending =>
                  let exactTag :
                      ProfiledRawJointHybridExactTaggedChildCode A strategy
                        hwin := .inr
                          ⟨strictReceiver.receiver.base.origin, pending.1⟩
                  let child := profiledRawJointHybridMegaChildOfExact A strategy
                    hwin initialBank exactTag
                  exact match profiledRawJointHybridMegaRightRoot? A strategy
                      hwin initialBank child with
                    | none => (default, .exceptional
                        (profiledRawJointHybridMegaExceptionalOneOfCommon A
                          strategy hwin controllers initialBank
                          (.inr (.inr (.inr strictReceiver)))))
                    | some root =>
                        profiledRawJointHybridMegaStartRightOwner A strategy
                          hwin controllers initialBank child root input
      · rcases pinned with oldPinned | rest
        · rcases oldPinned with rightOwner | leftReceiver
          · let next :=
              profiledRawJointHybridInitialImmediateRightOwnerNoRecv A strategy
                hwin rightOwner input
            exact (next.1, .exceptional
              (profiledRawJointHybridMegaExceptionalOneOfPinnedInitial A
                strategy hwin controllers initialBank
                  (.inl (.inl next.2))))
          · let exactTag :=
              profiledRawJointHybridInitialImmediateLeftReceiverChildTag A
                strategy hwin leftReceiver
            let child :=
              profiledRawJointHybridMegaChildOfInitialExact A strategy hwin
                initialBank exactTag
            let root :=
              profiledRawJointHybridInitialImmediateLeftReceiverChildRootMacro
                A strategy hwin leftReceiver
            exact profiledRawJointHybridMegaStartRightOwner A strategy hwin
              controllers initialBank child root input
        · rcases rest with coupled | front
          · let next :=
              profiledRawJointHybridMegaCoupledStartRightOwnerOne A strategy
                hwin coupled input
            exact (next.1, .exceptional
              (profiledRawJointHybridMegaExceptionalOneOfPinnedInitial A
                strategy hwin controllers initialBank
                (.inr (.inr (.inl next.2)))))
          · rcases front with rightOwner | leftReceiver
            · let move := profiledRawJointHybridInitialRightMoveAt A strategy
                hwin rightOwner.1
              let controller := move.memberController A false
              let label := controller.labelOf rightOwner.2
              exact (label.1 input, .exceptional
                (profiledRawJointHybridMegaExceptionalOneOfPinnedInitial A
                  strategy hwin controllers initialBank
                  (.inr (.inr (.inl
                    ⟨rightOwner.1, controller.step rightOwner.2 input⟩)))))
            · exact
                profiledRawJointHybridMegaInitialLeftReceiverNoRecvOne A
                  strategy hwin controllers initialBank leftReceiver input

/-- Every process-two exceptional no-receive transition. -/
noncomputable def profiledRawJointHybridMegaExceptionalNoRecvTwo
    (state : ExceptionalTwo) (input : In₂) : Out₂ × TwoControl := by
  classical
  rcases state with old | rest
  · rcases old with rootRightReceiver | rest
    · let next := startProfiledRawJointInitialRightExceptionalOwner A
          strategy initialBank rootRightReceiver input
      exact match next.2 with
      | none => (next.1, .exceptional (.inl (.inl rootRightReceiver)))
      | some owner =>
          (next.1, .exceptional (.inl (.inr (.inr (.inr owner)))))
    · rcases rest with rootLeftOwner | rest
      · let next := stepProfiledRawJointRootLeftOwner A strategy controllers
          rootLeftOwner input
        exact (next.1, .exceptional (.inl (.inr (.inl next.2))))
      · rcases rest with initialLeftReceiver | initialRightOwner
        · cases hpending : initialLeftReceiver.receiver.pending with
          | none =>
              exact (default,
                .exceptional (.inl (.inr (.inr (.inl initialLeftReceiver)))))
          | some pending =>
              let tagged : ProfiledRawJointInitialTaggedChildCode A strategy
                  initialBank :=
                .inl ⟨initialLeftReceiver.receiver.base.1, pending.1⟩
              let child := profiledRawJointHybridMegaChildOfInitial A strategy
                hwin initialBank tagged
              exact match profiledRawJointHybridMegaLeftRoot? A strategy hwin
                  initialBank child with
                | none => (default, .exceptional
                    (.inl (.inr (.inr (.inl initialLeftReceiver)))))
                | some root =>
                    profiledRawJointHybridMegaStartLeftOwner A strategy hwin
                      controllers initialBank child root input
        · let next := stepProfiledRawJointInitialRightOwner A strategy
            initialBank initialRightOwner input
          exact (next.1,
            .exceptional (.inl (.inr (.inr (.inr next.2)))))
  · rcases rest with initialShadow | rest
    · let next := profiledRawJointHybridInitialTwoShadowNoRecv A strategy
        hwin controllers initialShadow input
      exact (next.1, .exceptional
        (profiledRawJointHybridMegaExceptionalTwoOfPinnedInitial A strategy
          hwin controllers initialBank (.inl (.inr next.2))))
    · rcases rest with common | pinned
      · rcases common with commonControl | rest
        · let next := profiledRawJointHybridCommonNoRecvTwo A strategy hwin
            commonControl input
          exact (next.1, .exceptional
            (profiledRawJointHybridMegaExceptionalTwoOfCommon A strategy hwin
              controllers initialBank (.inr (.inr (.inl next.2)))))
        · rcases rest with shadow | rest
          · let next := profiledRawJointHybridTwoShadowNoRecv A strategy hwin
                shadow input
            let recurrent :=
              profiledRawJointHybridTwoReplacementOwnerToMega A strategy hwin
                initialBank next.2
            exact (next.1, .leftOwner recurrent.1 recurrent.2)
          · rcases rest with guardOwner | strictReceiver
            · let controller :=
                profiledRawJointHybridShadowLeftController A strategy hwin
                  guardOwner.origin
              let label := controller.labelOf guardOwner.owner
              exact (label.1 input, .exceptional
                (profiledRawJointHybridMegaExceptionalTwoOfCommon A strategy
                  hwin controllers initialBank
                  (.inr (.inr (.inl
                    ⟨guardOwner.origin,
                      controller.step guardOwner.owner input⟩)))))
            · cases hpending : strictReceiver.receiver.pending with
              | none =>
                  exact (default, .exceptional
                    (profiledRawJointHybridMegaExceptionalTwoOfCommon A
                      strategy hwin controllers initialBank
                      (.inr (.inr (.inr strictReceiver)))))
              | some pending =>
                  let exactTag :
                      ProfiledRawJointHybridExactTaggedChildCode A strategy
                        hwin := .inl
                          ⟨strictReceiver.receiver.base.origin, pending.1⟩
                  let child := profiledRawJointHybridMegaChildOfExact A strategy
                    hwin initialBank exactTag
                  exact match profiledRawJointHybridMegaLeftRoot? A strategy
                      hwin initialBank child with
                    | none => (default, .exceptional
                        (profiledRawJointHybridMegaExceptionalTwoOfCommon A
                          strategy hwin controllers initialBank
                          (.inr (.inr (.inr strictReceiver)))))
                    | some root =>
                        profiledRawJointHybridMegaStartLeftOwner A strategy
                          hwin controllers initialBank child root input
      · rcases pinned with oldPinned | rest
        · rcases oldPinned with rightReceiver | leftOwner
          · let exactTag :=
              profiledRawJointHybridInitialImmediateRightReceiverChildTag A
                strategy hwin rightReceiver
            let child :=
              profiledRawJointHybridMegaChildOfInitialExact A strategy hwin
                initialBank exactTag
            let root :=
              profiledRawJointHybridInitialImmediateRightReceiverChildRootMacro
                A strategy hwin rightReceiver
            exact profiledRawJointHybridMegaStartLeftOwner A strategy hwin
              controllers initialBank child root input
          · let next :=
              profiledRawJointHybridInitialImmediateLeftOwnerNoRecv A strategy
                hwin leftOwner input
            exact (next.1, .exceptional
              (profiledRawJointHybridMegaExceptionalTwoOfPinnedInitial A
                strategy hwin controllers initialBank
                  (.inl (.inr next.2))))
        · rcases rest with coupled | front
          · let next :=
              profiledRawJointHybridMegaCoupledStartLeftOwnerTwo A strategy
                hwin coupled input
            exact (next.1, .exceptional
              (profiledRawJointHybridMegaExceptionalTwoOfPinnedInitial A
                strategy hwin controllers initialBank
                (.inr (.inr (.inr next.2)))))
          · rcases front with rightReceiver | leftOwner
            · exact
                profiledRawJointHybridMegaInitialRightReceiverNoRecvTwo A
                  strategy hwin controllers initialBank rightReceiver input
            · let move := profiledRawJointHybridInitialLeftMoveAt A strategy
                hwin leftOwner.1
              let controller := move.memberController A false
              let label := controller.labelOf leftOwner.2
              exact (label.1 input, .exceptional
                (profiledRawJointHybridMegaExceptionalTwoOfPinnedInitial A
                  strategy hwin controllers initialBank
                  (.inr (.inr (.inr
                    ⟨leftOwner.1, controller.step leftOwner.2 input⟩)))))

end

end DetParityAutomaton

end DistributedSynthesis
