/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonLinkedTreeRationalization
import DistributedSynthesis.Formalizations.Lemma.LemSourceFreeBeliefCodePolicyPathAcceptance

/-!
# One exact parent-linked common occurrence

This file packages the strongest result available before a cross-anchor key
is related to a state of one global rational policy.  From one literal common
occurrence it provides:

* the exact parent-linked semantic tree and its validity/child equations;
* one finite rational policy selected from that tree;
* one root move whose whole child table is valid at the root code; and
* acceptance of every path that remains inside that same policy.

The package deliberately contains no map from an arbitrary finite pending
key to a policy state.  Such a map is the separate recurrence/factorization
obligation; hiding it here would reintroduce the cross-history mosaic.
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

private abbrev SemanticPoint :=
  ProfiledRawJointGuardedCommonSemanticPoint A strategy

private abbrev LinkedDPA (initial : SemanticPoint A strategy) :=
  profiledRawJointGuardedCommonLinkedCodeParityDPA A strategy hwin initial

private abbrev LinkedCode :=
  ProfiledRawJointGuardedCommonLinkedCode A strategy hwin

private abbrev LinkedMove :=
  ProfiledRawJointGuardedCommonLinkedMove A strategy hwin

private abbrev LinkedValid :=
  ProfiledRawJointGuardedCommonLinkedMoveValid A strategy hwin

private abbrev LinkedNext :=
  profiledRawJointGuardedCommonLinkedNext A strategy hwin

/-- One finite policy extracted from one exact parent-linked occurrence. -/
structure ProfiledRawJointGuardedCommonLinkedOccurrencePackage
    (initial : SemanticPoint A strategy) where
  policy : ProfiledRawJointGuardedCommonLinkedRationalPolicy A strategy hwin
    initial

/-- The exact linked semantic tree supplies the occurrence package
unconditionally from the original winner. -/
theorem nonempty_profiledRawJointGuardedCommonLinkedOccurrencePackage
    (initial : SemanticPoint A strategy) :
    Nonempty
      (ProfiledRawJointGuardedCommonLinkedOccurrencePackage A strategy hwin
        initial) := by
  rcases nonempty_profiledRawJointGuardedCommonLinkedRationalPolicy A strategy
      hwin initial with ⟨policy⟩
  exact ⟨⟨policy⟩⟩

namespace ProfiledRawJointGuardedCommonLinkedOccurrencePackage

variable {initial : SemanticPoint A strategy}

/-- Reachable root key of the single selected policy. -/
def rootKey
    (package : ProfiledRawJointGuardedCommonLinkedOccurrencePackage A strategy
      hwin initial) :
    ProfiledRawJointGuardedCommonLinkedPolicyKey A strategy hwin initial
      package.policy :=
  ProfiledRawJointGuardedCommonLinkedPolicyKey.root A strategy hwin initial
    package.policy

/-- The one raw parent/whole-child-table move selected at the root. -/
noncomputable def rootMove
    (package : ProfiledRawJointGuardedCommonLinkedOccurrencePackage A strategy
      hwin initial) : LinkedMove A strategy hwin :=
  (package.rootKey A strategy hwin).move A strategy hwin

/-- Root selection is valid at the exact linked root code. -/
theorem rootMove_valid
    (package : ProfiledRawJointGuardedCommonLinkedOccurrencePackage A strategy
      hwin initial) :
    LinkedValid A strategy hwin
      (package.rootKey A strategy hwin).state.1
      (package.rootMove A strategy hwin) :=
  (package.rootKey A strategy hwin).move_valid A strategy hwin

/-- The selected root move names exactly the guarded pair stored in the root
policy state. -/
theorem rootMove_current
    (package : ProfiledRawJointGuardedCommonLinkedOccurrencePackage A strategy
      hwin initial) :
    (package.rootMove A strategy hwin).1 =
      (package.rootKey A strategy hwin).pair A strategy hwin :=
  (package.rootKey A strategy hwin).move_current A strategy hwin

/-- Every input child is selected by that same root move, before the input is
chosen. -/
theorem root_successor_eq
    (package : ProfiledRawJointGuardedCommonLinkedOccurrencePackage A strategy
      hwin initial)
    (input : In₁ × In₂) :
    package.policy.successor (package.rootKey A strategy hwin).state input =
      let childCode :=
        LinkedNext A strategy hwin
          (package.rootKey A strategy hwin).state.1
          (package.rootMove A strategy hwin) input
      (childCode,
        (LinkedDPA A strategy hwin initial).step
          (package.rootKey A strategy hwin).state.2 childCode) :=
  (package.rootKey A strategy hwin).successor_eq A strategy hwin input

/-- A path that starts at this root and follows only successors of this one
policy is accepted.  This is the exact anti-mosaic scope of the package. -/
theorem path_accepts
    (package : ProfiledRawJointGuardedCommonLinkedOccurrencePackage A strategy
      hwin initial)
    (path : SourceFreeBeliefCodeParityPolicyPath
      (LinkedDPA A strategy hwin initial)
      (initial.linkedCode A strategy hwin)
      (LinkedValid A strategy hwin)
      (LinkedNext A strategy hwin)
      package.policy) :
    (LinkedDPA A strategy hwin initial).Accepts
      (path.childCodeWord
        (LinkedDPA A strategy hwin initial)
        (initial.linkedCode A strategy hwin)
        (LinkedValid A strategy hwin)
        (LinkedNext A strategy hwin)
        package.policy) :=
  path.accepts
    (LinkedDPA A strategy hwin initial)
    (initial.linkedCode A strategy hwin)
    (LinkedValid A strategy hwin)
    (LinkedNext A strategy hwin)
    package.policy

end ProfiledRawJointGuardedCommonLinkedOccurrencePackage

end

end DetParityAutomaton

end DistributedSynthesis
