/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointCommonHybridSemanticParity
import DistributedSynthesis.Formalizations.Lemma.LemSourceFreeBeliefParentLinkedFiniteAnnotation

/-!
# Parent-linked annotations at the hybrid block clock

The common/one-sided hybrid semantic tree already uses the right clock: one
proof-tree transition is either one simultaneous round or one complete strict
block.  In particular, a long strict block is not confused with several
simultaneous common-tree steps.

This file attaches an arbitrary finite annotation to that exact hybrid tree
before its one outer rationalization.  The selected move contains the
annotation of every literal hybrid child.  The finite-child-code reduction
then gives an unconditional rational policy even though strict directions
contain unbounded physical prefixes.

The validity relation retains one semantic witness tying together the current
hybrid code, current annotation, raw lambda family, and the complete child
annotation table.  Consequently policy inversion never reconstructs those
four fields from different representatives.  The witness and proof-side
hybrid direction are erased from executable finite states; no process learns
the graph, orientation, or strict leader.
-/

namespace DistributedSynthesis

universe u v x y s b

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
variable {Annotation : Type b} [Fintype Annotation]

private abbrev HybridState :=
  ProfiledRawJointHybridSemanticState A strategy

private abbrev HybridDirection :=
  ProfiledRawJointHybridDirection (In₁ := In₁) (In₂ := In₂)

/-- One proof-only source witnesses the current public data and the entire
child-annotation table simultaneously. -/
def ProfiledRawJointHybridParentLinkValid
    (annotation : HybridState A strategy → Annotation)
    (code : ProfiledRawJointHybridCode A)
    (current : Annotation)
    (move : ProfiledRawJointHybridMove A)
    (children : HybridDirection (In₁ := In₁) (In₂ := In₂) → Annotation) :
    Prop :=
  ∃ source : HybridState A strategy,
    source.code A = code ∧
      annotation source = current ∧
      source.move A = move ∧
      ∀ direction, annotation (source.step A direction) = children direction

omit [Fintype Annotation] [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁] [Fintype In₂]
    [Fintype Out₁] [Fintype Out₂] in
/-- Every exact hybrid node satisfies the linked validity law with itself as
the unique simultaneous witness for the four advertised fields. -/
theorem profiledRawJointHybridParentLinkValid_of_semantic
    (annotation : HybridState A strategy → Annotation)
    (source : HybridState A strategy) :
    ProfiledRawJointHybridParentLinkValid A strategy annotation
      (source.code A) (annotation source) (source.move A)
      (fun direction ↦ annotation (source.step A direction)) := by
  exact ⟨source, rfl, rfl, rfl, fun _ ↦ rfl⟩

/-- Finite linked code at the initial hybrid world. -/
abbrev ProfiledRawJointHybridParentLinkedCode :=
  SourceFreeBeliefParentLinkedCode
    (BeliefCode := ProfiledRawJointHybridCode A)
    (Annotation := Annotation)

/-- Raw hybrid lambda family together with its complete child-annotation
table.  This move type may be infinite; the rational policy state is finite. -/
abbrev ProfiledRawJointHybridParentLinkedMove :=
  SourceFreeBeliefParentLinkedMove
    (Direction := HybridDirection (In₁ := In₁) (In₂ := In₂))
    (Move := ProfiledRawJointHybridMove A)
    (Annotation := Annotation)

/-- The projected code-parity objective on linked hybrid codes. -/
noncomputable abbrev ProfiledRawJointHybridParentLinkedCodeParityDPA
    (initialCode : ProfiledRawJointHybridCode A) :=
  sourceFreeBeliefParentLinkedCodeParityDPA
    (Annotation := Annotation)
    (profiledRawJointHybridCodeParityDPA A initialCode)

/-- Source-free linked successor at the genuine hybrid block clock. -/
noncomputable def profiledRawJointHybridParentLinkedNext
    (code : ProfiledRawJointHybridParentLinkedCode A
      (Annotation := Annotation))
    (move : ProfiledRawJointHybridParentLinkedMove A
      (Annotation := Annotation))
    (direction : HybridDirection (In₁ := In₁) (In₂ := In₂)) :
    ProfiledRawJointHybridParentLinkedCode A (Annotation := Annotation) :=
  sourceFreeBeliefParentLinkedNext (profiledRawJointHybridNext A) code move
    direction

/-- Finite-child-code version of the linked successor. -/
noncomputable def profiledRawJointHybridParentLinkedFiniteCodeNext
    (code : ProfiledRawJointHybridParentLinkedCode A
      (Annotation := Annotation))
    (move : ProfiledRawJointHybridParentLinkedMove A
      (Annotation := Annotation))
    (childCode : ProfiledRawJointHybridParentLinkedCode A
      (Annotation := Annotation)) :
    ProfiledRawJointHybridParentLinkedCode A (Annotation := Annotation) :=
  sourceFreeBeliefFiniteCodeNext
    (profiledRawJointHybridParentLinkedNext A (Annotation := Annotation))
    code move childCode

/-- The single finite rational policy obtained after linking a chosen finite
annotation to the exact hybrid semantic tree. -/
noncomputable abbrev ProfiledRawJointHybridParentLinkedRationalPolicy
    (initial : ProfiledRawJointCommonBaseWorld A strategy)
    (annotation : HybridState A strategy → Annotation) :=
  SourceFreeBeliefCodeParityRationalPolicy
    (ProfiledRawJointHybridParentLinkedCodeParityDPA A
      (Annotation := Annotation)
      (.common ((profiledRawJointCommonWorldFamily A initial).incidenceCode A)))
    ((.common ((profiledRawJointCommonWorldFamily A initial).incidenceCode A)),
      annotation (.common initial))
    (sourceFreeBeliefParentLinkedValid
      (ProfiledRawJointHybridProvenanceValid A strategy)
      (ProfiledRawJointHybridParentLinkValid A strategy annotation))
    (profiledRawJointHybridParentLinkedFiniteCodeNext A)

/-- The complete policy state is finite: linked hybrid code times the
projected parity-monitor state. -/
noncomputable abbrev ProfiledRawJointHybridParentLinkedPolicyState
    (initial : ProfiledRawJointCommonBaseWorld A strategy)
    (annotation : HybridState A strategy → Annotation) :=
  (sourceFreeBeliefCodeParityRunAutomaton
    (ProfiledRawJointHybridParentLinkedCodeParityDPA A
      (Annotation := Annotation)
      (.common ((profiledRawJointCommonWorldFamily A initial).incidenceCode A)))
    ((.common ((profiledRawJointCommonWorldFamily A initial).incidenceCode A)),
      annotation (.common initial))
    (sourceFreeBeliefParentLinkedValid
      (ProfiledRawJointHybridProvenanceValid A strategy)
      (ProfiledRawJointHybridParentLinkValid A strategy annotation))
    (profiledRawJointHybridParentLinkedFiniteCodeNext A)).State

/-- Reachability inside the one selected linked hybrid policy. -/
abbrev ProfiledRawJointHybridParentLinkedReachable
    (initial : ProfiledRawJointCommonBaseWorld A strategy)
    (annotation : HybridState A strategy → Annotation)
    (policy : ProfiledRawJointHybridParentLinkedRationalPolicy A strategy
      initial annotation)
    (state : ProfiledRawJointHybridParentLinkedPolicyState A strategy initial
      annotation) : Prop :=
  SourceFreeBeliefCodeParityRationalPolicy.Reachable
    (ProfiledRawJointHybridParentLinkedCodeParityDPA A
      (Annotation := Annotation)
      (.common ((profiledRawJointCommonWorldFamily A initial).incidenceCode A)))
    ((.common ((profiledRawJointCommonWorldFamily A initial).incidenceCode A)),
      annotation (.common initial))
    (sourceFreeBeliefParentLinkedValid
      (ProfiledRawJointHybridProvenanceValid A strategy)
      (ProfiledRawJointHybridParentLinkValid A strategy annotation))
    (profiledRawJointHybridParentLinkedFiniteCodeNext A)
    policy state

section
omit [Inhabited Out₁] [Inhabited Out₂]

/-- The winning hybrid semantic tree yields the linked finite policy without
an arbitrary-direction rational-run premise. -/
theorem nonempty_profiledRawJointHybridParentLinkedRationalPolicy
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (initial : ProfiledRawJointCommonBaseWorld A strategy)
    (annotation : HybridState A strategy → Annotation) :
    Nonempty
      (ProfiledRawJointHybridParentLinkedRationalPolicy A strategy initial
        annotation) := by
  let raw := profiledRawJointHybridSemanticTree A initial
  let initialCode : ProfiledRawJointHybridCode A :=
    .common ((profiledRawJointCommonWorldFamily A initial).incidenceCode A)
  let certificate :=
    profiledRawJointHybridSemanticTree_codeParityCertificate A strategy hwin
      initial
  exact certificate.nonempty_parentLinkedFiniteCodeDirectionRationalPolicy
    (profiledRawJointHybridCodeParityDPA A initialCode)
    initialCode
    (ProfiledRawJointHybridProvenanceValid A strategy)
    (profiledRawJointHybridNext A)
    raw annotation
    (ProfiledRawJointHybridParentLinkValid A strategy annotation)
    (fun node ↦
      profiledRawJointHybridParentLinkValid_of_semantic A strategy annotation
        (raw.stateAt node))

/-- At every reachable linked state, one installed move exposes one semantic
source for the current code/annotation/raw move and every child annotation.
Moreover every raw hybrid direction is represented by the exact linked child
code in the finite policy. -/
theorem exists_profiledRawJointHybridParentLinkedInstalled
    (initial : ProfiledRawJointCommonBaseWorld A strategy)
    (annotation : HybridState A strategy → Annotation)
    (policy : ProfiledRawJointHybridParentLinkedRationalPolicy A strategy
      initial annotation)
    (state : ProfiledRawJointHybridParentLinkedPolicyState A strategy initial
      annotation)
    (hreachable : ProfiledRawJointHybridParentLinkedReachable A strategy
      initial annotation policy state) :
    ∃ move : ProfiledRawJointHybridParentLinkedMove A
        (Annotation := Annotation),
      ProfiledRawJointHybridProvenanceValid A strategy state.1.1 move.1 ∧
        ProfiledRawJointHybridParentLinkValid A strategy annotation
          state.1.1 state.1.2 move.1 move.2 ∧
        ∀ direction : HybridDirection (In₁ := In₁) (In₂ := In₂),
          policy.successor state
              (profiledRawJointHybridParentLinkedNext A state.1 move
                direction) =
            let childCode :=
              profiledRawJointHybridParentLinkedNext A state.1 move direction
            (childCode,
              (ProfiledRawJointHybridParentLinkedCodeParityDPA A
                (Annotation := Annotation)
                (.common ((profiledRawJointCommonWorldFamily A initial
                  ).incidenceCode A))).step state.2 childCode) := by
  exact
    SourceFreeBeliefCodeParityRationalPolicy.exists_parentLinkedMove_finiteCodeDirection
      (profiledRawJointHybridCodeParityDPA A
        (.common ((profiledRawJointCommonWorldFamily A initial).incidenceCode
          A)))
      (.common ((profiledRawJointCommonWorldFamily A initial).incidenceCode A))
      (annotation (.common initial))
      (ProfiledRawJointHybridProvenanceValid A strategy)
      (ProfiledRawJointHybridParentLinkValid A strategy annotation)
      (profiledRawJointHybridNext A)
      policy state hreachable

/-- Strong inversion form: all current and successor annotations come from
one exact semantic source selected inside the installed policy move. -/
theorem exists_profiledRawJointHybridParentLinkedSemanticSource
    (initial : ProfiledRawJointCommonBaseWorld A strategy)
    (annotation : HybridState A strategy → Annotation)
    (policy : ProfiledRawJointHybridParentLinkedRationalPolicy A strategy
      initial annotation)
    (state : ProfiledRawJointHybridParentLinkedPolicyState A strategy initial
      annotation)
    (hreachable : ProfiledRawJointHybridParentLinkedReachable A strategy
      initial annotation policy state) :
    ∃ move : ProfiledRawJointHybridParentLinkedMove A
        (Annotation := Annotation),
      ∃ source : HybridState A strategy,
        source.code A = state.1.1 ∧
          annotation source = state.1.2 ∧
          source.move A = move.1 ∧
          (∀ direction,
            annotation (source.step A direction) = move.2 direction) ∧
          ∀ direction : HybridDirection (In₁ := In₁) (In₂ := In₂),
            policy.successor state
                (profiledRawJointHybridParentLinkedNext A state.1 move
                  direction) =
              let childCode :=
                profiledRawJointHybridParentLinkedNext A state.1 move direction
              (childCode,
                (ProfiledRawJointHybridParentLinkedCodeParityDPA A
                  (Annotation := Annotation)
                  (.common ((profiledRawJointCommonWorldFamily A initial
                    ).incidenceCode A))).step state.2 childCode) := by
  rcases exists_profiledRawJointHybridParentLinkedInstalled A strategy initial
      annotation policy state hreachable with
    ⟨move, _hprovenance, hlinked, hsuccessor⟩
  rcases hlinked with
    ⟨source, hcode, hcurrent, hmove, hchildren⟩
  exact ⟨move, source, hcode, hcurrent, hmove, hchildren, hsuccessor⟩

end

end

end DetParityAutomaton

end DistributedSynthesis
