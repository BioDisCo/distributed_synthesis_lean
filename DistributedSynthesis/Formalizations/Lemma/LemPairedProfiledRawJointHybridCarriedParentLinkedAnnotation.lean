/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointCommonHybridSemanticParity
import DistributedSynthesis.Formalizations.Lemma.LemSourceFreeBeliefCarriedFiniteAnnotation
import DistributedSynthesis.Formalizations.Lemma.LemSourceFreeBeliefCodePolicyPathAcceptance

/-!
# Persistent parent-linked annotations at the hybrid block clock

This is the safe hybrid specialization of the generic carried-annotation
construction.  The proof-side semantic state is extended by one finite
installed package.  A whole hybrid transition computes the complete table of
child packages from one semantic source and the current package; the parent
move stores that table, and the finite successor installs its selected entry
literally at the child.

Unlike an annotation recomputed from a bare one-sided semantic state, the
carried package remembers the package selected at the preceding hierarchy
boundary.  One outer rationalization therefore cannot assemble current data,
raw moves, and child packages from different semantic representatives.

Hybrid directions remain proof-tree data.  No executable state receives the
graph, an orientation, a leader or strict-leader bit, a history, or a view.
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

/-- One semantic source simultaneously explains the public code, raw move,
and the complete next-package table.  The current package is an explicit
argument of `advance`; it is not reconstructed from the bare source. -/
def ProfiledRawJointHybridCarriedParentLinkValid
    (advance : HybridState A strategy → Annotation →
      HybridDirection (In₁ := In₁) (In₂ := In₂) → Annotation)
    (code : ProfiledRawJointHybridCode A)
    (current : Annotation)
    (move : ProfiledRawJointHybridMove A)
    (children : HybridDirection (In₁ := In₁) (In₂ := In₂) →
      Annotation) : Prop :=
  ∃ source : HybridState A strategy,
    source.code A = code ∧
      source.move A = move ∧
      ∀ direction, advance source current direction = children direction

omit [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁] [Fintype In₂] [Fintype Out₁]
    [Fintype Out₂] [Fintype Annotation] in
/-- The carried exact semantic node is its own simultaneous witness. -/
theorem profiledRawJointHybridCarriedParentLinkValid_of_semantic
    (advance : HybridState A strategy → Annotation →
      HybridDirection (In₁ := In₁) (In₂ := In₂) → Annotation)
    (source : HybridState A strategy) (current : Annotation) :
    ProfiledRawJointHybridCarriedParentLinkValid A strategy advance
      (source.code A) current (source.move A)
      (fun direction ↦ advance source current direction) := by
  exact ⟨source, rfl, rfl, fun _ ↦ rfl⟩

/-- Exact hybrid tree extended by the installed finite package. -/
abbrev ProfiledRawJointHybridCarriedSemanticTree
    (initial : ProfiledRawJointCommonBaseWorld A strategy)
    (initialAnnotation : Annotation)
    (advance : HybridState A strategy → Annotation →
      HybridDirection (In₁ := In₁) (In₂ := In₂) → Annotation) :=
  (profiledRawJointHybridSemanticTree A initial).carryFiniteAnnotation
    initialAnnotation advance

/-- The one finite rational policy after carrying and parent-linking the
installed package. -/
noncomputable abbrev ProfiledRawJointHybridCarriedParentLinkedRationalPolicy
    (initial : ProfiledRawJointCommonBaseWorld A strategy)
    (initialAnnotation : Annotation)
    (advance : HybridState A strategy → Annotation →
      HybridDirection (In₁ := In₁) (In₂ := In₂) → Annotation) :=
  SourceFreeBeliefCodeParityRationalPolicy
    (sourceFreeBeliefParentLinkedCodeParityDPA
      (Annotation := Annotation)
      (profiledRawJointHybridCodeParityDPA A
        (.common ((profiledRawJointCommonWorldFamily A initial).incidenceCode
          A))))
    ((.common ((profiledRawJointCommonWorldFamily A initial).incidenceCode A)),
      initialAnnotation)
    (sourceFreeBeliefParentLinkedValid
      (ProfiledRawJointHybridProvenanceValid A strategy)
      (ProfiledRawJointHybridCarriedParentLinkValid A strategy advance))
    (sourceFreeBeliefFiniteCodeNext
      (sourceFreeBeliefParentLinkedNext (profiledRawJointHybridNext A)))

/-- Complete finite state of the carried parent-linked policy. -/
noncomputable abbrev ProfiledRawJointHybridCarriedParentLinkedPolicyState
    (initial : ProfiledRawJointCommonBaseWorld A strategy)
    (initialAnnotation : Annotation)
    (advance : HybridState A strategy → Annotation →
      HybridDirection (In₁ := In₁) (In₂ := In₂) → Annotation) :=
  (sourceFreeBeliefCodeParityRunAutomaton
    (sourceFreeBeliefParentLinkedCodeParityDPA
      (Annotation := Annotation)
      (profiledRawJointHybridCodeParityDPA A
        (.common ((profiledRawJointCommonWorldFamily A initial).incidenceCode
          A))))
    ((.common ((profiledRawJointCommonWorldFamily A initial).incidenceCode A)),
      initialAnnotation)
    (sourceFreeBeliefParentLinkedValid
      (ProfiledRawJointHybridProvenanceValid A strategy)
      (ProfiledRawJointHybridCarriedParentLinkValid A strategy advance))
    (sourceFreeBeliefFiniteCodeNext
      (sourceFreeBeliefParentLinkedNext (profiledRawJointHybridNext A)))).State

/-- Reachability in the single selected carried policy. -/
abbrev ProfiledRawJointHybridCarriedParentLinkedReachable
    (initial : ProfiledRawJointCommonBaseWorld A strategy)
    (initialAnnotation : Annotation)
    (advance : HybridState A strategy → Annotation →
      HybridDirection (In₁ := In₁) (In₂ := In₂) → Annotation)
    (policy : ProfiledRawJointHybridCarriedParentLinkedRationalPolicy A strategy
      initial initialAnnotation advance)
    (state : ProfiledRawJointHybridCarriedParentLinkedPolicyState A strategy
      initial initialAnnotation advance) : Prop :=
  SourceFreeBeliefCodeParityRationalPolicy.Reachable
    (sourceFreeBeliefParentLinkedCodeParityDPA
      (Annotation := Annotation)
      (profiledRawJointHybridCodeParityDPA A
        (.common ((profiledRawJointCommonWorldFamily A initial).incidenceCode
          A))))
    ((.common ((profiledRawJointCommonWorldFamily A initial).incidenceCode A)),
      initialAnnotation)
    (sourceFreeBeliefParentLinkedValid
      (ProfiledRawJointHybridProvenanceValid A strategy)
      (ProfiledRawJointHybridCarriedParentLinkValid A strategy advance))
    (sourceFreeBeliefFiniteCodeNext
      (sourceFreeBeliefParentLinkedNext (profiledRawJointHybridNext A)))
    policy state

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- A winning strategy yields one finite policy carrying any prescribed
finite whole-block package transition.  This uses the checked finite-code
direction rationalization, so no finiteness premise on raw hybrid directions
and no external rational-run basis remain. -/
theorem nonempty_profiledRawJointHybridCarriedParentLinkedRationalPolicy
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (initial : ProfiledRawJointCommonBaseWorld A strategy)
    (initialAnnotation : Annotation)
    (advance : HybridState A strategy → Annotation →
      HybridDirection (In₁ := In₁) (In₂ := In₂) → Annotation) :
    Nonempty
      (ProfiledRawJointHybridCarriedParentLinkedRationalPolicy A strategy
        initial initialAnnotation advance) := by
  let raw := profiledRawJointHybridSemanticTree A initial
  let carried := raw.carryFiniteAnnotation initialAnnotation advance
  let initialCode : ProfiledRawJointHybridCode A :=
    .common ((profiledRawJointCommonWorldFamily A initial).incidenceCode A)
  let certificate :=
    profiledRawJointHybridSemanticTree_codeParityCertificate A strategy hwin
      initial
  let carriedCertificate :=
    certificate.carryFiniteAnnotation
      (profiledRawJointHybridCodeParityDPA A initialCode)
      initialCode
      (ProfiledRawJointHybridProvenanceValid A strategy)
      (profiledRawJointHybridNext A)
      raw initialAnnotation advance
  exact carriedCertificate.nonempty_parentLinkedFiniteCodeDirectionRationalPolicy
    (profiledRawJointHybridCodeParityDPA A initialCode)
    initialCode
    (ProfiledRawJointHybridProvenanceValid A strategy)
    (profiledRawJointHybridNext A)
    carried Prod.snd
    (ProfiledRawJointHybridCarriedParentLinkValid A strategy advance)
    (fun node ↦ by
      let state := carried.stateAt node
      exact
        profiledRawJointHybridCarriedParentLinkValid_of_semantic A strategy
          advance state.1 state.2)

/-! ## Exact code-word and hidden-thread acceptance of one policy branch -/

/-- Positive-time bare hybrid codes along one branch of the carried policy.
The direction alphabet of the rational policy is the finite linked child-code
type; annotations are erased only after the single policy run is fixed. -/
noncomputable def profiledRawJointHybridCarriedPolicyCodeWord
    (initial : ProfiledRawJointCommonBaseWorld A strategy)
    (initialAnnotation : Annotation)
    (advance : HybridState A strategy → Annotation →
      HybridDirection (In₁ := In₁) (In₂ := In₂) → Annotation)
    (policy : ProfiledRawJointHybridCarriedParentLinkedRationalPolicy A strategy
      initial initialAnnotation advance)
    (codeBranch : Nat → SourceFreeBeliefParentLinkedCode
      (BeliefCode := ProfiledRawJointHybridCode A)
      (Annotation := Annotation)) :
    OmegaWord (ProfiledRawJointHybridCode A) :=
  fun n ↦ (policy.run (branchNode codeBranch (n + 1))).1.1

section
omit [Inhabited Out₁] [Inhabited Out₂]

/-- Every finite-code branch of the one carried policy yields an accepted
bare hybrid-code word.  This is a code-DPA statement, not an identification
of the universal monitor state's priority with a physical thread priority. -/
theorem profiledRawJointHybridCarriedPolicyCodeWord_accepts
    (initial : ProfiledRawJointCommonBaseWorld A strategy)
    (initialAnnotation : Annotation)
    (advance : HybridState A strategy → Annotation →
      HybridDirection (In₁ := In₁) (In₂ := In₂) → Annotation)
    (policy : ProfiledRawJointHybridCarriedParentLinkedRationalPolicy A strategy
      initial initialAnnotation advance)
    (codeBranch : Nat → SourceFreeBeliefParentLinkedCode
      (BeliefCode := ProfiledRawJointHybridCode A)
      (Annotation := Annotation)) :
    (profiledRawJointHybridCodeParityDPA A
      (.common ((profiledRawJointCommonWorldFamily A initial).incidenceCode A))
      ).Accepts
        (profiledRawJointHybridCarriedPolicyCodeWord A strategy initial
          initialAnnotation advance policy codeBranch) := by
  let initialCode : ProfiledRawJointHybridCode A :=
    .common ((profiledRawJointCommonWorldFamily A initial).incidenceCode A)
  let linkedDPA := sourceFreeBeliefParentLinkedCodeParityDPA
    (Annotation := Annotation)
    (profiledRawJointHybridCodeParityDPA A initialCode)
  let linkedInitial : SourceFreeBeliefParentLinkedCode
      (BeliefCode := ProfiledRawJointHybridCode A)
      (Annotation := Annotation) :=
    (initialCode, initialAnnotation)
  let linkedValid := sourceFreeBeliefParentLinkedValid
    (ProfiledRawJointHybridProvenanceValid A strategy)
    (ProfiledRawJointHybridCarriedParentLinkValid A strategy advance)
  let linkedRawNext :
      SourceFreeBeliefParentLinkedCode
          (BeliefCode := ProfiledRawJointHybridCode A)
          (Annotation := Annotation) →
        SourceFreeBeliefParentLinkedMove
          (Direction := HybridDirection (In₁ := In₁) (In₂ := In₂))
          (Move := ProfiledRawJointHybridMove A)
          (Annotation := Annotation) →
        HybridDirection (In₁ := In₁) (In₂ := In₂) →
        SourceFreeBeliefParentLinkedCode
          (BeliefCode := ProfiledRawJointHybridCode A)
          (Annotation := Annotation) :=
    sourceFreeBeliefParentLinkedNext (Annotation := Annotation)
      (profiledRawJointHybridNext A)
  let linkedNext := sourceFreeBeliefFiniteCodeNext linkedRawNext
  let path : SourceFreeBeliefCodeParityPolicyPath linkedDPA linkedInitial
      linkedValid linkedNext policy :=
    { state := fun n ↦ policy.run (branchNode codeBranch n)
      direction := codeBranch
      initial := rfl
      successor := fun n ↦
        (policy.successor_at (branchNode codeBranch n) (codeBranch n)).symm }
  have hlinked := path.accepts linkedDPA linkedInitial linkedValid linkedNext
    policy
  change
    ((profiledRawJointHybridCodeParityDPA A initialCode).comap Prod.fst
      ).Accepts _ at hlinked
  rw [DetParityAutomaton.comap_accepts_iff] at hlinked
  simpa only [path, SourceFreeBeliefCodeParityPolicyPath.childCodeWord,
    profiledRawJointHybridCarriedPolicyCodeWord] using hlinked

/-- Exact hidden-thread consequence of the preceding accepted code word.
This is the parity sequence that may be aligned pointwise with physical block
minima.  The universal-DPA policy-state priority is intentionally absent. -/
theorem profiledRawJointHybridCarriedPolicyThreadParity
    (initial : ProfiledRawJointCommonBaseWorld A strategy)
    (initialAnnotation : Annotation)
    (advance : HybridState A strategy → Annotation →
      HybridDirection (In₁ := In₁) (In₂ := In₂) → Annotation)
    (policy : ProfiledRawJointHybridCarriedParentLinkedRationalPolicy A strategy
      initial initialAnnotation advance)
    (codeBranch : Nat → SourceFreeBeliefParentLinkedCode
      (BeliefCode := ProfiledRawJointHybridCode A)
      (Annotation := Annotation))
    (initialSide : IndexedLineageSide) :
    NatSeqMinEvenParity (fun n ↦
      (codedAlternatingIndexedLineageCodeThreadSystem
        (.common ((profiledRawJointCommonWorldFamily A initial).incidenceCode
          A))
        (profiledRawJointHybridCurrentSlots A)
        (profiledRawJointThreadRootPriority A)).priority
        (codedAlternatingIndexedLineageCodeRun
          (.common ((profiledRawJointCommonWorldFamily A initial).incidenceCode
            A))
          (profiledRawJointHybridCurrentSlots A)
          (profiledRawJointHybridCarriedPolicyCodeWord A strategy initial
            initialAnnotation advance policy codeBranch)
          initialSide () n)) := by
  let initialCode : ProfiledRawJointHybridCode A :=
    .common ((profiledRawJointCommonWorldFamily A initial).incidenceCode A)
  let word := profiledRawJointHybridCarriedPolicyCodeWord A strategy initial
    initialAnnotation advance policy codeBranch
  have haccepts :=
    profiledRawJointHybridCarriedPolicyCodeWord_accepts A strategy initial
      initialAnnotation advance policy codeBranch
  have hall :=
    (codedAlternatingIndexedLineageCodeDPA_accepts_iff initialCode
      (profiledRawJointHybridCurrentSlots A)
      (profiledRawJointThreadRootPriority A) word).mp
      (by simpa only [profiledRawJointHybridCodeParityDPA] using haccepts)
  exact hall initialSide ()

/-- Strong inversion at a reachable finite policy state.  One exact source
explains the current code and raw move, while `advance` on that same source
and the installed current package gives every child package in the selected
move. -/
theorem exists_profiledRawJointHybridCarriedParentLinkedSemanticSource
    (initial : ProfiledRawJointCommonBaseWorld A strategy)
    (initialAnnotation : Annotation)
    (advance : HybridState A strategy → Annotation →
      HybridDirection (In₁ := In₁) (In₂ := In₂) → Annotation)
    (policy : ProfiledRawJointHybridCarriedParentLinkedRationalPolicy A strategy
      initial initialAnnotation advance)
    (state : ProfiledRawJointHybridCarriedParentLinkedPolicyState A strategy
      initial initialAnnotation advance)
    (hreachable : ProfiledRawJointHybridCarriedParentLinkedReachable A strategy
      initial initialAnnotation advance policy state) :
    ∃ move : SourceFreeBeliefParentLinkedMove
        (Direction := HybridDirection (In₁ := In₁) (In₂ := In₂))
        (Move := ProfiledRawJointHybridMove A)
        (Annotation := Annotation),
      ∃ source : HybridState A strategy,
        source.code A = state.1.1 ∧
          source.move A = move.1 ∧
          (∀ direction, advance source state.1.2 direction =
            move.2 direction) ∧
          ∀ direction : HybridDirection (In₁ := In₁) (In₂ := In₂),
            policy.successor state
                (sourceFreeBeliefParentLinkedNext
                  (profiledRawJointHybridNext A) state.1 move direction) =
              let childCode := sourceFreeBeliefParentLinkedNext
                (profiledRawJointHybridNext A) state.1 move direction
              (childCode,
                (sourceFreeBeliefParentLinkedCodeParityDPA
                  (Annotation := Annotation)
                  (profiledRawJointHybridCodeParityDPA A
                    (.common ((profiledRawJointCommonWorldFamily A initial
                      ).incidenceCode A)))).step state.2 childCode) := by
  rcases
      SourceFreeBeliefCodeParityRationalPolicy.exists_parentLinkedMove_finiteCodeDirection
        (profiledRawJointHybridCodeParityDPA A
          (.common ((profiledRawJointCommonWorldFamily A initial).incidenceCode
            A)))
        (.common ((profiledRawJointCommonWorldFamily A initial).incidenceCode
          A))
        initialAnnotation
        (ProfiledRawJointHybridProvenanceValid A strategy)
        (ProfiledRawJointHybridCarriedParentLinkValid A strategy advance)
        (profiledRawJointHybridNext A)
        policy state hreachable with
    ⟨move, _hvalid, hlink, hsuccessor⟩
  rcases hlink with ⟨source, hcode, hmove, hchildren⟩
  exact ⟨move, source, hcode, hmove, hchildren, hsuccessor⟩

/-- Operational no-mosaic form of the preceding inversion theorem.  If the
finite policy is queried with the linked child code generated by one actual
whole-block direction, the annotation component of its successor is exactly
`advance` on the one source selected at the parent. -/
theorem exists_profiledRawJointHybridCarriedSuccessorAnnotation
    (initial : ProfiledRawJointCommonBaseWorld A strategy)
    (initialAnnotation : Annotation)
    (advance : HybridState A strategy → Annotation →
      HybridDirection (In₁ := In₁) (In₂ := In₂) → Annotation)
    (policy : ProfiledRawJointHybridCarriedParentLinkedRationalPolicy A strategy
      initial initialAnnotation advance)
    (state : ProfiledRawJointHybridCarriedParentLinkedPolicyState A strategy
      initial initialAnnotation advance)
    (hreachable : ProfiledRawJointHybridCarriedParentLinkedReachable A strategy
      initial initialAnnotation advance policy state) :
    ∃ move : SourceFreeBeliefParentLinkedMove
        (Direction := HybridDirection (In₁ := In₁) (In₂ := In₂))
        (Move := ProfiledRawJointHybridMove A)
        (Annotation := Annotation),
      ∃ source : HybridState A strategy,
        source.code A = state.1.1 ∧
          source.move A = move.1 ∧
          ∀ direction : HybridDirection (In₁ := In₁) (In₂ := In₂),
            (policy.successor state
              (sourceFreeBeliefParentLinkedNext
                (profiledRawJointHybridNext A) state.1 move direction)).1.2 =
              advance source state.1.2 direction := by
  rcases
      exists_profiledRawJointHybridCarriedParentLinkedSemanticSource A strategy
        initial initialAnnotation advance policy state hreachable with
    ⟨move, source, hcode, hmove, hchildren, hsuccessor⟩
  refine ⟨move, source, hcode, hmove, ?_⟩
  intro direction
  rw [hsuccessor direction]
  change move.2 direction = advance source state.1.2 direction
  exact (hchildren direction).symm

end

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- Complete literal child form.  Along every actual whole-block direction,
the finite successor simultaneously carries the bare code of the literal
semantic child and the package selected for that same child by `advance`.
This is the one-step induction rule used by concrete physical paths. -/
theorem exists_profiledRawJointHybridCarriedSuccessorSemantics
    (initial : ProfiledRawJointCommonBaseWorld A strategy)
    (initialAnnotation : Annotation)
    (advance : HybridState A strategy → Annotation →
      HybridDirection (In₁ := In₁) (In₂ := In₂) → Annotation)
    (policy : ProfiledRawJointHybridCarriedParentLinkedRationalPolicy A strategy
      initial initialAnnotation advance)
    (state : ProfiledRawJointHybridCarriedParentLinkedPolicyState A strategy
      initial initialAnnotation advance)
    (hreachable : ProfiledRawJointHybridCarriedParentLinkedReachable A strategy
      initial initialAnnotation advance policy state) :
    ∃ move : SourceFreeBeliefParentLinkedMove
        (Direction := HybridDirection (In₁ := In₁) (In₂ := In₂))
        (Move := ProfiledRawJointHybridMove A)
        (Annotation := Annotation),
      ∃ source : HybridState A strategy,
        source.code A = state.1.1 ∧
          source.move A = move.1 ∧
          ∀ direction : HybridDirection (In₁ := In₁) (In₂ := In₂),
            let childCode := sourceFreeBeliefParentLinkedNext
              (profiledRawJointHybridNext A) state.1 move direction
            let target := policy.successor state childCode
            target.1.1 = (source.step A direction).code A ∧
              target.1.2 = advance source state.1.2 direction := by
  rcases
      exists_profiledRawJointHybridCarriedParentLinkedSemanticSource A strategy
        initial initialAnnotation advance policy state hreachable with
    ⟨move, source, hcode, hmove, hchildren, hsuccessor⟩
  refine ⟨move, source, hcode, hmove, ?_⟩
  intro direction
  simp only
  rw [hsuccessor direction]
  constructor
  · change profiledRawJointHybridNext A state.1.1 move.1 direction =
      (source.step A direction).code A
    rw [← hcode, ← hmove]
    exact (source.step_code A direction).symm
  · change move.2 direction = advance source state.1.2 direction
    exact (hchildren direction).symm

end

end DetParityAutomaton

end DistributedSynthesis
