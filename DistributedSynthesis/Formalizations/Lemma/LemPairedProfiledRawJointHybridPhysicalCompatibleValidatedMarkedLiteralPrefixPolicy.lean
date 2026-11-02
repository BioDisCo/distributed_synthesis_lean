/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleValidatedExtraAnnotation
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleLiteralPrefixCurrent

/-!
# A fresh-root-marked validated literal-prefix policy

The unmarked current-provenance relation deliberately permits both of its
branches at an equal finite annotation.  Consequently it is useful at every
reachable state, but it cannot by itself identify the rational policy root.

This module adds one finite, proof/controller-local freshness bit.  The root
is `(true, seed)` and every semantic transition replaces it by
`(false, advance ...)`.  Validity interprets `true` as the exact initial
common source and interprets `false` as one actual incoming semantic edge.
Thus ordinary reachable inversion now pins the policy root, while all
positive-depth states use the same incoming-edge provenance as before.

The bit carries no graph, hierarchy, informed-side, leader, or strict-leader
information.  In particular no process is asked to recognize a switch of
hierarchy.
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

private abbrev HybridState :=
  ProfiledRawJointHybridSemanticState A strategy

private abbrev HybridDirection :=
  ProfiledRawJointHybridDirection (In₁ := In₁) (In₂ := In₂)

private abbrev LiteralAnnotation :=
  ProfiledRawJointHybridLiteralPrefixEdgeAnnotation A

/-! ## Marked annotation and its invariant -/

/-- A finite freshness marker paired with the existing literal annotation.
`true` occurs only at the installed rational root; replacement writes
`false` on every child. -/
abbrev ProfiledRawJointHybridMarkedLiteralPrefixExtra :=
  Bool × LiteralAnnotation A

/-- Exact marked payload installed at the initial common occurrence. -/
noncomputable def profiledRawJointHybridMarkedLiteralPrefixInitial
    (initial : ProfiledRawJointCommonBaseWorld A strategy) :
    ProfiledRawJointHybridMarkedLiteralPrefixExtra A :=
  (true,
    profiledRawJointHybridLiteralPrefixSeedAnnotation A strategy hwin initial)

/-- Replace-only update.  The old marker is never propagated. -/
noncomputable def profiledRawJointHybridMarkedLiteralPrefixAdvance
    (source : HybridState A strategy)
    (current : ProfiledRawJointHybridMarkedLiteralPrefixExtra A)
    (direction : HybridDirection (In₁ := In₁) (In₂ := In₂)) :
    ProfiledRawJointHybridMarkedLiteralPrefixExtra A :=
  (false,
    profiledRawJointHybridLiteralPrefixAnnotationAdvance A strategy hwin
      source current.2 direction)

/-- The marked root is the exact initial common source.  An unmarked payload
must be the output of one actual incoming semantic edge. -/
def ProfiledRawJointHybridMarkedLiteralPrefixCurrentCompatible
    (initial : ProfiledRawJointCommonBaseWorld A strategy)
    (source : HybridState A strategy)
    (extra : ProfiledRawJointHybridMarkedLiteralPrefixExtra A) : Prop :=
  match extra.1 with
  | true =>
      source = .common initial ∧
        extra.2 =
          profiledRawJointHybridLiteralPrefixSeedAnnotation A strategy hwin
            initial
  | false =>
      ∃ (parent : HybridState A strategy) (old : LiteralAnnotation A)
          (direction : HybridDirection (In₁ := In₁) (In₂ := In₂)),
        parent.step A direction = source ∧
          profiledRawJointHybridLiteralPrefixAnnotationAdvance A strategy hwin
              parent old direction =
            extra.2

theorem profiledRawJointHybridMarkedLiteralPrefixCurrentCompatible_initial
    (initial : ProfiledRawJointCommonBaseWorld A strategy) :
    ProfiledRawJointHybridMarkedLiteralPrefixCurrentCompatible A strategy hwin
      initial (.common initial)
        (profiledRawJointHybridMarkedLiteralPrefixInitial A strategy hwin
          initial) := by
  exact ⟨rfl, rfl⟩

/-- One transition establishes the incoming-edge branch without any
assumption on the old marked payload. -/
theorem profiledRawJointHybridMarkedLiteralPrefixCurrentCompatible_advance
    (initial : ProfiledRawJointCommonBaseWorld A strategy)
    (source : HybridState A strategy)
    (current : ProfiledRawJointHybridMarkedLiteralPrefixExtra A)
    (direction : HybridDirection (In₁ := In₁) (In₂ := In₂)) :
    ProfiledRawJointHybridMarkedLiteralPrefixCurrentCompatible A strategy hwin
      initial (source.step A direction)
        (profiledRawJointHybridMarkedLiteralPrefixAdvance A strategy hwin
          source current direction) := by
  exact ⟨source, current.2, direction, rfl, rfl⟩

/-- Forgetting the fresh-root bit recovers the ordinary current literal
provenance invariant.  This is the adapter used by all positive-depth Tail
lemmas, which therefore do not need to be reproved for the marked carrier. -/
theorem profiledRawJointHybridLiteralPrefixCurrentCompatible_of_marked
    (initial : ProfiledRawJointCommonBaseWorld A strategy)
    (source : HybridState A strategy)
    (extra : ProfiledRawJointHybridMarkedLiteralPrefixExtra A)
    (hvalid :
      ProfiledRawJointHybridMarkedLiteralPrefixCurrentCompatible A strategy
        hwin initial source extra) :
    ProfiledRawJointHybridLiteralPrefixCurrentCompatible A strategy hwin
      initial source extra.2 := by
  rcases extra with ⟨flag, extra⟩
  cases flag with
  | false =>
      exact Or.inr hvalid
  | true =>
      exact Or.inl hvalid

/-- At the exact marked initial payload, validity uniquely identifies both
the initial common semantic source and the literal seed. -/
theorem
    profiledRawJointHybridMarkedLiteralPrefixCurrentCompatible_initial_elim
    (initial : ProfiledRawJointCommonBaseWorld A strategy)
    (source : HybridState A strategy)
    (hvalid :
      ProfiledRawJointHybridMarkedLiteralPrefixCurrentCompatible A strategy
        hwin initial source
          (profiledRawJointHybridMarkedLiteralPrefixInitial A strategy hwin
            initial)) :
    source = .common initial ∧
      (profiledRawJointHybridMarkedLiteralPrefixInitial A strategy hwin
        initial).2 =
        profiledRawJointHybridLiteralPrefixSeedAnnotation A strategy hwin
          initial := by
  exact hvalid

/-! ## Validated finite policy -/

noncomputable abbrev
    ProfiledRawJointHybridPhysicalCompatibleValidatedMarkedLiteralPrefixPolicy
    (initial : ProfiledRawJointCommonBaseWorld A strategy) :=
  ProfiledRawJointHybridPhysicalCompatibleValidatedExtraRationalPolicy A
    strategy hwin initial
      (profiledRawJointHybridMarkedLiteralPrefixInitial A strategy hwin initial)
      (ProfiledRawJointHybridMarkedLiteralPrefixCurrentCompatible A strategy
        hwin initial)
      (profiledRawJointHybridMarkedLiteralPrefixAdvance A strategy hwin)

noncomputable abbrev
    ProfiledRawJointHybridPhysicalCompatibleValidatedMarkedLiteralPrefixPolicyState
    (initial : ProfiledRawJointCommonBaseWorld A strategy) :=
  ProfiledRawJointHybridPhysicalCompatibleValidatedExtraPolicyState A strategy
    hwin initial
      (profiledRawJointHybridMarkedLiteralPrefixInitial A strategy hwin initial)
      (ProfiledRawJointHybridMarkedLiteralPrefixCurrentCompatible A strategy
        hwin initial)
      (profiledRawJointHybridMarkedLiteralPrefixAdvance A strategy hwin)

abbrev
    ProfiledRawJointHybridPhysicalCompatibleValidatedMarkedLiteralPrefixReachable
    (initial : ProfiledRawJointCommonBaseWorld A strategy)
    (policy :
      ProfiledRawJointHybridPhysicalCompatibleValidatedMarkedLiteralPrefixPolicy
        A strategy hwin initial)
    (state :
      ProfiledRawJointHybridPhysicalCompatibleValidatedMarkedLiteralPrefixPolicyState
        A strategy hwin initial) : Prop :=
  ProfiledRawJointHybridPhysicalCompatibleValidatedExtraReachable A strategy
    hwin initial
      (profiledRawJointHybridMarkedLiteralPrefixInitial A strategy hwin initial)
      (ProfiledRawJointHybridMarkedLiteralPrefixCurrentCompatible A strategy
        hwin initial)
      (profiledRawJointHybridMarkedLiteralPrefixAdvance A strategy hwin)
      policy state

theorem
    nonempty_profiledRawJointHybridPhysicalCompatibleValidatedMarkedLiteralPrefixPolicy
    (initial : ProfiledRawJointCommonBaseWorld A strategy) :
    Nonempty
      (ProfiledRawJointHybridPhysicalCompatibleValidatedMarkedLiteralPrefixPolicy
        A strategy hwin initial) := by
  exact
    nonempty_profiledRawJointHybridPhysicalCompatibleValidatedExtraRationalPolicy
      A strategy hwin initial
        (profiledRawJointHybridMarkedLiteralPrefixInitial A strategy hwin
          initial)
        (ProfiledRawJointHybridMarkedLiteralPrefixCurrentCompatible A strategy
          hwin initial)
        (profiledRawJointHybridMarkedLiteralPrefixAdvance A strategy hwin)
        (profiledRawJointHybridMarkedLiteralPrefixCurrentCompatible_initial A
          strategy hwin initial)
        (fun source current direction _ ↦
          profiledRawJointHybridMarkedLiteralPrefixCurrentCompatible_advance A
            strategy hwin initial source current direction)

/-! ## Reachable inversion and the pinned root -/

/-- Reachable inversion specialized to the marked literal carrier. -/
theorem
    exists_profiledRawJointHybridPhysicalCompatibleValidatedMarkedLiteralPrefixSemanticSource
    (initial : ProfiledRawJointCommonBaseWorld A strategy)
    (policy :
      ProfiledRawJointHybridPhysicalCompatibleValidatedMarkedLiteralPrefixPolicy
        A strategy hwin initial)
    (state :
      ProfiledRawJointHybridPhysicalCompatibleValidatedMarkedLiteralPrefixPolicyState
        A strategy hwin initial)
    (hreachable :
      ProfiledRawJointHybridPhysicalCompatibleValidatedMarkedLiteralPrefixReachable
        A strategy hwin initial policy state) :
    ∃ move : SourceFreeBeliefParentLinkedMove
        (Direction := HybridDirection (In₁ := In₁) (In₂ := In₂))
        (Move := ProfiledRawJointHybridMove A)
        (Annotation :=
          ProfiledRawJointHybridPhysicalCompatibleExtraAnnotation A
            (ProfiledRawJointHybridMarkedLiteralPrefixExtra A)),
      ∃ source : HybridState A strategy,
        source.code A = state.1.1 ∧
          source.move A = move.1 ∧
          ProfiledRawJointHybridPhysicalCurrentCompatible A strategy source
            state.1.2.1 ∧
          ProfiledRawJointHybridMarkedLiteralPrefixCurrentCompatible A
            strategy hwin initial source state.1.2.2 ∧
          (∀ direction,
            profiledRawJointHybridPhysicalCompatibleExtraAdvance A strategy
                hwin
                (profiledRawJointHybridMarkedLiteralPrefixAdvance A strategy
                  hwin)
                source state.1.2 direction =
              move.2 direction) ∧
          ∀ direction : HybridDirection (In₁ := In₁) (In₂ := In₂),
            policy.successor state
                (sourceFreeBeliefParentLinkedNext
                  (profiledRawJointHybridNext A) state.1 move direction) =
              let childCode := sourceFreeBeliefParentLinkedNext
                (profiledRawJointHybridNext A) state.1 move direction
              (childCode,
                (sourceFreeBeliefParentLinkedCodeParityDPA
                  (Annotation :=
                    ProfiledRawJointHybridPhysicalCompatibleExtraAnnotation A
                      (ProfiledRawJointHybridMarkedLiteralPrefixExtra A))
                  (profiledRawJointHybridCodeParityDPA A
                    (.common ((profiledRawJointCommonWorldFamily A initial
                      ).incidenceCode A)))).step state.2 childCode) := by
  exact
    exists_profiledRawJointHybridPhysicalCompatibleValidatedExtraSemanticSource
      A strategy hwin initial
        (profiledRawJointHybridMarkedLiteralPrefixInitial A strategy hwin
          initial)
        (ProfiledRawJointHybridMarkedLiteralPrefixCurrentCompatible A strategy
          hwin initial)
        (profiledRawJointHybridMarkedLiteralPrefixAdvance A strategy hwin)
        policy state hreachable

/-- The marked rational root is explained by the literal initial common
occurrence.  In particular its selected raw move is exactly the initial raw
move, and the same move value contains the complete child-annotation map used
by every executable successor.

This is a proof/controller freshness fact.  It does not expose a leader or
hierarchy side to either process. -/
theorem
    exists_profiledRawJointHybridPhysicalCompatibleValidatedMarkedLiteralPrefixRootMove
    (initial : ProfiledRawJointCommonBaseWorld A strategy)
    (policy :
      ProfiledRawJointHybridPhysicalCompatibleValidatedMarkedLiteralPrefixPolicy
        A strategy hwin initial) :
    ∃ move : SourceFreeBeliefParentLinkedMove
        (Direction := HybridDirection (In₁ := In₁) (In₂ := In₂))
        (Move := ProfiledRawJointHybridMove A)
        (Annotation :=
          ProfiledRawJointHybridPhysicalCompatibleExtraAnnotation A
            (ProfiledRawJointHybridMarkedLiteralPrefixExtra A)),
      move.1 = ((.common initial : HybridState A strategy).move A) ∧
        (∀ direction,
          profiledRawJointHybridPhysicalCompatibleExtraAdvance A strategy
              hwin
              (profiledRawJointHybridMarkedLiteralPrefixAdvance A strategy
                hwin)
              (.common initial) (policy.run []).1.2 direction =
            move.2 direction) ∧
        ∀ direction : HybridDirection (In₁ := In₁) (In₂ := In₂),
          policy.successor (policy.run [])
              (sourceFreeBeliefParentLinkedNext
                (profiledRawJointHybridNext A) (policy.run []).1 move
                  direction) =
            let childCode := sourceFreeBeliefParentLinkedNext
              (profiledRawJointHybridNext A) (policy.run []).1 move direction
            (childCode,
              (sourceFreeBeliefParentLinkedCodeParityDPA
                (Annotation :=
                  ProfiledRawJointHybridPhysicalCompatibleExtraAnnotation A
                    (ProfiledRawJointHybridMarkedLiteralPrefixExtra A))
                (profiledRawJointHybridCodeParityDPA A
                  (.common ((profiledRawJointCommonWorldFamily A initial
                    ).incidenceCode A)))).step (policy.run []).2 childCode) := by
  rcases
      exists_profiledRawJointHybridPhysicalCompatibleValidatedMarkedLiteralPrefixSemanticSource
        A strategy hwin initial policy (policy.run []) ⟨[], rfl⟩ with
    ⟨move, source, _hcode, hmove, _hphysical, hextra, hchildren,
      hsuccessor⟩
  have hrootExtra :
      (policy.run []).1.2.2 =
        profiledRawJointHybridMarkedLiteralPrefixInitial A strategy hwin
          initial := by
    exact congrArg (fun state ↦ state.1.2.2) policy.accepts.1.1
  have hsource : source = .common initial := by
    rw [hrootExtra] at hextra
    exact
      (profiledRawJointHybridMarkedLiteralPrefixCurrentCompatible_initial_elim
        A strategy hwin initial source hextra).1
  subst source
  exact ⟨move, hmove.symm, hchildren, hsuccessor⟩

end

end DetParityAutomaton

end DistributedSynthesis
