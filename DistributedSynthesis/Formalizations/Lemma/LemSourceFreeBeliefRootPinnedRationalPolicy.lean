/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemSourceFreeBeliefFiniteCodeDirection
import DistributedSynthesis.Formalizations.Theorem.ThmRootGuardedPolicyActivation

/-!
# One-shot root pinning for source-free belief policies

An initial handoff may have to preserve one finite response of the literal
root move.  Strengthening `Valid code move` globally is wrong: the same code
may recur later, where another valid move is allowed.  The existing
`rootGuarded` construction is exactly the required separation.  Its fresh
Boolean is true only at the root; below every first child it delegates to the
ordinary source-free automaton.

This file specializes that construction to code-observable source-free
belief policies.  `RootPred` may express equality with the literal root move,
or merely equality of a finite response such as a boundary/overlap profile.
The predicate is checked only once.  For finite direction alphabets the
result is unconditional by the checked parity-tree emptiness theorem.  The
last theorem first replaces arbitrary raw directions by finite child-code
tags, so it is the form consumed by the raw-joint construction.
-/

namespace DistributedSynthesis

universe u v w z a

section

variable {Direction : Type u} {Move : Type v} {BeliefCode : Type z}
variable [Fintype BeliefCode]

/-- Root transition predicate for the code-parity automaton.  It repeats the
ordinary source-free transition law and adds `RootPred move` exactly at the
fresh root. -/
def sourceFreeBeliefCodeParityRootAllowed
    (D : DetParityAutomaton.{z, w} BeliefCode)
    (initialCode : BeliefCode)
    (Valid : BeliefCode → Move → Prop)
    (next : BeliefCode → Move → Direction → BeliefCode)
    (RootPred : Move → Prop)
    (children : Direction →
      (sourceFreeBeliefCodeParityRunAutomaton D initialCode Valid next).State) :
    Prop :=
  ∃ move : Move,
    Valid initialCode move ∧ RootPred move ∧
      ∀ direction,
        let childCode := next initialCode move direction
        children direction = (childCode, D.step D.initial childCode)

/-- The installed guarded root move and its complete successor equation. -/
def SourceFreeBeliefCodeParityRootMoveRealizes
    (D : DetParityAutomaton.{z, w} BeliefCode)
    (initialCode : BeliefCode)
    (Valid : BeliefCode → Move → Prop)
    (next : BeliefCode → Move → Direction → BeliefCode)
    (RootPred : Move → Prop)
    (policy :
      ((sourceFreeBeliefCodeParityRunAutomaton D initialCode Valid next)
        |>.rootGuarded
          (sourceFreeBeliefCodeParityRootAllowed D initialCode Valid next
            RootPred)).RationalTransitionPolicy)
    (move : Move) : Prop :=
  Valid initialCode move ∧ RootPred move ∧
    ∀ direction,
      let childCode := next initialCode move direction
      policy.successor
          (true,
            (sourceFreeBeliefCodeParityRunAutomaton D initialCode Valid next)
              |>.initial)
          direction =
        (false, (childCode, D.step D.initial childCode))

/-- One rational accepting guarded policy together with the move installed
at its unique fresh root. -/
structure SourceFreeBeliefCodeParityRootPinnedPolicy
    (D : DetParityAutomaton.{z, w} BeliefCode)
    (initialCode : BeliefCode)
    (Valid : BeliefCode → Move → Prop)
    (next : BeliefCode → Move → Direction → BeliefCode)
    (RootPred : Move → Prop) where
  policy :
    ((sourceFreeBeliefCodeParityRunAutomaton D initialCode Valid next)
      |>.rootGuarded
        (sourceFreeBeliefCodeParityRootAllowed D initialCode Valid next
          RootPred)).RationalTransitionPolicy
  rootMove : Move
  rootMove_realizes : SourceFreeBeliefCodeParityRootMoveRealizes D initialCode
    Valid next RootPred policy rootMove

namespace SourceFreeBeliefCodeParityRootPinnedPolicy

variable
  {D : DetParityAutomaton.{z, w} BeliefCode}
  {initialCode : BeliefCode}
  {Valid : BeliefCode → Move → Prop}
  {next : BeliefCode → Move → Direction → BeliefCode}
  {RootPred : Move → Prop}

/-- Below any first direction the fresh root bit disappears and the policy is
an ordinary source-free code-parity policy.  In particular `RootPred` is not
part of any later transition predicate. -/
noncomputable def ordinaryBelow
    (package : SourceFreeBeliefCodeParityRootPinnedPolicy D initialCode Valid
      next RootPred)
    (first : Direction) :
    ((sourceFreeBeliefCodeParityRunAutomaton D initialCode Valid next)
      |>.withInitial (package.policy.run [first]).2).RationalTransitionPolicy :=
  InputFreeRunParityTreeAutomaton.ordinaryPolicyBelowRootGuard
    (sourceFreeBeliefCodeParityRunAutomaton D initialCode Valid next)
    (sourceFreeBeliefCodeParityRootAllowed D initialCode Valid next RootPred)
    package.policy first

@[simp] theorem ordinaryBelow_successor
    (package : SourceFreeBeliefCodeParityRootPinnedPolicy D initialCode Valid
      next RootPred)
    (first : Direction) :
    (package.ordinaryBelow first).successor =
      fun state direction ↦
        (package.policy.successor (false, state) direction).2 :=
  rfl

end SourceFreeBeliefCodeParityRootPinnedPolicy

namespace SourceFreeBeliefCodeParityCertificate

variable
  (D : DetParityAutomaton.{z, w} BeliefCode)
  (initialCode : BeliefCode)
  (Valid : BeliefCode → Move → Prop)
  (next : BeliefCode → Move → Direction → BeliefCode)
  (raw : SourceFreeBeliefSemanticTree.{u, v, z, a}
    Direction Move BeliefCode)
  (certificate : SourceFreeBeliefCodeParityCertificate D initialCode Valid next
    raw)

include certificate

/-- The exact semantic run satisfies the guarded root transition whenever
its literal root move satisfies `RootPred`. -/
theorem rootAllowed_of_literalRoot
    (RootPred : Move → Prop)
    (hroot : RootPred (raw.move raw.initial)) :
    sourceFreeBeliefCodeParityRootAllowed D initialCode Valid next RootPred
      (fun direction ↦
        SourceFreeBeliefCodeParityCertificate.run D initialCode Valid next raw
          [direction]) := by
  refine ⟨raw.move raw.initial, ?_, hroot, ?_⟩
  · have hvalid := certificate.valid []
    simpa [certificate.initial_code] using hvalid
  · intro direction
    have hcode :
        raw.code (raw.step raw.initial direction) =
          next initialCode (raw.move raw.initial) direction := by
      have hnext := certificate.next_code [] direction
      simpa [certificate.initial_code] using hnext
    apply Prod.ext
    · exact hcode
    · change (raw.codeParityStateAt D [direction]).2 =
        D.step D.initial (next initialCode (raw.move raw.initial) direction)
      have hstep := congrArg Prod.snd
        (raw.codeParityStateAt_append D [] direction)
      simp only [raw.codeParityStateAt_nil] at hstep
      rw [hcode] at hstep
      exact hstep

omit certificate in
/-- Root legality of any guarded rational policy exposes a root move
satisfying the one-shot predicate and the complete guarded successor law. -/
theorem exists_rootMoveRealizes
    (RootPred : Move → Prop)
    (policy :
      ((sourceFreeBeliefCodeParityRunAutomaton D initialCode Valid next)
        |>.rootGuarded
          (sourceFreeBeliefCodeParityRootAllowed D initialCode Valid next
            RootPred)).RationalTransitionPolicy) :
    ∃ move : Move,
      SourceFreeBeliefCodeParityRootMoveRealizes D initialCode Valid next
        RootPred policy move := by
  have hlegal := policy.legal_at []
  rw [policy.accepts.1.1] at hlegal
  change ∃ children,
      sourceFreeBeliefCodeParityRootAllowed D initialCode Valid next RootPred
          children ∧
        policy.successor
            (true,
              (sourceFreeBeliefCodeParityRunAutomaton D initialCode Valid next)
                |>.initial) =
          fun direction ↦ (false, children direction) at hlegal
  rcases hlegal with ⟨children, hallowed, hsuccessor⟩
  rcases hallowed with ⟨move, hvalid, hroot, hchildren⟩
  refine ⟨move, hvalid, hroot, ?_⟩
  intro direction
  rw [hsuccessor]
  change (false, children direction) =
    (false,
      (next initialCode move direction,
        D.step D.initial (next initialCode move direction)))
  rw [hchildren direction]
  rfl

/-- General root-pinned rationalization.  The only external ingredient is
the ordinary rational-run basis for the one-bit guarded automaton. -/
theorem nonempty_rootPinnedRationalPolicy
    (RootPred : Move → Prop)
    (hroot : RootPred (raw.move raw.initial))
    (basis :
      ((sourceFreeBeliefCodeParityRunAutomaton D initialCode Valid next)
        |>.rootGuarded
          (sourceFreeBeliefCodeParityRootAllowed D initialCode Valid next
            RootPred)).RationalRunBasis) :
    Nonempty (SourceFreeBeliefCodeParityRootPinnedPolicy D initialCode Valid
      next RootPred) := by
  let A := sourceFreeBeliefCodeParityRunAutomaton D initialCode Valid next
  let RootAllowed := sourceFreeBeliefCodeParityRootAllowed D initialCode Valid
    next RootPred
  have hguarded : (A.rootGuarded RootAllowed).HasRationalRun :=
    InputFreeRunParityTreeAutomaton.rootGuarded_hasRationalRun A RootAllowed
      (SourceFreeBeliefCodeParityCertificate.run D initialCode Valid next raw)
      (certificate.isAcceptingRun D initialCode Valid next raw)
      (certificate.rootAllowed_of_literalRoot D initialCode Valid next raw
        RootPred hroot)
      basis
  have hpolicy :=
    InputFreeRunParityTreeAutomaton.nonempty_rationalTransitionPolicy_of_hasRationalRun
      (A.rootGuarded RootAllowed) hguarded
  rcases hpolicy with ⟨policy⟩
  rcases SourceFreeBeliefCodeParityCertificate.exists_rootMoveRealizes D
      initialCode Valid next RootPred policy with ⟨move, hmove⟩
  exact ⟨⟨policy, move, hmove⟩⟩

/-- With finite directions, root-pinned rationalization is unconditional. -/
theorem nonempty_rootPinnedRationalPolicy_of_finite
    [Fintype Direction]
    (RootPred : Move → Prop)
    (hroot : RootPred (raw.move raw.initial)) :
    Nonempty (SourceFreeBeliefCodeParityRootPinnedPolicy D initialCode Valid
      next RootPred) := by
  apply certificate.nonempty_rootPinnedRationalPolicy D initialCode Valid next
    raw RootPred hroot
  exact InputFreeRunParityTreeAutomaton.rationalRunBasis_of_finite _

end SourceFreeBeliefCodeParityCertificate

/-! ## Arbitrary raw directions, finite child-code policy -/

variable [Nonempty Direction]

/-- The root-pinned policy after replacing arbitrary raw directions by the
finite child-code alphabet. -/
abbrev SourceFreeBeliefFiniteCodeRootPinnedPolicy
    (D : DetParityAutomaton.{z, w} BeliefCode)
    (initialCode : BeliefCode)
    (Valid : BeliefCode → Move → Prop)
    (rawNext : BeliefCode → Move → Direction → BeliefCode)
    (RootPred : Move → Prop) :=
  SourceFreeBeliefCodeParityRootPinnedPolicy D initialCode Valid
    (sourceFreeBeliefFiniteCodeNext rawNext) RootPred

namespace SourceFreeBeliefCodeParityCertificate

/-- Unconditional finite-code root pinning for an arbitrary-direction raw
semantic tree.  Only the literal root must satisfy `RootPred`; all later
same-code nodes use ordinary `Valid`. -/
theorem nonempty_finiteCodeDirectionRootPinnedRationalPolicy
    (D : DetParityAutomaton.{z, w} BeliefCode)
    (initialCode : BeliefCode)
    (Valid : BeliefCode → Move → Prop)
    (rawNext : BeliefCode → Move → Direction → BeliefCode)
    (raw : SourceFreeBeliefSemanticTree.{u, v, z, a}
      Direction Move BeliefCode)
    (certificate : SourceFreeBeliefCodeParityCertificate D initialCode Valid
      rawNext raw)
    (RootPred : Move → Prop)
    (hroot : RootPred (raw.move raw.initial)) :
    Nonempty (SourceFreeBeliefFiniteCodeRootPinnedPolicy D initialCode Valid
      rawNext RootPred) := by
  let finite := sourceFreeBeliefFiniteCodeSemanticTree raw rawNext
  let finiteCertificate := certificate.finiteCodeDirectionCertificate D
    initialCode Valid rawNext raw
  exact finiteCertificate.nonempty_rootPinnedRationalPolicy_of_finite D
    initialCode Valid (sourceFreeBeliefFiniteCodeNext rawNext) finite RootPred
      hroot

/-- Exact literal-root-move specialization.  This is stronger than pinning a
finite response; callers normally use the predicate form above to avoid
retaining unnecessary infinite move data. -/
theorem nonempty_finiteCodeDirectionExactRootRationalPolicy
    (D : DetParityAutomaton.{z, w} BeliefCode)
    (initialCode : BeliefCode)
    (Valid : BeliefCode → Move → Prop)
    (rawNext : BeliefCode → Move → Direction → BeliefCode)
    (raw : SourceFreeBeliefSemanticTree.{u, v, z, a}
      Direction Move BeliefCode)
    (certificate : SourceFreeBeliefCodeParityCertificate D initialCode Valid
      rawNext raw) :
    Nonempty (SourceFreeBeliefFiniteCodeRootPinnedPolicy D initialCode Valid
      rawNext (fun move ↦ move = raw.move raw.initial)) := by
  exact certificate.nonempty_finiteCodeDirectionRootPinnedRationalPolicy D
    initialCode Valid rawNext raw _ rfl

end SourceFreeBeliefCodeParityCertificate

end


end DistributedSynthesis
