/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonTreeRationalization
import DistributedSynthesis.Formalizations.Lemma.LemSourceFreeBeliefFiniteMoveDecoration

/-!
# Finite annotations on the occurrence-sensitive guarded common policy

The common semantic tree already chooses one coherent guarded move pair at
each actual semantic occurrence and one whole child-code assignment for every
next input pair.  Operational integration may need to retain more finite
provenance at that same occurrence (for example, the IDs of two cross tables).
Choosing it after rationalization would be unsound for exactly the same reason
that choosing a new semantic representative would be unsound.

This file decorates the common move before the single outer rationalization.
The annotation is checked by an arbitrary source-free finite predicate.  It
does not enter the child-code transition, so the selected `(pair, extra)` at a
reachable policy state realizes exactly the old all-input successor table.
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
variable [DecidableEq In₁] [DecidableEq In₂]

variable
  (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
  (hwin : ∀ env : EnvironmentSequence In₁ In₂,
    A.Accepts (execution strategy env))

variable {Extra : Type b} [Fintype Extra]

private abbrev CommonPair :=
  ProfiledRawJointGuardedCommonPair A strategy hwin

private abbrev CommonCode :=
  ProfiledRawJointIncidenceCode A (I := Unit)

private abbrev CommonPoint :=
  ProfiledRawJointGuardedCommonSemanticPoint A strategy

/-! ## Decorated source-free interface -/

/-- Source-free validity of one guarded pair and its finite annotation. -/
def ProfiledRawJointGuardedCommonDecoratedMoveValid
    (ExtraValid : CommonCode A → CommonPair A strategy hwin → Extra → Prop)
    (code : CommonCode A) (move : CommonPair A strategy hwin × Extra) :
    Prop :=
  sourceFreeBeliefDecoratedValid
    (ProfiledRawJointGuardedCommonMoveValid A strategy hwin) ExtraValid code
      move

/-- The annotation is retained as policy payload but is deliberately absent
from the common child-code transition. -/
noncomputable def ProfiledRawJointGuardedCommonDecoratedNext
    (code : CommonCode A) (move : CommonPair A strategy hwin × Extra)
    (input : In₁ × In₂) : CommonCode A :=
  sourceFreeBeliefDecoratedNext
    (profiledRawJointGuardedCommonNext A strategy hwin) code move input

/-- Occurrence-sensitive common tree with a finite annotation chosen at the
same semantic point as the guarded pair. -/
noncomputable def profiledRawJointGuardedCommonDecoratedSemanticTree
    (initial : CommonPoint A strategy)
    (extra : CommonPoint A strategy → Extra) :=
  (profiledRawJointGuardedCommonSemanticTree A strategy hwin initial
    ).decorateMove extra

omit [Fintype Extra] in
@[simp] theorem
    profiledRawJointGuardedCommonDecoratedSemanticTree_childCodeWord
    (initial : CommonPoint A strategy)
    (extra : CommonPoint A strategy → Extra)
    (branch : Nat → In₁ × In₂) :
    (profiledRawJointGuardedCommonDecoratedSemanticTree A strategy hwin
      initial extra).childCodeWord branch =
      (profiledRawJointGuardedCommonSemanticTree A strategy hwin initial
        ).childCodeWord branch :=
  rfl

/-! ## One decorated code-parity certificate -/

omit [Fintype Extra] in
/-- Any finite annotation valid at every actual semantic occurrence survives
the common tree's source-free code-parity certificate. -/
theorem
    profiledRawJointGuardedCommonDecoratedSemanticTree_codeParityCertificate
    (initial : CommonPoint A strategy)
    (extra : CommonPoint A strategy → Extra)
    (ExtraValid : CommonCode A → CommonPair A strategy hwin → Extra → Prop)
    (hextra : ∀ point : CommonPoint A strategy,
      ExtraValid (point.code A strategy) (point.move A strategy hwin)
        (extra point)) :
    let raw := profiledRawJointGuardedCommonDecoratedSemanticTree A strategy
      hwin initial extra
    SourceFreeBeliefCodeParityCertificate
      (profiledRawJointGuardedCommonCodeParityDPA A
        (initial.code A strategy))
      (initial.code A strategy)
      (ProfiledRawJointGuardedCommonDecoratedMoveValid A strategy hwin
        ExtraValid)
      (ProfiledRawJointGuardedCommonDecoratedNext A strategy hwin)
      raw := by
  let baseRaw :=
    profiledRawJointGuardedCommonSemanticTree A strategy hwin initial
  let baseCertificate :=
    profiledRawJointGuardedCommonSemanticTree_codeParityCertificate A strategy
      hwin initial
  exact baseCertificate.decorateMove
    (profiledRawJointGuardedCommonCodeParityDPA A
      (initial.code A strategy))
    (initial.code A strategy)
    (ProfiledRawJointGuardedCommonMoveValid A strategy hwin)
    (profiledRawJointGuardedCommonNext A strategy hwin)
    baseRaw extra ExtraValid (fun node ↦ hextra (baseRaw.stateAt node))

/-! ## Decorated rational policy and reachable readout -/

/-- Finite occurrence-sensitive common policy whose selected move contains
both the guarded pair and the pre-rational annotation. -/
noncomputable abbrev ProfiledRawJointGuardedCommonDecoratedRationalPolicy
    (initial : CommonPoint A strategy)
    (ExtraValid : CommonCode A → CommonPair A strategy hwin → Extra → Prop) :=
  SourceFreeBeliefCodeParityRationalPolicy
    (profiledRawJointGuardedCommonCodeParityDPA A
      (initial.code A strategy))
    (initial.code A strategy)
    (ProfiledRawJointGuardedCommonDecoratedMoveValid A strategy hwin
      ExtraValid)
    (ProfiledRawJointGuardedCommonDecoratedNext A strategy hwin)

omit [Fintype Extra] in
/-- The decorated common policy exists unconditionally from the checked
finite-direction rational basis. -/
theorem
    nonempty_profiledRawJointGuardedCommonDecoratedRationalPolicy
    (initial : CommonPoint A strategy)
    (extra : CommonPoint A strategy → Extra)
    (ExtraValid : CommonCode A → CommonPair A strategy hwin → Extra → Prop)
    (hextra : ∀ point : CommonPoint A strategy,
      ExtraValid (point.code A strategy) (point.move A strategy hwin)
        (extra point)) :
    Nonempty
      (ProfiledRawJointGuardedCommonDecoratedRationalPolicy A strategy hwin
        initial ExtraValid) := by
  let raw := profiledRawJointGuardedCommonDecoratedSemanticTree A strategy
    hwin initial extra
  let certificate :=
    profiledRawJointGuardedCommonDecoratedSemanticTree_codeParityCertificate A
      strategy hwin initial extra ExtraValid hextra
  exact SourceFreeBeliefCodeParityCertificate.nonempty_rationalPolicy
    (profiledRawJointGuardedCommonCodeParityDPA A
      (initial.code A strategy))
    (initial.code A strategy)
    (ProfiledRawJointGuardedCommonDecoratedMoveValid A strategy hwin
      ExtraValid)
    (ProfiledRawJointGuardedCommonDecoratedNext A strategy hwin)
    raw certificate
    (InputFreeRunParityTreeAutomaton.rationalRunBasis_of_finite _)

/-- Reachability inside one selected decorated common policy. -/
abbrev ProfiledRawJointGuardedCommonDecoratedPolicyReachable
    (initial : CommonPoint A strategy)
    (ExtraValid : CommonCode A → CommonPair A strategy hwin → Extra → Prop)
    (policy : ProfiledRawJointGuardedCommonDecoratedRationalPolicy A strategy
      hwin initial ExtraValid)
    (state : (sourceFreeBeliefCodeParityRunAutomaton
      (profiledRawJointGuardedCommonCodeParityDPA A
        (initial.code A strategy))
      (initial.code A strategy)
      (ProfiledRawJointGuardedCommonDecoratedMoveValid A strategy hwin
        ExtraValid)
      (ProfiledRawJointGuardedCommonDecoratedNext A strategy hwin)).State) :
    Prop :=
  SourceFreeBeliefCodeParityRationalPolicy.Reachable
    (profiledRawJointGuardedCommonCodeParityDPA A
      (initial.code A strategy))
    (initial.code A strategy)
    (ProfiledRawJointGuardedCommonDecoratedMoveValid A strategy hwin
      ExtraValid)
    (ProfiledRawJointGuardedCommonDecoratedNext A strategy hwin)
    policy state

omit [Fintype Extra] in
/-- At every reachable policy state, one valid `(guarded pair, extra)` is
read once and realizes the unchanged whole child-code table for every input
pair.  This is the concrete integration socket for finite cross-table IDs. -/
theorem exists_profiledRawJointGuardedCommonDecoratedMoveAt
    (initial : CommonPoint A strategy)
    (ExtraValid : CommonCode A → CommonPair A strategy hwin → Extra → Prop)
    (policy : ProfiledRawJointGuardedCommonDecoratedRationalPolicy A strategy
      hwin initial ExtraValid)
    (state : (sourceFreeBeliefCodeParityRunAutomaton
      (profiledRawJointGuardedCommonCodeParityDPA A
        (initial.code A strategy))
      (initial.code A strategy)
      (ProfiledRawJointGuardedCommonDecoratedMoveValid A strategy hwin
        ExtraValid)
      (ProfiledRawJointGuardedCommonDecoratedNext A strategy hwin)).State)
    (hreachable :
      ProfiledRawJointGuardedCommonDecoratedPolicyReachable A strategy hwin
        initial ExtraValid policy state) :
    ∃ move : CommonPair A strategy hwin × Extra,
      ProfiledRawJointGuardedCommonDecoratedMoveValid A strategy hwin
          ExtraValid state.1 move ∧
        ∀ input : In₁ × In₂,
          policy.successor state input =
            (move.1.bothNextCode A strategy hwin input,
              (profiledRawJointGuardedCommonCodeParityDPA A
                (initial.code A strategy)).step state.2
                  (move.1.bothNextCode A strategy hwin input)) := by
  obtain ⟨move, hvalid, hnext⟩ :=
    SourceFreeBeliefCodeParityRationalPolicy.exists_sourceFreeMove
      (profiledRawJointGuardedCommonCodeParityDPA A
        (initial.code A strategy))
      (initial.code A strategy)
      (ProfiledRawJointGuardedCommonDecoratedMoveValid A strategy hwin
        ExtraValid)
      (ProfiledRawJointGuardedCommonDecoratedNext A strategy hwin)
      policy state hreachable
  refine ⟨move, hvalid, ?_⟩
  intro input
  simpa only [ProfiledRawJointGuardedCommonDecoratedNext,
    sourceFreeBeliefDecoratedNext,
    profiledRawJointGuardedCommonNext] using hnext input

end


end DetParityAutomaton

end DistributedSynthesis
