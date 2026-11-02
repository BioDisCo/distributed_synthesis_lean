/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledRawJointInitialLeaderFreeCarrier
import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledRawJointUnitPolicyLeaderFreeKernel

/-!
# The finite tagged child family below the exceptional seam

This module constructs a finite tagged family for strict exits with
heterogeneous keys. Its results identify the child sources and their
controller banks; they do not assert acceptance for arbitrary continuations.

The two exceptional orientations do not in general emit the same literal
child.  The global finite child index is therefore a tagged dependent sum:
an initial-left guarded key and one of its literal children, or an
initial-right guarded key and one of its literal children.  The tag is static
provenance used to recover the chosen policy; it is not an observable graph,
leader, or orientation signal.

Every tag determines its semantic child source, the fresh rational policy at
that source, and the complete recurrent controller bank.  Consequently the
four dependent control families required by
`ProfiledRawJointLeaderFreeKernel` are finite.  A cross may contain two
different tags.  A later strict event selects one through the ordinary local
receive/no-receive table; no equality between tags is assumed here.
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
  (hstrategy : ∀ env : EnvironmentSequence In₁ In₂,
    A.Accepts (execution strategy env))
  (initialBank : ProfiledRawJointInitialControllerBank A strategy)

/-! ## The two dependent child summands -/

abbrev ProfiledRawJointInitialLeftSelectedSource
    (key : ProfiledRawJointInitialLeftGuardedKey A strategy) :=
  profiledRawJointRootPinnedSelectedSource A strategy
    (initialBank.initialLeft key).activation.source
    (ProfiledRawJointInitialLeftRootPredicate A strategy key)
    (initialBank.initialLeft key).activation.pinned

abbrev ProfiledRawJointInitialRightSelectedSource
    (key : ProfiledRawJointInitialRightGuardedKey A strategy) :=
  profiledRawJointRootPinnedSelectedSource A strategy
    (initialBank.initialRight key).activation.source
    (ProfiledRawJointInitialRightRootPredicate A strategy key)
    (initialBank.initialRight key).activation.pinned

abbrev ProfiledRawJointInitialLeftTaggedChild :=
  Σ key : ProfiledRawJointInitialLeftGuardedKey A strategy,
    ProfiledRawJointOneSidedLiteralChildCode A strategy
      (ProfiledRawJointInitialLeftSelectedSource A strategy initialBank key)

abbrev ProfiledRawJointInitialRightTaggedChild :=
  Σ key : ProfiledRawJointInitialRightGuardedKey A strategy,
    ProfiledRawJointOneSidedLiteralChildCode A strategy
      (ProfiledRawJointInitialRightSelectedSource A strategy initialBank key)

/-- Concrete finite `ChildCode` for the global heterogeneous carrier. -/
abbrev ProfiledRawJointInitialTaggedChildCode :=
  ProfiledRawJointInitialLeftTaggedChild A strategy initialBank ⊕
    ProfiledRawJointInitialRightTaggedChild A strategy initialBank

noncomputable instance profiledRawJointInitialTaggedChildCodeFintype :
    Fintype (ProfiledRawJointInitialTaggedChildCode A strategy initialBank) := by
  classical
  infer_instance

/-! ## Recovering the source and the fresh policy -/

/-- The literal semantic child represented by a tag. -/
noncomputable def profiledRawJointInitialTaggedChildSource
    (child : ProfiledRawJointInitialTaggedChildCode A strategy initialBank) :
    ProfiledRawJointOneSidedSemanticState A strategy (I := Unit) :=
  match child with
  | .inl child =>
      profiledRawJointOneSidedLiteralChildSource A strategy
        (ProfiledRawJointInitialLeftSelectedSource A strategy initialBank
          child.1) child.2
  | .inr child =>
      profiledRawJointOneSidedLiteralChildSource A strategy
        (ProfiledRawJointInitialRightSelectedSource A strategy initialBank
          child.1) child.2

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- The code of the recovered semantic source is the literal child code in
the corresponding tag. -/
theorem profiledRawJointInitialTaggedChildSource_code
    (child : ProfiledRawJointInitialTaggedChildCode A strategy initialBank) :
    (profiledRawJointInitialTaggedChildSource A strategy initialBank child).code
        A =
      match child with
      | .inl child => child.2.1
      | .inr child => child.2.1 := by
  cases child with
  | inl child =>
      exact profiledRawJointOneSidedLiteralChildSource_code A strategy
        (ProfiledRawJointInitialLeftSelectedSource A strategy initialBank
          child.1) child.2
  | inr child =>
      exact profiledRawJointOneSidedLiteralChildSource_code A strategy
        (ProfiledRawJointInitialRightSelectedSource A strategy initialBank
          child.1) child.2

/-- Recover the fresh policy attached to this exact literal child. -/
noncomputable def profiledRawJointInitialTaggedChildPolicy
    (child : ProfiledRawJointInitialTaggedChildCode A strategy initialBank) :
    ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
      ((profiledRawJointInitialTaggedChildSource A strategy initialBank
        child).code A) := by
  cases child with
  | inl child =>
      let policy :=
        (initialBank.initialLeft child.1).activation.childPolicyBank A
          hstrategy child.2
      simpa only [profiledRawJointInitialTaggedChildSource,
        profiledRawJointOneSidedLiteralChildSource_code] using policy
  | inr child =>
      let policy :=
        (initialBank.initialRight child.1).activation.childPolicyBank A
          hstrategy child.2
      simpa only [profiledRawJointInitialTaggedChildSource,
        profiledRawJointOneSidedLiteralChildSource_code] using policy

/-- Complete recurrent controllers below the tag. -/
noncomputable def profiledRawJointInitialTaggedChildControllerBank
    (child : ProfiledRawJointInitialTaggedChildCode A strategy initialBank) :
    ProfiledRawJointUnitPolicyControllerBank A strategy
      (profiledRawJointInitialTaggedChildSource A strategy initialBank child)
      (profiledRawJointInitialTaggedChildPolicy A strategy hstrategy initialBank
        child) :=
  profiledRawJointUnitPolicyControllerBank A strategy
    (profiledRawJointInitialTaggedChildSource A strategy initialBank child)
    (profiledRawJointInitialTaggedChildPolicy A strategy hstrategy initialBank
      child)

/-! ## The four finite dependent carrier families -/

abbrev ProfiledRawJointInitialTaggedRightOwner
    (child : ProfiledRawJointInitialTaggedChildCode A strategy initialBank) :=
  ProfiledRawJointUnitPolicyRightOwner A strategy
    (profiledRawJointInitialTaggedChildSource A strategy initialBank child)
    (profiledRawJointInitialTaggedChildPolicy A strategy hstrategy initialBank
      child)
    (profiledRawJointInitialTaggedChildControllerBank A strategy hstrategy
      initialBank child) ()

abbrev ProfiledRawJointInitialTaggedLeftReceiver
    (child : ProfiledRawJointInitialTaggedChildCode A strategy initialBank) :=
  ProfiledRawJointUnitPolicyLeftReceiver A strategy
    (profiledRawJointInitialTaggedChildSource A strategy initialBank child)
    (profiledRawJointInitialTaggedChildPolicy A strategy hstrategy initialBank
      child) ()

abbrev ProfiledRawJointInitialTaggedRightReceiver
    (child : ProfiledRawJointInitialTaggedChildCode A strategy initialBank) :=
  ProfiledRawJointUnitPolicyRightReceiver A strategy
    (profiledRawJointInitialTaggedChildSource A strategy initialBank child)
    (profiledRawJointInitialTaggedChildPolicy A strategy hstrategy initialBank
      child) ()

abbrev ProfiledRawJointInitialTaggedLeftOwner
    (child : ProfiledRawJointInitialTaggedChildCode A strategy initialBank) :=
  ProfiledRawJointUnitPolicyLeftOwner A strategy
    (profiledRawJointInitialTaggedChildSource A strategy initialBank child)
    (profiledRawJointInitialTaggedChildPolicy A strategy hstrategy initialBank
      child)
    (profiledRawJointInitialTaggedChildControllerBank A strategy hstrategy
      initialBank child) ()

noncomputable instance profiledRawJointInitialTaggedRightOwnerFintype
    (child : ProfiledRawJointInitialTaggedChildCode A strategy initialBank) :
    Fintype (ProfiledRawJointInitialTaggedRightOwner A strategy hstrategy
      initialBank child) := by
  classical
  infer_instance

noncomputable instance profiledRawJointInitialTaggedLeftReceiverFintype
    (child : ProfiledRawJointInitialTaggedChildCode A strategy initialBank) :
    Fintype (ProfiledRawJointInitialTaggedLeftReceiver A strategy hstrategy
      initialBank child) := by
  classical
  infer_instance

noncomputable instance profiledRawJointInitialTaggedRightReceiverFintype
    (child : ProfiledRawJointInitialTaggedChildCode A strategy initialBank) :
    Fintype (ProfiledRawJointInitialTaggedRightReceiver A strategy hstrategy
      initialBank child) := by
  classical
  infer_instance

noncomputable instance profiledRawJointInitialTaggedLeftOwnerFintype
    (child : ProfiledRawJointInitialTaggedChildCode A strategy initialBank) :
    Fintype (ProfiledRawJointInitialTaggedLeftOwner A strategy hstrategy
      initialBank child) := by
  classical
  infer_instance

end


end DetParityAutomaton

end DistributedSynthesis
