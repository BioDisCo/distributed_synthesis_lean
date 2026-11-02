/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonDecoratedPolicyPackage

/-!
# Pointwise finite preselection before common-policy rationalization

Concrete occurrence-sensitive annotations are most naturally supplied by an
existence proof at every literal common point.  This file performs the single
proof-side choice before rationalization and immediately hides it behind the
finite decorated policy package.  The chosen semantic function never appears
in the operational package or in any executable transition.
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

omit [Fintype Extra] in
/-- Pointwise existence of a finite annotation is enough to construct the
operational decorated package.  Choice occurs only in this proof-side
constructor and is consumed by the one outer rationalization. -/
theorem
    nonempty_profiledRawJointGuardedCommonDecoratedPolicyPackage_of_pointwise
    (initial : CommonPoint A strategy)
    (ExtraValid : CommonCode A → CommonPair A strategy hwin → Extra → Prop)
    (hexists : ∀ point : CommonPoint A strategy,
      ∃ extra : Extra,
        ExtraValid (point.code A strategy) (point.move A strategy hwin)
          extra) :
    Nonempty
      (ProfiledRawJointGuardedCommonDecoratedPolicyPackage A strategy hwin
        initial ExtraValid) := by
  classical
  let extra : CommonPoint A strategy → Extra := fun point ↦
    Classical.choose (hexists point)
  apply nonempty_profiledRawJointGuardedCommonDecoratedPolicyPackage A
    strategy hwin initial extra ExtraValid
  intro point
  exact Classical.choose_spec (hexists point)

/-- Canonical finite operational package obtained directly from pointwise
preselection.  Its runtime state contains only the finite rational-policy
state; neither the semantic point nor the choice function is retained. -/
noncomputable def
    profiledRawJointGuardedCommonDecoratedPolicyPackageOfPointwise
    (initial : CommonPoint A strategy)
    (ExtraValid : CommonCode A → CommonPair A strategy hwin → Extra → Prop)
    (hexists : ∀ point : CommonPoint A strategy,
      ∃ extra : Extra,
        ExtraValid (point.code A strategy) (point.move A strategy hwin)
          extra) :
    ProfiledRawJointGuardedCommonDecoratedPolicyPackage A strategy hwin
      initial ExtraValid :=
  Classical.choice
    (nonempty_profiledRawJointGuardedCommonDecoratedPolicyPackage_of_pointwise
      A strategy hwin initial ExtraValid hexists)

end

end DetParityAutomaton

end DistributedSynthesis
