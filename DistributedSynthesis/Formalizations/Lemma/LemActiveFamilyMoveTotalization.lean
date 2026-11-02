/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemFamilyAwareGuardedHiddenDescriptorTreeAssembly

/-!
# Totalizing moves only outside the live family image

The guarded public tree needs a legal move at every finite family code,
including codes which are not attained by the semantic construction.  A
plain fallback move is unsafe at an attained family: after rationalization it
could be selected on a real branch and make the universal exact-thread
objective true only because no exact thread survives.

This file supplies the safe generic totalization.  A move is wrapped in
`Option`.  `none` is valid exactly when the advertised family contains no
live descriptor, and has neither supported observations nor exact edges.
Every live family therefore forces `some` of a genuine move.  Existing
one-step totality and family-aware semantic lifting transfer definitionally
through the wrapper.

The construction is proof-side and symmetric.  It contains no orientation,
lane, selected family member, or strict-leader signal.
-/

namespace DistributedSynthesis

universe u v m b x y

section

variable {Code : Type u} {MoveIdentity : Type v}
variable (D : DetParityAutomaton.{u, x} Code)
variable {Move : Type m} {Direction : Type b} {Semantic : Type y}
variable [Fintype Code] [Fintype MoveIdentity]

/-- A public family is active when it contains at least one descriptor which
the model marks as live. -/
def HiddenDescriptorFamilyActive
    (Live : HiddenCodeControlDescriptor D
        (MoveIdentity := MoveIdentity) →
      HiddenDescriptorTwoFibreFamily D
        (MoveIdentity := MoveIdentity) → Prop)
    (family : HiddenDescriptorTwoFibreFamily D
      (MoveIdentity := MoveIdentity)) : Prop :=
  ∃ descriptor, Live descriptor family

/-- Safe validity for an optional move.  A missing move is legal only outside
the live family image. -/
def ActiveFamilyOptionValid
    (Live : HiddenCodeControlDescriptor D
        (MoveIdentity := MoveIdentity) →
      HiddenDescriptorTwoFibreFamily D
        (MoveIdentity := MoveIdentity) → Prop)
    (Good : HiddenDescriptorTwoFibreFamily D
        (MoveIdentity := MoveIdentity) → Move → Prop)
    (family : HiddenDescriptorTwoFibreFamily D
      (MoveIdentity := MoveIdentity)) : Option Move → Prop
  | some move => Good family move
  | none => ¬ HiddenDescriptorFamilyActive D Live family

/-- Existing genuine moves remain valid under the optional wrapper. -/
theorem activeFamilyOptionValid_some
    (Live : HiddenCodeControlDescriptor D
        (MoveIdentity := MoveIdentity) →
      HiddenDescriptorTwoFibreFamily D
        (MoveIdentity := MoveIdentity) → Prop)
    (Good : HiddenDescriptorTwoFibreFamily D
        (MoveIdentity := MoveIdentity) → Move → Prop)
    {family : HiddenDescriptorTwoFibreFamily D
      (MoveIdentity := MoveIdentity)} {move : Move}
    (hgood : Good family move) :
    ActiveFamilyOptionValid D Live Good family (some move) :=
  hgood

/-- A live descriptor rules out the vacuous fallback at its family. -/
theorem not_activeFamilyOptionValid_none_of_live
    (Live : HiddenCodeControlDescriptor D
        (MoveIdentity := MoveIdentity) →
      HiddenDescriptorTwoFibreFamily D
        (MoveIdentity := MoveIdentity) → Prop)
    (Good : HiddenDescriptorTwoFibreFamily D
        (MoveIdentity := MoveIdentity) → Move → Prop)
    {descriptor : HiddenCodeControlDescriptor D
      (MoveIdentity := MoveIdentity)}
    {family : HiddenDescriptorTwoFibreFamily D
      (MoveIdentity := MoveIdentity)}
    (hlive : Live descriptor family) :
    ¬ ActiveFamilyOptionValid D Live Good family none := by
  intro hvalid
  exact hvalid ⟨descriptor, hlive⟩

/-- If every active family has a genuine good move, optional validity is
total on the entire finite public family alphabet. -/
theorem activeFamilyOptionValid_total
    (Live : HiddenCodeControlDescriptor D
        (MoveIdentity := MoveIdentity) →
      HiddenDescriptorTwoFibreFamily D
        (MoveIdentity := MoveIdentity) → Prop)
    (Good : HiddenDescriptorTwoFibreFamily D
        (MoveIdentity := MoveIdentity) → Move → Prop)
    (hgood : ∀ family, HiddenDescriptorFamilyActive D Live family →
      ∃ move, Good family move) :
    ∀ family, ∃ move, ActiveFamilyOptionValid D Live Good family move := by
  intro family
  classical
  by_cases hactive : HiddenDescriptorFamilyActive D Live family
  · obtain ⟨move, hmove⟩ := hgood family hactive
    exact ⟨some move, hmove⟩
  · exact ⟨none, hactive⟩

/-- Optional exact edges erase `some`; `none` has no exact successor. -/
def ActiveFamilyOptionExactEdge
    (ExactEdge : HiddenCodeControlDescriptor D
        (MoveIdentity := MoveIdentity) →
      Move → Direction →
        HiddenDescriptorTwoFibreFamily D
          (MoveIdentity := MoveIdentity) →
      HiddenCodeControlDescriptor D (MoveIdentity := MoveIdentity) → Prop) :
    HiddenCodeControlDescriptor D (MoveIdentity := MoveIdentity) →
      Option Move → Direction →
        HiddenDescriptorTwoFibreFamily D
          (MoveIdentity := MoveIdentity) →
      HiddenCodeControlDescriptor D (MoveIdentity := MoveIdentity) → Prop
  | current, some move, direction, nextFamily, target =>
      ExactEdge current move direction nextFamily target
  | _, none, _, _, _ => False

/-- Optional supported observations erase `some`; `none` supports no claimed
model transition. -/
def ActiveFamilyOptionSupported
    (Supported : HiddenDescriptorTwoFibreFamily D
        (MoveIdentity := MoveIdentity) → Move → Direction →
      HiddenDescriptorTwoFibreFamily D
        (MoveIdentity := MoveIdentity) → Prop) :
    HiddenDescriptorTwoFibreFamily D
        (MoveIdentity := MoveIdentity) → Option Move → Direction →
      HiddenDescriptorTwoFibreFamily D
        (MoveIdentity := MoveIdentity) → Prop
  | family, some move, direction, nextFamily =>
      Supported family move direction nextFamily
  | _, none, _, _ => False

namespace HiddenDescriptorFamilyTotality

/-- One-step live coverage transfers through active-family totalization.
The `none` cases are impossible already from `Supported`; no semantic
existence principle is used. -/
def optionTotalization
    (Represented : HiddenCodeControlDescriptor D
        (MoveIdentity := MoveIdentity) →
      HiddenDescriptorTwoFibreFamily D
        (MoveIdentity := MoveIdentity) → Prop)
    (Live : HiddenCodeControlDescriptor D
        (MoveIdentity := MoveIdentity) →
      HiddenDescriptorTwoFibreFamily D
        (MoveIdentity := MoveIdentity) → Prop)
    (ExactEdge : HiddenCodeControlDescriptor D
        (MoveIdentity := MoveIdentity) →
      Move → Direction →
        HiddenDescriptorTwoFibreFamily D
          (MoveIdentity := MoveIdentity) →
      HiddenCodeControlDescriptor D (MoveIdentity := MoveIdentity) → Prop)
    (Good : HiddenDescriptorTwoFibreFamily D
        (MoveIdentity := MoveIdentity) → Move → Prop)
    (Supported : HiddenDescriptorTwoFibreFamily D
        (MoveIdentity := MoveIdentity) → Move → Direction →
      HiddenDescriptorTwoFibreFamily D
        (MoveIdentity := MoveIdentity) → Prop)
    (totality : HiddenDescriptorFamilyTotality D Represented Live ExactEdge
      Good Supported) :
    HiddenDescriptorFamilyTotality D Represented Live
      (ActiveFamilyOptionExactEdge D ExactEdge)
      (ActiveFamilyOptionValid D Live Good)
      (ActiveFamilyOptionSupported D Supported) where
  live_represented := totality.live_represented
  target_live := by
    intro current currentFamily move direction nextFamily target hcurrent
      hvalid hsupported hedge
    cases move with
    | none => exact hsupported.elim
    | some move =>
        exact totality.target_live current currentFamily move direction
          nextFamily target hcurrent hvalid hsupported hedge
  covers := by
    intro current currentFamily move direction nextFamily hcurrent hvalid
      hsupported
    cases move with
    | none => exact hsupported.elim
    | some move =>
        exact totality.covers current currentFamily move direction nextFamily
          hcurrent hvalid hsupported

end HiddenDescriptorFamilyTotality

namespace FamilyAwareHiddenDescriptorEdgeLifter

/-- Family-aware semantic lifting transfers through the optional wrapper. -/
def optionTotalization
    (semanticStep : Semantic → Direction → Semantic)
    (semanticDescriptor : Semantic → HiddenCodeControlDescriptor D
      (MoveIdentity := MoveIdentity))
    (familyOf : Semantic → HiddenDescriptorTwoFibreFamily D
      (MoveIdentity := MoveIdentity))
    (Live : HiddenCodeControlDescriptor D
        (MoveIdentity := MoveIdentity) →
      HiddenDescriptorTwoFibreFamily D
        (MoveIdentity := MoveIdentity) → Prop)
    (ExactEdge : HiddenCodeControlDescriptor D
        (MoveIdentity := MoveIdentity) →
      Move → Direction →
        HiddenDescriptorTwoFibreFamily D
          (MoveIdentity := MoveIdentity) →
      HiddenCodeControlDescriptor D (MoveIdentity := MoveIdentity) → Prop)
    (Good : HiddenDescriptorTwoFibreFamily D
        (MoveIdentity := MoveIdentity) → Move → Prop)
    (lifter : FamilyAwareHiddenDescriptorEdgeLifter D semanticStep
      semanticDescriptor familyOf ExactEdge Good) :
    FamilyAwareHiddenDescriptorEdgeLifter D semanticStep semanticDescriptor
      familyOf (ActiveFamilyOptionExactEdge D ExactEdge)
      (ActiveFamilyOptionValid D Live Good) where
  lifts := by
    intro state move direction nextFamily target hvalid hedge
    cases move with
    | none => exact hedge.elim
    | some move =>
        apply lifter.lifts state move direction nextFamily target
        · exact hvalid
        · exact hedge

end FamilyAwareHiddenDescriptorEdgeLifter

/-! ## Direct guarded-package assembly -/

/-- Assemble the corrected guarded-tree package from genuine moves which are
available only on active families.  Semantic nodes always use `some`; the
safe `none` completion is confined to inactive advertised families. -/
noncomputable def familyAwareGuardedPackageOfActiveMoves
    [Fintype Move] [Fintype Direction] [Inhabited Direction]
    (semanticStep : Semantic → Direction → Semantic)
    (semanticDescriptor : Semantic → HiddenCodeControlDescriptor D
      (MoveIdentity := MoveIdentity))
    (familyOf : Semantic → HiddenDescriptorTwoFibreFamily D
      (MoveIdentity := MoveIdentity))
    (semanticMove : Semantic → Move)
    (Represented : HiddenCodeControlDescriptor D
        (MoveIdentity := MoveIdentity) →
      HiddenDescriptorTwoFibreFamily D
        (MoveIdentity := MoveIdentity) → Prop)
    (Live : HiddenCodeControlDescriptor D
        (MoveIdentity := MoveIdentity) →
      HiddenDescriptorTwoFibreFamily D
        (MoveIdentity := MoveIdentity) → Prop)
    (ExactEdge : HiddenCodeControlDescriptor D
        (MoveIdentity := MoveIdentity) →
      Move → Direction →
        HiddenDescriptorTwoFibreFamily D
          (MoveIdentity := MoveIdentity) →
      HiddenCodeControlDescriptor D (MoveIdentity := MoveIdentity) → Prop)
    (Good : HiddenDescriptorTwoFibreFamily D
        (MoveIdentity := MoveIdentity) → Move → Prop)
    (Supported : HiddenDescriptorTwoFibreFamily D
        (MoveIdentity := MoveIdentity) → Move → Direction →
      HiddenDescriptorTwoFibreFamily D
        (MoveIdentity := MoveIdentity) → Prop)
    (initial : Semantic)
    (totality : HiddenDescriptorFamilyTotality D Represented Live ExactEdge
      Good Supported)
    (lifter : FamilyAwareHiddenDescriptorEdgeLifter D semanticStep
      semanticDescriptor familyOf ExactEdge Good)
    (initial_control : (semanticDescriptor initial).control = D.initial)
    (initial_live : Live (semanticDescriptor initial) (familyOf initial))
    (active_good : ∀ family, HiddenDescriptorFamilyActive D Live family →
      ∃ move, Good family move)
    (semantic_move_good : ∀ state,
      Good (familyOf state) (semanticMove state))
    (semantic_observation_supported : ∀ state direction,
      Supported (familyOf state) (semanticMove state) direction
        (familyOf (semanticStep state direction)))
    (semantic_branch_accepts : ∀ branch : Nat → Direction,
      D.Accepts (fun n ↦
        (semanticDescriptor
          ((branchNode branch (n + 1)).foldl semanticStep initial)).code)) :
    FamilyAwareGuardedHiddenDescriptorTreePackage D semanticStep
      semanticDescriptor familyOf (fun state ↦ some (semanticMove state))
      Represented Live (ActiveFamilyOptionExactEdge D ExactEdge)
      (ActiveFamilyOptionValid D Live Good)
      (ActiveFamilyOptionSupported D Supported) initial where
  totality := totality.optionTotalization D Represented Live ExactEdge Good
    Supported
  semanticLifter := lifter.optionTotalization D semanticStep
    semanticDescriptor familyOf Live ExactEdge Good
  initial_control := initial_control
  initial_live := initial_live
  valid_total := activeFamilyOptionValid_total D Live Good active_good
  semantic_move_valid := fun state ↦ semantic_move_good state
  semantic_observation_supported := fun state direction ↦
    semantic_observation_supported state direction
  semantic_branch_accepts := semantic_branch_accepts

end

end DistributedSynthesis
