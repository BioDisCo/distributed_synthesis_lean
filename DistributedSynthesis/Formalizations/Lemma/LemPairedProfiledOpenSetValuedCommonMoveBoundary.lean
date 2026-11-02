/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemSetValuedPointedSuccessorReceive
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledOpenConcretePinnedRealization

/-!
# The full-family common-move boundary

The set-valued receive construction removes the need to decode one hidden
descriptor.  At the concrete optional pinned alphabet, however, one complete
family move still carries its advertised source family as its first
coordinate.  Consequently a single complete move can be valid at two live
candidates only when their family tags agree.

This is a useful fail-fast theorem.  Iterating arbitrary family-tagged
candidate sets with one *complete* pinned family move would silently recreate
child-family functionality.  The positive route must instead retain the
generated-set provenance of one parent union controller and use its common
local sender projection (the existing `sender_eq` theorem), or prove that a
later full-view receive has recovered the ambiguity.  No cardinality or
"one hidden bit" argument is used here.
-/

namespace DistributedSynthesis

universe i u v x y s

namespace DetParityAutomaton

variable {I : Type i}
variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable
  (A : DetParityAutomaton.{max u v x y, s}
    (RoundRecord In₁ In₂ Graph Out₁ Out₂))

noncomputable section

variable [Fintype I]
variable [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁]
  [Inhabited Out₂]
variable [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
variable [DecidableEq In₁] [DecidableEq In₂]

variable (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
variable (hwin : ∀ env : EnvironmentSequence In₁ In₂,
  A.Accepts (execution strategy env))
variable (basis : ∀ state : PairedProfiledTreeState A,
  (pairedProfiledEntryRunAutomaton A state).RationalRunBasis)
variable (initialCode : ProfiledOpenIndexedBiBeliefCode A (I := I))

/-! ## A valid concrete move pins its family coordinate -/

/-- Concrete pointed validity at one live descriptor forces the literal
first coordinate of the complete pinned move to be the advertised family.
This follows from provenance, not from equality of finite family images. -/
theorem profiledOpenOptionalPointedPinnedMoveValid_family
    (family : ProfiledOpenIndexedHiddenDescriptorFamilyCode A (I := I)
      initialCode)
    (move : ProfiledOpenHiddenDescriptorPairedPinnedFamilyMove.{i, u, v, x,
      y, s, 0, 0} A (I := I) initialCode)
    (current : ProfiledOpenIndexedOldMoveHiddenDescriptor A (I := I)
      initialCode)
    (hlive : ProfiledOpenOptionalPointedSemanticLive A strategy hwin basis
      initialCode current family)
    (hvalid : ProfiledOpenOptionalPointedPinnedMoveValid A strategy hwin basis
      initialCode
      (profiledOpenOptionalPinnedQueryRealizes A strategy hwin basis
        initialCode)
      family move) :
    move.1 = family := by
  obtain ⟨state, hrealizes, _hdescriptor, _hfamily⟩ :=
    hvalid current hlive
  exact hrealizes.2.2.2.1

/-! ## Therefore a full common move collapses live family tags -/

/-- If the set-valued carrier uses the concrete complete pinned-move
alphabet, any two live candidates covered by one common move have the same
family tag.  Descriptor ambiguity is retained, but family ambiguity has not
been solved by this interface. -/
theorem profiledOpenOptionalSetValuedCommonMoveValid_families_eq
    (current : Finset
      (SetValuedPointedCandidate
        (profiledOpenIndexedBiBeliefCodeParityDPA A initialCode)
        (MoveIdentity := ProfiledOpenIndexedBiBeliefMove A)))
    (move : ProfiledOpenHiddenDescriptorPairedPinnedFamilyMove.{i, u, v, x,
      y, s, 0, 0} A (I := I) initialCode)
    (hcommon : SetValuedPointedCommonMoveValid
      (profiledOpenIndexedBiBeliefCodeParityDPA A initialCode)
      (ProfiledOpenOptionalPointedSemanticLive A strategy hwin basis
        initialCode)
      (ProfiledOpenOptionalPointedPinnedMoveValid A strategy hwin basis
        initialCode
        (profiledOpenOptionalPinnedQueryRealizes A strategy hwin basis
          initialCode))
      current move)
    {left right : SetValuedPointedCandidate
      (profiledOpenIndexedBiBeliefCodeParityDPA A initialCode)
      (MoveIdentity := ProfiledOpenIndexedBiBeliefMove A)}
    (hleft : left ∈ current) (hright : right ∈ current)
    (hliveLeft : ProfiledOpenOptionalPointedSemanticLive A strategy hwin basis
      initialCode left.2 left.1)
    (hliveRight : ProfiledOpenOptionalPointedSemanticLive A strategy hwin basis
      initialCode right.2 right.1) :
    left.1 = right.1 := by
  have hleftValid := hcommon left hleft hliveLeft
  have hrightValid := hcommon right hright hliveRight
  have hmoveLeft : move.1 = left.1 :=
    profiledOpenOptionalPointedPinnedMoveValid_family A strategy hwin basis
      initialCode left.1 move left.2 hliveLeft hleftValid
  have hmoveRight : move.1 = right.1 :=
    profiledOpenOptionalPointedPinnedMoveValid_family A strategy hwin basis
      initialCode right.1 move right.2 hliveRight hrightValid
  exact hmoveLeft.symm.trans hmoveRight

/-! ## The converse: one live family fibre has a common move -/

/-- If every live member of a carried candidate set has the same public
family as one live anchor, the anchor's literal provenance-preserving
dispatcher is a common move for the whole set.  The hidden descriptors may
still differ; only the family coordinate is required to agree.

This is the positive half of the boundary theorem.  It uses the already
proved fact that the one strong dispatcher at a family realizes *every* live
descriptor of that family, rather than selecting a distinguished descriptor
or semantic representative for each candidate. -/
theorem exists_profiledOpenOptionalSetValuedCommonMoveValid_of_liveFamily_eq
    (current : Finset
      (SetValuedPointedCandidate
        (profiledOpenIndexedBiBeliefCodeParityDPA A initialCode)
        (MoveIdentity := ProfiledOpenIndexedBiBeliefMove A)))
    (anchor : SetValuedPointedCandidate
      (profiledOpenIndexedBiBeliefCodeParityDPA A initialCode)
      (MoveIdentity := ProfiledOpenIndexedBiBeliefMove A))
    (hliveAnchor : ProfiledOpenOptionalPointedSemanticLive A strategy hwin
      basis initialCode anchor.2 anchor.1)
    (hfamilies : ∀ source ∈ current,
      ProfiledOpenOptionalPointedSemanticLive A strategy hwin basis
          initialCode source.2 source.1 →
        source.1 = anchor.1) :
    ∃ move : ProfiledOpenHiddenDescriptorPairedPinnedFamilyMove.{i, u, v,
        x, y, s, 0, 0} A (I := I) initialCode,
      SetValuedPointedCommonMoveValid
        (profiledOpenIndexedBiBeliefCodeParityDPA A initialCode)
        (ProfiledOpenOptionalPointedSemanticLive A strategy hwin basis
          initialCode)
        (ProfiledOpenOptionalPointedPinnedMoveValid A strategy hwin basis
          initialCode
          (profiledOpenOptionalPinnedQueryRealizes A strategy hwin basis
            initialCode))
        current move := by
  obtain ⟨point, hdescriptor, hfamily⟩ := hliveAnchor
  let move :=
    profiledOpenOptionalFixedPinnedSemanticMoveOfWinning.{i, u, v, x, y, s,
      0, 0} A strategy hwin basis initialCode (fun _ ↦ point.2) point.1
  have hvalidAtPoint :
      ProfiledOpenOptionalPointedPinnedMoveValid A strategy hwin basis
        initialCode
        (profiledOpenOptionalPinnedQueryRealizes A strategy hwin basis
          initialCode)
        (profiledOpenOptionalControlledFamilyOf A strategy hwin basis
          initialCode point) move :=
    profiledOpenOptionalFixedPinnedSemanticMoveOfWinning_moveValid A strategy
      hwin basis initialCode point
  have hvalidAtAnchor :
      ProfiledOpenOptionalPointedPinnedMoveValid A strategy hwin basis
        initialCode
        (profiledOpenOptionalPinnedQueryRealizes A strategy hwin basis
          initialCode)
        anchor.1 move := by
    simpa only [hfamily] using hvalidAtPoint
  refine ⟨move, ?_⟩
  intro source hsource hlive
  have heq : source.1 = anchor.1 := hfamilies source hsource hlive
  simpa only [heq] using hvalidAtAnchor

/-- Around any live anchor, existence of one complete concrete common move is
*equivalent* to equality of all live family tags.  Thus the present
set-valued carrier has removed descriptor selection, but not family
selection.  A candidate successor construction which genuinely produces
several live family tags must use a sidewise/union-family move interface; the
complete sigma move used here cannot cover it. -/
theorem exists_profiledOpenOptionalSetValuedCommonMoveValid_iff_liveFamily_eq
    (current : Finset
      (SetValuedPointedCandidate
        (profiledOpenIndexedBiBeliefCodeParityDPA A initialCode)
        (MoveIdentity := ProfiledOpenIndexedBiBeliefMove A)))
    (anchor : SetValuedPointedCandidate
      (profiledOpenIndexedBiBeliefCodeParityDPA A initialCode)
      (MoveIdentity := ProfiledOpenIndexedBiBeliefMove A))
    (hanchor : anchor ∈ current)
    (hliveAnchor : ProfiledOpenOptionalPointedSemanticLive A strategy hwin
      basis initialCode anchor.2 anchor.1) :
    (∃ move : ProfiledOpenHiddenDescriptorPairedPinnedFamilyMove.{i, u, v,
        x, y, s, 0, 0} A (I := I) initialCode,
      SetValuedPointedCommonMoveValid
        (profiledOpenIndexedBiBeliefCodeParityDPA A initialCode)
        (ProfiledOpenOptionalPointedSemanticLive A strategy hwin basis
          initialCode)
        (ProfiledOpenOptionalPointedPinnedMoveValid A strategy hwin basis
          initialCode
          (profiledOpenOptionalPinnedQueryRealizes A strategy hwin basis
            initialCode))
        current move) ↔
      ∀ source ∈ current,
        ProfiledOpenOptionalPointedSemanticLive A strategy hwin basis
            initialCode source.2 source.1 →
          source.1 = anchor.1 := by
  constructor
  · rintro ⟨move, hcommon⟩ source hsource hlive
    exact profiledOpenOptionalSetValuedCommonMoveValid_families_eq A strategy
      hwin basis initialCode current move hcommon hsource hanchor hlive
      hliveAnchor
  · intro hfamilies
    exact
      exists_profiledOpenOptionalSetValuedCommonMoveValid_of_liveFamily_eq A
        strategy hwin basis initialCode current anchor hliveAnchor
        hfamilies

end

end DetParityAutomaton

end DistributedSynthesis
