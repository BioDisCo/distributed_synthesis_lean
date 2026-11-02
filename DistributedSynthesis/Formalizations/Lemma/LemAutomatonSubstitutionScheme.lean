/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemAutomatonedgetypesubstitution
import DistributedSynthesis.Formalizations.Lemma.LemSubstitutiontransducer

/-!
# The concrete substitution scheme of the direct-reversal transduction

The paper's direct-reversal relation `Θ_q`
(`AutomatonEdgeSubstitutionRelation`, `lem:automatonedgetypesubstitution`)
is packaged as a `FiniteSubstitutionScheme`, the interface consumed by
the label profile, the window profile, and the saturation tower.  A
choice at an old oriented automaton edge is the quadruple of owned
boundary labels (left endpoint, right endpoint, internal at target,
internal at source); the emitted block is the exact three-edge automaton
substitution block, and the threaded labels are the endpoint labels.

`automatonSubstitutionScheme_relation_iff` proves the scheme generates
exactly `Θ_q`: scheme relations are the relation elements of
`lem:automatonedgetypesubstitution` with the endpoint ownership made
explicit.  The scheme family is indexed by the closing input pair
(`ReversalClosingParam`) -- the only closing data entering the block
construction -- providing the concrete `Param` instantiation of the
saturation tower.
-/

namespace DistributedSynthesis

universe u v w x y

instance (State : Type u) [DecidableEq State] :
    DecidableEq (AutomatonEdgeType State) := fun a b =>
  decidable_of_iff
    (a.srcOwner = b.srcOwner ∧ a.tgtOwner = b.tgtOwner ∧ a.state = b.state)
    (by
      constructor
      · rintro ⟨h1, h2, h3⟩
        cases a
        cases b
        simp_all
      · rintro rfl
        exact ⟨rfl, rfl, rfl⟩)

noncomputable instance (State : Type u) [Fintype State] :
    Fintype (AutomatonEdgeType State) :=
  Fintype.ofInjective
    (fun q : AutomatonEdgeType State => (q.srcOwner, q.tgtOwner, q.state))
    (by
      rintro ⟨s, t, h, st⟩ ⟨s', t', h', st'⟩ heq
      simp only [Prod.mk.injEq] at heq
      obtain ⟨rfl, rfl, rfl⟩ := heq
      rfl)

section Scheme

variable {Alphabet : Type u} {In₁ : Type v} {In₂ : Type w}
variable {Out₁ : Type x} {Out₂ : Type y}
variable [Fintype Out₁] [Fintype Out₂]
variable (A : DetParityAutomaton Alphabet)
variable (letter : EdgeExtensionLetter Alphabet In₁ In₂ Out₁ Out₂)

/-- The concrete finite substitution scheme of one direct reversal at the
fixed closing input pair: choices are the owned endpoint and internal
labels, blocks are the exact three-edge automaton substitution blocks,
and the threaded labels are the endpoint labels. -/
noncomputable def automatonSubstitutionScheme (x₁ : In₁) (x₂ : In₂) :
    FiniteSubstitutionScheme (AutomatonEdgeType A.State)
      (AutomatonEdgeType A.State) (BoundaryLabel Out₁ Out₂) where
  Choice q :=
    OwnedLabel Out₁ Out₂ q.srcOwner × OwnedLabel Out₁ Out₂ q.tgtOwner ×
      OwnedLabel Out₁ Out₂ q.tgtOwner × OwnedLabel Out₁ Out₂ q.srcOwner
  choiceFinite q := inferInstance
  left q choice := choice.1.val
  block q choice :=
    automatonSubstitutionTriple A letter x₁ x₂ q choice.1 choice.2.1
      choice.2.2.1 choice.2.2.2
  right q choice := choice.2.1.val

/-- **Exact representation**: the scheme relation is precisely the
paper's direct-reversal relation `Θ_q` with explicit endpoint
ownership. -/
theorem automatonSubstitutionScheme_relation_iff (x₁ : In₁) (x₂ : In₂)
    (q : AutomatonEdgeType A.State)
    (lab rab : BoundaryLabel Out₁ Out₂)
    (block : EdgeBlock3 (AutomatonEdgeType A.State)) :
    (automatonSubstitutionScheme A letter x₁ x₂).Relation q lab block rab ↔
      ∃ (l : OwnedLabel Out₁ Out₂ q.srcOwner)
        (r : OwnedLabel Out₁ Out₂ q.tgtOwner),
        l.val = lab ∧ r.val = rab ∧
          AutomatonEdgeSubstitutionRelation A letter x₁ x₂ q l block r := by
  constructor
  · rintro ⟨⟨l, r, iat, ias⟩, hleft, hblock, hright⟩
    exact ⟨l, r, hleft, hright, iat, ias, hblock.symm⟩
  · rintro ⟨l, r, hleft, hright, iat, ias, hblock⟩
    exact ⟨⟨l, r, iat, ias⟩, hleft, hblock.symm, hright⟩

/-- The closing parameter of the concrete reversal substitution: the
fixed next input pair, the only closing data entering the block
construction. -/
abbrev ReversalClosingParam (In₁ : Type v) (In₂ : Type w) := In₁ × In₂

/-- The concrete scheme family for the saturation tower: one scheme per
closing input pair, uniform in the side (orientation is read per edge
from the endpoint owners). -/
noncomputable def automatonSchemeFamily :
    Proc -> ReversalClosingParam In₁ In₂ ->
      FiniteSubstitutionScheme (AutomatonEdgeType A.State)
        (AutomatonEdgeType A.State) (BoundaryLabel Out₁ Out₂) :=
  fun _ p => automatonSubstitutionScheme A letter p.1 p.2

end Scheme

end DistributedSynthesis
