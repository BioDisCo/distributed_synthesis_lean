/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Formalizations.Definition.DefPathSummary

/-!
# Exact one-round substitution for automaton edge types
-/

namespace DistributedSynthesis

universe u v w x y

/--
The graph label on the first edge of the expanded block, as read from the
source owner of the old oriented edge.
-/
def firstExpansionGraph : Proc -> Graph
  | Proc.one => Graph.right
  | Proc.two => Graph.left

/--
The graph label on the last edge of the expanded block, as read toward the
target owner of the old oriented edge.
-/
def lastExpansionGraph : Proc -> Graph
  | Proc.one => Graph.left
  | Proc.two => Graph.right

/-- A concrete triple of successor automaton edge types. -/
abbrev AutomatonEdgeTriple (State : Type u) :=
  AutomatonEdgeType State × AutomatonEdgeType State × AutomatonEdgeType State

/--
An alphabet constructor for one-round edge extensions.  It packages the
fixed next input pair, the graph symbol, and the two endpoint labels into
the alphabet read by the deterministic parity automaton.
-/
abbrev EdgeExtensionLetter
    (Alphabet : Type u)
    (In₁ : Type v) (In₂ : Type w)
    (Out₁ : Type x) (Out₂ : Type y) :=
  In₁ -> In₂ -> Graph ->
    BoundaryLabel Out₁ Out₂ -> BoundaryLabel Out₁ Out₂ -> Alphabet

/--
The exact three-edge automaton substitution block for one old oriented edge.

The internal label at the old target owner supplies the first new internal
vertex; the internal label at the old source owner supplies the second one.
For a `1 -> 2` old edge this is the block
`right, both, left`; for a `2 -> 1` old edge it is read in the opposite
orientation as `left, both, right`.
-/
def automatonSubstitutionTriple
    {Alphabet : Type u} {In₁ : Type v} {In₂ : Type w}
    {Out₁ : Type x} {Out₂ : Type y}
    (A : DetParityAutomaton Alphabet)
    (letter : EdgeExtensionLetter Alphabet In₁ In₂ Out₁ Out₂)
    (x₁ : In₁) (x₂ : In₂)
    (q : AutomatonEdgeType A.State)
    (left : OwnedLabel Out₁ Out₂ q.srcOwner)
    (right : OwnedLabel Out₁ Out₂ q.tgtOwner)
    (internalAtTarget : OwnedLabel Out₁ Out₂ q.tgtOwner)
    (internalAtSource : OwnedLabel Out₁ Out₂ q.srcOwner) :
    AutomatonEdgeTriple A.State :=
  let s₁ :=
    A.step q.state
      (letter x₁ x₂ (firstExpansionGraph q.srcOwner)
        left.val internalAtTarget.val)
  let s₂ :=
    A.step q.state
      (letter x₁ x₂ Graph.both
        internalAtTarget.val internalAtSource.val)
  let s₃ :=
    A.step q.state
      (letter x₁ x₂ (lastExpansionGraph q.srcOwner)
        internalAtSource.val right.val)
  (
    { srcOwner := q.srcOwner
      tgtOwner := q.tgtOwner
      ownersDistinct := q.ownersDistinct
      state := s₁ },
    { srcOwner := q.tgtOwner
      tgtOwner := q.srcOwner
      ownersDistinct := Ne.symm q.ownersDistinct
      state := s₂ },
    { srcOwner := q.srcOwner
      tgtOwner := q.tgtOwner
      ownersDistinct := q.ownersDistinct
      state := s₃ }
  )

/-- The finite relation `Θ_q` induced by the exact automaton substitution. -/
def AutomatonEdgeSubstitutionRelation
    {Alphabet : Type u} {In₁ : Type v} {In₂ : Type w}
    {Out₁ : Type x} {Out₂ : Type y}
    (A : DetParityAutomaton Alphabet)
    (letter : EdgeExtensionLetter Alphabet In₁ In₂ Out₁ Out₂)
    (x₁ : In₁) (x₂ : In₂)
    (q : AutomatonEdgeType A.State)
    (left : OwnedLabel Out₁ Out₂ q.srcOwner)
    (triple : AutomatonEdgeTriple A.State)
    (right : OwnedLabel Out₁ Out₂ q.tgtOwner) :
    Prop :=
  ∃ internalAtTarget : OwnedLabel Out₁ Out₂ q.tgtOwner,
    ∃ internalAtSource : OwnedLabel Out₁ Out₂ q.srcOwner,
      triple =
        automatonSubstitutionTriple A letter x₁ x₂ q
          left right internalAtTarget internalAtSource

@[simp]
theorem automatonSubstitutionTriple_first_srcOwner
    {Alphabet : Type u} {In₁ : Type v} {In₂ : Type w}
    {Out₁ : Type x} {Out₂ : Type y}
    (A : DetParityAutomaton Alphabet)
    (letter : EdgeExtensionLetter Alphabet In₁ In₂ Out₁ Out₂)
    (x₁ : In₁) (x₂ : In₂)
    (q : AutomatonEdgeType A.State)
    (left : OwnedLabel Out₁ Out₂ q.srcOwner)
    (right : OwnedLabel Out₁ Out₂ q.tgtOwner)
    (internalAtTarget : OwnedLabel Out₁ Out₂ q.tgtOwner)
    (internalAtSource : OwnedLabel Out₁ Out₂ q.srcOwner) :
    (automatonSubstitutionTriple A letter x₁ x₂ q
      left right internalAtTarget internalAtSource).1.srcOwner = q.srcOwner := by
  rfl

@[simp]
theorem automatonSubstitutionTriple_middle_srcOwner
    {Alphabet : Type u} {In₁ : Type v} {In₂ : Type w}
    {Out₁ : Type x} {Out₂ : Type y}
    (A : DetParityAutomaton Alphabet)
    (letter : EdgeExtensionLetter Alphabet In₁ In₂ Out₁ Out₂)
    (x₁ : In₁) (x₂ : In₂)
    (q : AutomatonEdgeType A.State)
    (left : OwnedLabel Out₁ Out₂ q.srcOwner)
    (right : OwnedLabel Out₁ Out₂ q.tgtOwner)
    (internalAtTarget : OwnedLabel Out₁ Out₂ q.tgtOwner)
    (internalAtSource : OwnedLabel Out₁ Out₂ q.srcOwner) :
    (automatonSubstitutionTriple A letter x₁ x₂ q
      left right internalAtTarget internalAtSource).2.1.srcOwner = q.tgtOwner := by
  rfl

@[simp]
theorem automatonSubstitutionTriple_last_srcOwner
    {Alphabet : Type u} {In₁ : Type v} {In₂ : Type w}
    {Out₁ : Type x} {Out₂ : Type y}
    (A : DetParityAutomaton Alphabet)
    (letter : EdgeExtensionLetter Alphabet In₁ In₂ Out₁ Out₂)
    (x₁ : In₁) (x₂ : In₂)
    (q : AutomatonEdgeType A.State)
    (left : OwnedLabel Out₁ Out₂ q.srcOwner)
    (right : OwnedLabel Out₁ Out₂ q.tgtOwner)
    (internalAtTarget : OwnedLabel Out₁ Out₂ q.tgtOwner)
    (internalAtSource : OwnedLabel Out₁ Out₂ q.srcOwner) :
    (automatonSubstitutionTriple A letter x₁ x₂ q
      left right internalAtTarget internalAtSource).2.2.srcOwner = q.srcOwner := by
  rfl

/--
Paper-facing exactness theorem for `lem:automatonedgetypesubstitution`.
Every relation element is exactly one of the three-transition blocks
computed from some choice of the two internal output labels.
-/
theorem automaton_edge_type_substitution_exact
    {Alphabet : Type u} {In₁ : Type v} {In₂ : Type w}
    {Out₁ : Type x} {Out₂ : Type y}
    (A : DetParityAutomaton Alphabet)
    (letter : EdgeExtensionLetter Alphabet In₁ In₂ Out₁ Out₂)
    (x₁ : In₁) (x₂ : In₂)
    (q : AutomatonEdgeType A.State)
    {left : OwnedLabel Out₁ Out₂ q.srcOwner}
    {triple : AutomatonEdgeTriple A.State}
    {right : OwnedLabel Out₁ Out₂ q.tgtOwner} :
    AutomatonEdgeSubstitutionRelation A letter x₁ x₂ q left triple right ↔
      ∃ internalAtTarget : OwnedLabel Out₁ Out₂ q.tgtOwner,
        ∃ internalAtSource : OwnedLabel Out₁ Out₂ q.srcOwner,
          triple =
            automatonSubstitutionTriple A letter x₁ x₂ q
              left right internalAtTarget internalAtSource := by
  rfl

/--
The choices generating `Θ_q` are finite whenever the two output alphabets
are finite.  Together with `automaton_edge_type_substitution_exact`, this is
the finite effective relation used by the paper lemma.
-/
theorem automaton_edge_type_substitution_finite_choices
    {Alphabet : Type u} {In₁ : Type v} {In₂ : Type w}
    {Out₁ : Type x} {Out₂ : Type y}
    (A : DetParityAutomaton Alphabet)
    [Fintype Out₁] [Fintype Out₂]
    (letter : EdgeExtensionLetter Alphabet In₁ In₂ Out₁ Out₂)
    (x₁ : In₁) (x₂ : In₂)
    (q : AutomatonEdgeType A.State) :
    Nonempty
      (Fintype
        (
            OwnedLabel Out₁ Out₂ q.srcOwner ×
              OwnedLabel Out₁ Out₂ q.tgtOwner ×
              OwnedLabel Out₁ Out₂ q.tgtOwner ×
              OwnedLabel Out₁ Out₂ q.srcOwner
        )) := by
  classical
  exact ⟨inferInstance⟩

end DistributedSynthesis
