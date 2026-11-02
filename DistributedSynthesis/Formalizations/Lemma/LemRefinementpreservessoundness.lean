/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Formalizations.Definition.DefPathSummary

/-!
# Refinements preserve one-directional soundness
-/

namespace DistributedSynthesis

universe u v w x

/--
An atom map is one-directionally sound for a continuation semantics when
equal atoms imply equal continuation semantics.
-/
def OneDirectionalSound
    {Path : Type u} {Atom : Type v} {Continuation : Type w}
    (atomOf : Path -> Atom)
    (continuationOf : Path -> Continuation) :
    Prop :=
  ∀ old new,
    atomOf old = atomOf new ->
      continuationOf old = continuationOf new

/-- A refined atom map refines a base atom map if equality refined atoms imply equality base atoms. -/
def AtomRefines
    {Path : Type u} {BaseAtom : Type v} {RefinedAtom : Type w}
    (baseAtomOf : Path -> BaseAtom)
    (refinedAtomOf : Path -> RefinedAtom) :
    Prop :=
  ∀ old new,
    refinedAtomOf old = refinedAtomOf new ->
      baseAtomOf old = baseAtomOf new

/--
Lemma `lem:refinementpreservessoundness`: finite regular refinements do not
invalidate the one-directional continuation soundness implication.  The
finiteness/regularity hypotheses are orthogonal to the implication and are
therefore represented by the refinement map itself.
-/
theorem refinement_preserves_one_directional_soundness
    {Path : Type u} {BaseAtom : Type v} {RefinedAtom : Type w} {Continuation : Type x}
    (baseAtomOf : Path -> BaseAtom)
    (refinedAtomOf : Path -> RefinedAtom)
    (continuationOf : Path -> Continuation)
    (hsound : OneDirectionalSound baseAtomOf continuationOf)
    (hrefines : AtomRefines baseAtomOf refinedAtomOf) :
    OneDirectionalSound refinedAtomOf continuationOf := by
  intro old new hrefined
  exact hsound old new (hrefines old new hrefined)

end DistributedSynthesis
