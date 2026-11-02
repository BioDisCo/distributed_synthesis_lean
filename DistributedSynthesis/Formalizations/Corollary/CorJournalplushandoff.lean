/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Formalizations.Lemma.LemDecompositionunique
import DistributedSynthesis.Formalizations.Proposition.PropNodirectfromjournal

/-!
# Journal summaries plus functional handoff

This file packages `cor:journalplushandoff` as the finite-basis certificate
assembled from synchronized-block summaries and functional direct-reversal
handoff data.
-/

namespace DistributedSynthesis

universe u v w x y z q

/--
Certificate that the journal summaries and functional direct-reversal handoff
assemble into the finite regular-test basis required by the decision route.
-/
structure JournalPlusHandoffCertificate
    (Alphabet : Type u)
    (EdgeType : Proc -> Type v)
    (In₁ : Type w) (In₂ : Type x) (Out₁ : Type y) (Out₂ : Type z)
    (Atom : Proc -> Type (max u v w x y z)) where
  Realizable : Prop
  uniform :
    UniformOneDirectionalFiniteIndexLemma.{u, w, x, y, z, max u v w x y z}
      Alphabet In₁ In₂ Out₁ Out₂
  directClosing :
    FunctionalDirectClosingExtension EdgeType Atom In₁ In₂ Out₁ Out₂
  blockDecompositionUnique : ∀ word : List Graph,
    ∃! decomposition : List BlockRound, IsBlockDecomposition word decomposition
  regularBasis :
    (d : Proc) ->
      FiniteRegularTestBasis.{max u v w x y z, v, q} uniform.boundary (EdgeType d)
  directReversalHandoff :
    FiniteDirectReversalHandoff Atom In₁ In₂ Out₁ Out₂
  finiteGame :
    FiniteDynamicHierarchyParityGame.{max u v w x y z, max u v w x y z}
  finiteGameRealizableIff : finiteGame.realizable ↔ Realizable
  finiteRegularBasisAssembled : Prop
  directReversalHandoffPreservesContinuations : Prop
  finiteRegularBasisAssembled_proof : finiteRegularBasisAssembled
  directReversalHandoffPreservesContinuations_proof :
    directReversalHandoffPreservesContinuations

/--
Corollary `cor:journalplushandoff`: the assembled synchronized-block and
direct-reversal certificate yields the decidability conclusion.
-/
noncomputable def journal_plus_handoff
    {Alphabet : Type u}
    {EdgeType : Proc -> Type v}
    {In₁ : Type w} {In₂ : Type x} {Out₁ : Type y} {Out₂ : Type z}
    {Atom : Proc -> Type (max u v w x y z)}
    (certificate :
      JournalPlusHandoffCertificate.{u, v, w, x, y, z, q}
        Alphabet EdgeType In₁ In₂ Out₁ Out₂ Atom) :
    Decidable certificate.Realizable := by
  let finiteGameDecision :=
    finite_dynamic_hierarchy_parity_game_decidable certificate.finiteGame
  cases finiteGameDecision with
  | isTrue h =>
      exact isTrue (certificate.finiteGameRealizableIff.mp h)
  | isFalse h =>
      exact isFalse (fun hRealizable =>
        h (certificate.finiteGameRealizableIff.mpr hRealizable))

/--
Paper-facing audit theorem: the full-model route depends on exactly the
assembled finite regular basis, the continuation-preserving reversal handoff,
and the finite dynamic-hierarchy parity game equivalence.
-/
theorem journal_plus_handoff_certificate_payload
    {Alphabet : Type u}
    {EdgeType : Proc -> Type v}
    {In₁ : Type w} {In₂ : Type x} {Out₁ : Type y} {Out₂ : Type z}
    {Atom : Proc -> Type (max u v w x y z)}
    (certificate :
      JournalPlusHandoffCertificate.{u, v, w, x, y, z, q}
        Alphabet EdgeType In₁ In₂ Out₁ Out₂ Atom) :
    certificate.finiteRegularBasisAssembled ∧
      certificate.directReversalHandoffPreservesContinuations ∧
      certificate.finiteGame.dynamicHierarchy ∧
      certificate.finiteGame.parityObjective ∧
      Nonempty (Decidable certificate.Realizable) := by
  exact
    ⟨certificate.finiteRegularBasisAssembled_proof,
      certificate.directReversalHandoffPreservesContinuations_proof,
      certificate.finiteGame.dynamicHierarchy_proof,
      certificate.finiteGame.parityObjective_proof,
      ⟨journal_plus_handoff certificate⟩⟩

/-- The canonical block-decomposition uniqueness proof supplies the certificate field. -/
theorem journalPlusHandoff_blockDecompositionUnique :
    ∀ word : List Graph,
      ∃! decomposition : List BlockRound, IsBlockDecomposition word decomposition := by
  intro word
  exact decomposition_unique word

end DistributedSynthesis
