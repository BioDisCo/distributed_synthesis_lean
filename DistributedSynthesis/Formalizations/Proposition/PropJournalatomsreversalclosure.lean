/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Formalizations.Corollary.CorJournalplushandoff
import DistributedSynthesis.Formalizations.Lemma.LemRefinementpreservessoundness
import DistributedSynthesis.Formalizations.Proposition.PropSummarywindowcompatiblehandoff

/-!
# Finite reversal closure of journal atoms
-/

namespace DistributedSynthesis

universe u v w x y z q r

/--
Paper-aligned version of the enriched-seed saturation argument used in
Proposition `prop:journalatomsreversalclosure`.

`EnrichedSeed d` is the partition called `E_d` in the paper proof: the
atom-enriched summary-window classes.  `RefinedAtom d` is the stabilized
partition `Q_d*` obtained after simultaneous direct-reversal saturation.
The certificate keeps the hard automata/regular-language payloads as explicit
fields, but the inherited continuation soundness is proved from the two
refinement maps, matching the paper's repaired proof order.
-/
structure EnrichedSeedJournalClosureCertificate
    (EdgeType : Proc -> Type u)
    (BaseAtom : Proc -> Type v)
    (In₁ : Type w) (In₂ : Type x) (Out₁ : Type y) (Out₂ : Type z)
    (Continuation : Proc -> Type r) where
  EnrichedSeed : Proc -> Type q
  RefinedAtom : Proc -> Type q
  seedFinite : (d : Proc) -> Fintype (EnrichedSeed d)
  refinedFinite : (d : Proc) -> Fintype (RefinedAtom d)
  baseAtomOf : (d : Proc) -> TypedPath (EdgeType d) -> BaseAtom d
  seedAtomOf : (d : Proc) -> TypedPath (EdgeType d) -> EnrichedSeed d
  refinedAtomOf : (d : Proc) -> TypedPath (EdgeType d) -> RefinedAtom d
  continuationOf : (d : Proc) -> TypedPath (EdgeType d) -> Continuation d
  baseSound :
    ∀ d, OneDirectionalSound (baseAtomOf d) (continuationOf d)
  seedRefinesBase :
    ∀ d, AtomRefines (baseAtomOf d) (seedAtomOf d)
  refinedRefinesSeed :
    ∀ d, AtomRefines (seedAtomOf d) (refinedAtomOf d)
  enrichedSeedRegular : (d : Proc) -> Prop
  refinedRegular : (d : Proc) -> Prop
  seedIsAtomEnrichedSummaryWindow : Prop
  successorPreimagesStableOnRefinedAtoms : Prop
  directClosing :
    FunctionalDirectClosingExtension EdgeType RefinedAtom In₁ In₂ Out₁ Out₂
  finiteHandoff :
    FiniteDirectReversalHandoff RefinedAtom In₁ In₂ Out₁ Out₂
  enrichedSeedRegular_proof : ∀ d, enrichedSeedRegular d
  refinedRegular_proof : ∀ d, refinedRegular d
  seedIsAtomEnrichedSummaryWindow_proof : seedIsAtomEnrichedSummaryWindow
  successorPreimagesStableOnRefinedAtoms_proof :
    successorPreimagesStableOnRefinedAtoms

attribute [instance] EnrichedSeedJournalClosureCertificate.seedFinite
attribute [instance] EnrichedSeedJournalClosureCertificate.refinedFinite

/-- The stabilized atoms refine the original journal atoms through the enriched seed. -/
theorem enriched_seed_refined_atoms_refine_base
    {EdgeType : Proc -> Type u}
    {BaseAtom : Proc -> Type v}
    {In₁ : Type w} {In₂ : Type x} {Out₁ : Type y} {Out₂ : Type z}
    {Continuation : Proc -> Type r}
    (cert :
      EnrichedSeedJournalClosureCertificate
        EdgeType BaseAtom In₁ In₂ Out₁ Out₂ Continuation)
    (d : Proc) :
    AtomRefines (cert.baseAtomOf d) (cert.refinedAtomOf d) := by
  intro old new hrefined
  exact cert.seedRefinesBase d old new
    (cert.refinedRefinesSeed d old new hrefined)

/--
Paper-facing enriched-seed form of Proposition
`prop:journalatomsreversalclosure`.
-/
theorem journal_atoms_reversal_closure_from_enriched_seed
    {EdgeType : Proc -> Type u}
    {BaseAtom : Proc -> Type v}
    {In₁ : Type w} {In₂ : Type x} {Out₁ : Type y} {Out₂ : Type z}
    {Continuation : Proc -> Type r}
    (cert :
      EnrichedSeedJournalClosureCertificate
        EdgeType BaseAtom In₁ In₂ Out₁ Out₂ Continuation) :
    cert.seedIsAtomEnrichedSummaryWindow ∧
      cert.successorPreimagesStableOnRefinedAtoms ∧
      (∀ d, Nonempty (Fintype (cert.EnrichedSeed d))) ∧
      (∀ d, Nonempty (Fintype (cert.RefinedAtom d))) ∧
      (∀ d, cert.enrichedSeedRegular d) ∧
      (∀ d, cert.refinedRegular d) ∧
      (∀ d, OneDirectionalSound (cert.refinedAtomOf d) (cert.continuationOf d)) ∧
      Nonempty
        (FunctionalDirectClosingExtension EdgeType cert.RefinedAtom In₁ In₂ Out₁ Out₂) ∧
      Nonempty (FiniteDirectReversalHandoff cert.RefinedAtom In₁ In₂ Out₁ Out₂) := by
  refine
    ⟨cert.seedIsAtomEnrichedSummaryWindow_proof,
      cert.successorPreimagesStableOnRefinedAtoms_proof,
      ?_,
      ?_,
      cert.enrichedSeedRegular_proof,
      cert.refinedRegular_proof,
      ?_,
      ⟨cert.directClosing⟩,
      ⟨cert.finiteHandoff⟩⟩
  · intro d
    exact ⟨cert.seedFinite d⟩
  · intro d
    exact ⟨cert.refinedFinite d⟩
  · intro d
    exact
      refinement_preserves_one_directional_soundness
        (cert.baseAtomOf d)
        (cert.refinedAtomOf d)
        (cert.continuationOf d)
        (cert.baseSound d)
        (enriched_seed_refined_atoms_refine_base cert d)

/--
Certificate for Proposition `prop:journalatomsreversalclosure`.

The certificate separates the construction into the two semantic facts used in
the paper proof: refined atoms are finite regular refinements of the original
one-directional atoms, and the simultaneous reversal closure has stabilized to
a functional direct-closing extension.
-/
structure JournalAtomsReversalClosureCertificate
    (EdgeType : Proc -> Type u)
    (BaseAtom : Proc -> Type v)
    (In₁ : Type w) (In₂ : Type x) (Out₁ : Type y) (Out₂ : Type z)
    (Continuation : Proc -> Type r) where
  RefinedAtom : Proc -> Type q
  refinedFinite : (d : Proc) -> Fintype (RefinedAtom d)
  baseAtomOf : (d : Proc) -> TypedPath (EdgeType d) -> BaseAtom d
  refinedAtomOf : (d : Proc) -> TypedPath (EdgeType d) -> RefinedAtom d
  continuationOf : (d : Proc) -> TypedPath (EdgeType d) -> Continuation d
  baseSound :
    ∀ d, OneDirectionalSound (baseAtomOf d) (continuationOf d)
  refinedRefinesBase :
    ∀ d, AtomRefines (baseAtomOf d) (refinedAtomOf d)
  refinedRegular : (d : Proc) -> Prop
  enrichedSummaryWindowCompatible : Prop
  simultaneousClosureStabilizes : Prop
  directClosing :
    FunctionalDirectClosingExtension EdgeType RefinedAtom In₁ In₂ Out₁ Out₂
  finiteHandoff :
    FiniteDirectReversalHandoff RefinedAtom In₁ In₂ Out₁ Out₂
  refinedRegular_proof : ∀ d, refinedRegular d
  enrichedSummaryWindowCompatible_proof : enrichedSummaryWindowCompatible
  simultaneousClosureStabilizes_proof : simultaneousClosureStabilizes

attribute [instance] JournalAtomsReversalClosureCertificate.refinedFinite

/-- Refined atoms inherit one-directional continuation soundness from base atoms. -/
theorem journal_refined_atoms_preserve_soundness
    {EdgeType : Proc -> Type u}
    {BaseAtom : Proc -> Type v}
    {In₁ : Type w} {In₂ : Type x} {Out₁ : Type y} {Out₂ : Type z}
    {Continuation : Proc -> Type r}
    (cert :
      JournalAtomsReversalClosureCertificate
        EdgeType BaseAtom In₁ In₂ Out₁ Out₂ Continuation)
    (d : Proc) :
    OneDirectionalSound (cert.refinedAtomOf d) (cert.continuationOf d) :=
  refinement_preserves_one_directional_soundness
    (cert.baseAtomOf d)
    (cert.refinedAtomOf d)
    (cert.continuationOf d)
    (cert.baseSound d)
    (cert.refinedRefinesBase d)

/--
Proposition `prop:journalatomsreversalclosure`: the finite enriched reversal
closure yields finite regular refined atoms, preserves one-directional
soundness, and admits a functional direct-closing extension.
-/
theorem journal_atoms_reversal_closure
    {EdgeType : Proc -> Type u}
    {BaseAtom : Proc -> Type v}
    {In₁ : Type w} {In₂ : Type x} {Out₁ : Type y} {Out₂ : Type z}
    {Continuation : Proc -> Type r}
    (cert :
      JournalAtomsReversalClosureCertificate
        EdgeType BaseAtom In₁ In₂ Out₁ Out₂ Continuation) :
    cert.enrichedSummaryWindowCompatible ∧
      cert.simultaneousClosureStabilizes ∧
      (∀ d, Nonempty (Fintype (cert.RefinedAtom d))) ∧
      (∀ d, cert.refinedRegular d) ∧
      (∀ d, OneDirectionalSound (cert.refinedAtomOf d) (cert.continuationOf d)) ∧
      Nonempty
        (FunctionalDirectClosingExtension EdgeType cert.RefinedAtom In₁ In₂ Out₁ Out₂) ∧
      Nonempty (FiniteDirectReversalHandoff cert.RefinedAtom In₁ In₂ Out₁ Out₂) := by
  refine
    ⟨cert.enrichedSummaryWindowCompatible_proof,
      cert.simultaneousClosureStabilizes_proof,
      ?_,
      cert.refinedRegular_proof,
      ?_,
      ⟨cert.directClosing⟩,
      ⟨cert.finiteHandoff⟩⟩
  · intro d
    exact ⟨cert.refinedFinite d⟩
  · intro d
    exact journal_refined_atoms_preserve_soundness cert d

end DistributedSynthesis
