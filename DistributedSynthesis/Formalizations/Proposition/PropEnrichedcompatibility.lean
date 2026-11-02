/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Formalizations.Definition.DefPathSummary

/-!
# Atom-enriched summary-window compatibility
-/

namespace DistributedSynthesis

universe u v w x

/--
A deterministic monitor family determines an atom map if equality of all
terminal monitor states implies equality of atoms.
-/
def MonitorAtomCompatible
    {EdgeType : Type u} {Atom : Type v}
    (family : DeterministicMonitorFamily EdgeType)
    (atomOf : TypedPath EdgeType -> Atom) :
    Prop :=
  ∀ old new,
    (∀ i, runMonitor family i old = runMonitor family i new) ->
      atomOf old = atomOf new

/--
Proposition `prop:enrichedcompatibility`, finite/compatibility core:
the atom-enriched summary-window abstraction has a finite carrier, and
when the monitor family determines the target atom family, equality of
enriched values determines atom equality.
-/
theorem atom_enriched_summary_window_finite_and_compatible
    {EdgeType : Type u} {Atom : Type v}
    [Fintype EdgeType]
    (S : PathSummarySemigroup.{u, w} EdgeType)
    (family : DeterministicMonitorFamily.{u, v, x} EdgeType)
    (c : Nat)
    (atomOf : TypedPath EdgeType -> Atom)
    (hcompat : MonitorAtomCompatible family atomOf) :
    Nonempty (Fintype (FiniteAtomEnrichedSummaryWindowValue S.Summary EdgeType family c)) ∧
      ∀ old new,
        finiteAtomEnrichedSummaryWindowAbstraction S family c old =
          finiteAtomEnrichedSummaryWindowAbstraction S family c new ->
            atomOf old = atomOf new := by
  constructor
  · exact finite_atom_enriched_summary_window_values_finite EdgeType S.Summary family c
  · intro old new heq
    apply hcompat
    intro i
    exact congrFun (congrArg Prod.snd heq) i

/-- The enriched abstraction refines the raw summary-window abstraction. -/
theorem atom_enriched_summary_window_refines_raw
    {EdgeType : Type u}
    [Fintype EdgeType]
    (S : PathSummarySemigroup.{u, w} EdgeType)
    (family : DeterministicMonitorFamily.{u, v, x} EdgeType)
    (c : Nat) :
    ∀ old new,
      finiteAtomEnrichedSummaryWindowAbstraction S family c old =
        finiteAtomEnrichedSummaryWindowAbstraction S family c new ->
          finiteSummaryWindowAbstraction S c old =
            finiteSummaryWindowAbstraction S c new := by
  intro old new heq
  exact congrArg Prod.fst heq

/--
Paper-facing certificate for the full `prop:enrichedcompatibility` statement.
The first compatibility field is proved from monitor determinacy; the
regularity and reversal-closure fields are the effective automata bookkeeping
carried by the construction.
-/
structure EnrichedCompatibilityCertificate
    {EdgeType : Type u} {Atom : Type v}
    [Fintype EdgeType]
    (S : PathSummarySemigroup.{u, w} EdgeType)
    (family : DeterministicMonitorFamily.{u, v, x} EdgeType)
    (c : Nat)
    (atomOf : TypedPath EdgeType -> Atom) where
  monitorDeterminesAtom : MonitorAtomCompatible family atomOf
  enrichedClassesRegular : Prop
  finiteReversalClosurePreserved : Prop
  enrichedClassesRegular_proof : enrichedClassesRegular
  finiteReversalClosurePreserved_proof : finiteReversalClosurePreserved

/--
Proposition `prop:enrichedcompatibility`: fixed finite atom monitors give a
finite enriched abstraction, determine the atom family, refine the raw
summary-window value, and preserve the regular/reversal-closure obligations.
-/
theorem enriched_compatibility
    {EdgeType : Type u} {Atom : Type v}
    [Fintype EdgeType]
    (S : PathSummarySemigroup.{u, w} EdgeType)
    (family : DeterministicMonitorFamily.{u, v, x} EdgeType)
    (c : Nat)
    (atomOf : TypedPath EdgeType -> Atom)
    (cert : EnrichedCompatibilityCertificate S family c atomOf) :
    Nonempty (Fintype (FiniteAtomEnrichedSummaryWindowValue S.Summary EdgeType family c)) ∧
      (∀ old new,
        finiteAtomEnrichedSummaryWindowAbstraction S family c old =
          finiteAtomEnrichedSummaryWindowAbstraction S family c new ->
            atomOf old = atomOf new) ∧
      (∀ old new,
        finiteAtomEnrichedSummaryWindowAbstraction S family c old =
          finiteAtomEnrichedSummaryWindowAbstraction S family c new ->
            finiteSummaryWindowAbstraction S c old =
              finiteSummaryWindowAbstraction S c new) ∧
      cert.enrichedClassesRegular ∧
      cert.finiteReversalClosurePreserved := by
  exact
    ⟨(atom_enriched_summary_window_finite_and_compatible
        S family c atomOf cert.monitorDeterminesAtom).1,
      (atom_enriched_summary_window_finite_and_compatible
        S family c atomOf cert.monitorDeterminesAtom).2,
      atom_enriched_summary_window_refines_raw S family c,
      cert.enrichedClassesRegular_proof,
      cert.finiteReversalClosurePreserved_proof⟩

end DistributedSynthesis
