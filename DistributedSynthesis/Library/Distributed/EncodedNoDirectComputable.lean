/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.EncodedJournalTablesCorrect

/-! # Computable perfect-recall LTL synthesis without direct reversals

The input is the existing finite instance encoding. Every stage is proved
primitive recursive: LTL to parity, the reversal-forgiving companion, journal
tables, and finite-tree nonemptiness. No compiler, checker, or solver is an
additional premise. The exhaustive construction is not an efficiency claim.
-/
namespace DistributedSynthesis.EncodedNoDirectComputable
open EncodedNoDirect

def compile (d : Instance) : EncodedTreeNonemptiness.Data :=
  EncodedJournalTables.compile (EncodedReversalForgiving.compile (EncodedRoundObjectives.fromInstance d))
theorem compile_primrec : Primrec compile := EncodedJournalTables.compile_primrec.comp
  (EncodedReversalForgiving.compile_primrec.comp EncodedRoundObjectives.fromInstance_primrec)

/-- An LTL instance is realizable on the no-direct-reversal graph language
exactly when its compiled finite tree automaton accepts a tree. Realizability
quantifies over arbitrary perfect-recall strategies and all private inputs. -/
theorem compile_correct (d : Instance) : Realizable d ↔ EncodedTreeNonemptiness.Nonempty (compile d) := by
  have h := EncodedJournalTablesCorrect.realizable_iff_nonempty (EncodedRoundObjectives.fromInstance d)
  rw [EncodedRoundObjectives.automaton_fromInstance] at h
  exact (EncodedNoDirectParity.realizable_iff d).trans h

/-- Decide realizability by compiling the instance to finite tree nonemptiness
and running the verified nonemptiness procedure. -/
def solve (d : Instance) := EncodedTreeNonemptiness.solve (compile d)
/-- The solver is primitive recursive in the finite encoding of the instance. -/
theorem solve_primrec : Primrec solve := EncodedTreeNonemptiness.solve_primrec.comp compile_primrec
/-- The solver returns true if and only if two local strategies can satisfy
the instance against all allowed graph sequences and all private input streams. -/
theorem solve_correct (d : Instance) : solve d = true ↔ Realizable d :=
  (EncodedTreeNonemptiness.solve_correct (compile d)).trans (compile_correct d).symm

/-- There is an algorithm deciding LTL realizability under the prohibition of
direct reversals, with finite nonempty alphabets specified by the instance. -/
theorem realizable_computable : ComputablePred Realizable :=
  (Primrec.eq.comp solve_primrec (Primrec.const true)).computablePred.of_eq solve_correct

/-- The earlier executable procedure computes exactly the same Boolean answer. -/
theorem solve_eq_original (d : Instance) : solve d = EncodedNoDirect.solve d :=
  Bool.eq_iff_iff.mpr ((solve_correct d).trans (EncodedNoDirect.solve_correct d).symm)

/-- The original executable solver is also primitive recursive, since it
computes the same Boolean function as the numeric solver. -/
theorem original_solve_primrec : Primrec EncodedNoDirect.solve := solve_primrec.of_eq solve_eq_original
end DistributedSynthesis.EncodedNoDirectComputable
