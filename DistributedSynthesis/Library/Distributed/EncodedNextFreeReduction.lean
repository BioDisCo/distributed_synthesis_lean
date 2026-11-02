/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/
import DistributedSynthesis.Library.Distributed.NextFreeReduction
import DistributedSynthesis.Library.Distributed.EncodedBinaryReduction
import DistributedSynthesis.Library.Logic.EncodedNextFree
import Mathlib.Computability.Reduce

/-! # Encoded reduction to next-free LTL with four output symbols

The target predicate explicitly requires next-free syntax. The compiler is
primitive recursive, and all its outputs satisfy that syntactic restriction.
Only the final result module imports an undecidability theorem.
-/
namespace DistributedSynthesis.EncodedNextFreeReduction
open NextFreeClock EncodedFiniteLTL

noncomputable instance : Primcodable Atom :=
  Primcodable.ofEquiv (Fin (Fintype.card Atom)) (Fintype.equivFin Atom)

abbrev Instance := Code Atom

/-- The restricted synthesis problem, not unrestricted four-symbol LTL. -/
def Realizable (c : Instance) : Prop :=
  LTL.NextFree (decode c) ∧ NextFreeReduction.Realizable (decode c)

def compile (c : EncodedBinaryReduction.Instance) : Instance :=
  binary 3 (EncodedNextFree.encode protocol)
    (EncodedNextFree.translate (.inr .one) Sum.inl c)

set_option maxHeartbeats 1000000 in
theorem compile_primrec : Primrec compile := by
  unfold compile
  apply (binary_primrec 3).comp (Primrec.const (EncodedNextFree.encode protocol))
  have hf : Primrec (Sum.inl : BinaryAgreement.Atom → Atom) := Primrec.dom_finite _
  exact EncodedNextFree.translate_primrec (B := Atom) (.inr .one) Sum.inl hf

theorem compile_rep (c : EncodedBinaryReduction.Instance) :
    Represents (compile c) (NextFreeReduction.formula (decode c)) :=
  conj_rep (EncodedNextFree.encode_rep protocol) (EncodedNextFree.translate_rep _ _ c)

theorem compile_nextFree (c : EncodedBinaryReduction.Instance) :
    LTL.NextFree (decode (compile c)) := by
  rw [(compile_rep c).decode]
  exact NextFreeReduction.formula_nextFree _

theorem compile_correct (c : EncodedBinaryReduction.Instance) :
    Realizable (compile c) ↔ EncodedBinaryReduction.Realizable c := by
  unfold Realizable
  rw [(compile_rep c).decode]
  exact (and_iff_right (NextFreeReduction.formula_nextFree _)).trans
    (NextFreeReduction.realizable_iff _)

theorem binary_manyOneReducible : EncodedBinaryReduction.Realizable ≤₀ Realizable :=
  ⟨compile, compile_primrec.to_comp, fun c ↦ (compile_correct c).symm⟩

end DistributedSynthesis.EncodedNextFreeReduction
