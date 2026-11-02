/-
Lean adaptation and development: the paper authors listed in AUTHORS.md
at the repository root. The credits below refer to upstream formalizations,
not authorship of this Lean implementation; see the CounterMachines README.md.
-/

/-
SPDX-License-Identifier: MPL-2.0
Lean adaptation of the MM2 halting/determinism facts used by Andrej Dudenhefner's
MM2_HALTING_to_MM2_ZERO_HALTING.v in the Coq library of undecidability proofs.
The MM2 model is due to Dominique Larchey-Wendling and Andrej Dudenhefner.
Upstream revision: 11c41e0637f0c5219ad1c4c92d11609b7e072c31.
See README.md and LICENSE-MPL-2.0 in this directory.
-/
import DistributedSynthesis.Library.Computability.CounterMachines.MM2

/-! # Halting from arbitrary initial counter values

These are operational facts, not an undecidability assumption. The deterministic
terminal-suffix argument replaces the upstream confluence helper with Mathlib's
`ReflTransGen.total_of_right_unique`.
-/
namespace DistributedSynthesis.CounterMachine.MM2

abbrev Reaches (P : Program) := Relation.ReflTransGen (Step P)
def Terminates (P : Program) (x : Cfg) : Prop :=
  ∃ y, Reaches P x y ∧ Stops P y
abbrev HaltingInput := Program × Nat × Nat
def Halts (d : HaltingInput) : Prop := Terminates d.1 (1, d.2)

theorem zeroHalts_iff_terminates (P : Program) :
    ZeroHalts P ↔ Terminates P (1, (0, 0)) := Iff.rfl

theorem step_deterministic (P : Program) : Relator.RightUnique (Step P) := by
  intro x y z hy hz
  exact (step_eq P hy).trans (step_eq P hz).symm

theorem lookup_some_pos {P : Program} {i : Nat} {ρ : Instr}
    (h : lookup P i = some ρ) : i ≠ 0 := by
  intro hi
  simp [lookup, hi] at h

theorem stops_reaches_eq {P : Program} {x y : Cfg}
    (hs : Stops P x) (h : Reaches P x y) : y = x := by
  rcases h.cases_head with he | ⟨z, hz, _⟩
  · exact he.symm
  · exact False.elim (hs z hz)

/-- A finite execution prefix neither creates nor destroys eventual halting. -/
theorem terminates_iff_of_reaches {P : Program} {x y : Cfg}
    (hxy : Reaches P x y) : Terminates P x ↔ Terminates P y := by
  constructor
  · rintro ⟨z, hxz, hz⟩
    rcases Relation.ReflTransGen.total_of_right_unique (step_deterministic P) hxy hxz with h | h
    · exact ⟨z, h, hz⟩
    · have he := stops_reaches_eq hz h
      subst y
      exact ⟨z, .refl, hz⟩
  · rintro ⟨z, hyz, hz⟩
    exact ⟨z, hxy.trans hyz, hz⟩

end DistributedSynthesis.CounterMachine.MM2
