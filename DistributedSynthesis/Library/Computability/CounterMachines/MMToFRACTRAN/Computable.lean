/-
Lean adaptation and development: the paper authors listed in AUTHORS.md
at the repository root. The credits below refer to upstream formalizations,
not authorship of this Lean implementation; see the CounterMachines README.md.
-/

/-
SPDX-License-Identifier: MPL-2.0
Primitive-recursive input certification for the credited prime-power encoding.
This proof is added by the Lean port. See ../README.md.
-/
import DistributedSynthesis.Library.Computability.CounterMachines.MMToFRACTRAN.Encoding

namespace DistributedSynthesis.CounterMachine.MMToFRACTRAN
open scoped BigOperators
variable {n : Nat}

theorem registers_primrec : Primrec (@registers n) := by
  have hp : Primrec₂ (fun a b : Nat => a ^ b) := Primrec₂.unpaired'.mp Nat.Primrec.pow
  have hprod (s : Finset (Fin n)) : Primrec (fun v : MM.Registers n => ∏ k ∈ s, reg k ^ v k) := by
    induction s using Finset.induction_on with
    | empty => simpa using (Primrec.const (1 : Nat) : Primrec (fun _ : MM.Registers n => 1))
    | @insert k s hk ih =>
      simpa [Finset.prod_insert hk] using Primrec.nat_mul.comp
        (hp.comp (Primrec.const (reg k)) (Primrec.fin_app.comp Primrec.id (Primrec.const k))) ih
  exact hprod Finset.univ

theorem initial_primrec : Primrec (fun v : MM.Registers n => state (1,v)) :=
  Primrec.nat_mul.comp (Primrec.const (entry 1)) registers_primrec

end DistributedSynthesis.CounterMachine.MMToFRACTRAN
