/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Automata.EncodedParityProduct
import DistributedSynthesis.Library.Distributed.LeaderGame.Encoding.EncodedLeaderObjective

/-! Uniform guarded-LTL compilation. Adversary rows use the original
library graph order (left, right, both); all physical letters retain the
existing EncodedNoDirect enumeration. -/
namespace Characterisation.EncodedGuardedObjective
open DistributedSynthesis
attribute [local irreducible] Primrec

abbrev Data := EncodedParityTables.Data × EncodedNoDirect.Instance

def translations (i : EncodedNoDirect.Instance) : List (Nat × Nat) :=
  (List.range (EncodedNoDirect.letters i).length).map (fun a =>
    (((EncodedNoDirect.letters i).getD a (0,0,0,0,0)).2.2.1,a))
def product (d : Data) : EncodedParityProduct.Data :=
  (d.1,EncodedNoDirectParity.compile d.2,translations d.2)
def compile (d : Data) : EncodedParityTables.Data := EncodedParityProduct.guard (product d)
/-- The same compiled table in the existing round-objective interface. -/
def roundData (d : Data) : EncodedRoundObjectives.Data := (d.2,compile d)
def priorityBound (d : Data) := EncodedLeaderObjective.priorityBound (roundData d)

theorem translations_primrec : Primrec translations :=
  Primrec.list_map (Primrec.list_range.comp (Primrec.list_length.comp EncodedNoDirect.letters_primrec))
    ((Primrec.fin_val.comp (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp
      ((Primrec.list_getD (0,0,0,0,0)).comp (EncodedNoDirect.letters_primrec.comp Primrec.fst) Primrec.snd))))).pair Primrec.snd).to₂
theorem product_primrec : Primrec product := Primrec.fst.pair
  ((EncodedNoDirectParity.compile_primrec.comp Primrec.snd).pair (translations_primrec.comp Primrec.snd))
theorem compile_primrec : Primrec compile := EncodedParityProduct.guard_primrec.comp product_primrec
theorem roundData_primrec : Primrec roundData := Primrec.snd.pair compile_primrec
theorem priorityBound_primrec : Primrec priorityBound := EncodedLeaderObjective.priorityBound_primrec.comp roundData_primrec

end Characterisation.EncodedGuardedObjective
