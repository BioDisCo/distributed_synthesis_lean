/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Automata.EncodedParityFamiliesCorrect

/-! A uniform synchronous product of two numeric parity automata. Each row
specifies one physical letter and its translation for each component. Both
components advance once per letter; no rounds are contracted. -/
namespace Characterisation.EncodedParityProduct
open DistributedSynthesis
attribute [local irreducible] Primrec

abbrev Data := EncodedParityTables.Data × EncodedParityTables.Data × List (Nat × Nat)
def left (d : Data) := d.1
def right (d : Data) := d.2.1
def letters (d : Data) := d.2.2
def count (d : Data) := EncodedParityTables.size (left d) * EncodedParityTables.size (right d)
def leftState (d : Data) (q : Nat) := q / EncodedParityTables.size (right d)
def rightState (d : Data) (q : Nat) := q % EncodedParityTables.size (right d)
def letter (d : Data) (a : Nat) := (letters d).getD a (0,0)
def join (d : Data) (l r : Nat) := r + EncodedParityTables.size (right d) * l
def first (d : Data) := join d
  (EncodedParityTables.initial (left d) % EncodedParityTables.size (left d))
  (EncodedParityTables.initial (right d) % EncodedParityTables.size (right d))
def step (d : Data) (q a : Nat) := join d
  (EncodedParityTables.next (left d) (leftState d q) (letter d a).1)
  (EncodedParityTables.next (right d) (rightState d q) (letter d a).2)
def leftPriorities (d : Data) := (List.range (count d)).map
  (fun q => EncodedParityTables.priority (left d) (leftState d q))
def rightPriorities (d : Data) := (List.range (count d)).map
  (fun q => EncodedParityTables.priority (right d) (rightState d q))
def transition (d : Data) : EncodedParityTables.Data :=
  (count d-1,first d,[],(List.range (letters d).length).map
    (fun a => (List.range (count d)).map (fun q => step d q a)))
def guardData (d : Data) := EncodedParityFamilies.guardData
  (transition d) (leftPriorities d) (rightPriorities d)
def conjunctionData (d : Data) := EncodedParityFamilies.conjunctionData
  (transition d) [leftPriorities d,rightPriorities d]
def guard (d : Data) := EncodedParityFamilies.compile (guardData d)
def conjunction (d : Data) := EncodedParityFamilies.compile (conjunctionData d)

theorem left_primrec : Primrec left := Primrec.fst
theorem right_primrec : Primrec right := Primrec.fst.comp Primrec.snd
theorem letters_primrec : Primrec letters := Primrec.snd.comp Primrec.snd
theorem count_primrec : Primrec count := Primrec.nat_mul.comp
  (EncodedParityTables.size_primrec.comp left_primrec) (EncodedParityTables.size_primrec.comp right_primrec)
theorem leftState_primrec : Primrec₂ leftState := Primrec.nat_div.comp Primrec.snd
  (EncodedParityTables.size_primrec.comp (right_primrec.comp Primrec.fst))
theorem rightState_primrec : Primrec₂ rightState := Primrec.nat_mod.comp Primrec.snd
  (EncodedParityTables.size_primrec.comp (right_primrec.comp Primrec.fst))
theorem letter_primrec : Primrec₂ letter := (Primrec.list_getD (0,0)).comp (letters_primrec.comp Primrec.fst) Primrec.snd
theorem join_primrec : Primrec (fun x : Data × Nat × Nat => join x.1 x.2.1 x.2.2) :=
  Primrec.nat_add.comp (Primrec.snd.comp Primrec.snd)
    (Primrec.nat_mul.comp (EncodedParityTables.size_primrec.comp (right_primrec.comp Primrec.fst))
      (Primrec.fst.comp Primrec.snd))
theorem first_primrec : Primrec first := join_primrec.comp (Primrec.id.pair
  ((Primrec.nat_mod.comp (EncodedParityTables.initial_primrec.comp left_primrec)
    (EncodedParityTables.size_primrec.comp left_primrec)).pair
  (Primrec.nat_mod.comp (EncodedParityTables.initial_primrec.comp right_primrec)
    (EncodedParityTables.size_primrec.comp right_primrec))))
theorem step_primrec : Primrec (fun x : Data × Nat × Nat => step x.1 x.2.1 x.2.2) :=
  join_primrec.comp (Primrec.fst.pair
    ((EncodedParityTables.next_primrec.comp ((left_primrec.comp Primrec.fst).pair
      ((leftState_primrec.comp Primrec.fst (Primrec.fst.comp Primrec.snd)).pair
        (Primrec.fst.comp (letter_primrec.comp Primrec.fst (Primrec.snd.comp Primrec.snd)))))).pair
    (EncodedParityTables.next_primrec.comp ((right_primrec.comp Primrec.fst).pair
      ((rightState_primrec.comp Primrec.fst (Primrec.fst.comp Primrec.snd)).pair
        (Primrec.snd.comp (letter_primrec.comp Primrec.fst (Primrec.snd.comp Primrec.snd))))))))
theorem leftPriorities_primrec : Primrec leftPriorities :=
  Primrec.list_map (Primrec.list_range.comp count_primrec)
    (EncodedParityTables.priority_primrec.comp (left_primrec.comp Primrec.fst) leftState_primrec).to₂
theorem rightPriorities_primrec : Primrec rightPriorities :=
  Primrec.list_map (Primrec.list_range.comp count_primrec)
    (EncodedParityTables.priority_primrec.comp (right_primrec.comp Primrec.fst) rightState_primrec).to₂
theorem transition_primrec : Primrec transition :=
  (Primrec.nat_sub.comp count_primrec (Primrec.const 1)).pair (first_primrec.pair
    ((Primrec.const []).pair
      (Primrec.list_map (Primrec.list_range.comp (Primrec.list_length.comp letters_primrec))
        (Primrec.list_map (Primrec.list_range.comp (count_primrec.comp Primrec.fst))
          (step_primrec.comp ((Primrec.fst.comp Primrec.fst).pair
            (Primrec.snd.pair (Primrec.snd.comp Primrec.fst)))).to₂).to₂)))
theorem guardData_primrec : Primrec guardData := EncodedParityFamilies.guardData_primrec.comp
  (transition_primrec.pair (leftPriorities_primrec.pair rightPriorities_primrec))
theorem conjunctionData_primrec : Primrec conjunctionData := EncodedParityFamilies.conjunctionData_primrec.comp
  transition_primrec (Primrec.list_cons.comp leftPriorities_primrec
    (Primrec.list_cons.comp rightPriorities_primrec (Primrec.const [])))
theorem guard_primrec : Primrec guard := EncodedParityFamilies.compile_primrec.comp guardData_primrec
theorem conjunction_primrec : Primrec conjunction := EncodedParityFamilies.compile_primrec.comp conjunctionData_primrec

end Characterisation.EncodedParityProduct
