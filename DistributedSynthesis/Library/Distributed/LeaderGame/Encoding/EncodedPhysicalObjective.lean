/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderGame.Encoding.EncodedLeaderObjective
import DistributedSynthesis.Library.Distributed.LeaderGame.Encoding.EncodedParityPresentation
import DistributedSynthesis.Library.Computability.FiniteFunctionCodes

/-! Present the physical objective on the environment/output product used
by graph-memory annotations. The original objective states, initial state,
priorities, and physical rounds are retained. -/
namespace Characterisation.EncodedPhysicalObjective
open DistributedSynthesis
attribute [local irreducible] Primrec

def environments (o : EncodedRoundObjectives.Data) :=
  EncodedRoundObjectives.inputOne o * (EncodedRoundObjectives.inputTwo o * 3)
def outputs (o : EncodedRoundObjectives.Data) :=
  EncodedRoundObjectives.outputOne o * EncodedRoundObjectives.outputTwo o
def alphabet (o : EncodedRoundObjectives.Data) := environments o * outputs o

def environmentNumber (o : EncodedRoundObjectives.Data) :
    (Fin (EncodedRoundObjectives.inputOne o) × Fin (EncodedRoundObjectives.inputTwo o) × Graph) ≃ Fin (environments o) :=
  FiniteFunctionCodes.prod (Equiv.refl _) (FiniteFunctionCodes.prod (Equiv.refl _) EncodedParityPresentation.graphNumber)
def outputNumber (o : EncodedRoundObjectives.Data) :
    (Fin (EncodedRoundObjectives.outputOne o) × Fin (EncodedRoundObjectives.outputTwo o)) ≃ Fin (outputs o) :=
  FiniteFunctionCodes.prod (Equiv.refl _) (Equiv.refl _)
def letterNumber (o : EncodedRoundObjectives.Data) : WithInputs.TupleLetter o.1 ≃ Fin (alphabet o) :=
  FiniteFunctionCodes.prod (environmentNumber o) (outputNumber o)

def decode (o : EncodedRoundObjectives.Data) (a : Nat) : EncodedNoDirect.LetterCode :=
  (a / outputs o / (EncodedRoundObjectives.inputTwo o * 3),
    a / outputs o % (EncodedRoundObjectives.inputTwo o * 3) / 3,
    ⟨a / outputs o % (EncodedRoundObjectives.inputTwo o * 3) % 3,Nat.mod_lt _ (by decide)⟩,
    a % outputs o / EncodedRoundObjectives.outputTwo o,a % outputs o % EncodedRoundObjectives.outputTwo o)
def compile (o : EncodedRoundObjectives.Data) : EncodedParityTables.Data :=
  (o.2.1,EncodedParityTables.initial o.2,EncodedParityTables.priorities o.2,
    (List.range (alphabet o)).map (fun a => (List.range (EncodedRoundObjectives.stateCount o)).map
      (fun q => EncodedRoundObjectives.objectiveStep o q (decode o a))))

theorem environments_primrec : Primrec environments := Primrec.nat_mul.comp EncodedRoundObjectives.inputOne_primrec
  (Primrec.nat_mul.comp EncodedRoundObjectives.inputTwo_primrec (Primrec.const 3))
theorem outputs_primrec : Primrec outputs := Primrec.nat_mul.comp EncodedRoundObjectives.outputOne_primrec
  EncodedRoundObjectives.outputTwo_primrec
theorem alphabet_primrec : Primrec alphabet := Primrec.nat_mul.comp environments_primrec outputs_primrec
theorem decode_primrec : Primrec₂ decode := by
  have hd : Primrec (fun x : EncodedRoundObjectives.Data × Nat => x.1) := Primrec.fst
  have env := Primrec.nat_div.comp Primrec.snd (outputs_primrec.comp hd)
  have out := Primrec.nat_mod.comp Primrec.snd (outputs_primrec.comp hd)
  have tailSize := Primrec.nat_mul.comp (EncodedRoundObjectives.inputTwo_primrec.comp hd) (Primrec.const 3)
  have tail := Primrec.nat_mod.comp env tailSize
  have graph : Primrec (fun x : EncodedRoundObjectives.Data × Nat =>
      (⟨x.2 / outputs x.1 % (EncodedRoundObjectives.inputTwo x.1 * 3) % 3,Nat.mod_lt _ (by decide)⟩ : Fin 3)) :=
    Primrec.fin_val_iff.mp (Primrec.nat_mod.comp tail (Primrec.const 3))
  exact (Primrec.nat_div.comp env tailSize).pair
    ((Primrec.nat_div.comp tail (Primrec.const 3)).pair (graph.pair
      ((Primrec.nat_div.comp out (EncodedRoundObjectives.outputTwo_primrec.comp hd)).pair
        (Primrec.nat_mod.comp out (EncodedRoundObjectives.outputTwo_primrec.comp hd)))))
theorem compile_primrec : Primrec compile :=
  (Primrec.fst.comp Primrec.snd).pair ((EncodedParityTables.initial_primrec.comp Primrec.snd).pair
    ((EncodedParityTables.priorities_primrec.comp Primrec.snd).pair
      (Primrec.list_map (Primrec.list_range.comp alphabet_primrec)
        (Primrec.list_map (Primrec.list_range.comp (EncodedRoundObjectives.stateCount_primrec.comp Primrec.fst))
          (EncodedRoundObjectives.objectiveStep_comp (Primrec.fst.comp Primrec.fst) Primrec.snd
            (decode_primrec.comp (Primrec.fst.comp Primrec.fst) (Primrec.snd.comp Primrec.fst))).to₂).to₂)))

theorem decode_fin (o : EncodedRoundObjectives.Data) (a : Fin (alphabet o)) : decode o a.val =
    EncodedNoDirect.letterCode (continuationRecord ((letterNumber o).symm a)) := by
  change (_,_,_,_,_) = (_,_,EncodedParityPresentation.graphNumber
    (EncodedParityPresentation.graphNumber.symm _),_,_)
  rw [Equiv.apply_symm_apply]
  rfl

theorem decode_number (o : EncodedRoundObjectives.Data) (a : WithInputs.TupleLetter o.1) :
    decode o (letterNumber o a).val = EncodedNoDirect.letterCode (continuationRecord a) := by
  rw [decode_fin,Equiv.symm_apply_apply]

theorem compile_next (o : EncodedRoundObjectives.Data) (q : (EncodedLeaderObjective.automaton o).State)
    (a : WithInputs.TupleLetter o.1) : EncodedParityTables.next (compile o) q.val (letterNumber o a).val =
      ((EncodedLeaderObjective.automaton o).step q a).val := by
  have row : (EncodedParityTables.rows (compile o)).getD (letterNumber o a).val [] =
      (List.range (EncodedRoundObjectives.stateCount o)).map
        (fun q => EncodedRoundObjectives.objectiveStep o q (decode o (letterNumber o a).val)) := by
    rw [List.getD_eq_getElem _ _ (by simpa only [compile,EncodedParityTables.rows,List.length_map,List.length_range]
      using (letterNumber o a).isLt)]
    simp only [compile,EncodedParityTables.rows,List.getElem_map,List.getElem_range]
  unfold EncodedParityTables.next
  rw [row,List.getD_eq_getElem _ _ (by simpa only [List.length_map,List.length_range] using q.isLt)]
  simp only [List.getElem_map,List.getElem_range,decode_number]
  change (_ % EncodedRoundObjectives.stateCount o) % EncodedRoundObjectives.stateCount o = _
  rw [Nat.mod_mod]
  rfl

theorem transition (o : EncodedRoundObjectives.Data) (q : (EncodedLeaderObjective.automaton o).State)
    (r : Fin (EncodedRoundObjectives.inputOne o) × Fin (EncodedRoundObjectives.inputTwo o) × Graph)
    (a : Fin (EncodedRoundObjectives.outputOne o) × Fin (EncodedRoundObjectives.outputTwo o)) :
    EncodedParityTables.next (compile o) q.val ((environmentNumber o r).val * outputs o + (outputNumber o a).val) =
      ((EncodedLeaderObjective.automaton o).step q (r,a)).val := by
  have code : (letterNumber o (r,a)).val = (environmentNumber o r).val * outputs o + (outputNumber o a).val := by
    change (outputNumber o a).val + outputs o * (environmentNumber o r).val = _
    ac_rfl
  rw [← code]
  exact compile_next o q (r,a)

theorem priority (o : EncodedRoundObjectives.Data) (q : (EncodedLeaderObjective.automaton o).State) :
    EncodedParityTables.priority (compile o) q.val = (EncodedLeaderObjective.rank o q).val := rfl

end Characterisation.EncodedPhysicalObjective
