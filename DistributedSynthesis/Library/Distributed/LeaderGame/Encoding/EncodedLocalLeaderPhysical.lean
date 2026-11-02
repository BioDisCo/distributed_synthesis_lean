/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderGame.Encoding.EncodedLocalLeaderAlphabet
import DistributedSynthesis.Library.Automata.EncodedParityConjunctionCorrect

/-! The local monitor reads the complete physical input/output alphabet.
The numbering neither removes a round nor hides a local input. -/
namespace Characterisation.EncodedLocalLeaderTest
open DistributedSynthesis

variable (d : Data)
abbrev PhysicalRound := RealizedBlockRound (Fin (receiverInputs d)) (Fin (senderInputs d))
  (Fin (receiverOutputs d)) (Fin (senderOutputs d))

def physicalNumber : PhysicalRound d ≃ Fin (physicalSize d) :=
  FiniteFunctionCodes.prod (FiniteFunctionCodes.prod (Equiv.refl _) (Equiv.refl _))
    (FiniteFunctionCodes.prod (Equiv.refl _) (Equiv.refl _))

theorem physicalNumber_val (a : PhysicalRound d) : (physicalNumber d a).val =
    physicalIndex d a.1.1.val a.1.2.val a.2.1.val a.2.2.val := rfl

theorem run_physical (play : Nat → PhysicalRound d) (n : Nat) :
    (monitor d).run play n =
      (EncodedParityConjunction.read (monitorData d) (physicalSize d)).run
        (fun n => physicalNumber d (play n)) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    apply Fin.ext
    change EncodedParityTables.next (monitorData d) ((monitor d).run play n).val _ = _
    rw [ih]
    rfl

theorem winsPlay_iff_accepts (play : Nat → PhysicalRound d) :
    (monitor d).WinsPlay play ↔
      (EncodedParityConjunction.read (monitorData d) (physicalSize d)).Accepts
        (fun n => physicalNumber d (play n)) := by
  rw [DetParityAutomaton.accepts_iff_natSeqMinEvenParity]
  unfold BlockRecordMonitor.WinsPlay
  simp only [run_physical]
  rfl

end Characterisation.EncodedLocalLeaderTest
