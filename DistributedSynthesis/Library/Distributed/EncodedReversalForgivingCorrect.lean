/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.EncodedReversalForgiving

/-! # Language correctness of the numeric reversal-forgiving companion -/
namespace DistributedSynthesis.EncodedReversalForgiving
open EncodedRoundObjectives EncodedNoDirect DetParityAutomaton
variable (d : Data)
local notation "A" => EncodedRoundObjectives.automaton d

def lastCode : Option Graph → Nat
  | none => 0
  | some g => (graphCode g).val+1
theorem lastCode_lt (g : Option Graph) : lastCode g < 4 := by
  cases g with
  | none => decide
  | some g => have h := (graphCode g).isLt; dsimp only [lastCode]; omega

def code : (A).reversalForgiving.State → Nat
  | Sum.inl (q,last) => 1 + lastCode last.down + 4*q.val
  | Sum.inr _ => 0
theorem code_lt (q : (A).reversalForgiving.State) : code d q < 4*stateCount d+1 := by
  cases q with
  | inl q => have hl := lastCode_lt q.2.down; have hq := q.1.isLt; dsimp only [code]; omega
  | inr q => dsimp only [code]; omega
def encode (q : (A).reversalForgiving.State) : (EncodedRoundObjectives.automaton (compile d)).State :=
  ⟨code d q,code_lt d q⟩

theorem killed_correct (last : Option Graph) (g : Graph) :
    killed (lastCode last) (graphCode g).val ↔ reversalKill last g = true := by
  cases last with
  | none => cases g <;> decide
  | some last => cases last <;> cases g <;> decide

theorem code_step (q : (A).reversalForgiving.State) (a : Letter d) :
    next (d,code d q,letterCode a) = code d ((A).reversalForgiving.step q a) := by
  cases q with
  | inr q => rfl
  | inl q =>
    have hl := lastCode_lt q.2.down
    have hn : 1+lastCode q.2.down+4*q.1.val ≠ 0 := by omega
    have hm : (1+lastCode q.2.down+4*q.1.val-1)%4 = lastCode q.2.down := by omega
    have hd : (1+lastCode q.2.down+4*q.1.val-1)/4 = q.1.val := by omega
    dsimp only [next,code,letterCode]
    simp only [hn,false_or,hm,hd,killed_correct]
    dsimp only [reversalForgiving]
    split_ifs <;> rfl

theorem step_encode (q : (A).reversalForgiving.State) (a : Letter d) :
    (EncodedRoundObjectives.automaton (compile d)).step (encode d q) a =
      encode d ((A).reversalForgiving.step q a) := by
  apply Fin.ext
  exact (next_correct d (encode d q) a).trans (code_step d q a)

theorem priority_encode (q : (A).reversalForgiving.State) :
    (EncodedRoundObjectives.automaton (compile d)).priority (encode d q) = (A).reversalForgiving.priority q := by
  change EncodedParityTables.priority (tables d) (encode d q).val = _
  rw [priority_getD]
  cases q with
  | inr q => rfl
  | inl q =>
    have hl := lastCode_lt q.2.down
    have hn : 1+lastCode q.2.down+4*q.1.val ≠ 0 := by omega
    have hd : (1+lastCode q.2.down+4*q.1.val-1)/4 = q.1.val := by omega
    change (if 1+lastCode q.2.down+4*q.1.val = 0 then 0 else
      objectivePriority d ((1+lastCode q.2.down+4*q.1.val-1)/4)) = _
    rw [if_neg hn,hd]
    rfl

theorem initial_encode : (EncodedRoundObjectives.automaton (compile d)).initial =
    encode d (A).reversalForgiving.initial := by
  apply Fin.ext
  exact Nat.mod_eq_of_lt (code_lt d (A).reversalForgiving.initial)

theorem run_encode (w : OmegaWord (Letter d)) (t : Nat) :
    (EncodedRoundObjectives.automaton (compile d)).run w t = encode d ((A).reversalForgiving.run w t) := by
  induction t with
  | zero => exact initial_encode d
  | succ t ih =>
    change (EncodedRoundObjectives.automaton (compile d)).step
      ((EncodedRoundObjectives.automaton (compile d)).run w t) (w t) = _
    rw [ih,step_encode]
    rfl

theorem accepts_iff (w : OmegaWord (Letter d)) :
    (EncodedRoundObjectives.automaton (compile d)).Accepts w ↔ (A).reversalForgiving.Accepts w := by
  rw [DetParityAutomaton.accepts_iff_natSeqMinEvenParity,
    DetParityAutomaton.accepts_iff_natSeqMinEvenParity]
  simp only [run_encode,priority_encode]
end DistributedSynthesis.EncodedReversalForgiving
