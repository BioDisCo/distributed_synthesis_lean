/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Automata.EncodedParityProductCorrect
import DistributedSynthesis.Library.Distributed.EncodedNoDirect

/-! Present an arbitrary finite deterministic parity automaton in the
library's numeric table format. The state and letter numberings are explicit.
For a fixed adversary this presentation is chosen before the input instance. -/
namespace Characterisation.EncodedParityPresentation
open DistributedSynthesis

variable {Letter : Type} (M : DetParityAutomaton Letter) {N E : Nat}
variable (states : M.State ≃ Fin (N+1)) (letters : Letter ≃ Fin E)

def data : EncodedParityTables.Data :=
  (N,(states M.initial).val,List.ofFn (fun q => M.priority (states.symm q)),
    List.ofFn (fun a => List.ofFn (fun q => (states (M.step (states.symm q) (letters.symm a))).val)))

theorem alphabet : (EncodedParityTables.rows (data M states letters)).length = E := by
  simp [data,EncodedParityTables.rows]

def automaton : DetParityAutomaton Letter :=
  (EncodedParityTables.automaton (data M states letters)).comap
    (fun a => Fin.cast (alphabet M states letters).symm (letters a))

theorem priority_encode (q : M.State) :
    (automaton M states letters).priority (states q) = M.priority q := by
  change (List.ofFn (fun q => M.priority (states.symm q))).getD (states q).val 0 = _
  rw [List.getD_eq_getElem _ _ (by simpa using (states q).isLt)]
  simp only [List.getElem_ofFn,Fin.eta,Equiv.symm_apply_apply]

theorem initial_encode : (automaton M states letters).initial = states M.initial := by
  apply Fin.ext
  exact Nat.mod_eq_of_lt (states M.initial).isLt

theorem step_encode (q : M.State) (a : Letter) :
    (automaton M states letters).step (states q) a = states (M.step q a) := by
  apply Fin.ext
  change ((List.ofFn (fun a => List.ofFn (fun q => (states (M.step (states.symm q) (letters.symm a))).val))).getD
    (letters a).val []).getD (states q).val 0 % (N+1) = _
  have row : (List.ofFn (fun a => List.ofFn (fun q => (states (M.step (states.symm q) (letters.symm a))).val))).getD
      (letters a).val [] = List.ofFn (fun q => (states (M.step (states.symm q) a)).val) := by
    rw [List.getD_eq_getElem _ _ (by simpa using (letters a).isLt)]
    simp only [List.getElem_ofFn,Fin.eta,Equiv.symm_apply_apply]
  rw [row,List.getD_eq_getElem _ _ (by simpa using (states q).isLt)]
  simp only [List.getElem_ofFn,Fin.eta,Equiv.symm_apply_apply]
  exact Nat.mod_eq_of_lt (states (M.step q a)).isLt

theorem run_encode (word : OmegaWord Letter) (t : Nat) :
    (automaton M states letters).run word t = states (M.run word t) := by
  induction t with
  | zero => exact initial_encode M states letters
  | succ t ih => rw [DetParityAutomaton.run_succ,ih,step_encode]; rfl

theorem accepts_iff (word : OmegaWord Letter) :
    (automaton M states letters).Accepts word ↔ M.Accepts word := by
  rw [DetParityAutomaton.accepts_iff_natSeqMinEvenParity,DetParityAutomaton.accepts_iff_natSeqMinEvenParity]
  simp only [run_encode,priority_encode]

/-- The same graph order as the existing LTL frontend. -/
def graphNumber : Graph ≃ Fin 3 where
  toFun := EncodedNoDirect.graphCode
  invFun g := if g.val = 0 then .left else if g.val = 1 then .right else .both
  left_inv g := by cases g <;> rfl
  right_inv g := by fin_cases g <;> rfl

/-- Every fixed graph adversary has a fixed finite numeric presentation.
This is existence of constant data, not a computability claim about an
arbitrarily presented semantic automaton. -/
theorem graph_presentation (A : DetParityAutomaton Graph) :
    ∃ d : EncodedParityTables.Data, ∃ h : (EncodedParityTables.rows d).length = 3,
      ∀ word : OmegaWord Graph,
        ((EncodedParityTables.automaton d).comap
          (fun g => Fin.cast h.symm (EncodedNoDirect.graphCode g))).Accepts word ↔ A.Accepts word := by
  classical
  letI : Fintype A.State := Fintype.ofFinite _
  have positive : 0 < Fintype.card A.State := Fintype.card_pos_iff.mpr ⟨A.initial⟩
  let number : A.State ≃ Fin (Fintype.card A.State - 1 + 1) :=
    (Fintype.equivFin A.State).trans (finCongr (Nat.sub_add_cancel positive).symm)
  refine ⟨data A number graphNumber,alphabet A number graphNumber,?_⟩
  intro word
  exact accepts_iff A number graphNumber word

end Characterisation.EncodedParityPresentation
