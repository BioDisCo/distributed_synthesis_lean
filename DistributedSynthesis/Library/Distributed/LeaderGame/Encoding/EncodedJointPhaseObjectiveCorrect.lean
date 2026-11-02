/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderGame.Encoding.EncodedJointPhaseAlphabet
import DistributedSynthesis.Library.Automata.EncodedParityConjunctionCorrect

/-! Exact equivalence to the existing all-root endless leader objective.
Each root starts in its own carried residual state and reads its own outputs
at every physical round. -/
namespace Characterisation.EncodedJointPhaseObjective
open DistributedSynthesis
open EncodedParityConjunction (read)

theorem component_alphabet (d : Data) (h : Nat) :
    (EncodedParityTables.rows (component d h)).length = (letters d).length := by
  simp [component,EncodedParityTables.rows]
theorem compile_alphabet (d : Data) :
    (EncodedParityTables.rows (compile d)).length = (letters d).length :=
  EncodedParityConjunction.compile_alphabet _

theorem component_next (d : Data) (h q a : Nat)
    (hq : q < EncodedRoundObjectives.stateCount (objective d)) (ha : a < (letters d).length) :
    EncodedParityTables.next (component d h) q a = step d h q a := by
  have row : ((List.range (letters d).length).map (fun a =>
      (List.range (EncodedRoundObjectives.stateCount (objective d))).map (fun q => step d h q a))).getD a [] =
      (List.range (EncodedRoundObjectives.stateCount (objective d))).map (fun q => step d h q a) := by
    rw [List.getD_eq_getElem _ _ (by simpa using ha)]
    simp only [List.getElem_map,List.getElem_range]
  unfold EncodedParityTables.next component EncodedParityTables.rows
  rw [row,List.getD_eq_getElem _ _ (by simpa using hq)]
  simp only [List.getElem_map,List.getElem_range]
  change step d h q a % EncodedRoundObjectives.stateCount (objective d) = _
  exact Nat.mod_eq_of_lt (Nat.mod_lt _ (Nat.succ_pos _))

variable {H G : Type} {R S : Nat} [Fintype H] [Fintype G]
variable (o : EncodedRoundObjectives.Data) (root : H ≃ Fin R) (groupNumber : G ≃ Fin S)
variable (start : H → (EncodedLeaderObjective.automaton o).State) (group : H → G)
local notation "input" => dataEncode o root groupNumber start group
local notation "M" => EncodedLeaderObjective.automaton o
local notation "index" => number o root groupNumber start group

omit [Fintype H] [Fintype G] in
theorem component_run (h : H) (word : OmegaWord (PhaseLetter (H:=H) (G:=G) o)) (t : Nat) :
    ((read (component input (root h).val) (letters input).length).run (fun n => index (word n)) t).val =
      ((M).runFrom (start h) (fun n => jointPhaseLetter group (word n) h) t).val := by
  induction t with
  | zero =>
    change ((List.ofFn (fun h => (start (root.symm h)).val)).getD (root h).val 0) %
      EncodedRoundObjectives.stateCount o = (start h).val
    rw [EncodedClosingBanks.table_eval root (fun h => (start h).val) 0 h]
    exact Nat.mod_eq_of_lt (start h).isLt
  | succ t ih =>
    change EncodedParityTables.next (component input (root h).val)
      ((read (component input (root h).val) (letters input).length).run (fun n => index (word n)) t).val
      (index (word t)).val = _
    rw [component_next _ _ _ _ (by exact ((read (component input (root h).val) (letters input).length).run
      (fun n => index (word n)) t).isLt) (index (word t)).isLt,step,ih,letter_encode,physical_encode]
    rfl

omit [Fintype H] [Fintype G] in
theorem component_accepts_iff (h : H) (word : OmegaWord (PhaseLetter (H:=H) (G:=G) o)) :
    (read (component input (root h).val) (letters input).length).Accepts (fun n => index (word n)) ↔
      (M).AcceptsFrom (start h) (fun n => jointPhaseLetter group (word n) h) := by
  rw [← DetParityAutomaton.withInitial_accepts_iff]
  rw [DetParityAutomaton.accepts_iff_natSeqMinEvenParity,DetParityAutomaton.accepts_iff_natSeqMinEvenParity]
  simp only [DetParityAutomaton.withInitial_run]
  have priorities (t : Nat) :
      (read (component input (root h).val) (letters input).length).priority
        ((read (component input (root h).val) (letters input).length).run (fun n => index (word n)) t) =
      ((M).withInitial (start h)).priority ((M).runFrom (start h) (fun n => jointPhaseLetter group (word n) h) t) := by
    change EncodedParityTables.priority o.2 _ = EncodedParityTables.priority o.2 _
    rw [component_run]
  simp only [priorities]

noncomputable def automaton : DetParityAutomaton (PhaseLetter (H:=H) (G:=G) o) :=
  (read (compile input) (letters input).length).comap index

omit [Fintype H] [Fintype G] in
/-- The generated automaton checks every possible initial root, including
its carried residual state. Empty root families impose no obligation. -/
theorem accepts_iff (word : OmegaWord (PhaseLetter (H:=H) (G:=G) o)) :
    (automaton o root groupNumber start group).Accepts word ↔
      ∀ h, (M).AcceptsFrom (start h) (fun n => jointPhaseLetter group (word n) h) := by
  rw [automaton,DetParityAutomaton.comap_accepts_iff]
  apply (EncodedParityConjunction.accepts_iff ((letters input).length,components input) (by
    intro c hc
    obtain ⟨h,_,rfl⟩ := List.mem_map.mp hc
    exact component_alphabet input h) _).trans
  constructor
  · intro checked h
    exact (component_accepts_iff o root groupNumber start group h word).mp
      (checked _ (List.mem_map.mpr ⟨(root h).val,by rw [List.mem_range,roots_encode]; exact (root h).isLt,rfl⟩))
  · intro checked c hc
    obtain ⟨h,hh,rfl⟩ := List.mem_map.mp hc
    have bound : h < R := by simpa only [List.mem_range,roots_encode] using hh
    have ok := (component_accepts_iff o root groupNumber start group (root.symm ⟨h,bound⟩) word).mpr (checked _)
    simpa only [Equiv.apply_symm_apply] using ok

omit [Fintype G] in
/-- Language equality with the existing semantic leader-phase automaton;
no equality between the two internal Muller/LAR state spaces is needed. -/
theorem accepts_jointPhaseDPA_iff (word : OmegaWord (PhaseLetter (H:=H) (G:=G) o)) :
    (automaton o root groupNumber start group).Accepts word ↔ (jointPhaseDPA M start group).Accepts word :=
  (accepts_iff o root groupNumber start group word).trans (jointPhaseDPA_accepts_iff M start group word).symm

omit [Fintype G] in
theorem accepts_jointPhaseObjective_iff (word : OmegaWord (PhaseLetter (H:=H) (G:=G) o)) :
    (automaton o root groupNumber start group).Accepts word ↔ (jointPhaseObjective M start group).WinsPlay word :=
  (accepts_iff o root groupNumber start group word).trans (jointPhaseObjective_wins_iff M start group word).symm

end Characterisation.EncodedJointPhaseObjective
