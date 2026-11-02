/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Automata.EncodedParityConjunction
import DistributedSynthesis.Library.Distributed.LeaderGame.Encoding.EncodedLeaderObjective
import DistributedSynthesis.Library.Computability.FiniteCodeNumbering
import DistributedSynthesis.Library.Computability.FiniteFunctionCodes

/-! Generate the endless-phase objective from the actual leader groups and
residual objective states. No root's residual state is reset. Each root reads
its own receiver output and the output of its leader's observable group. -/
namespace Characterisation.EncodedJointPhaseObjective
open DistributedSynthesis
attribute [local irreducible] Primrec

abbrev Data := EncodedRoundObjectives.Data × Nat × List Nat × List Nat
abbrev Letter := (Nat × Nat) × List Nat × List Nat
def objective (d : Data) := d.1
def groups (d : Data) := d.2.1
def initial (d : Data) := d.2.2.1
def assignment (d : Data) := d.2.2.2
def roots (d : Data) := (initial d).length
def rawLetters (d : Data) : List Letter :=
  ((List.range (EncodedRoundObjectives.inputTwo (objective d))).product
    (List.range (EncodedRoundObjectives.inputOne (objective d)))).product
    ((FiniteSearch.tables (EncodedRoundObjectives.outputTwo (objective d)) (roots d)).product
      (FiniteSearch.tables (EncodedRoundObjectives.outputOne (objective d)) (groups d)))
def letters (d : Data) := FiniteCodeNumbering.unique (rawLetters d)
def letter (d : Data) (a : Nat) := (letters d).getD a ((0,0),[],[])
def physical (d : Data) (h : Nat) (a : Letter) : EncodedNoDirect.LetterCode :=
  (a.1.2,a.1.1,1,a.2.2.getD ((assignment d).getD h 0) 0,a.2.1.getD h 0)
def step (d : Data) (h q a : Nat) :=
  EncodedRoundObjectives.objectiveStep (objective d) q (physical d h (letter d a))
def component (d : Data) (h : Nat) : EncodedParityTables.Data :=
  ((objective d).2.1,(initial d).getD h 0,EncodedParityTables.priorities (objective d).2,
    (List.range (letters d).length).map (fun a =>
      (List.range (EncodedRoundObjectives.stateCount (objective d))).map (fun q => step d h q a)))
def components (d : Data) := (List.range (roots d)).map (component d)
def compile (d : Data) := EncodedParityConjunction.compile ((letters d).length,components d)

theorem objective_primrec : Primrec objective := Primrec.fst
theorem groups_primrec : Primrec groups := Primrec.fst.comp Primrec.snd
theorem initial_primrec : Primrec initial := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
theorem assignment_primrec : Primrec assignment := Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
theorem roots_primrec : Primrec roots := Primrec.list_length.comp initial_primrec
theorem rawLetters_primrec : Primrec rawLetters := FiniteSearch.product_primrec.comp
  (FiniteSearch.product_primrec.comp
    (Primrec.list_range.comp (EncodedRoundObjectives.inputTwo_primrec.comp objective_primrec))
    (Primrec.list_range.comp (EncodedRoundObjectives.inputOne_primrec.comp objective_primrec)))
  (FiniteSearch.product_primrec.comp
    (FiniteSearch.tables_primrec.comp (EncodedRoundObjectives.outputTwo_primrec.comp objective_primrec) roots_primrec)
    (FiniteSearch.tables_primrec.comp (EncodedRoundObjectives.outputOne_primrec.comp objective_primrec) groups_primrec))
theorem letters_primrec : Primrec letters := FiniteCodeNumbering.unique_primrec.comp rawLetters_primrec
theorem letter_primrec : Primrec₂ letter :=
  (Primrec.list_getD ((0,0),[],[])).comp (letters_primrec.comp Primrec.fst) Primrec.snd
theorem physical_primrec : Primrec (fun x : Data × Nat × Letter => physical x.1 x.2.1 x.2.2) := by
  have hd : Primrec (fun x : Data × Nat × Letter => x.1) := Primrec.fst
  have hh : Primrec (fun x : Data × Nat × Letter => x.2.1) := Primrec.fst.comp Primrec.snd
  have ha : Primrec (fun x : Data × Nat × Letter => x.2.2) := Primrec.snd.comp Primrec.snd
  exact (Primrec.snd.comp (Primrec.fst.comp ha)).pair ((Primrec.fst.comp (Primrec.fst.comp ha)).pair
    ((Primrec.const (1 : Fin 3)).pair
      (((Primrec.list_getD 0).comp (Primrec.snd.comp (Primrec.snd.comp ha))
        ((Primrec.list_getD 0).comp (assignment_primrec.comp hd) hh)).pair
        ((Primrec.list_getD 0).comp (Primrec.fst.comp (Primrec.snd.comp ha)) hh))))
theorem step_primrec : Primrec (fun x : Data × Nat × Nat × Nat => step x.1 x.2.1 x.2.2.1 x.2.2.2) :=
  EncodedRoundObjectives.objectiveStep_comp (objective_primrec.comp Primrec.fst)
    (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
    (physical_primrec.comp (Primrec.fst.pair ((Primrec.fst.comp Primrec.snd).pair
      (letter_primrec.comp Primrec.fst (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))))))
theorem component_primrec : Primrec₂ component := by
  have hd : Primrec (fun x : Data × Nat => x.1) := Primrec.fst
  have ho := objective_primrec.comp hd
  have rows : Primrec (fun x : Data × Nat => (List.range (letters x.1).length).map (fun a =>
      (List.range (EncodedRoundObjectives.stateCount (objective x.1))).map (fun q => step x.1 x.2 q a))) :=
    Primrec.list_map (Primrec.list_range.comp (Primrec.list_length.comp (letters_primrec.comp hd)))
      (Primrec.list_map (Primrec.list_range.comp (EncodedRoundObjectives.stateCount_primrec.comp
        (objective_primrec.comp (Primrec.fst.comp Primrec.fst))))
        (step_primrec.comp ((Primrec.fst.comp (Primrec.fst.comp Primrec.fst)).pair
          ((Primrec.snd.comp (Primrec.fst.comp Primrec.fst)).pair
            (Primrec.snd.pair (Primrec.snd.comp Primrec.fst))))).to₂).to₂
  exact (Primrec.fst.comp (Primrec.snd.comp ho)).pair
    (((Primrec.list_getD 0).comp (initial_primrec.comp hd) Primrec.snd).pair
      ((EncodedParityTables.priorities_primrec.comp (Primrec.snd.comp ho)).pair rows))
theorem components_primrec : Primrec components :=
  Primrec.list_map (Primrec.list_range.comp roots_primrec) component_primrec.to₂
theorem compile_primrec : Primrec compile := EncodedParityConjunction.compile_primrec.comp
  ((Primrec.list_length.comp letters_primrec).pair components_primrec)

end Characterisation.EncodedJointPhaseObjective
