/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Automata.EncodedParityFamilies

/-! Correctness of Boolean combinations on a common finite run. No priority
condition is evaluated on a contracted or sampled time sequence. -/
namespace Characterisation.EncodedParityFamilies
open DistributedSynthesis

attribute [local instance] Classical.propDecidable

variable (d : Data)
local notation "M" => EncodedMuller.semantic (muller d)

theorem common_run (ps : List Nat) (q : Fin (EncodedParityTables.size (base d)))
    (word : OmegaWord (Fin (EncodedParityTables.rows (base d)).length)) (t : Nat) :
    (M).runFrom q word t = (condition d ps).toMuller.runFrom q word t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    change (M).step ((M).runFrom q word t) (word t) =
      (condition d ps).toMuller.step ((condition d ps).toMuller.runFrom q word t) (word t)
    rw [ih]
    rfl

theorem common_inf (ps : List Nat)
    (word : OmegaWord (Fin (EncodedParityTables.rows (base d)).length)) :
    (M).InfStatesFrom (M).initial word =
      (condition d ps).toMuller.InfStatesFrom (condition d ps).initial word := by
  ext q
  change (∀ n, ∃ k, n ≤ k ∧ (M).runFrom (M).initial word k = q) ↔ _
  simp only [common_run d ps]
  rfl

/-- Arbitrary finite Boolean combinations of parity conditions are compiled
uniformly to the library's numeric parity format. -/
theorem accepts_iff
    (word : OmegaWord (Fin (EncodedParityTables.rows (base d)).length)) :
    (automaton d).Accepts word ↔
      (priorities d).map (fun ps => decide ((condition d ps).Accepts word)) ∈ profiles d := by
  classical
  rw [automaton,EncodedMuller.accepts_iff]
  change (M).AcceptsFrom (M).initial word ↔ _
  rw [(M).acceptsFrom_iff_infStateFinsetFrom_accepting]
  erw [EncodedMuller.accepting_encode,family_encode]
  have one (ps : List Nat) :
      passes ps (FiniteSubsets.encode ((M).infStateFinsetFrom (M).initial word)) =
        decide ((condition d ps).Accepts word) := by
    apply Bool.eq_iff_iff.mpr
    erw [passes_encode d ps,decide_eq_true_eq]
    erw [(M).coe_infStateFinsetFrom,common_inf d ps]
    exact DetParityAutomaton.toMuller_accepts_iff (condition d ps) word
  have profilesEq : profile d (FiniteSubsets.encode ((M).infStateFinsetFrom (M).initial word)) =
      (priorities d).map (fun ps => decide ((condition d ps).Accepts word)) := by
    apply List.map_congr_left
    intro ps _
    exact one ps
  exact iff_of_eq (congrArg (fun xs => xs ∈ profiles d) profilesEq)

/-- The two-priority implication profile is the adversary guard: either the
adversary priority condition fails or the objective priority condition holds. -/
def guardData (transition : EncodedParityTables.Data) (adversary objective : List Nat) : Data :=
  (transition,[adversary,objective],[[false,false],[false,true],[true,true]])

theorem guardData_primrec : Primrec (fun x : EncodedParityTables.Data × List Nat × List Nat =>
    guardData x.1 x.2.1 x.2.2) := Primrec.fst.pair
  ((Primrec.list_cons.comp (Primrec.fst.comp Primrec.snd)
    (Primrec.list_cons.comp (Primrec.snd.comp Primrec.snd) (Primrec.const []))).pair (Primrec.const _))

theorem accepts_guard_iff (transition : EncodedParityTables.Data) (adversary objective : List Nat)
    (word : OmegaWord (Fin (EncodedParityTables.rows transition).length)) :
    (automaton (guardData transition adversary objective)).Accepts word ↔
      (condition (guardData transition adversary objective) adversary).Accepts word →
        (condition (guardData transition adversary objective) objective).Accepts word := by
  classical
  rw [accepts_iff]
  change ([decide ((condition (guardData transition adversary objective) adversary).Accepts word),
    decide ((condition (guardData transition adversary objective) objective).Accepts word)] ∈
    [[false,false],[false,true],[true,true]]) ↔ _
  by_cases ha : (condition (guardData transition adversary objective) adversary).Accepts word <;>
    by_cases ho : (condition (guardData transition adversary objective) objective).Accepts word <;>
      simp [ha,ho]

/-- Every priority obligation on the common run must hold. -/
def conjunctionData (transition : EncodedParityTables.Data) (ps : List (List Nat)) : Data :=
  (transition,ps,[ps.map (fun _ => true)])

theorem conjunctionData_primrec : Primrec₂ conjunctionData := Primrec.fst.pair
  (Primrec.snd.pair (Primrec.list_cons.comp
    (Primrec.list_map Primrec.snd (Primrec.const true).to₂) (Primrec.const [])))

theorem accepts_conjunction_iff (transition : EncodedParityTables.Data) (ps : List (List Nat))
    (word : OmegaWord (Fin (EncodedParityTables.rows transition).length)) :
    (automaton (conjunctionData transition ps)).Accepts word ↔
      ∀ p ∈ ps, (condition (conjunctionData transition ps) p).Accepts word := by
  classical
  rw [accepts_iff]
  change (ps.map (fun p => decide ((condition (conjunctionData transition ps) p).Accepts word)) ∈
    [ps.map (fun _ => true)]) ↔ _
  rw [List.mem_singleton,List.map_eq_map_iff]
  simp only [decide_eq_true_eq]

end Characterisation.EncodedParityFamilies
