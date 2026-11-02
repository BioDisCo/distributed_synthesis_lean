/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Automata.EncodedParityFamiliesCorrect
import DistributedSynthesis.Formalizations.Theorem.ThmParityBlockPasting

/-! # Streaming pairs of bounded priorities through the shared parity compiler

The finite input table remembers the latest pair of priorities. Its two priority
tables read the respective coordinates. All Boolean combination and parity
compilation is performed by `EncodedParityFamilies`; this module only proves
the numeric input-table and streaming interfaces.
-/

namespace DistributedSynthesis.PriorityPairMonitor

open Characterisation

def count (b₁ b₂ : Nat) : Nat := (b₁ + 1) * (b₂ + 1)

theorem count_pos (b₁ b₂ : Nat) : 0 < count b₁ b₂ := by
  unfold count
  positivity

def echo (b₁ b₂ : Nat) : EncodedParityTables.Data :=
  (count b₁ b₂ - 1, 0, [],
    (List.range (count b₁ b₂)).map (fun a => List.replicate (count b₁ b₂) a))

@[simp] theorem echo_size (b₁ b₂ : Nat) :
    EncodedParityTables.size (echo b₁ b₂) = count b₁ b₂ := by
  have := count_pos b₁ b₂
  simp only [echo, EncodedParityTables.size]
  omega

@[simp] theorem echo_rows (b₁ b₂ : Nat) :
    (EncodedParityTables.rows (echo b₁ b₂)).length = count b₁ b₂ := by
  simp [echo, EncodedParityTables.rows]

def leftPriorities (b₁ b₂ : Nat) : List Nat :=
  (List.range (count b₁ b₂)).map (fun a => a / (b₂ + 1))

def rightPriorities (b₁ b₂ : Nat) : List Nat :=
  (List.range (count b₁ b₂)).map (fun a => a % (b₂ + 1))

def data (b₁ b₂ : Nat) : EncodedParityFamilies.Data :=
  (echo b₁ b₂, [leftPriorities b₁ b₂, rightPriorities b₁ b₂],
    [[true, false], [false, true], [true, true]])

abbrev Alphabet (b₁ b₂ : Nat) := Fin (EncodedParityTables.rows (echo b₁ b₂)).length

/-- Out-of-range observations are reduced modulo the supplied finite range. -/
def letter (b₁ b₂ : Nat) (x : Nat × Nat) : Alphabet b₁ b₂ :=
  ⟨(x.1 * (b₂ + 1) + x.2) % count b₁ b₂,
    by rw [echo_rows]; exact Nat.mod_lt _ (count_pos b₁ b₂)⟩

theorem letter_val {b₁ b₂ : Nat} {x : Nat × Nat} (h₁ : x.1 ≤ b₁) (h₂ : x.2 ≤ b₂) :
    (letter b₁ b₂ x).val = x.1 * (b₂ + 1) + x.2 := by
  apply Nat.mod_eq_of_lt
  unfold count
  nlinarith

def automaton (b₁ b₂ : Nat) := EncodedParityFamilies.automaton (data b₁ b₂)

def Memory (b₁ b₂ : Nat) : Type := (automaton b₁ b₂).State

instance (b₁ b₂ : Nat) : Fintype (Memory b₁ b₂) :=
  inferInstanceAs (Fintype (Fin _))

instance (b₁ b₂ : Nat) : DecidableEq (Memory b₁ b₂) :=
  inferInstanceAs (DecidableEq (Fin _))

def initial (b₁ b₂ : Nat) : Memory b₁ b₂ := (automaton b₁ b₂).initial

def update (b₁ b₂ : Nat) (m : Memory b₁ b₂) (x : Nat × Nat) : Memory b₁ b₂ :=
  (automaton b₁ b₂).step m (letter b₁ b₂ x)

def priority (b₁ b₂ : Nat) (m : Memory b₁ b₂) (x : Nat × Nat) : Nat :=
  (automaton b₁ b₂).priority (update b₁ b₂ m x)

def bound (b₁ b₂ : Nat) : Nat := Finset.univ.sup (automaton b₁ b₂).priority

theorem priority_le (b₁ b₂ : Nat) (m : Memory b₁ b₂) (x : Nat × Nat) :
    priority b₁ b₂ m x ≤ bound b₁ b₂ := by
  exact Finset.le_sup (f := (automaton b₁ b₂).priority)
    (Finset.mem_univ (update b₁ b₂ m x))

def run (b₁ b₂ : Nat) (c₁ c₂ : Nat → Nat) : Nat → Memory b₁ b₂
  | 0 => initial b₁ b₂
  | n + 1 => update b₁ b₂ (run b₁ b₂ c₁ c₂ n) (c₁ n, c₂ n)

def combined (b₁ b₂ : Nat) (c₁ c₂ : Nat → Nat) : Nat → Nat :=
  fun n => priority b₁ b₂ (run b₁ b₂ c₁ c₂ n) (c₁ n, c₂ n)

private theorem condition_step (b₁ b₂ : Nat) (ps : List Nat)
    (q : (EncodedParityFamilies.condition (data b₁ b₂) ps).State) (a : Alphabet b₁ b₂) :
    ((EncodedParityFamilies.condition (data b₁ b₂) ps).step q a).val = a.val := by
  have ha : a.val < count b₁ b₂ := by simpa using a.isLt
  have hq : q.val < count b₁ b₂ := by simpa [data, EncodedParityFamilies.base] using q.isLt
  change EncodedParityTables.next (echo b₁ b₂) q.val a.val = a.val
  unfold EncodedParityTables.next
  rw [echo_size]
  change (((List.range (count b₁ b₂)).map
    (fun a => List.replicate (count b₁ b₂) a)).getD a.val []).getD q.val 0 % _ = _
  rw [List.getD_eq_getElem ((List.range (count b₁ b₂)).map
    (fun a => List.replicate (count b₁ b₂) a)) [] (n := a.val) (by simpa using ha)]
  simp only [List.getElem_map, List.getElem_range]
  rw [List.getD_replicate _ hq, Nat.mod_eq_of_lt ha]

private theorem condition_priority_succ (b₁ b₂ : Nat) (ps : List Nat)
    (word : OmegaWord (Alphabet b₁ b₂)) (n : Nat) :
    (EncodedParityFamilies.condition (data b₁ b₂) ps).priority
      ((EncodedParityFamilies.condition (data b₁ b₂) ps).run word (n + 1)) =
      ps.getD (word n).val 0 := by
  change ps.getD (((EncodedParityFamilies.condition (data b₁ b₂) ps).step _ (word n)).val) 0 = _
  rw [condition_step]

private theorem coordinates {b₁ b₂ : Nat} {x : Nat × Nat}
    (h₁ : x.1 ≤ b₁) (h₂ : x.2 ≤ b₂) :
    (leftPriorities b₁ b₂).getD (letter b₁ b₂ x).val 0 = x.1 ∧
    (rightPriorities b₁ b₂).getD (letter b₁ b₂ x).val 0 = x.2 := by
  have ha : (letter b₁ b₂ x).val < count b₁ b₂ := by
    simpa using (letter b₁ b₂ x).isLt
  have hx₂ : x.2 < b₂ + 1 := by omega
  have get (f : Nat → Nat) : ((List.range (count b₁ b₂)).map f).getD
      (letter b₁ b₂ x).val 0 = f (letter b₁ b₂ x).val := by
    rw [List.getD_eq_getElem ((List.range (count b₁ b₂)).map f) 0
      (n := (letter b₁ b₂ x).val) (by simpa using ha)]
    simp only [List.getElem_map, List.getElem_range]
  simp only [leftPriorities, rightPriorities, get]
  rw [letter_val h₁ h₂]
  constructor
  · simp [Nat.add_div, Nat.div_eq_of_lt hx₂, Nat.mod_eq_of_lt hx₂, h₂]
  · simp [Nat.add_mod, Nat.mod_eq_of_lt hx₂]

private theorem condition_accepts {b₁ b₂ : Nat} {c₁ c₂ : Nat → Nat}
    (h₁ : ∀ n, c₁ n ≤ b₁) (h₂ : ∀ n, c₂ n ≤ b₂) :
    let word := fun n => letter b₁ b₂ (c₁ n, c₂ n)
    ((EncodedParityFamilies.condition (data b₁ b₂) (leftPriorities b₁ b₂)).Accepts word ↔
        NatSeqMinEvenParity c₁) ∧
    ((EncodedParityFamilies.condition (data b₁ b₂) (rightPriorities b₁ b₂)).Accepts word ↔
        NatSeqMinEvenParity c₂) := by
  let word := fun n => letter b₁ b₂ (c₁ n, c₂ n)
  have one (ps : List Nat) (c : Nat → Nat)
      (hc : ∀ n, ps.getD (word n).val 0 = c n) :
      (EncodedParityFamilies.condition (data b₁ b₂) ps).Accepts word ↔ NatSeqMinEvenParity c := by
    let D := EncodedParityFamilies.condition (data b₁ b₂) ps
    change NatSeqMinEvenParity (fun n => D.priority (D.run word n)) ↔ _
    rw [← natSeqMinEvenParity_shift _ 1]
    have heq : (fun n => D.priority (D.run word (1 + n))) = c := by
      funext n
      rw [Nat.add_comm 1 n]
      exact (condition_priority_succ b₁ b₂ ps word n).trans (hc n)
    rw [heq]
  exact ⟨one _ _ (fun n => (coordinates (x := (c₁ n, c₂ n)) (h₁ n) (h₂ n)).1),
    one _ _ (fun n => (coordinates (x := (c₁ n, c₂ n)) (h₁ n) (h₂ n)).2)⟩

theorem combined_correct {b₁ b₂ : Nat} {c₁ c₂ : Nat → Nat}
    (h₁ : ∀ n, c₁ n ≤ b₁) (h₂ : ∀ n, c₂ n ≤ b₂) :
    NatSeqMinEvenParity (combined b₁ b₂ c₁ c₂) ↔
      NatSeqMinEvenParity c₁ ∨ NatSeqMinEvenParity c₂ := by
  classical
  let word := fun n => letter b₁ b₂ (c₁ n, c₂ n)
  have hr : ∀ n, run b₁ b₂ c₁ c₂ n = (automaton b₁ b₂).run word n := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => change (automaton b₁ b₂).step _ _ = _; rw [ih]; rfl
  have hp : combined b₁ b₂ c₁ c₂ = fun n =>
      (automaton b₁ b₂).priority ((automaton b₁ b₂).run word (n + 1)) := by
    funext n
    change (automaton b₁ b₂).priority ((automaton b₁ b₂).step _ _) = _
    rw [hr]
    rfl
  rw [hp]
  have hs := natSeqMinEvenParity_shift
    (fun n => (automaton b₁ b₂).priority ((automaton b₁ b₂).run word n)) 1
  rw [show (fun n => (automaton b₁ b₂).priority ((automaton b₁ b₂).run word (n + 1))) =
      (fun n => (automaton b₁ b₂).priority ((automaton b₁ b₂).run word (1 + n))) by
        funext n; rw [Nat.add_comm n 1], hs]
  change (automaton b₁ b₂).Accepts word ↔ _
  rw [automaton, EncodedParityFamilies.accepts_iff]
  obtain ⟨hl, hr⟩ := condition_accepts h₁ h₂
  change ([decide ((EncodedParityFamilies.condition (data b₁ b₂) (leftPriorities b₁ b₂)).Accepts word),
    decide ((EncodedParityFamilies.condition (data b₁ b₂) (rightPriorities b₁ b₂)).Accepts word)] ∈
    [[true,false],[false,true],[true,true]]) ↔ _
  by_cases hleft : NatSeqMinEvenParity c₁ <;> by_cases hright : NatSeqMinEvenParity c₂ <;>
    simp [word, hl, hr, hleft, hright]

-- Keep compiled numeric tables behind the finite-memory interface during elaboration.
attribute [irreducible] Memory

end DistributedSynthesis.PriorityPairMonitor
