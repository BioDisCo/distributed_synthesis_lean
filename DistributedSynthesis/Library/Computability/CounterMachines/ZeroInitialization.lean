/-
Lean adaptation and development: the paper authors listed in AUTHORS.md
at the repository root. The credits below refer to upstream formalizations,
not authorship of this Lean implementation; see the CounterMachines README.md.
-/

/-
SPDX-License-Identifier: MPL-2.0
Port of Andrej Dudenhefner's MM2_HALTING_to_MM2_ZERO_HALTING.v, from the
Coq library of undecidability proofs (TU Dortmund affiliation in upstream).
Upstream revision: 11c41e0637f0c5219ad1c4c92d11609b7e072c31.
Upstream path: theories/MinskyMachines/Reductions/MM2_HALTING_to_MM2_ZERO_HALTING.v
See README.md and LICENSE-MPL-2.0 in this directory.
-/
import DistributedSynthesis.Library.Computability.CounterMachines.Halting

/-! # Eliminating the two initial counter values

Prepend `a` increments of counter A and `b` increments of counter B. Relocate
every positive original address by `a+b`, but leave address zero unchanged.
The latter is essential: zero is a halting address, not part of the prefix.
The construction and proof follow the pinned Rocq reduction. Computability is
proved separately in `ZeroInitializationComputable`.
-/
namespace DistributedSynthesis.CounterMachine.MM2.ZeroInitialization

def shiftAddress (k i : Nat) : Nat := if i = 0 then 0 else i + k

def shiftInstr (k : Nat) : Instr → Instr
  | .incA => .incA
  | .incB => .incB
  | .decA j => .decA (shiftAddress k j)
  | .decB j => .decB (shiftAddress k j)

def shiftState (k : Nat) (x : Cfg) : Cfg := (shiftAddress k x.1, x.2)

def compile (P : Program) (a b : Nat) : Program :=
  List.replicate a .incA ++ List.replicate b .incB ++ P.map (shiftInstr (a+b))

theorem compile_length (P : Program) (a b : Nat) :
    (compile P a b).length = a + b + P.length := by simp [compile, Nat.add_assoc]

@[simp] theorem shiftAddress_zero (k : Nat) : shiftAddress k 0 = 0 := by
  simp [shiftAddress]

theorem shiftAddress_of_ne_zero (k : Nat) {i : Nat} (hi : i ≠ 0) :
    shiftAddress k i = i+k := by simp [shiftAddress, hi]

@[simp] theorem shiftAddress_succ (k i : Nat) :
    shiftAddress k (i+1) = i+k+1 := by simp [shiftAddress]; omega

theorem atomNext_shift (k : Nat) (ρ : Instr) (x : Cfg) (hi : x.1 ≠ 0) :
    atomNext (shiftInstr k ρ) (shiftState k x) = shiftState k (atomNext ρ x) := by
  rcases x with ⟨i,a,b⟩
  cases ρ <;> simp [atomNext, shiftInstr, shiftState, shiftAddress_of_ne_zero k hi]
  all_goals split <;> simp_all [shiftState, shiftAddress, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

/-- Lookup after relocation is exactly lookup before relocation, including
missing addresses zero and addresses beyond the end of the original program. -/
theorem lookup_shift (P : Program) (a b i : Nat) :
    lookup (compile P a b) (shiftAddress (a+b) i) =
      (lookup P i).map (shiftInstr (a+b)) := by
  by_cases hi : i = 0
  · subst i; simp [lookup]
  · have ha : ¬ i+(a+b)-1 < a+b := by omega
    have hn : i+(a+b)-1-(a+b) = i-1 := by omega
    simp only [shiftAddress_of_ne_zero (a+b) hi, lookup, if_neg hi, compile]
    rw [if_neg (by omega)]
    simp only [List.getElem?_append, List.length_append, List.length_replicate,
      if_neg ha, hn, List.getElem?_map]

theorem step_shift {P : Program} {a b : Nat} {x y : Cfg}
    (h : Step P x y) :
    Step (compile P a b) (shiftState (a+b) x) (shiftState (a+b) y) := by
  obtain ⟨ρ, hl, ha⟩ := h
  refine ⟨shiftInstr (a+b) ρ, ?_, ?_⟩
  · simpa [shiftState, hl] using lookup_shift P a b x.1
  · rw [atom_iff] at ha ⊢
    rw [ha, atomNext_shift (a+b) ρ x (lookup_some_pos hl)]

/-- No extra transition is possible from a relocated source configuration. -/
theorem step_from_shift {P : Program} {a b : Nat} {x y : Cfg}
    (h : Step (compile P a b) (shiftState (a+b) x) y) :
    ∃ z, Step P x z ∧ y = shiftState (a+b) z := by
  obtain ⟨ρ, hl, ha⟩ := h
  change lookup (compile P a b) (shiftAddress (a+b) x.1) = some ρ at hl
  rw [lookup_shift] at hl
  cases hs : lookup P x.1 with
  | none => simp [hs] at hl
  | some τ =>
    have he : shiftInstr (a+b) τ = ρ := by simpa [hs] using hl
    subst ρ
    refine ⟨atomNext τ x, ⟨τ, hs, (atom_iff _ _ _).mpr rfl⟩, ?_⟩
    exact ((atom_iff _ _ _).mp ha).trans
      (atomNext_shift (a+b) τ x (lookup_some_pos hs))

theorem reaches_shift {P : Program} {a b : Nat} {x y : Cfg}
    (h : Reaches P x y) :
    Reaches (compile P a b) (shiftState (a+b) x) (shiftState (a+b) y) := by
  induction h with
  | refl => exact .refl
  | tail _ hs ih => exact ih.tail (step_shift hs)

theorem reaches_from_shift {P : Program} {a b : Nat} {x y : Cfg}
    (h : Reaches (compile P a b) (shiftState (a+b) x) y) :
    ∃ z, Reaches P x z ∧ y = shiftState (a+b) z := by
  induction h with
  | refl => exact ⟨x, .refl, rfl⟩
  | tail _ hs ih =>
    obtain ⟨z, hz, rfl⟩ := ih
    obtain ⟨w, hw, he⟩ := step_from_shift hs
    exact ⟨w, hz.tail hw, he⟩

theorem stops_shift (P : Program) (a b : Nat) (x : Cfg) :
    Stops (compile P a b) (shiftState (a+b) x) ↔ Stops P x := by
  simp only [stops_iff, shiftState, lookup_shift, Option.map_eq_none_iff]

theorem terminates_shift (P : Program) (a b : Nat) (x : Cfg) :
    Terminates (compile P a b) (shiftState (a+b) x) ↔ Terminates P x := by
  constructor
  · rintro ⟨y, hy, hs⟩
    obtain ⟨z, hz, rfl⟩ := reaches_from_shift hy
    exact ⟨z, hz, (stops_shift P a b z).mp hs⟩
  · rintro ⟨y, hy, hs⟩
    exact ⟨shiftState (a+b) y, reaches_shift hy, (stops_shift P a b y).mpr hs⟩

theorem lookup_initA (P : Program) (a b n : Nat) (hn : n < a) :
    lookup (compile P a b) (1+n) = some .incA := by
  simp [lookup, compile, List.getElem?_append, hn, show n < a+b by omega]

theorem lookup_initB (P : Program) (a b n : Nat) (hn : n < b) :
    lookup (compile P a b) (1+a+n) = some .incB := by
  have he : 1+a+n-1 = a+n := by omega
  simp [lookup, compile, he, List.getElem?_append, hn, show a+n < a+b by omega]

theorem initA (P : Program) (a b n : Nat) (hn : n ≤ a) :
    Reaches (compile P a b) (1,(0,0)) (1+n,(n,0)) := by
  induction n with
  | zero => exact .refl
  | succ n ih =>
    apply (ih (by omega)).tail
    refine ⟨.incA, lookup_initA P a b n (by omega), ?_⟩
    exact Atom.incA (1+n) n 0

theorem initB (P : Program) (a b n : Nat) (hn : n ≤ b) :
    Reaches (compile P a b) (1+a,(a,0)) (1+a+n,(a,n)) := by
  induction n with
  | zero => exact .refl
  | succ n ih =>
    apply (ih (by omega)).tail
    refine ⟨.incB, lookup_initB P a b n (by omega), ?_⟩
    exact Atom.incB (1+a+n) a n

theorem initializes (P : Program) (a b : Nat) :
    Reaches (compile P a b) (1,(0,0)) (shiftState (a+b) (1,(a,b))) := by
  simpa [shiftState, shiftAddress, Nat.add_assoc] using
    (initA P a b a le_rfl).trans (initB P a b b le_rfl)

/-- Exact zero-initialization reduction, with no program well-formedness
or positive-initial-counter premise. -/
theorem compile_correct (P : Program) (a b : Nat) :
    ZeroHalts (compile P a b) ↔ Halts (P,a,b) :=
  (terminates_iff_of_reaches (initializes P a b)).trans (terminates_shift P a b (1,(a,b)))

end DistributedSynthesis.CounterMachine.MM2.ZeroInitialization
