/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Logic.MSO.NumericAtoms
import DistributedSynthesis.Library.Automata.EncodedRunTreeCorrect
import DistributedSynthesis.Library.Logic.MSO.ExecutableRecognition

/-! # Atomic numeric automata and the existing MSO semantics -/
namespace DistributedSynthesis.MSO.Tree.NumericAtoms
open NumericValuations

variable (x : Input)

abbrev Alphabet := ValuationLabel (Fin ((shape x).1 + 1)) (shape x).2.1 (shape x).2.2
abbrev Direction := Fin (branches x)

noncomputable def view : RunParityTreeAutomaton (Direction x) (Alphabet x) :=
  (EncodedRunTree.source (rawData x)).comap (number (shape x))

theorem delta_iff (q : Fin 2) (a : Alphabet x) (v : Direction x → Fin 2) :
    (view x).delta q a v ↔ condition x q.val (equiv (shape x) a).val (FiniteFunctionCoding.encode v) := by
  change (_, _, _) ∈ EncodedRunTree.enumerate (branches x) 2 (count (shape x)) (condition x) ↔ _
  rw [EncodedRunTree.mem_enumerate]
  have hv : FiniteFunctionCoding.encode v ∈ FiniteFunctionCoding.codes (branches x) 2 :=
    (FiniteCodeNumbering.mem_unique _ _).mpr (FiniteSearch.ofFn_mem_tables v)
  simp only [number_val, q.isLt, (equiv (shape x) a).isLt, true_and]
  exact ⟨And.right, fun h => ⟨hv, h⟩⟩

theorem zeroVector_eq {b : Nat} : zeroVector b = FiniteFunctionCoding.encode (fun _ : Fin b => (0 : Fin 2)) :=
  FiniteSearch.tabulate_eq_ofFn _ _ (fun _ => rfl)

theorem encode_zero_iff {b : Nat} (v : Fin b → Fin 2) :
    FiniteFunctionCoding.encode v = zeroVector b ↔ ∀ i, v i = 0 := by
  rw [zeroVector_eq]
  exact FiniteFunctionCoding.encode_injective.eq_iff.trans funext_iff

theorem encode_edge_iff {b : Nat} (v : Fin b → Fin 2) (mark : Bool) (dir : Fin b) :
    FiniteFunctionCoding.encode v = edgeVector b (if mark then 1 else 0) dir.val ↔
      ∀ i, v i = finTwoEquiv.symm (mark && decide (i = dir)) := by
  have heq : edgeVector b (if mark then 1 else 0) dir.val =
      FiniteFunctionCoding.encode (fun i : Fin b => finTwoEquiv.symm (mark && decide (i = dir))) := by
    apply FiniteSearch.tabulate_eq_ofFn
    intro i
    cases mark <;> by_cases h : i = dir <;> simp [finTwoEquiv, h, Fin.val_inj]
  rw [heq]
  exact FiniteFunctionCoding.encode_injective.eq_iff.trans funext_iff

theorem local_accepts_iff (htag : tag x < 4) (tree : LabeledTree (Direction x) (Alphabet x)) :
    (view x).acceptsTree tree ↔ ∀ n, localCondition x (equiv (shape x) (tree n)).val := by
  constructor
  · rintro ⟨run, ⟨_, step⟩, _⟩ n
    have h := (delta_iff x (run n) (tree n) _).mp (step n)
    rw [condition, if_pos htag] at h
    exact h.1
  · intro h
    refine ⟨fun _ => (0 : Fin 2), ⟨?_, ?_⟩, fun _ => ?_⟩
    · apply Fin.ext
      change 0 = initial x % 2
      simp [initial, show tag x ≠ 4 by omega, show tag x ≠ 7 by omega]
    · intro n
      apply (delta_iff x 0 (tree n) _).mpr
      rw [condition, if_pos htag]
      exact ⟨h n, zeroVector_eq.symm⟩
    · change NatSeqMinEvenParity (fun _ => (if tag x = 7 then [0,1] else [0,0]).getD 0 0)
      rw [if_neg (show tag x ≠ 7 by omega)]
      exact ⟨0, ⟨0, rfl⟩, fun n => ⟨n, le_rfl, rfl⟩, fun _ _ => Nat.zero_le _⟩

variable [Inhabited (Direction x)]

theorem compile_accepts_iff (tree : LabeledTree (Direction x) (Alphabet x)) :
    (EncodedProjectedTree.automaton (compile x)).acceptsTree (number (shape x) ∘ tree) ↔
      (view x).acceptsTree tree := by
  letI : Inhabited (EncodedRunTree.Direction (rawData x)) := inferInstanceAs (Inhabited (Direction x))
  exact EncodedRunTree.compile_correct (rawData x) (number (shape x) ∘ tree)

end DistributedSynthesis.MSO.Tree.NumericAtoms
