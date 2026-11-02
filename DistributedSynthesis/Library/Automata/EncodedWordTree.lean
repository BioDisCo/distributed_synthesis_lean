/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Automata.EncodedTreeNonemptiness
import DistributedSynthesis.Library.Automata.EncodedParityTables
import DistributedSynthesis.Library.Automata.WordTreeMonitor
import DistributedSynthesis.Library.Computability.PrimrecFunProp

/-! # Numeric word-to-tree monitors

A word letter is a node label paired with the next direction. Tabulation uses
the existing state-major tree-table layout and letter-major word-table layout.
-/
namespace DistributedSynthesis.EncodedWordTree

abbrev Input := Nat × Nat × EncodedParityTables.Data

def compile (x : Input) : EncodedTreeNonemptiness.Data :=
  (x.2.2.1, x.2.1, x.1,
    (List.range (EncodedParityTables.size x.2.2 * x.2.1 * x.1)).map
      (fun i => EncodedParityTables.next x.2.2 (i / (x.2.1 * x.1)) (i % (x.2.1 * x.1))),
    EncodedParityTables.priorities x.2.2, EncodedParityTables.initial x.2.2)

attribute [local fun_prop] EncodedParityTables.size_primrec EncodedParityTables.next_primrec
  EncodedParityTables.priorities_primrec EncodedParityTables.initial_primrec

theorem compile_primrec : Primrec compile := by
  unfold compile
  fun_prop

variable (B L : Nat) (d : EncodedParityTables.Data)

/-- Read paired letters directly from the same numeric table, even if rows are omitted. -/
def wordAutomaton : DetParityAutomaton (Fin L × Fin B) where
  State := Fin (EncodedParityTables.size d)
  stateFinite := inferInstance
  initial := ⟨EncodedParityTables.initial d % EncodedParityTables.size d, Nat.mod_lt _ (Nat.succ_pos _)⟩
  step q a := ⟨EncodedParityTables.next d q.val (a.1.val * B + a.2.val), Nat.mod_lt _ (Nat.succ_pos _)⟩
  priority q := EncodedParityTables.priority d q.val

theorem step_eq (q : Fin (EncodedParityTables.size d)) (l : Fin L) (b : Fin B) :
    (EncodedTreeNonemptiness.monitor (compile (B, L, d))).step q l b =
      (wordAutomaton B L d).step q (l, b) := by
  apply Fin.ext
  let j := l.val * B + b.val
  have hj : j < L * B := by
    dsimp [j]
    calc
      l.val * B + b.val < l.val * B + B := Nat.add_lt_add_left b.isLt _
      _ = (l.val + 1) * B := by ring
      _ ≤ L * B := Nat.mul_le_mul_right B l.isLt
  have index_eq : (q.val * L + l.val) * B + b.val = j + L * B * q.val := by
    dsimp [j]
    ring
  have bound : (q.val * L + l.val) * B + b.val < EncodedParityTables.size d * L * B := by
    rw [index_eq]
    calc
      j + L * B * q.val < L * B + L * B * q.val := Nat.add_lt_add_right hj _
      _ = (q.val + 1) * L * B := by ring
      _ ≤ EncodedParityTables.size d * L * B :=
        Nat.mul_le_mul_right B (Nat.mul_le_mul_right L q.isLt)
  change ((List.range (EncodedParityTables.size d * L * B)).map _).getD
    ((q.val * L + l.val) * B + b.val) 0 % EncodedParityTables.size d = _
  rw [List.getD_eq_getElem _ _ (by simpa using bound)]
  simp only [List.getElem_map, List.getElem_range]
  rw [index_eq, Nat.add_mul_div_left _ _ (by omega : 0 < L * B),
    Nat.div_eq_of_lt hj, Nat.zero_add, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hj]
  exact Nat.mod_eq_of_lt (Nat.mod_lt _ (Nat.succ_pos _))

theorem monitor_eq : EncodedTreeNonemptiness.monitor (compile (B, L, d)) =
    WordTreeMonitor.monitor (wordAutomaton B L d) := by
  unfold EncodedTreeNonemptiness.monitor compile WordTreeMonitor.monitor wordAutomaton
  congr 1
  funext q l b
  exact step_eq B L d q l b

theorem accepts_iff (tree : LabeledTree (Fin B) (Fin L)) :
    (EncodedTreeNonemptiness.monitor (compile (B, L, d))).toRunAutomaton.acceptsTree tree ↔
      ∀ branch, (wordAutomaton B L d).Accepts (WordTreeMonitor.word tree branch) := by
  rw [monitor_eq, DeterministicBlockMonitor.acceptsTree_iff_winningTree]
  exact WordTreeMonitor.winning_iff (wordAutomaton B L d) tree

end DistributedSynthesis.EncodedWordTree
