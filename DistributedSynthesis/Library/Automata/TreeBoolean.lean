/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Automata.TreeComplement
import DistributedSynthesis.Library.Automata.TreeLocal
import DistributedSynthesis.Formalizations.Theorem.ThmMullerToDPA
import DistributedSynthesis.Formalizations.Theorem.ThmParityBlockPasting

/-! # Boolean operations on parity tree languages

Intersection uses the existing Muller-to-parity word construction to combine
the two parity conditions. Taking the minimum of the two priorities would not
implement conjunction. Union and implication then use tree complementation.
-/
namespace DistributedSynthesis.TreeBoolean

variable {Branch Alphabet : Type*}
variable (A B : RunParityTreeAutomaton Branch Alphabet)

private def left : DetParityAutomaton (A.State × B.State) where
  State := A.State
  stateFinite := A.stateFinite
  initial := A.initial
  step _ letter := letter.1
  priority := A.priority

private def right : DetParityAutomaton (A.State × B.State) where
  State := B.State
  stateFinite := B.stateFinite
  initial := B.initial
  step _ letter := letter.2
  priority := B.priority

noncomputable def pairMonitor : DetParityAutomaton (A.State × B.State) :=
  (DetMullerAutomaton.LAR.eventAutomaton_toDPACompilation
    (A := (left A B).toMuller.inter (right A B).toMuller)).dpa

theorem pairMonitor_accepts_iff (word : OmegaWord (A.State × B.State)) :
    (pairMonitor A B).Accepts word ↔
      NatSeqMinEvenParity (fun n => A.priority (word n).1) ∧
      NatSeqMinEvenParity (fun n => B.priority (word n).2) := by
  rw [pairMonitor, DetMullerAutomaton.LAR.eventAutomaton_toDPACompilation.correct,
    DetMullerAutomaton.inter_accepts_iff,
    DetParityAutomaton.toMuller_accepts_iff, DetParityAutomaton.toMuller_accepts_iff]
  have l : (left A B).Accepts word ↔ NatSeqMinEvenParity (fun n => A.priority (word n).1) := by
    change NatSeqMinEvenParity (fun n => (left A B).priority ((left A B).run word n)) ↔ _
    rw [← natSeqMinEvenParity_shift _ 1]
    simp only [Nat.add_comm 1, DetParityAutomaton.run, DetParityAutomaton.runFrom, left]
  have r : (right A B).Accepts word ↔ NatSeqMinEvenParity (fun n => B.priority (word n).2) := by
    change NatSeqMinEvenParity (fun n => (right A B).priority ((right A B).run word n)) ↔ _
    rw [← natSeqMinEvenParity_shift _ 1]
    simp only [Nat.add_comm 1, DetParityAutomaton.run, DetParityAutomaton.runFrom, right]
  exact and_congr l r

variable [Fintype Branch]

noncomputable def monitor : DeterministicBlockMonitor Branch (A.State × B.State) := by
  classical
  exact WordTreeMonitor.monitor ((pairMonitor A B).comap Prod.fst)

theorem monitor_winning_iff (labels : LabeledTree Branch (A.State × B.State)) :
    (monitor A B).WinningTree labels ↔
      (∀ branch, NatSeqMinEvenParity (fun n => A.priority (labels (branchNode branch n)).1)) ∧
      (∀ branch, NatSeqMinEvenParity (fun n => B.priority (labels (branchNode branch n)).2)) := by
  classical
  rw [monitor, WordTreeMonitor.winning_iff]
  simp only [DetParityAutomaton.comap_accepts_iff, pairMonitor_accepts_iff,
    WordTreeMonitor.word, OmegaWord.map, Function.comp_apply, forall_and]

/-- Synchronous product with the existing finite parity monitor. -/
noncomputable def inter : RunParityTreeAutomaton Branch Alphabet where
  State := (A.State × B.State) × (pairMonitor A B).State
  stateFinite := inferInstance
  initial := ((A.initial, B.initial), (pairMonitor A B).initial)
  delta q a next :=
    A.delta q.1.1 a (fun b => (next b).1.1) ∧
    B.delta q.1.2 a (fun b => (next b).1.2) ∧
    ∀ b, (next b).2 = (pairMonitor A B).step q.2 q.1
  priority q := (pairMonitor A B).priority q.2

theorem inter_accepts_iff (tree : LabeledTree Branch Alphabet) :
    (inter A B).acceptsTree tree ↔ A.acceptsTree tree ∧ B.acceptsTree tree := by
  classical
  constructor
  · rintro ⟨run, ⟨initial, transition⟩, parity⟩
    let labels := fun node => (run node).1
    have memory : (monitor A B).toRunAutomaton.acceptsTree labels :=
      ⟨fun node => (run node).2, ⟨congrArg Prod.snd initial, fun node => (transition node).2.2⟩, parity⟩
    have branches := (monitor_winning_iff A B labels).mp
      ((DeterministicBlockMonitor.acceptsTree_iff_winningTree _ _).mp memory)
    exact ⟨⟨fun node => (run node).1.1,
      ⟨congrArg (fun q => q.1.1) initial, fun node => (transition node).1⟩, branches.1⟩,
      ⟨fun node => (run node).1.2,
      ⟨congrArg (fun q => q.1.2) initial, fun node => (transition node).2.1⟩, branches.2⟩⟩
  · rintro ⟨⟨runA, ⟨initA, stepA⟩, parityA⟩, ⟨runB, ⟨initB, stepB⟩, parityB⟩⟩
    let labels := fun node => (runA node, runB node)
    let memory := (monitor A B).control labels
    have memoryRun := (monitor A B).isRun_control labels
    have winning := (monitor_winning_iff A B labels).mpr ⟨parityA, parityB⟩
    refine ⟨fun node => ((runA node, runB node), memory node), ⟨?_, ?_⟩, winning⟩
    · exact Prod.ext (Prod.ext initA initB) memoryRun.1
    · intro node
      exact ⟨stepA node, stepB node, memoryRun.2 node⟩

variable [Nonempty Branch] [Fintype Alphabet]

noncomputable def union : RunParityTreeAutomaton Branch Alphabet :=
  TreeComplement.automaton (inter (TreeComplement.automaton A) (TreeComplement.automaton B))

theorem union_accepts_iff (tree : LabeledTree Branch Alphabet) :
    (union A B).acceptsTree tree ↔ A.acceptsTree tree ∨ B.acceptsTree tree := by
  classical
  by_cases h : A.acceptsTree tree <;>
    simp [union, TreeComplement.accepts_iff, inter_accepts_iff, h]

/-- Finite language union, choosing one automaton for the whole input tree. -/
noncomputable def finiteUnion : List (RunParityTreeAutomaton Branch Alphabet) →
    RunParityTreeAutomaton Branch Alphabet
  | [] => RunParityTreeAutomaton.localTest (fun _ => False)
  | A :: rest => union A (finiteUnion rest)

theorem finiteUnion_accepts_iff (automata : List (RunParityTreeAutomaton Branch Alphabet))
    (tree : LabeledTree Branch Alphabet) :
    (finiteUnion automata).acceptsTree tree ↔ ∃ A ∈ automata, A.acceptsTree tree := by
  induction automata with
  | nil => simp [finiteUnion, RunParityTreeAutomaton.localTest_accepts_iff]
  | cons A rest ih => simp [finiteUnion, union_accepts_iff, ih]

end DistributedSynthesis.TreeBoolean
