/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Automata.TreeComplement
import DistributedSynthesis.Library.Automata.ParityPairComputable
import DistributedSynthesis.Library.Automata.TreeSingleton
import DistributedSynthesis.Library.Automata.RunTreeNonemptiness

/-! # Executable finite data for parity tree automata

This wrapper adds state equality and transition deciders to the existing
run-based automaton. It retains its semantics and finite-state representation.
All constructors below are executable definitions, including complementation.
-/
namespace DistributedSynthesis

structure TreeAutomatonData (Branch Alphabet : Type*) where
  toAutomaton : RunParityTreeAutomaton.{_,_,0} Branch Alphabet
  stateDecidableEq : DecidableEq toAutomaton.State
  deltaDecidable : ∀ q a next, Decidable (toAutomaton.delta q a next)

attribute [instance] TreeAutomatonData.stateDecidableEq TreeAutomatonData.deltaDecidable

namespace TreeAutomatonData
variable {Branch Alphabet Label : Type*}

abbrev Accepts (A : TreeAutomatonData Branch Alphabet) := A.toAutomaton.acceptsTree

def comap (A : TreeAutomatonData Branch Label) (f : Alphabet → Label) :
    TreeAutomatonData Branch Alphabet where
  toAutomaton := A.toAutomaton.comap f
  stateDecidableEq := A.stateDecidableEq
  deltaDecidable q a next := A.deltaDecidable q (f a) next

def project [Fintype Alphabet] [DecidableEq Label] (A : TreeAutomatonData Branch Alphabet)
    (f : Alphabet → Label) : TreeAutomatonData Branch Label where
  toAutomaton := A.toAutomaton.project f
  stateDecidableEq := A.stateDecidableEq
  deltaDecidable := inferInstance

variable [Fintype Branch] [DecidableEq Branch]

/-- The rejecting-policy thread system, using the supplied transition test. -/
def complementThreads (A : TreeAutomatonData Branch Alphabet) :
    FiniteThreadSystem ((Alphabet × TreeComplement.Policy A.toAutomaton) × Branch) where
  State := Option A.toAutomaton.State
  stateFinite := inferInstance
  initial := some A.toAutomaton.initial
  Resolution := Branch → A.toAutomaton.State
  step q letter next := match q with
    | none => none
    | some q => if A.toAutomaton.delta q letter.1.1 next ∧ letter.1.2 q next = letter.2
        then some (next letter.2) else none
  priority q := match q with
    | none => 0
    | some q => A.toAutomaton.priority q + 1

omit [Fintype Branch] in
theorem complementThreads_eq (A : TreeAutomatonData Branch Alphabet) :
    complementThreads A = TreeComplement.threads A.toAutomaton := by
  unfold complementThreads TreeComplement.threads
  congr 1
  · funext q letter next
    cases q <;> simp
  · funext q
    cases q <;> rfl

instance complementResolutionFintype (A : TreeAutomatonData Branch Alphabet) :
    Fintype (complementThreads A).Resolution :=
  inferInstanceAs (Fintype (Branch → A.toAutomaton.State))

instance complementThreadStateDecidableEq (A : TreeAutomatonData Branch Alphabet) :
    DecidableEq (complementThreads A).State :=
  inferInstanceAs (DecidableEq (Option A.toAutomaton.State))

variable [Fintype Alphabet] [DecidableEq Alphabet]

def complementDPA (A : TreeAutomatonData Branch Alphabet) :=
  FiniteThreadSystem.Computable.universalDPA (complementThreads A)

instance complementStateDecidableEq (A : TreeAutomatonData Branch Alphabet) :
    DecidableEq (complementDPA A).State :=
  FiniteThreadSystem.Computable.universalStateDecidableEq (complementThreads A)

def complementAnnotated (A : TreeAutomatonData Branch Alphabet) :
    TreeAutomatonData Branch (Alphabet × TreeComplement.Policy A.toAutomaton) where
  toAutomaton := (WordTreeMonitor.monitor (complementDPA A)).toRunAutomaton
  stateDecidableEq := complementStateDecidableEq A
  deltaDecidable q a next := by
    letI : DecidableEq (complementDPA A).State := complementStateDecidableEq A
    change Decidable (∀ b, next b = (complementDPA A).step q (a,b))
    exact @Fintype.decidableForallFintype Branch _
      (fun b => complementStateDecidableEq A (next b) ((complementDPA A).step q (a,b))) _

def complement (A : TreeAutomatonData Branch Alphabet) : TreeAutomatonData Branch Alphabet :=
  (complementAnnotated A).project Prod.fst

variable [Nonempty Branch]

theorem complement_correct (A : TreeAutomatonData Branch Alphabet) (tree : LabeledTree Branch Alphabet) :
    (complement A).Accepts tree ↔ ¬ A.Accepts tree := by
  change ((complementAnnotated A).toAutomaton.project Prod.fst).acceptsTree tree ↔ _
  rw [RunParityTreeAutomaton.project_fst_acceptsTree_iff, TreeComplement.rejects_iff_exists_policy]
  apply exists_congr
  intro policy
  change (WordTreeMonitor.monitor (complementDPA A)).toRunAutomaton.acceptsTree _ ↔ _
  rw [DeterministicBlockMonitor.acceptsTree_iff_winningTree, WordTreeMonitor.winning_iff]
  simp only [complementDPA, FiniteThreadSystem.Computable.universalDPA_correct]
  rw [complementThreads_eq]
  exact TreeComplement.universal_threads_iff A.toAutomaton tree policy

/-- A computable parity monitor for the synchronous product's two state streams. -/
def pairDPA (A B : TreeAutomatonData Branch Alphabet) :=
  ParityPairComputable.automaton A.toAutomaton.priority B.toAutomaton.priority

instance pairStateDecidableEq (A B : TreeAutomatonData Branch Alphabet) :
    DecidableEq (pairDPA A B).State :=
  ParityPairComputable.stateDecidableEq A.toAutomaton.priority B.toAutomaton.priority

def pairMonitor (A B : TreeAutomatonData Branch Alphabet) :=
  WordTreeMonitor.monitor ((pairDPA A B).comap (Prod.fst :
    (A.toAutomaton.State × B.toAutomaton.State) × Branch → _))

omit [DecidableEq Branch] [Fintype Alphabet] [DecidableEq Alphabet] [Nonempty Branch] in
theorem pairMonitor_correct (A B : TreeAutomatonData Branch Alphabet)
    (labels : LabeledTree Branch (A.toAutomaton.State × B.toAutomaton.State)) :
    (pairMonitor A B).WinningTree labels ↔
      (∀ branch, NatSeqMinEvenParity (fun n => A.toAutomaton.priority (labels (branchNode branch n)).1)) ∧
      (∀ branch, NatSeqMinEvenParity (fun n => B.toAutomaton.priority (labels (branchNode branch n)).2)) := by
  rw [pairMonitor, WordTreeMonitor.winning_iff]
  simp only [DetParityAutomaton.comap_accepts_iff, pairDPA, ParityPairComputable.accepts_iff,
    WordTreeMonitor.word, OmegaWord.map, Function.comp_apply, forall_and]

def inter (A B : TreeAutomatonData Branch Alphabet) : TreeAutomatonData Branch Alphabet where
  toAutomaton := {
    State := (A.toAutomaton.State × B.toAutomaton.State) × (pairDPA A B).State
    stateFinite := inferInstance
    initial := ((A.toAutomaton.initial,B.toAutomaton.initial),(pairDPA A B).initial)
    delta q a next := A.toAutomaton.delta q.1.1 a (fun b => (next b).1.1) ∧
      B.toAutomaton.delta q.1.2 a (fun b => (next b).1.2) ∧
      ∀ b, (next b).2 = (pairDPA A B).step q.2 q.1
    priority q := (pairDPA A B).priority q.2 }
  stateDecidableEq := inferInstance
  deltaDecidable _ _ _ := inferInstance

omit [DecidableEq Branch] [Fintype Alphabet] [DecidableEq Alphabet] [Nonempty Branch] in
theorem inter_correct (A B : TreeAutomatonData Branch Alphabet) (tree : LabeledTree Branch Alphabet) :
    (inter A B).Accepts tree ↔ A.Accepts tree ∧ B.Accepts tree := by
  constructor
  · rintro ⟨run,⟨initial,transition⟩,parity⟩
    let labels := fun node => (run node).1
    have memory : (pairMonitor A B).toRunAutomaton.acceptsTree labels :=
      ⟨fun node => (run node).2,⟨congrArg Prod.snd initial,fun node => (transition node).2.2⟩,parity⟩
    have branches := (pairMonitor_correct A B labels).mp
      ((DeterministicBlockMonitor.acceptsTree_iff_winningTree _ _).mp memory)
    exact ⟨⟨fun node => (run node).1.1,
      ⟨congrArg (fun q => q.1.1) initial,fun node => (transition node).1⟩,branches.1⟩,
      ⟨fun node => (run node).1.2,
      ⟨congrArg (fun q => q.1.2) initial,fun node => (transition node).2.1⟩,branches.2⟩⟩
  · rintro ⟨⟨runA,⟨initA,stepA⟩,parityA⟩,⟨runB,⟨initB,stepB⟩,parityB⟩⟩
    let labels := fun node => (runA node,runB node)
    let memory := (pairMonitor A B).control labels
    have memoryRun := (pairMonitor A B).isRun_control labels
    have winning := (pairMonitor_correct A B labels).mpr ⟨parityA,parityB⟩
    refine ⟨fun node => ((runA node,runB node),memory node),⟨?_,?_⟩,winning⟩
    · exact Prod.ext (Prod.ext initA initB) memoryRun.1
    · intro node
      exact ⟨stepA node,stepB node,memoryRun.2 node⟩

def union (A B : TreeAutomatonData Branch Alphabet) : TreeAutomatonData Branch Alphabet :=
  (A.complement.inter B.complement).complement

theorem union_correct (A B : TreeAutomatonData Branch Alphabet) (tree : LabeledTree Branch Alphabet) :
    (union A B).Accepts tree ↔ A.Accepts tree ∨ B.Accepts tree := by
  simp only [union,complement_correct,inter_correct]
  tauto

/-- The existing finite-policy/nonemptiness search, with no semantic oracle. -/
def nonemptyDecidable [Inhabited Branch] (A : TreeAutomatonData Branch Alphabet) :
    Decidable (∃ tree, A.Accepts tree) := RunParityTreeAutomaton.nonemptyDecidable A.toAutomaton

end TreeAutomatonData
end DistributedSynthesis
