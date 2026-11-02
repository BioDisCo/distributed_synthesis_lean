/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.ThreadCompilation
import DistributedSynthesis.Library.Distributed.NoDirectJournal

/-! # Executable journal checkers and finite labels

Each boundary state (or handoff set) selects one compiled universal-thread
monitor. Their disjoint union retains that index during every transition.
All output labels are enumerated as finite response tables.
-/

namespace DistributedSynthesis.JournalCheckers
open DetParityAutomaton
set_option synthInstance.maxSize 1024


variable {In₁ In₂ Out₁ Out₂ : Type}
variable [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
variable [DecidableEq In₁] [DecidableEq In₂]
variable (A : DetParityAutomaton.{0, 0} (RoundRecord In₁ In₂ Graph Out₁ Out₂))
variable [DecidableEq A.State]

local instance (b : A.State) : DecidableEq (A.leftBlockMonitor b).State :=
  inferInstanceAs (DecidableEq (A.State × A.State))

local instance (b : A.State) : DecidableEq (A.rightBlockMonitor b).State :=
  inferInstanceAs (DecidableEq (A.State × A.State))

local instance (T : Finset (ChainThread A)) : DecidableEq (chainSetMonitor A T).State :=
  inferInstanceAs (DecidableEq (Option (Option (ChainThread A))))

/-- Enumerate all response tables, including both reversal orientations. -/
@[reducible] def labelFintype : Fintype (GlobalJournalLabel A) := by
  unfold GlobalJournalLabel NarrowedBlockLabel RevLeftBlockLabel RevRightBlockLabel
  infer_instance

@[reducible] def chainLabelFintype :
    Fintype (ChainLabel In₁ In₂ Out₁ Out₂ (A.State × A.State)) := by
  unfold ChainLabel RevLeftBlockLabel RevRightBlockLabel
  infer_instance

/-- Finite disjoint union of a family of deterministic monitors. -/
def family {Index Branch Label : Type} [Fintype Index]
    [Fintype Branch] [Fintype Label] (initialIndex : Index)
    (monitors : Index → DeterministicBlockMonitor.{0, 0, 0} Branch Label) :
    DeterministicBlockMonitor Branch Label where
  branchFinite := inferInstance
  alphabetFinite := inferInstance
  State := Σ i, (monitors i).State
  stateFinite := by
    letI : ∀ i, Fintype (monitors i).State := fun i => (monitors i).stateFinite
    infer_instance
  initial := ⟨initialIndex, (monitors initialIndex).initial⟩
  step := fun q label branch => ⟨q.1, (monitors q.1).step q.2 label branch⟩
  priority := fun q => (monitors q.1).priority q.2

@[reducible] def familyDecidableEq {Index Branch Label : Type} [Fintype Index]
    [Fintype Branch] [Fintype Label] [DecidableEq Index] (i : Index)
    (monitors : Index → DeterministicBlockMonitor.{0, 0, 0} Branch Label)
    (ds : ∀ b, DecidableEq (monitors b).State) : DecidableEq (family i monitors).State :=
  letI := ds
  inferInstanceAs (DecidableEq (Σ b, (monitors b).State))

theorem family_winningTree_iff {Index Branch Label : Type} [Fintype Index]
    [Fintype Branch] [Fintype Label] (i b : Index)
    (monitors : Index → DeterministicBlockMonitor.{0, 0, 0} Branch Label)
    (tree : LabeledTree Branch Label) :
    ({ family i monitors with initial := ⟨b, (monitors b).initial⟩ } :
      DeterministicBlockMonitor Branch Label).WinningTree tree ↔
      (monitors b).WinningTree tree := by
  have hc : ∀ node : List Branch, ∀ tree : LabeledTree Branch Label,
      ∀ q : (monitors b).State,
      (family i monitors).controlIn tree ⟨b, q⟩ node =
        ⟨b, (monitors b).controlIn tree q node⟩ := by
    intro node
    induction node with
    | nil => intros; rfl
    | cons d rest ih =>
      intro tree q
      exact ih (fun node => tree (d :: node)) ((monitors b).step q (tree []) d)
  have hp : ∀ node,
      ({ family i monitors with initial := ⟨b, (monitors b).initial⟩ } :
        DeterministicBlockMonitor Branch Label).priority
        (({ family i monitors with initial := ⟨b, (monitors b).initial⟩ } :
          DeterministicBlockMonitor Branch Label).control tree node) =
        (monitors b).priority ((monitors b).control tree node) := by
    intro node
    unfold DeterministicBlockMonitor.control
    rw [DeterministicBlockMonitor.controlIn_update_initial, hc]
    rfl
  constructor
  · intro h branch
    exact Eq.mp (congrArg NatSeqMinEvenParity
      (funext fun n => hp (branchNode branch n))) (h branch)
  · intro h branch
    exact Eq.mpr (congrArg NatSeqMinEvenParity
      (funext fun n => hp (branchNode branch n))) (h branch)

def leftMonitor : DeterministicBlockMonitor In₂
    (NarrowedBlockLabel In₁ In₂ Out₁ Out₂ (A.State × A.State)) :=
  letI := ThreadCompilation.labelFintype (A.leftBlockMonitor A.initial)
  family A.initial (fun b => ThreadCompilation.monitor (A.leftBlockMonitor b))

def rightMonitor : DeterministicBlockMonitor In₁
    (NarrowedBlockLabel In₂ In₁ Out₂ Out₁ (A.State × A.State)) :=
  letI := ThreadCompilation.labelFintype (A.rightBlockMonitor A.initial)
  family A.initial (fun b => ThreadCompilation.monitor (A.rightBlockMonitor b))

theorem leftMonitor_eq : leftMonitor A = leftCheckerMonitor A := by
  unfold leftMonitor
  simp only [ThreadCompilation.monitor_eq]
  unfold family leftCheckerMonitor
  congr 1
  exact Subsingleton.elim _ _

theorem rightMonitor_eq : rightMonitor A = rightCheckerMonitor A := by
  unfold rightMonitor
  simp only [ThreadCompilation.monitor_eq]
  unfold family rightCheckerMonitor
  congr 1
  exact Subsingleton.elim _ _

def left : LeftThreadChecker A where
  monitor := leftMonitor A
  start := fun b => ⟨b, (ThreadCompilation.monitor (A.leftBlockMonitor b)).initial⟩
  winning_iff := by
    intro b tree
    exact (family_winningTree_iff A.initial b _ tree).trans
      (ThreadCompilation.winningTree_iff (A.leftBlockMonitor b) tree)

def right : RightThreadChecker A where
  monitor := rightMonitor A
  start := fun b => ⟨b, (ThreadCompilation.monitor (A.rightBlockMonitor b)).initial⟩
  winning_iff := by
    intro b tree
    exact (family_winningTree_iff A.initial b _ tree).trans
      (ThreadCompilation.winningTree_iff (A.rightBlockMonitor b) tree)

variable [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]

def chainSet (T : Finset (ChainThread A)) :
    DeterministicBlockMonitor (In₂ ⊕ In₁)
      (ChainLabel In₁ In₂ Out₁ Out₂ (A.State × A.State)) where
  branchFinite := inferInstance
  alphabetFinite := chainLabelFintype A
  State := (ThreadCompilation.monitor (chainSetMonitor A T)).State
  stateFinite := (ThreadCompilation.monitor (chainSetMonitor A T)).stateFinite
  initial := (ThreadCompilation.monitor (chainSetMonitor A T)).initial
  step := fun q label branch =>
    (ThreadCompilation.monitor (chainSetMonitor A T)).step q (packChainSetLabel label) branch
  priority := (ThreadCompilation.monitor (chainSetMonitor A T)).priority

omit [Inhabited In₁] [Inhabited In₂] in
theorem chainSet_eq (T : Finset (ChainThread A)) :
    chainSet A T = chainSetPerMonitor A T := by
  unfold chainSet
  rw [ThreadCompilation.monitor_eq]
  unfold chainSetPerMonitor
  congr 1

def chainMonitor :=
  letI := chainLabelFintype A
  family ∅ (chainSet A)

omit [Inhabited In₁] [Inhabited In₂] in
theorem chainMonitor_eq : chainMonitor A = chainCheckerMonitor A := by
  unfold chainMonitor
  have h := funext (chainSet_eq A)
  rw [h]
  unfold family chainCheckerMonitor
  congr 1

def chain : ChainThreadChecker (A := A) where
  monitor := chainMonitor A
  start := fun T => ⟨T, (chainSet A T).initial⟩
  winning_iff := by
    intro T tree
    apply (family_winningTree_iff ∅ T (chainSet A) tree).trans
    rw [chainSet_eq]
    exact chainSetPerMonitor_winningTree_iff (A := A) T tree

/-- Complete objective-to-journal construction, with no checker parameters. -/
def compile :=
  letI := labelFintype A
  JournalCompilation.compile A (left A) (right A) (chain A)

@[reducible] def stateDecidableEq : DecidableEq (compile A).State := by
  letI : Fintype (NarrowedBlockLabel In₁ In₂ Out₁ Out₂ (A.State × A.State)) :=
    ThreadCompilation.labelFintype (A.leftBlockMonitor A.initial)
  letI : Fintype (NarrowedBlockLabel In₂ In₁ Out₂ Out₁ (A.State × A.State)) :=
    ThreadCompilation.labelFintype (A.rightBlockMonitor A.initial)
  letI := chainLabelFintype A
  letI : DecidableEq (left A).monitor.State :=
    familyDecidableEq A.initial _ (fun b =>
      ThreadCompilation.stateDecidableEq (A.leftBlockMonitor b))
  letI : DecidableEq (right A).monitor.State :=
    familyDecidableEq A.initial _ (fun b =>
      ThreadCompilation.stateDecidableEq (A.rightBlockMonitor b))
  letI : DecidableEq (chain A).monitor.State :=
    familyDecidableEq ∅ (chainSet A) (fun T =>
      ThreadCompilation.stateDecidableEq (chainSetMonitor A T))
  letI : DecidableEq ((left A).monitor.State × Finset (A.State × A.State)) := inferInstance
  letI : DecidableEq ((right A).monitor.State × Finset (A.State × A.State)) := inferInstance
  letI : DecidableEq ((chain A).monitor.State × Finset (ChainThread A)) := inferInstance
  change DecidableEq (GlobalJournalState A (left A) (right A) (chain A))
  unfold GlobalJournalState
  infer_instance

/-- Compile the reversal-forgiving companion without inspecting realizability. -/
def noDirect := compile A.reversalForgiving

theorem realizable_iff_nonempty : NoDirectJournal.Realizable A ↔
    ∃ tree, (noDirect A).toRunAutomaton.acceptsTree tree :=
  NoDirectJournal.realizable_iff_nonempty_of_checkers A _ _ _

end DistributedSynthesis.JournalCheckers
