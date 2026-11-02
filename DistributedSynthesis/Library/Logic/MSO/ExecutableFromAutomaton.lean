/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Logic.MSO.FromTreeAutomaton
import DistributedSynthesis.Library.Automata.TreeComputable
import DistributedSynthesis.Library.Computability.FiniteOrders
import Mathlib.Data.Fintype.Sort

/-! # Executable parity-tree-automaton to MSO translation

Finite input carriers are given computable orders (in particular, numeric finite
carriers satisfy this interface). Sorted enumeration replaces the semantic
translation's classical list choices. Run and parity semantics are unchanged.
-/
namespace DistributedSynthesis.MSO.Tree.Automaton.Ordered
open scoped DistributedSynthesis.FiniteOrders
private def enumeration (α : Type) [Fintype α] [LinearOrder α] : List α :=
  Finset.univ.sort (· ≤ ·)

@[simp] private theorem mem_enumeration {α : Type} [Fintype α] [LinearOrder α] (x : α) :
    x ∈ enumeration α := by simp [enumeration]

variable {Branch Alphabet : Type} {n m : Nat}
variable [Fintype Branch] [LinearOrder Branch] [Nonempty Branch]
variable [Fintype Alphabet] [LinearOrder Alphabet]
variable (A : RunParityTreeAutomaton.{0,0,0} Branch Alphabet) [LinearOrder A.State]
variable [∀ q a next, Decidable (A.delta q a next)] (stateVars : A.State → Fin m)

local instance : LinearOrder (Branch → A.State) := FiniteOrders.functionOrder

local instance (p : Nat) : Decidable (DetParityAutomaton.NatEven p) :=
  FiniteThreadSystem.Computable.natEvenDecidable p

def partitionFormula : Formula (language Branch Alphabet) 0 m := by
  exact .allNode (.anyOf ((enumeration _).map (fun q : A.State =>
    (Formula.mem 0 (stateVars q)).and (.allOf ((enumeration _).map (fun q' : A.State =>
      (Formula.mem 0 (stateVars q')).imp (.ofBool (decide (q' = q)))))))))

omit [Fintype Branch] [LinearOrder Branch] [Nonempty Branch] [Fintype Alphabet] [LinearOrder Alphabet] [∀ q a next, Decidable (A.delta q a next)] in
theorem partitionFormula_correct (tree : LabeledTree Branch Alphabet) (sets : Fin m → Set (TreeNode Branch)) :
    Realize tree (partitionFormula A stateVars) Fin.elim0 sets ↔
      ∀ node, ∃! q, node ∈ sets (stateVars q) := by
  classical
  simp [partitionFormula, Realize, Fin.snoc, ExistsUnique]


def stepFormula : Formula (language Branch Alphabet) 0 m := by
  exact .allNode (.anyOf ((enumeration _).map (fun q : A.State =>
    .anyOf ((enumeration _).map (fun a : Alphabet =>
      .anyOf ((enumeration _).map (fun next : Branch → A.State =>
        (Formula.ofBool (decide (A.delta q a next))).and
          ((Formula.mem 0 (stateVars q)).and ((label a 0).and
            (.allOf ((enumeration _).map (fun b : Branch =>
              .allNode ((successor b 0 1).imp (.mem 1 (stateVars (next b))))))))))))))))

omit [Nonempty Branch] in
theorem stepFormula_correct (tree : LabeledTree Branch Alphabet) (sets : Fin m → Set (TreeNode Branch)) :
    Realize tree (stepFormula A stateVars) Fin.elim0 sets ↔
      ∀ node, ∃ q a next, A.delta q a next ∧ node ∈ sets (stateVars q) ∧ tree node = a ∧
        ∀ b, node ++ [b] ∈ sets (stateVars (next b)) := by
  classical
  simp [stepFormula, Realize, Fin.snoc]

def runFormula : Formula (language Branch Alphabet) 0 m :=
  (partitionFormula A stateVars).and ((initialFormula A stateVars).and (stepFormula A stateVars))

omit [Nonempty Branch] in
theorem runFormula_correct (tree : LabeledTree Branch Alphabet) (sets : Fin m → Set (TreeNode Branch)) :
    Realize tree (runFormula A stateVars) Fin.elim0 sets ↔
      ∃ run, EncodesRun A stateVars sets run ∧ A.IsRun tree run := by
  unfold runFormula Realize
  simp only [Formula.realize_and]
  change (Realize tree (partitionFormula A stateVars) Fin.elim0 sets ∧
    Realize tree (initialFormula A stateVars) Fin.elim0 sets ∧
    Realize tree (stepFormula A stateVars) Fin.elim0 sets) ↔ _
  rw [partitionFormula_correct, initialFormula_correct, stepFormula_correct, partition_iff_exists_run]
  constructor
  · rintro ⟨⟨run,encodes⟩,initial,transitions⟩
    refine ⟨run,encodes,⟨(encodes [] A.initial).mp initial,?_⟩⟩
    intro node
    obtain ⟨q,a,next,legal,member,letter,children⟩ := transitions node
    have state := (encodes node q).mp member
    have values : (fun b => run (node ++ [b])) = next := funext (fun b => (encodes _ _).mp (children b))
    simpa only [state,letter,values] using legal
  · rintro ⟨run,encodes,initial,transitions⟩
    refine ⟨⟨run,encodes⟩,(encodes [] A.initial).mpr initial,?_⟩
    intro node
    exact ⟨run node,tree node,(fun b => run (node ++ [b])),transitions node,
      (encodes node _).mpr rfl,rfl,fun b => (encodes _ _).mpr rfl⟩
def priorityAt (p : Nat) (x : Fin n) : Formula (language Branch Alphabet) n m := by
  exact .anyOf ((enumeration _).map (fun q : A.State =>
    (Formula.ofBool (decide (A.priority q = p))).and (.mem x (stateVars q))))

omit [Fintype Branch] [LinearOrder Branch] [Nonempty Branch] [Fintype Alphabet] [LinearOrder Alphabet] [∀ q a next, Decidable (A.delta q a next)] in
theorem priorityAt_correct (tree : LabeledTree Branch Alphabet) (nodes : Fin n → TreeNode Branch)
    (sets : Fin m → Set (TreeNode Branch)) (run : TreeNode Branch → A.State)
    (encodes : EncodesRun A stateVars sets run) (p : Nat) (x : Fin n) :
    Realize tree (priorityAt A stateVars p x) nodes sets ↔ A.priority (run (nodes x)) = p := by
  classical
  unfold EncodesRun at encodes
  simp [priorityAt, Realize, encodes, eq_comm]

def cofinalFormula (X : Fin m) (p : Nat) : Formula (language Branch Alphabet) 0 m :=
  .allNode ((Formula.mem 0 X).imp
    (((Formula.mem 1 X).and ((ancestor 0 1).and (priorityAt A stateVars p 1))).exNode))

omit [Fintype Branch] [LinearOrder Branch] [Nonempty Branch] [Fintype Alphabet] [LinearOrder Alphabet] [∀ q a next, Decidable (A.delta q a next)] in
theorem cofinalFormula_correct (tree : LabeledTree Branch Alphabet)
    (sets : Fin m → Set (TreeNode Branch)) (run : TreeNode Branch → A.State)
    (encodes : EncodesRun A stateVars sets run) (X : Fin m) (p : Nat) :
    Realize tree (cofinalFormula A stateVars X p) Fin.elim0 sets ↔
      ∀ x, x ∈ sets X → ∃ y, y ∈ sets X ∧ x <+: y ∧ A.priority (run y) = p := by
  classical
  unfold EncodesRun at encodes
  simp [cofinalFormula, priorityAt, Realize, Fin.snoc, encodes, eq_comm]

omit [Fintype Branch] [LinearOrder Branch] [Nonempty Branch] [Fintype Alphabet] [LinearOrder Alphabet] [∀ q a next, Decidable (A.delta q a next)] in
theorem cofinalFormula_branch (tree : LabeledTree Branch Alphabet)
    (sets : Fin m → Set (TreeNode Branch)) (run : TreeNode Branch → A.State)
    (encodes : EncodesRun A stateVars sets run) (X : Fin m) (branch : Nat → Branch)
    (branchSet : sets X = Set.range (branchNode branch)) (p : Nat) :
    Realize tree (cofinalFormula A stateVars X p) Fin.elim0 sets ↔
      NatSeqSeenInfinitelyOften (fun k => A.priority (run (branchNode branch k))) p := by
  rw [cofinalFormula_correct A stateVars tree sets run encodes, branchSet]
  constructor
  · intro h k
    obtain ⟨_,⟨j,rfl⟩,ancestor,priority⟩ := h _ ⟨k,rfl⟩
    exact ⟨j,(branchNode_prefix_iff branch k j).mp ancestor,priority⟩
  · intro h x hx
    obtain ⟨k,rfl⟩ := hx
    obtain ⟨j,le,priority⟩ := h k
    exact ⟨_,⟨j,rfl⟩,(branchNode_prefix_iff branch k j).mpr le,priority⟩

def parityFormula (X : Fin m) : Formula (language Branch Alphabet) 0 m := by
  exact .anyOf ((enumeration _).map (fun q : A.State =>
    (Formula.ofBool (decide (DetParityAutomaton.NatEven (A.priority q)))).and
      ((cofinalFormula A stateVars X (A.priority q)).and
        (.allOf ((enumeration _).map (fun q' : A.State =>
          (Formula.ofBool (decide (A.priority q' < A.priority q))).imp
            (cofinalFormula A stateVars X (A.priority q')).not))))))

omit [Fintype Branch] [LinearOrder Branch] [Nonempty Branch] [Fintype Alphabet] [LinearOrder Alphabet] [∀ q a next, Decidable (A.delta q a next)] in
theorem parityFormula_branch (tree : LabeledTree Branch Alphabet)
    (sets : Fin m → Set (TreeNode Branch)) (run : TreeNode Branch → A.State)
    (encodes : EncodesRun A stateVars sets run) (X : Fin m) (branch : Nat → Branch)
    (branchSet : sets X = Set.range (branchNode branch)) :
    Realize tree (parityFormula A stateVars X) Fin.elim0 sets ↔
      NatSeqMinEvenParity (fun k => A.priority (run (branchNode branch k))) := by
  classical
  have raw : Realize tree (parityFormula A stateVars X) Fin.elim0 sets ↔
      ∃ q : A.State, DetParityAutomaton.NatEven (A.priority q) ∧
        Realize tree (cofinalFormula A stateVars X (A.priority q)) Fin.elim0 sets ∧
        ∀ q' : A.State, A.priority q' < A.priority q →
          ¬ Realize tree (cofinalFormula A stateVars X (A.priority q')) Fin.elim0 sets := by
    simp [parityFormula, Realize]
  rw [raw]
  simp only [cofinalFormula_branch A stateVars tree sets run encodes X branch branchSet]
  constructor
  · rintro ⟨q,even,seen,smaller⟩
    refine ⟨A.priority q,even,seen,?_⟩
    intro p recurring
    obtain ⟨k,_,eq⟩ := recurring 0
    dsimp at eq
    by_contra h
    have lt : A.priority (run (branchNode branch k)) < A.priority q := by omega
    apply smaller _ lt
    simpa only [eq] using recurring
  · rintro ⟨p,even,seen,minimum⟩
    obtain ⟨k,_,eq⟩ := seen 0
    dsimp at eq
    refine ⟨run (branchNode branch k),?_,?_,?_⟩
    · simpa only [eq] using even
    · simpa only [eq] using seen
    · intro q lt recurring
      have le := minimum (A.priority q) recurring
      omega

def branchParityFormula : Formula (language Branch Alphabet) 0 m :=
  .allSet ((branchFormula (Fin.last m)).imp
    (parityFormula A (fun q => (stateVars q).castSucc) (Fin.last m)))


omit [Fintype Branch] [LinearOrder Branch] [Fintype Alphabet] [LinearOrder Alphabet] [∀ q a next, Decidable (A.delta q a next)] in
theorem branchParityFormula_correct (tree : LabeledTree Branch Alphabet)
    (sets : Fin m → Set (TreeNode Branch)) (run : TreeNode Branch → A.State)
    (encodes : EncodesRun A stateVars sets run) :
    Realize tree (branchParityFormula A stateVars) Fin.elim0 sets ↔
      ∀ branch : Nat → Branch,
        NatSeqMinEvenParity (fun k => A.priority (run (branchNode branch k))) := by
  have extended (X : Set (TreeNode Branch)) :
      EncodesRun A (fun q => (stateVars q).castSucc) (Fin.snoc sets X) run := by
    intro node q
    simpa only [Fin.snoc_castSucc] using encodes node q
  change (∀ X : Set (TreeNode Branch),
    Realize tree (branchFormula (Fin.last m)) Fin.elim0 (Fin.snoc sets X) →
    Realize tree (parityFormula A (fun q => (stateVars q).castSucc) (Fin.last m))
      Fin.elim0 (Fin.snoc sets X)) ↔ _
  simp only [branchFormula_correct, Fin.snoc_last]
  constructor
  · intro h branch
    exact (parityFormula_branch A _ tree _ run (extended _) (Fin.last m) branch
      (by simp)).mp (h _ (isBranchSet_range branch))
  · intro h X branchSet
    obtain ⟨branch,rfl⟩ := (isBranchSet_iff X).mp branchSet
    exact (parityFormula_branch A _ tree _ run (extended _) (Fin.last m) branch
      (by simp)).mpr (h branch)

def acceptingRunFormula (stateVars : A.State → Fin m) :
    Formula (language Branch Alphabet) 0 m :=
  (runFormula A stateVars).and (branchParityFormula A stateVars)

theorem acceptingRunFormula_correct (stateVars : A.State → Fin m)
    (tree : LabeledTree Branch Alphabet) (sets : Fin m → Set (TreeNode Branch)) :
    Realize tree (acceptingRunFormula A stateVars) Fin.elim0 sets ↔
      ∃ run, EncodesRun A stateVars sets run ∧ A.IsAcceptingRun tree run := by
  unfold acceptingRunFormula Realize
  simp only [Formula.realize_and]
  change (Realize tree (runFormula A stateVars) Fin.elim0 sets ∧
    Realize tree (branchParityFormula A stateVars) Fin.elim0 sets) ↔ _
  rw [runFormula_correct]
  constructor
  · rintro ⟨⟨run,encodes,legal⟩,parity⟩
    exact ⟨run,encodes,legal,
      (branchParityFormula_correct A stateVars tree sets run encodes).mp parity⟩
  · rintro ⟨run,encodes,legal,parity⟩
    exact ⟨⟨run,encodes,legal⟩,
      (branchParityFormula_correct A stateVars tree sets run encodes).mpr parity⟩

/-- Computable state numbering using Mathlib's finite order isomorphism. -/
def stateNumber : A.State ≃ Fin (Fintype.card A.State) :=
  (monoEquivOfFin A.State rfl).toEquiv.symm

def ofAutomaton : Sentence (language Branch Alphabet) :=
  (acceptingRunFormula A (stateNumber A)).exAllSets

theorem ofAutomaton_correct (tree : LabeledTree Branch Alphabet) :
    Satisfies tree (ofAutomaton A) ↔ A.acceptsTree tree := by
  letI := treeStructure Branch Alphabet tree
  change Formula.Realize (Formula.exAllSets _) Fin.elim0 Fin.elim0 ↔ _
  rw [Formula.realize_exAllSets]
  change (∃ sets, Realize tree (acceptingRunFormula A (stateNumber A)) Fin.elim0 sets) ↔ _
  simp only [acceptingRunFormula_correct]
  constructor
  · rintro ⟨sets,run,_,accepting⟩
    exact ⟨run,accepting⟩
  · rintro ⟨run,accepting⟩
    refine ⟨fun i => {node | run node = (stateNumber A).symm i},run,?_,accepting⟩
    intro node q
    simp

end DistributedSynthesis.MSO.Tree.Automaton.Ordered
