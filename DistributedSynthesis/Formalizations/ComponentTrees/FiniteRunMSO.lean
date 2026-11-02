/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Logic.MSO.AutomatonParity
import DistributedSynthesis.Library.Logic.MSO.Executable
import DistributedSynthesis.Library.Computability.FiniteOrders
import Mathlib.Data.Fintype.Sort

/-! The MSO formulas in `lem:tree-mso`, once the finite letter/edge tables
have been computed. This module proves the logical encoding only; connecting
these tables to concrete component trees is proved in `ModelEquivalence`.
Input letters are the existing tree labeling, hence already partition nodes.
The H sets partition exactly the selected branch, including no off-branch nodes.
-/
namespace Characterisation.ComponentTrees.FiniteRunMSO
open DistributedSynthesis DistributedSynthesis.MSO DistributedSynthesis.MSO.Tree
open scoped DistributedSynthesis.FiniteOrders
set_option maxHeartbeats 1800000
set_option linter.unusedSectionVars false
variable {Branch Alphabet Edge : Type}
variable [Fintype Branch] [Fintype Alphabet] [Fintype Edge]
variable [LinearOrder Branch] [LinearOrder Alphabet] [LinearOrder Edge]

private def enumeration (α : Type) [Fintype α] [LinearOrder α] : List α :=
  Finset.univ.sort (· ≤ ·)

@[simp] private theorem mem_enumeration {α : Type} [Fintype α] [LinearOrder α] (x : α) :
    x ∈ enumeration α := by simp [enumeration]

local instance (p : Nat) : Decidable (DetParityAutomaton.NatEven p) :=
  FiniteThreadSystem.Computable.natEvenDecidable p

/-- Finite tables for the local tests stated in the manuscript. Padding is
represented by a letter with no allowed edge. -/
structure Tables (Branch Alphabet Edge : Type) where
  initial : Edge
  root : Alphabet → Bool
  child : Alphabet → Branch → Alphabet → Bool
  allowed : Alphabet → Edge → Bool
  step : Alphabet → Branch → Edge → Edge → Bool
  priority : Alphabet → Edge → Nat

variable (T : Tables Branch Alphabet Edge)

def Local (tree : LabeledTree Branch Alphabet) : Prop :=
  T.root (tree []) = true ∧ ∀ node b, T.child (tree node) b (tree (node ++ [b])) = true

def Run (tree : LabeledTree Branch Alphabet) (branch : Nat → Branch) (edges : Nat → Edge) : Prop :=
  edges 0 = T.initial ∧
    (∀ n, T.allowed (tree (branchNode branch n)) (edges n) = true) ∧
    ∀ n, T.step (tree (branchNode branch n)) (branch n) (edges n) (edges (n+1)) = true

def Accepting (tree : LabeledTree Branch Alphabet) : Prop :=
  Local T tree ∧ ∀ branch edges, Run T tree branch edges →
    NatSeqMinEvenParity (fun n => T.priority (tree (branchNode branch n)) (edges n))

def localFormula : Sentence (language Branch Alphabet) := by
  exact ((Formula.anyOf ((enumeration _).map (fun a : Alphabet =>
    (root 0).and ((label a 0).and (.ofBool (T.root a)))))).exNode).and
    (.allNode (.allNode (.allOf ((enumeration _).map (fun b : Branch =>
      (successor b 0 1).imp (.anyOf ((enumeration _).map (fun a : Alphabet =>
        .anyOf ((enumeration _).map (fun c : Alphabet =>
          (label a 0).and ((label c 1).and (.ofBool (T.child a b c)))))))))))))

theorem localFormula_correct (tree : LabeledTree Branch Alphabet) :
    Satisfies tree (localFormula T) ↔ Local T tree := by
  classical
  simp [Tree.Satisfies, localFormula, Realize, Fin.snoc, Local]
  intro _
  constructor
  · intro step node b
    exact step node (node ++ [b]) b rfl
  · intro step node child b eq
    exact eq ▸ step node b

variable {m : Nat} (P : Fin m) (H : Edge → Fin m)

def partitionFormula : Formula (language Branch Alphabet) 0 m := by
  let unique : Formula (language Branch Alphabet) 1 m := .anyOf ((enumeration _).map (fun e : Edge =>
    (Formula.mem 0 (H e)).and (.allOf ((enumeration _).map (fun f : Edge =>
      (Formula.mem 0 (H f)).imp (.ofBool (decide (f = e))))))))
  let inside : Formula (language Branch Alphabet) 1 m := .allOf ((enumeration _).map (fun e : Edge =>
    (Formula.mem 0 (H e)).imp (.mem 0 P)))
  exact (Formula.allNode ((Formula.mem 0 P).iff unique)).and (.allNode inside)

theorem partitionFormula_correct (tree : LabeledTree Branch Alphabet)
    (sets : Fin m → Set (TreeNode Branch)) :
    Realize tree (partitionFormula (Edge:=Edge) P H) Fin.elim0 sets ↔
      (∀ node, node ∈ sets P → ∃! e, node ∈ sets (H e)) ∧
      (∀ node e, node ∈ sets (H e) → node ∈ sets P) := by
  classical
  simp [partitionFormula, Realize, Fin.snoc, ExistsUnique]
  intro inside
  constructor
  · intro unique node mem
    exact (unique node).mp mem
  · intro unique node
    exact ⟨unique node, fun ⟨e, mem, _⟩ => inside node e mem⟩

def edgeFormula : Formula (language Branch Alphabet) 0 m := by
  let allowed : Formula (language Branch Alphabet) 1 m := .allOf ((enumeration _).map (fun e : Edge =>
    (Formula.mem 0 (H e)).imp (.anyOf ((enumeration _).map (fun a : Alphabet =>
      (label a 0).and (.ofBool (T.allowed a e)))))))
  exact (((root 0).and (.mem 0 (H T.initial))).exNode).and (.allNode allowed)

def stepFormula : Formula (language Branch Alphabet) 0 m := by
  exact .allNode (.allNode (.allOf ((enumeration _).map (fun b : Branch =>
    ((successor b 0 1).and ((Formula.mem 0 P).and (.mem 1 P))).imp
      (.anyOf ((enumeration _).map (fun a : Alphabet =>
        .anyOf ((enumeration _).map (fun e : Edge =>
          .anyOf ((enumeration _).map (fun f : Edge =>
            (label a 0).and ((Formula.mem 0 (H e)).and
              ((Formula.mem 1 (H f)).and (.ofBool (T.step a b e f)))))))))))))))

def runFormula : Formula (language Branch Alphabet) 0 m :=
  (branchFormula P).and ((partitionFormula P H).and ((edgeFormula T H).and (stepFormula T P H)))

def SetRun (tree : LabeledTree Branch Alphabet) (sets : Fin m → Set (TreeNode Branch)) : Prop :=
  IsBranchSet (sets P) ∧
  ((∀ node, node ∈ sets P → ∃! e, node ∈ sets (H e)) ∧
   (∀ node e, node ∈ sets (H e) → node ∈ sets P)) ∧
  ([] ∈ sets (H T.initial) ∧ ∀ node e, node ∈ sets (H e) → T.allowed (tree node) e = true) ∧
  ∀ node b, node ∈ sets P → node ++ [b] ∈ sets P →
    ∃ e f, node ∈ sets (H e) ∧ node ++ [b] ∈ sets (H f) ∧ T.step (tree node) b e f = true

theorem runFormula_correct (tree : LabeledTree Branch Alphabet)
    (sets : Fin m → Set (TreeNode Branch)) :
    Realize tree (runFormula T P H) Fin.elim0 sets ↔ SetRun T P H tree sets := by
  classical
  have edge : Realize tree (edgeFormula T H) Fin.elim0 sets ↔
      [] ∈ sets (H T.initial) ∧ ∀ node e, node ∈ sets (H e) → T.allowed (tree node) e = true := by
    simp [edgeFormula, Realize, Fin.snoc]
  have step : Realize tree (stepFormula T P H) Fin.elim0 sets ↔
      ∀ node b, node ∈ sets P → node ++ [b] ∈ sets P →
        ∃ e f, node ∈ sets (H e) ∧ node ++ [b] ∈ sets (H f) ∧ T.step (tree node) b e f = true := by
    simp [stepFormula, Realize, Fin.snoc]
    constructor
    · intro h node b
      exact h node (node ++ [b]) b rfl
    · intro h node child b eq
      subst child
      exact h node b
  unfold runFormula Realize
  simp only [Formula.realize_and]
  change (Realize tree (branchFormula P) Fin.elim0 sets ∧
    Realize tree (partitionFormula P H) Fin.elim0 sets ∧
    Realize tree (edgeFormula T H) Fin.elim0 sets ∧
    Realize tree (stepFormula T P H) Fin.elim0 sets) ↔ _
  rw [branchFormula_correct, partitionFormula_correct, edge, step]
  rfl

/-- Exactly one edge at each node of the branch, and none elsewhere. -/
def Encodes (sets : Fin m → Set (TreeNode Branch))
    (branch : Nat → Branch) (edges : Nat → Edge) : Prop :=
  sets P = Set.range (branchNode branch) ∧
    ∀ node e, node ∈ sets (H e) ↔ ∃ n, node = branchNode branch n ∧ edges n = e

variable [Nonempty Branch]

theorem setRun_iff (tree : LabeledTree Branch Alphabet) (sets : Fin m → Set (TreeNode Branch)) :
    SetRun T P H tree sets ↔ ∃ branch edges, Encodes P H sets branch edges ∧ Run T tree branch edges := by
  classical
  constructor
  · rintro ⟨path, partition, initial, steps⟩
    obtain ⟨branch, branchSet⟩ := (isBranchSet_iff (sets P)).mp path
    have member n : branchNode branch n ∈ sets P := branchSet ▸ ⟨n,rfl⟩
    choose edges chosen unique using fun n => partition.1 (branchNode branch n) (member n)
    have encodes : ∀ node e, node ∈ sets (H e) ↔ ∃ n, node = branchNode branch n ∧ edges n = e := by
      intro node e
      constructor
      · intro mem
        obtain ⟨n,rfl⟩ := branchSet ▸ partition.2 node e mem
        exact ⟨n,rfl,(unique n e mem).symm⟩
      · rintro ⟨n,rfl,rfl⟩
        exact chosen n
    refine ⟨branch, edges, ⟨branchSet, encodes⟩, ?_, fun n => initial.2 _ _ (chosen n), ?_⟩
    · exact (unique 0 T.initial initial.1).symm
    · intro n
      obtain ⟨e,f,he,hf,step⟩ := steps (branchNode branch n) (branch n) (member n) (member (n+1))
      rw [unique n e he, unique (n+1) f hf] at step
      exact step
  · rintro ⟨branch, edges, ⟨branchSet, encodes⟩, initial, allowed, steps⟩
    have member n : branchNode branch n ∈ sets P := branchSet ▸ ⟨n,rfl⟩
    have chosen n : branchNode branch n ∈ sets (H (edges n)) := (encodes _ _).mpr ⟨n,rfl,rfl⟩
    have unique n e (mem : branchNode branch n ∈ sets (H e)) : e = edges n := by
      obtain ⟨k,eq,state⟩ := (encodes _ _).mp mem
      have lengths := congrArg List.length eq
      simp only [TreeNonemptiness.branch_length] at lengths
      subst k
      exact state.symm
    refine ⟨branchSet ▸ isBranchSet_range branch, ⟨?_,?_⟩, ⟨?_,?_⟩, ?_⟩
    · intro node mem
      obtain ⟨n,rfl⟩ := branchSet ▸ mem
      exact ⟨edges n, chosen n, unique n⟩
    · intro node e mem
      obtain ⟨n,rfl,_⟩ := (encodes _ _).mp mem
      exact member n
    · rw [← initial]
      exact chosen 0
    · intro node e mem
      obtain ⟨n,rfl,rfl⟩ := (encodes _ _).mp mem
      exact allowed n
    · intro node b mem next
      obtain ⟨n,rfl⟩ := branchSet ▸ mem
      obtain ⟨k,eq⟩ := branchSet ▸ next
      have length := congrArg List.length eq
      simp only [TreeNonemptiness.branch_length,List.length_append,List.length_singleton] at length
      subst k
      have direction : branch n = b := by
        exact List.singleton_injective (List.append_cancel_left eq)
      subst b
      exact ⟨edges n, edges (n+1), chosen n, chosen (n+1), steps n⟩


def priorityFormula {n : Nat} (c : Nat) (x : Fin n) : Formula (language Branch Alphabet) n m := by
  exact .anyOf ((enumeration _).map (fun a : Alphabet =>
    .anyOf ((enumeration _).map (fun e : Edge =>
      (label a x).and ((Formula.mem x (H e)).and (.ofBool (decide (T.priority a e = c))))))))

theorem priorityFormula_correct {n : Nat} (c : Nat) (x : Fin n)
    (tree : LabeledTree Branch Alphabet) (nodes : Fin n → TreeNode Branch)
    (sets : Fin m → Set (TreeNode Branch)) :
    Realize tree (priorityFormula T H c x) nodes sets ↔
      ∃ e, nodes x ∈ sets (H e) ∧ T.priority (tree (nodes x)) e = c := by
  classical
  simp [priorityFormula, Realize]

def infinitelyOftenFormula (c : Nat) : Formula (language Branch Alphabet) 0 m :=
  .allNode ((Formula.mem 0 P).imp
    (((Formula.mem 1 P).and ((ancestor 0 1).and
      ((Formula.equal 0 1).not.and (priorityFormula T H c 1)))).exNode))

theorem infinitelyOftenFormula_correct (c : Nat) (tree : LabeledTree Branch Alphabet)
    (sets : Fin m → Set (TreeNode Branch)) :
    Realize tree (infinitelyOftenFormula T P H c) Fin.elim0 sets ↔
      ∀ x, x ∈ sets P → ∃ y, y ∈ sets P ∧ x <+: y ∧ x ≠ y ∧
        ∃ e, y ∈ sets (H e) ∧ T.priority (tree y) e = c := by
  classical
  simp [infinitelyOftenFormula, priorityFormula, Realize, Fin.snoc]

theorem infinitelyOftenFormula_branch (c : Nat) (tree : LabeledTree Branch Alphabet)
    (sets : Fin m → Set (TreeNode Branch)) (branch : Nat → Branch) (edges : Nat → Edge)
    (encodes : Encodes P H sets branch edges) :
    Realize tree (infinitelyOftenFormula T P H c) Fin.elim0 sets ↔
      NatSeqSeenInfinitelyOften (fun n => T.priority (tree (branchNode branch n)) (edges n)) c := by
  rw [infinitelyOftenFormula_correct T P H c tree sets]
  constructor
  · intro infinitely k
    have member : branchNode branch k ∈ sets P := encodes.1 ▸ ⟨k,rfl⟩
    obtain ⟨y,hy,ancestor,_,e,he,priority⟩ := infinitely _ member
    obtain ⟨j,rfl⟩ := encodes.1 ▸ hy
    obtain ⟨n,eq,state⟩ := (encodes.2 _ e).mp he
    have length := congrArg List.length eq
    simp only [TreeNonemptiness.branch_length] at length
    subst n
    exact ⟨j,(branchNode_prefix_iff branch k j).mp ancestor,by simpa only [state] using priority⟩
  · intro infinitely x hx
    obtain ⟨k,rfl⟩ := encodes.1 ▸ hx
    obtain ⟨j,le,priority⟩ := infinitely (k+1)
    refine ⟨branchNode branch j, encodes.1 ▸ ⟨j,rfl⟩,
      (branchNode_prefix_iff branch k j).mpr (by omega), ?_, edges j,
      (encodes.2 _ _).mpr ⟨j,rfl,rfl⟩, priority⟩
    intro eq
    have length := congrArg List.length eq
    simp only [TreeNonemptiness.branch_length] at length
    omega

def parityFormula : Formula (language Branch Alphabet) 0 m := by
  exact .anyOf ((enumeration _).map (fun ae : Alphabet × Edge =>
    (Formula.ofBool (decide (DetParityAutomaton.NatEven (T.priority ae.1 ae.2)))).and
      ((infinitelyOftenFormula T P H (T.priority ae.1 ae.2)).and
        (.allOf ((enumeration _).map (fun cf : Alphabet × Edge =>
          (Formula.ofBool (decide (T.priority cf.1 cf.2 < T.priority ae.1 ae.2))).imp
            (infinitelyOftenFormula T P H (T.priority cf.1 cf.2)).not))))))

theorem parityFormula_branch (tree : LabeledTree Branch Alphabet)
    (sets : Fin m → Set (TreeNode Branch)) (branch : Nat → Branch) (edges : Nat → Edge)
    (encodes : Encodes P H sets branch edges) :
    Realize tree (parityFormula T P H) Fin.elim0 sets ↔
      NatSeqMinEvenParity (fun n => T.priority (tree (branchNode branch n)) (edges n)) := by
  classical
  have raw : Realize tree (parityFormula T P H) Fin.elim0 sets ↔
      ∃ ae : Alphabet × Edge, DetParityAutomaton.NatEven (T.priority ae.1 ae.2) ∧
        Realize tree (infinitelyOftenFormula T P H (T.priority ae.1 ae.2)) Fin.elim0 sets ∧
        ∀ cf : Alphabet × Edge, T.priority cf.1 cf.2 < T.priority ae.1 ae.2 →
          ¬ Realize tree (infinitelyOftenFormula T P H (T.priority cf.1 cf.2)) Fin.elim0 sets := by
    simp [parityFormula, Realize]
    constructor
    · rintro ⟨a,e,even,seen,smaller⟩
      refine ⟨a,e,even,seen,?_⟩
      intro c f
      simpa only [Formula.realize_imp, Formula.realize_ofBool, decide_eq_true_eq,
        Formula.realize_not] using smaller _ c f rfl
    · rintro ⟨a,e,even,seen,smaller⟩
      refine ⟨a,e,even,seen,?_⟩
      intro φ c f eq
      subst φ
      simpa only [Formula.realize_imp, Formula.realize_ofBool, decide_eq_true_eq,
        Formula.realize_not] using smaller c f
  rw [raw]
  simp only [infinitelyOftenFormula_branch T P H _ tree sets branch edges encodes]
  constructor
  · rintro ⟨ae,even,seen,smaller⟩
    refine ⟨T.priority ae.1 ae.2,even,seen,?_⟩
    intro c recurring
    obtain ⟨k,_,eq⟩ := recurring 0
    dsimp at eq
    by_contra h
    have lt : T.priority (tree (branchNode branch k)) (edges k) < T.priority ae.1 ae.2 := by omega
    apply smaller ⟨tree (branchNode branch k),edges k⟩ lt
    simpa only [eq] using recurring
  · rintro ⟨c,even,seen,minimum⟩
    obtain ⟨k,_,eq⟩ := seen 0
    dsimp at eq
    refine ⟨⟨tree (branchNode branch k),edges k⟩,?_,?_,?_⟩
    · simpa only [eq] using even
    · simpa only [eq] using seen
    · intro cf lt recurring
      have le := minimum (T.priority cf.1 cf.2) recurring
      dsimp at lt
      omega


variable {k : Nat} (index : Edge ≃ Fin k)

/-- Universal quantification over the branch and all edge sets. Negating
an existential counterexample is exactly the displayed Run => Parity formula. -/
def acceptanceFormula : Sentence (language Branch Alphabet) :=
  (localFormula T).and
    (((runFormula T (Fin.last k) (fun e => (index e).castSucc)).and
      (parityFormula T (Fin.last k) (fun e => (index e).castSucc)).not).exAllSets).not

theorem acceptanceFormula_correct (tree : LabeledTree Branch Alphabet) :
    Tree.Satisfies tree (acceptanceFormula T index) ↔ Accepting T tree := by
  classical
  have semantics : Tree.Satisfies tree (acceptanceFormula T index) ↔
      Local T tree ∧ ∀ sets : Fin (k+1) → Set (TreeNode Branch),
        SetRun T (Fin.last k) (fun e => (index e).castSucc) tree sets →
        Realize tree (parityFormula T (Fin.last k) (fun e => (index e).castSucc)) Fin.elim0 sets := by
    unfold acceptanceFormula Tree.Satisfies Realize
    simp only [Formula.realize_and, Formula.realize_not, Formula.realize_exAllSets,
      not_exists, not_and, not_not]
    change (Tree.Satisfies tree (localFormula T) ∧ _) ↔ _
    rw [localFormula_correct]
    simp only [← runFormula_correct]
    rfl
  rw [semantics]
  constructor
  · rintro ⟨locallyValid, universal⟩
    refine ⟨locallyValid, fun branch edges run => ?_⟩
    let sets : Fin (k+1) → Set (TreeNode Branch) :=
      Fin.snoc (fun j => {node | ∃ n, node = branchNode branch n ∧ edges n = index.symm j})
        (Set.range (branchNode branch))
    have encodes : Encodes (Fin.last k) (fun e => (index e).castSucc) sets branch edges := by
      constructor
      · simp only [sets,Fin.snoc_last]
      · intro node e
        simp only [sets,Fin.snoc_castSucc,index.symm_apply_apply,Set.mem_setOf_eq]
    exact (parityFormula_branch T _ _ tree sets branch edges encodes).mp
      (universal sets ((setRun_iff T _ _ tree sets).mpr ⟨branch,edges,encodes,run⟩))
  · rintro ⟨locallyValid, accepting⟩
    refine ⟨locallyValid, fun sets run => ?_⟩
    obtain ⟨branch,edges,encodes,compatible⟩ := (setRun_iff T _ _ tree sets).mp run
    exact (parityFormula_branch T _ _ tree sets branch edges encodes).mpr
      (accepting branch edges compatible)

variable [Inhabited Branch]

/-- Executable satisfiability for these finite run tables, using the
existing MSO compiler and parity-tree-automaton decision procedure. -/
def satisfiable : Bool := Tree.Executable.satisfiable (acceptanceFormula T index)

theorem satisfiable_correct : satisfiable T index = true ↔ ∃ tree, Accepting T tree := by
  rw [satisfiable, Tree.Executable.satisfiable_correct]
  exact exists_congr (acceptanceFormula_correct T index)

end Characterisation.ComponentTrees.FiniteRunMSO
