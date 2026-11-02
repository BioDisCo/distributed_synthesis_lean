/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Logic.MSO.AutomatonRuns

/-! # MSO description of parity along every branch

A priority recurs on a branch precisely when its occurrences are cofinal in the
ancestor order. All priority tests are finite disjunctions over automaton states.
-/
namespace DistributedSynthesis.MSO.Tree.Automaton

variable {Branch Alphabet : Type*} {n m : Nat}
variable (A : RunParityTreeAutomaton Branch Alphabet) (stateVars : A.State → Fin m)

noncomputable def priorityAt (p : Nat) (x : Fin n) : Formula (language Branch Alphabet) n m := by
  classical
  exact .anyOf (Finset.univ.toList.map (fun q : A.State =>
    (Formula.ofBool (decide (A.priority q = p))).and (.mem x (stateVars q))))

theorem priorityAt_correct (tree : LabeledTree Branch Alphabet) (nodes : Fin n → TreeNode Branch)
    (sets : Fin m → Set (TreeNode Branch)) (run : TreeNode Branch → A.State)
    (encodes : EncodesRun A stateVars sets run) (p : Nat) (x : Fin n) :
    Realize tree (priorityAt A stateVars p x) nodes sets ↔ A.priority (run (nodes x)) = p := by
  classical
  unfold EncodesRun at encodes
  simp [priorityAt, Realize, encodes, eq_comm]

noncomputable def cofinalFormula (X : Fin m) (p : Nat) : Formula (language Branch Alphabet) 0 m :=
  .allNode ((Formula.mem 0 X).imp
    (((Formula.mem 1 X).and ((ancestor 0 1).and (priorityAt A stateVars p 1))).exNode))

theorem cofinalFormula_correct (tree : LabeledTree Branch Alphabet)
    (sets : Fin m → Set (TreeNode Branch)) (run : TreeNode Branch → A.State)
    (encodes : EncodesRun A stateVars sets run) (X : Fin m) (p : Nat) :
    Realize tree (cofinalFormula A stateVars X p) Fin.elim0 sets ↔
      ∀ x, x ∈ sets X → ∃ y, y ∈ sets X ∧ x <+: y ∧ A.priority (run y) = p := by
  classical
  unfold EncodesRun at encodes
  simp [cofinalFormula, priorityAt, Realize, Fin.snoc, encodes, eq_comm]

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

noncomputable def parityFormula (X : Fin m) : Formula (language Branch Alphabet) 0 m := by
  classical
  exact .anyOf (Finset.univ.toList.map (fun q : A.State =>
    (Formula.ofBool (decide (DetParityAutomaton.NatEven (A.priority q)))).and
      ((cofinalFormula A stateVars X (A.priority q)).and
        (.allOf (Finset.univ.toList.map (fun q' : A.State =>
          (Formula.ofBool (decide (A.priority q' < A.priority q))).imp
            (cofinalFormula A stateVars X (A.priority q')).not))))))

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

noncomputable def branchParityFormula : Formula (language Branch Alphabet) 0 m :=
  .allSet ((branchFormula (Fin.last m)).imp
    (parityFormula A (fun q => (stateVars q).castSucc) (Fin.last m)))

variable [Nonempty Branch]

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

end DistributedSynthesis.MSO.Tree.Automaton
