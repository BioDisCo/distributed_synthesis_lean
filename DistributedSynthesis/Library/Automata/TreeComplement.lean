/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Automata.TreeAcceptanceGame
import DistributedSynthesis.Library.Automata.TreeProjection
import DistributedSynthesis.Library.Automata.TreeNonemptiness
import DistributedSynthesis.Library.Automata.WordTreeMonitor
import DistributedSynthesis.Library.Automata.UniversalThreads

/-! # Complementation of nondeterministic parity tree automata

A rejecting strategy supplies a finite direction table at each node. The
existing universal word-automaton construction checks all state threads
consistent with those tables. Projection forgets the tables.
-/
namespace DistributedSynthesis.TreeComplement

variable {Branch Alphabet : Type*} [Fintype Branch] [Nonempty Branch]
variable (A : RunParityTreeAutomaton Branch Alphabet)

/-- Odd's local choices, for every state and proposed successor vector. -/
abbrev Policy := A.State → (Branch → A.State) → Branch

/-- Every infinite legal thread following the node policies fails min-even parity. -/
def Rejects (tree : LabeledTree Branch Alphabet) (policy : TreeNode Branch → Policy A) : Prop :=
  ∀ (branch : Nat → Branch) (q : Nat → A.State) (next : Nat → Branch → A.State),
    q 0 = A.initial →
    (∀ n, A.delta (q n) (tree (branchNode branch n)) (next n)) →
    (∀ n, q (n + 1) = next n (branch n)) →
    (∀ n, branch n = policy (branchNode branch n) (q n) (next n)) →
    ¬ NatSeqMinEvenParity (fun n => A.priority (q n))

omit [Fintype Branch] [Nonempty Branch] in
theorem rejects_of_policy (tree : LabeledTree Branch Alphabet)
    (policy : TreeNode Branch → Policy A) (rejects : Rejects A tree policy) :
    ¬ A.acceptsTree tree := by
  rintro ⟨run, ⟨initial, transition⟩, parity⟩
  let select := fun node => policy node (run node) (fun b => run (node ++ [b]))
  let branch := fun n => select (selectorNode select n)
  have nodes (n : Nat) : branchNode branch n = selectorNode select n :=
    (selectorNode_eq_branchNode select n).symm
  exact rejects branch (fun n => run (branchNode branch n))
    (fun n b => run (branchNode branch n ++ [b])) initial (fun n => transition (branchNode branch n))
    (fun _ => rfl) (fun n => by simp only [branch, nodes]; rfl) (parity branch)

theorem exists_policy_of_rejects (tree : LabeledTree Branch Alphabet)
    (rejects : ¬ A.acceptsTree tree) : ∃ policy, Rejects A tree policy := by
  classical
  obtain ⟨τ, wins⟩ := (TreeAcceptance.rejects_iff_odd_winning A tree).mp rejects
  have legal (node : TreeNode Branch) (q : A.State) (next : Branch → A.State) :
      ∃ direction, τ.move (TreeAcceptance.choice A node q next) =
        TreeAcceptance.state A (node ++ [direction]) (next direction) :=
    τ.legal (TreeAcceptance.choice A node q next) rfl
  choose policy selected using legal
  refine ⟨policy, ?_⟩
  intro branch q next initial transition follow directions even
  let states := fun n => TreeAcceptance.state A (branchNode branch n) (q n)
  let choices := fun n => TreeAcceptance.choice A (branchNode branch n) (q n) (next n)
  have play : (TreeAcceptance.game A tree).Play (interleavePlay states choices) := by
    apply interleavePlay_play
    · intro n
      exact Or.inl ⟨_, transition n, rfl⟩
    · intro n
      exact ⟨branch n, by simp only [states, follow, branchNode]⟩
  have start : interleavePlay states choices 0 = TreeAcceptance.state A [] A.initial := by
    simp [interleavePlay_zero, states, branchNode, initial]
  have consistent : τ.Consistent (interleavePlay states choices) := by
    intro k own
    rcases Nat.mod_two_eq_zero_or_one k with hzero | hone
    · rw [interleavePlay_of_mod_eq_zero _ _ hzero] at own
      simp [states, TreeAcceptance.game, TreeAcceptance.owner, TreeAcceptance.state] at own
    · rw [interleavePlay_of_mod_eq_one _ _ hone,
        interleavePlay_of_mod_eq_zero _ _ (by omega : (k+1)%2=0),
        (by omega : (k+1)/2=k/2+1)]
      change TreeAcceptance.state A _ _ = τ.move (TreeAcceptance.choice A _ _ _)
      rw [selected, ← directions, ← follow]
      rfl
  have odd := wins _ ⟨start, play⟩ consistent
  have values : ∀ k, TreeAcceptance.priority A (interleavePlay states choices k) =
      A.priority (q (k / 2)) :=
    interleavePlay_priority _ states choices _ (fun _ => rfl) (fun _ => rfl)
  exact not_natSeqMinEvenParity_and_natSeqMinOddParity _
    ⟨even, (natSeqMinOddParity_halved values).mp odd⟩

theorem rejects_iff_exists_policy (tree : LabeledTree Branch Alphabet) :
    ¬ A.acceptsTree tree ↔ ∃ policy, Rejects A tree policy :=
  ⟨exists_policy_of_rejects A tree, fun ⟨policy, h⟩ => rejects_of_policy A tree policy h⟩

/-- Invalid threads enter an accepting sink; live threads use the complemented
priority. The source automaton's transition relation is not assumed computable. -/
noncomputable def threads : FiniteThreadSystem ((Alphabet × Policy A) × Branch) := by
  classical
  exact {
    State := Option A.State
    stateFinite := inferInstance
    initial := some A.initial
    Resolution := Branch → A.State
    step := fun q letter next => match q with
      | none => none
      | some q => if A.delta q letter.1.1 next ∧ letter.1.2 q next = letter.2
          then some (next letter.2) else none
    priority := fun q => match q with
      | none => 0
      | some q => A.priority q + 1 }

omit [Fintype Branch] [Nonempty Branch] in
@[simp] theorem step_none (letter : (Alphabet × Policy A) × Branch)
    (next : Branch → A.State) : (threads A).step none letter next = none := rfl

omit [Fintype Branch] [Nonempty Branch] in
theorem step_some_iff (q target : A.State) (a : Alphabet) (policy : Policy A)
    (direction : Branch) (next : Branch → A.State) :
    (threads A).step (some q) ((a, policy), direction) next = some target ↔
      A.delta q a next ∧ policy q next = direction ∧ next direction = target := by
  classical
  simp only [threads]
  split_ifs with legal
  · simp [legal]
  · simp only [Option.noConfusion, false_iff]
    rintro ⟨h, h', _⟩
    exact legal ⟨h, h'⟩

omit [Fintype Branch] [Nonempty Branch] in
/-- Checking all threads is exactly checking all legal policy-following paths. -/
theorem universal_threads_iff (tree : LabeledTree Branch Alphabet)
    (policy : TreeNode Branch → Policy A) :
    (∀ branch q, (threads A).IsRun
      (WordTreeMonitor.word (fun node => (tree node, policy node)) branch) q →
      NatSeqMinEvenParity (fun n => (threads A).priority (q n))) ↔
      Rejects A tree policy := by
  classical
  constructor
  · intro allThreads branch q next initial transition follow directions
    have isRun : (threads A).IsRun
        (WordTreeMonitor.word (fun node => (tree node, policy node)) branch)
        (fun n => some (q n)) := by
      refine ⟨congrArg some initial, fun n => ⟨next n, ?_⟩⟩
      symm
      exact (step_some_iff A _ _ _ _ _ _).mpr
        ⟨transition n, (directions n).symm, (follow n).symm⟩
    exact (TreeNonemptiness.shifted_parity_iff_not A.priority q).mp
      (allThreads branch _ isRun)
  · intro rejects branch path isRun
    by_cases sink : ∃ N, path N = none
    · obtain ⟨N, hN⟩ := sink
      have stays (k : Nat) : path (N + k) = none := by
        induction k with
        | zero => simpa using hN
        | succ k ih =>
          obtain ⟨next, hnext⟩ := isRun.2 (N+k)
          simpa only [Nat.add_succ, ih, step_none] using hnext
      refine ⟨0, ⟨0, rfl⟩, ?_, fun _ _ => Nat.zero_le _⟩
      intro n
      exact ⟨N+n, by omega, by change (threads A).priority (path (N+n)) = 0; rw [stays]; rfl⟩
    · have live (n : Nat) : path n ≠ none := fun h => sink ⟨n,h⟩
      let q := fun n => (path n).getD A.initial
      have values (n : Nat) : path n = some (q n) := by
        dsimp [q]
        cases h : path n with
        | none => exact False.elim (live n h)
        | some p => rfl
      choose next steps using isRun.2
      have conditions (n : Nat) := (step_some_iff A (q n) (q (n+1))
        (tree (branchNode branch n)) (policy (branchNode branch n)) (branch n) (next n)).mp
        (by simpa only [values] using (steps n).symm)
      have initial : q 0 = A.initial := by
        have h := isRun.1
        rw [values] at h
        exact Option.some.inj h
      have bad := rejects branch q next initial (fun n => (conditions n).1)
        (fun n => (conditions n).2.2.symm) (fun n => (conditions n).2.1.symm)
      have good := (TreeNonemptiness.shifted_parity_iff_not A.priority q).mpr bad
      simpa only [values] using good

variable [Fintype Alphabet]

/-- The automaton on input labels decorated with local rejecting policies. -/
noncomputable def annotated : RunParityTreeAutomaton Branch (Alphabet × Policy A) := by
  classical
  exact (WordTreeMonitor.monitor (threads A).universalRunDPA).toRunAutomaton

omit [Nonempty Branch] in
theorem annotated_accepts_iff (tree : LabeledTree Branch Alphabet)
    (policy : TreeNode Branch → Policy A) :
    (annotated A).acceptsTree (fun node => (tree node, policy node)) ↔
      Rejects A tree policy := by
  classical
  rw [annotated, DeterministicBlockMonitor.acceptsTree_iff_winningTree,
    WordTreeMonitor.winning_iff]
  simp only [FiniteThreadSystem.universalRunDPA_accepts_iff]
  exact universal_threads_iff A tree policy

/-- Language complementation, using the existing semantic Piterman construction.
This definition is noncomputable; an executable finite-table compiler is a
separate interface and is not claimed here. -/
noncomputable def automaton : RunParityTreeAutomaton Branch Alphabet :=
  (annotated A).project Prod.fst

/-- No closure certificate or determinacy hypothesis is required from the caller. -/
theorem accepts_iff (tree : LabeledTree Branch Alphabet) :
    (automaton A).acceptsTree tree ↔ ¬ A.acceptsTree tree := by
  rw [automaton, RunParityTreeAutomaton.project_fst_acceptsTree_iff,
    rejects_iff_exists_policy]
  exact exists_congr (fun policy => annotated_accepts_iff A tree policy)

end DistributedSynthesis.TreeComplement
