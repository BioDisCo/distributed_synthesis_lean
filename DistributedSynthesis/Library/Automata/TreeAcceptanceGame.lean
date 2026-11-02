/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Automata.Tree

/-! # The acceptance game of a fixed input tree

The existing emptiness game lets Even choose the input labels. Here the input
tree is fixed: Even chooses a legal successor vector and Odd chooses a direction.
The arena is countable, and its priority range is finite. We use the existing
countable parity-game determinacy theorem, not a second parity-game solver.
-/
namespace DistributedSynthesis.TreeAcceptance

universe u v w
variable {Branch : Type u} {Alphabet : Type v} [Fintype Branch] [Nonempty Branch]
variable (A : RunParityTreeAutomaton.{u, v, w} Branch Alphabet)
variable (tree : LabeledTree Branch Alphabet)

abbrev Position := Option (TreeNode Branch × (A.State ⊕ A.State × (Branch → A.State)))

def state (node : TreeNode Branch) (q : A.State) : Position A := some (node, .inl q)
def choice (node : TreeNode Branch) (q : A.State) (next : Branch → A.State) : Position A :=
  some (node, .inr (q, next))

def owner : Position A → ParityPlayer
  | some (_, .inr _) => .odd
  | _ => .even

def priority : Position A → Nat
  | none => 1
  | some (_, .inl q) => A.priority q
  | some (_, .inr (q, _)) => A.priority q

def step : Position A → Position A → Prop
  | none, target => target = none
  | some (node, .inl q), target =>
      (∃ next : Branch → A.State, A.delta q (tree node) next ∧ target = choice A node q next) ∨
        ((¬ ∃ next : Branch → A.State, A.delta q (tree node) next) ∧ target = none)
  | some (node, .inr (_, next)), target =>
      ∃ direction : Branch, target = state A (node ++ [direction]) (next direction)

theorem step_total (position : Position A) : ∃ next, step A tree position next := by
  classical
  rcases position with _ | ⟨node, q | ⟨q, next⟩⟩
  · exact ⟨none, rfl⟩
  · by_cases possible : ∃ next : Branch → A.State, A.delta q (tree node) next
    · obtain ⟨next, legal⟩ := possible
      exact ⟨choice A node q next, Or.inl ⟨next, legal, rfl⟩⟩
    · exact ⟨none, Or.inr ⟨possible, rfl⟩⟩
  · exact ⟨state A (node ++ [Classical.arbitrary Branch]) (next (Classical.arbitrary Branch)),
      Classical.arbitrary Branch, rfl⟩

def game : CountableParityGame.{max u w} where
  Position := Position A
  positionCountable := inferInstance
  owner := owner A
  step := step A tree
  step_total := step_total A tree
  priority := priority A
  priority_finite := by
    apply ((Set.finite_range A.priority).insert 1).subset
    rintro _ ⟨position, rfl⟩
    rcases position with _ | ⟨node, q | ⟨q, next⟩⟩
    · exact Set.mem_insert _ _
    · exact Set.mem_insert_of_mem _ ⟨q, rfl⟩
    · exact Set.mem_insert_of_mem _ ⟨q, rfl⟩

/-- An accepting run defeats every positional Odd strategy on the fixed tree. -/
theorem not_odd_winning_of_accepts (accepts : A.acceptsTree tree) :
    state A [] A.initial ∉ (game A tree).PositionalWinningRegion .odd := by
  classical
  rintro ⟨τ, wins⟩
  obtain ⟨run, ⟨initial, transition⟩, parity⟩ := accepts
  have legalChoice (node : TreeNode Branch) :
      ∃ direction : Branch,
        τ.move (choice A node (run node) (fun b => run (node ++ [b]))) =
          state A (node ++ [direction]) (run (node ++ [direction])) :=
    τ.legal (choice A node (run node) (fun b => run (node ++ [b]))) rfl
  choose select selected using legalChoice
  let states := fun j => state A (selectorNode select j) (run (selectorNode select j))
  let choices := fun j => choice A (selectorNode select j) (run (selectorNode select j))
    (fun b => run (selectorNode select j ++ [b]))
  have play : (game A tree).Play (interleavePlay states choices) := by
    apply interleavePlay_play
    · intro j
      exact Or.inl ⟨_, transition _, rfl⟩
    · intro j
      exact ⟨select (selectorNode select j), rfl⟩
  have start : interleavePlay states choices 0 = state A [] A.initial := by
    simp [states, interleavePlay_zero, selectorNode, initial]
  have consistent : τ.Consistent (interleavePlay states choices) := by
    intro k own
    rcases Nat.mod_two_eq_zero_or_one k with even | odd
    · rw [interleavePlay_of_mod_eq_zero _ _ even] at own
      simp [game, owner, states, state] at own
    · rw [interleavePlay_of_mod_eq_one _ _ odd,
        interleavePlay_of_mod_eq_zero _ _ (by omega : (k + 1) % 2 = 0),
        (by omega : (k + 1) / 2 = k / 2 + 1)]
      exact (selected (selectorNode select (k / 2))).symm
  have loses := wins (interleavePlay states choices) ⟨start, play⟩ consistent
  have values : ∀ k, priority A (interleavePlay states choices k) =
      A.priority (run (selectorNode select (k / 2))) :=
    interleavePlay_priority (priority A) states choices _ (fun _ => rfl) (fun _ => rfl)
  have odd : NatSeqMinOddParity (fun n => A.priority (run (selectorNode select n))) :=
    (natSeqMinOddParity_halved values).mp loses
  have even : NatSeqMinEvenParity (fun n => A.priority (run (selectorNode select n))) := by
    have accepted := parity (fun k => select (selectorNode select k))
    simpa only [← selectorNode_eq_branchNode] using accepted
  exact not_natSeqMinEvenParity_and_natSeqMinOddParity _ ⟨even, odd⟩

section Extraction
variable (σ : (game A tree).PositionalStrategy .even)

/-- Winning cannot hold at the permanent odd sink. -/
theorem not_winning_none : ¬ CountableParityGame.PositionalStrategy.WinningFrom (G := game A tree) σ none := by
  intro wins
  have sink : σ.move none = none := σ.legal none rfl
  have accepts := wins (fun _ => none) ⟨rfl, fun _ => rfl⟩ (fun _ _ => sink.symm)
  exact not_natSeqMinEvenParity_of_eventually_one _ 0 (fun _ _ => rfl) accepts

/-- At a winning state the strategy must choose a legal successor vector. -/
theorem winning_choice (node : TreeNode Branch) (q : A.State)
    (wins : CountableParityGame.PositionalStrategy.WinningFrom (G := game A tree) σ (state A node q)) :
    ∃ next : Branch → A.State, A.delta q (tree node) next ∧
      σ.move (state A node q) = choice A node q next := by
  have legal := σ.legal (state A node q) rfl
  rcases legal with good | ⟨stuck, sink⟩
  · exact good
  · apply False.elim
    apply not_winning_none A tree σ
    exact CountableParityGame.PositionalStrategy.winningFrom_successor wins (Or.inr ⟨stuck, rfl⟩)
      (fun _ => sink.symm)

noncomputable def children (node : TreeNode Branch) (q : A.State) : Branch → A.State := by
  classical
  exact if possible : ∃ next, A.delta q (tree node) next ∧
      σ.move (state A node q) = choice A node q next then possible.choose else fun _ => q

theorem children_spec (node : TreeNode Branch) (q : A.State)
    (wins : CountableParityGame.PositionalStrategy.WinningFrom (G := game A tree) σ (state A node q)) :
    A.delta q (tree node) (children A tree σ node q) ∧
      σ.move (state A node q) = choice A node q (children A tree σ node q) := by
  classical
  have possible := winning_choice A tree σ node q wins
  simpa only [children, dif_pos possible] using possible.choose_spec

noncomputable def runAlong (history : TreeNode Branch) (q : A.State) : TreeNode Branch → A.State
  | [] => q
  | direction :: rest => runAlong (history ++ [direction]) (children A tree σ history q direction) rest

theorem runAlong_append (history : TreeNode Branch) (q : A.State) (left right : TreeNode Branch) :
    runAlong A tree σ history q (left ++ right) =
      runAlong A tree σ (history ++ left) (runAlong A tree σ history q left) right := by
  induction left generalizing history q with
  | nil => simp [runAlong]
  | cons direction rest ih => simp [runAlong, ih, List.append_assoc]

noncomputable def run (node : TreeNode Branch) : A.State := runAlong A tree σ [] A.initial node

@[simp] theorem run_nil : run A tree σ [] = A.initial := rfl

theorem run_append (node : TreeNode Branch) (direction : Branch) :
    run A tree σ (node ++ [direction]) = children A tree σ node (run A tree σ node) direction := by
  simp only [run, runAlong_append, List.nil_append, runAlong]

theorem run_winning (wins : CountableParityGame.PositionalStrategy.WinningFrom (G := game A tree) σ (state A [] A.initial)) (node : TreeNode Branch) :
    CountableParityGame.PositionalStrategy.WinningFrom (G := game A tree) σ (state A node (run A tree σ node)) := by
  induction node using List.reverseRecOn with
  | nil => exact wins
  | append_singleton node direction ih =>
    have chosen := children_spec A tree σ node (run A tree σ node) ih
    have choiceWins := CountableParityGame.PositionalStrategy.winningFrom_successor ih
      (Or.inl ⟨children A tree σ node (run A tree σ node), chosen.1, rfl⟩)
      (fun _ => chosen.2.symm)
    rw [run_append]
    apply CountableParityGame.PositionalStrategy.winningFrom_successor choiceWins ⟨direction, rfl⟩
    intro impossible
    cases impossible

/-- A positional Even strategy on the fixed tree supplies an accepting run. -/
theorem accepts_of_even_winning (wins : CountableParityGame.PositionalStrategy.WinningFrom (G := game A tree) σ (state A [] A.initial)) :
    A.acceptsTree tree := by
  refine ⟨run A tree σ, ⟨rfl, ?_⟩, ?_⟩
  · intro node
    have chosen := (children_spec A tree σ node _ (run_winning A tree σ wins node)).1
    simpa only [run_append] using chosen
  · intro branch
    let states := fun j => state A (branchNode branch j) (run A tree σ (branchNode branch j))
    let choices := fun j => choice A (branchNode branch j) (run A tree σ (branchNode branch j))
      (children A tree σ (branchNode branch j) (run A tree σ (branchNode branch j)))
    have play : (game A tree).Play (interleavePlay states choices) := by
      apply interleavePlay_play
      · intro j
        exact Or.inl ⟨_, (children_spec A tree σ _ _ (run_winning A tree σ wins _)).1, rfl⟩
      · intro j
        refine ⟨branch j, ?_⟩
        simp only [states, choices, branchNode, run_append]
    have start : interleavePlay states choices 0 = state A [] A.initial := by
      simp [states, interleavePlay_zero, branchNode]
    have consistent : σ.Consistent (interleavePlay states choices) := by
      intro k own
      rcases Nat.mod_two_eq_zero_or_one k with even | odd
      · rw [interleavePlay_of_mod_eq_zero _ _ even,
          interleavePlay_of_mod_eq_one _ _ (by omega : (k + 1) % 2 = 1),
          (by omega : (k + 1) / 2 = k / 2)]
        exact (children_spec A tree σ _ _ (run_winning A tree σ wins _)).2.symm
      · rw [interleavePlay_of_mod_eq_one _ _ odd] at own
        simp [game, owner, choices, choice] at own
    have accepted := wins (interleavePlay states choices) ⟨start, play⟩ consistent
    have values : ∀ k, priority A (interleavePlay states choices k) =
        A.priority (run A tree σ (branchNode branch (k / 2))) :=
      interleavePlay_priority (priority A) states choices _ (fun _ => rfl) (fun _ => rfl)
    exact (natSeqMinEvenParity_halved values).mp accepted
end Extraction

/-- Acceptance is exactly the Even winning region of the fixed-tree game. -/
theorem accepts_iff_even_winning :
    A.acceptsTree tree ↔ state A [] A.initial ∈ (game A tree).PositionalWinningRegion .even := by
  constructor
  · intro accepts
    rcases (game A tree).positionalGameDetermined (state A [] A.initial) with even | odd
    · exact even
    · exact False.elim (not_odd_winning_of_accepts A tree accepts odd)
  · rintro ⟨σ, wins⟩
    exact accepts_of_even_winning A tree σ wins

/-- Rejection has one positional Odd strategy valid against every possible run. -/
theorem rejects_iff_odd_winning :
    ¬ A.acceptsTree tree ↔ state A [] A.initial ∈ (game A tree).PositionalWinningRegion .odd := by
  constructor
  · intro rejects
    rcases (game A tree).positionalGameDetermined (state A [] A.initial) with even | odd
    · exact False.elim (rejects ((accepts_iff_even_winning A tree).mpr even))
    · exact odd
  · intro odd accepts
    exact not_odd_winning_of_accepts A tree accepts odd

end DistributedSynthesis.TreeAcceptance
