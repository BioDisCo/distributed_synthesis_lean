/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemObservableThreadTreeRationalization

/-!
# Ranked belief does not manufacture a finite observation quotient

The finite ranked-belief game correctly checks a *given* public observation
alphabet.  It cannot by itself prove that forgetting exact observations is
sound.  This file gives a kernel-small instance of that quantifier boundary.

With the exact Boolean observation exposed, the move `move = observation`
wins.  After both observations are quotiented to `Unit`, every public move
tree loses: the hidden resolution chooses the next Boolean state opposite to
the move that the tree will make at the next node.  The public move never sees
that hidden bit.

This is not a counterexample to the delay-one theorem.  It isolates the
missing model-specific premise in a proposed direct proof of
`ProfiledOpenSemanticRankedBeliefWinning`: one must first prove that the
finite public classes are a strategy-preserving uniformization (or retain a
sound finite refinement).  Positional determinacy and parity ranks do not
supply that premise.
-/

namespace DistributedSynthesis

namespace RankedBeliefNeedsUniformization

/-- The exact Boolean state is proof-side.  `bad` is a sticky odd sink. -/
inductive HiddenState where
  | live (bit : Bool)
  | bad
deriving DecidableEq, Fintype

/-- With exact observations, the next observation itself updates the hidden
state. -/
def exactSystem : FiniteThreadSystem (Bool × Bool) where
  State := HiddenState
  stateFinite := inferInstance
  initial := .live false
  Resolution := PUnit
  step := fun state letter _ =>
    match state with
    | .bad => .bad
    | .live current =>
        if letter.1 = current then .live letter.2 else .bad
  priority := fun state =>
    match state with
    | .live _ => 0
    | .bad => 1

/-- The exact-observation strategy plays the bit it currently sees. -/
def exactTree : LabeledTree Bool Bool :=
  fun node => observableAt false node

private theorem observableAt_branchNode_succ
    (branch : Nat → Bool) (n : Nat) :
    observableAt false (branchNode branch (n + 1)) = branch n := by
  rw [show branchNode branch (n + 1) =
      branchNode branch n ++ [branch n] from rfl]
  simp [observableAt]

/-- Every hidden run under the exact strategy is the live state named by the
current exact observation. -/
theorem exactSystem_run_eq
    (branch : Nat → Bool)
    (run : Nat → HiddenState)
    (hrun : exactSystem.IsRun (observableThreadWord exactTree branch) run) :
    ∀ n, run n = .live (observableAt false (branchNode branch n)) := by
  intro n
  induction n with
  | zero =>
      simpa [observableAt] using hrun.1
  | succ n ih =>
      rcases hrun.2 n with ⟨resolution, hnext⟩
      cases resolution
      rw [hnext, ih]
      simp [observableThreadWord, exactTree, exactSystem,
        observableAt_branchNode_succ]

/-- The exact-observation tree wins the universal hidden-thread monitor. -/
theorem exactTree_winning :
    (observableThreadTreeMonitor exactSystem false (fun _ _ => True)).WinningTree
      exactTree := by
  apply observableThreadTreeMonitor_winning_of
    exactSystem false (fun _ _ => True) exactTree
  · intro _
    trivial
  · intro branch
    rw [exactSystem.universalRunDPA_accepts_iff]
    intro run hrun
    have hlive := exactSystem_run_eq branch run hrun
    refine ⟨0, ⟨0, rfl⟩, ?_, ?_⟩
    · intro base
      refine ⟨base, le_rfl, ?_⟩
      change exactSystem.priority (run base) = 0
      rw [hlive base]
      rfl
    · intro priority _
      exact Nat.zero_le priority

/-! ## The quotient loses the winning strategy -/

/-- After quotienting observations to `Unit`, the next exact bit is a hidden
resolution. -/
def publicSystem : FiniteThreadSystem (Bool × Unit) where
  State := HiddenState
  stateFinite := inferInstance
  initial := .live false
  Resolution := Bool
  step := fun state letter nextBit =>
    match state with
    | .bad => .bad
    | .live current =>
        if letter.1 = current then .live nextBit else .bad
  priority := fun state =>
    match state with
    | .live _ => 0
    | .bad => 1

/-- The adversary installs at step `n` the complement of the move that the
public word will make at step `n+1`. -/
def adversarialPublicRun
    (word : OmegaWord (Bool × Unit)) : Nat → HiddenState
  | 0 => .live false
  | n + 1 =>
      publicSystem.step (adversarialPublicRun word n) (word n)
        (!(word (n + 1)).1)

theorem adversarialPublicRun_isRun
    (word : OmegaWord (Bool × Unit)) :
    publicSystem.IsRun word (adversarialPublicRun word) := by
  constructor
  · rfl
  · intro n
    exact ⟨!(word (n + 1)).1, rfl⟩

/-- Independently of the first public move, the adversarial run is in the odd
sink after at most two steps. -/
theorem adversarialPublicRun_two
    (word : OmegaWord (Bool × Unit)) :
    adversarialPublicRun word 2 = .bad := by
  cases hzero : (word 0).1 <;> cases hone : (word 1).1 <;>
    simp [adversarialPublicRun, publicSystem, hzero, hone]

theorem adversarialPublicRun_bad_persists
    (word : OmegaWord (Bool × Unit)) :
    ∀ k, adversarialPublicRun word (2 + k) = .bad := by
  intro k
  induction k with
  | zero => simpa using adversarialPublicRun_two word
  | succ k ih =>
      rw [Nat.add_succ]
      simp [adversarialPublicRun, ih, publicSystem]

/-- No public word satisfies the universal hidden-thread objective. -/
theorem publicSystem_universalRunDPA_rejects
    (word : OmegaWord (Bool × Unit)) :
    ¬ publicSystem.universalRunDPA.Accepts word := by
  intro haccepts
  have hall := (publicSystem.universalRunDPA_accepts_iff word).mp haccepts
  have hrun := adversarialPublicRun_isRun word
  have hparity := hall (adversarialPublicRun word) hrun
  apply not_natSeqMinEvenParity_of_eventually_one
      (fun n => publicSystem.priority (adversarialPublicRun word n)) 2
  · intro n hn
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
    rw [adversarialPublicRun_bad_persists]
    rfl
  · exact hparity

/-- Therefore no tree over the coarsened public observation can win, even
though the exact-observation tree above wins. -/
theorem no_publicTree_winning
    (tree : LabeledTree Unit Bool) :
    ¬ (observableThreadTreeMonitor publicSystem () (fun _ _ => True)).WinningTree
      tree := by
  intro hwinning
  have hbundle := observableThreadTreeMonitor_bundle_of_winning
    publicSystem () (fun _ _ => True) tree hwinning (fun _ => ())
  exact publicSystem_universalRunDPA_rejects _ hbundle

/-- The corresponding finite parity arena is literally the ranked-belief
game used by the positive construction. -/
noncomputable abbrev publicRankedBeliefGame :=
  RunParityTreeAutomaton.emptinessGame
    (observableThreadTreeMonitor publicSystem ()
      (fun _ _ => True)).toRunAutomaton

def PublicRankedBeliefWinning : Prop :=
  some (Sum.inl
      (observableThreadTreeMonitor publicSystem ()
        (fun _ _ => True)).initial) ∈
    publicRankedBeliefGame.PositionalWinningRegion ParityPlayer.even

/-- Even does not win the finite ranked-belief game after the unsound
observation quotient.  Thus adding progress ranks after quotienting cannot
repair the lost uniformity. -/
theorem not_publicRankedBeliefWinning :
    ¬ PublicRankedBeliefWinning := by
  rintro ⟨sigma, hsigma⟩
  let monitor := observableThreadTreeMonitor publicSystem ()
    (fun _ _ => True)
  let tree := RunParityTreeAutomaton.extractedTree monitor.toRunAutomaton
    sigma false
  have haccepts : monitor.toRunAutomaton.acceptsTree tree.labeledTree :=
    RunParityTreeAutomaton.acceptsTree_extractedTree monitor.toRunAutomaton
      sigma false hsigma
  have hwinning : monitor.WinningTree tree.labeledTree :=
    (monitor.acceptsTree_iff_winningTree tree.labeledTree).mp haccepts
  exact no_publicTree_winning tree.labeledTree hwinning

end RankedBeliefNeedsUniformization

end DistributedSynthesis
