/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderPhases.GlobalLeaderProgress

/-! Public observations outside the offers of the chosen move stop the
semantic obligation. A bad move at a supported node is nevertheless rejected,
including when the following observation is unsupported. -/
namespace Characterisation
open DistributedSynthesis

section Support
variable {Observation Move : Type}

def publicSupport (offers : Move → Observation → Bool)
    (tree : LabeledTree Observation Move) (node : List Observation) : Bool :=
  node.reverseRecOn true (fun previous observation supported =>
    supported && offers (tree previous) observation)

@[simp] theorem publicSupport_nil (offers : Move → Observation → Bool)
    (tree : LabeledTree Observation Move) : publicSupport offers tree [] = true := by
  simp [publicSupport]

@[simp] theorem publicSupport_append (offers : Move → Observation → Bool)
    (tree : LabeledTree Observation Move) (node : List Observation) (observation : Observation) :
    publicSupport offers tree (node ++ [observation]) =
      (publicSupport offers tree node && offers (tree node) observation) := by
  simp only [publicSupport, List.reverseRecOn_concat]

def SupportedMovesValid (offers : Move → Observation → Bool)
    (initial : Observation) (Legal : Observation → Move → Prop)
    (tree : LabeledTree Observation Move) : Prop :=
  ∀ node, publicSupport offers tree node = true →
    Legal (observableAt initial node) (tree node)

theorem publicSupport_branch_of_offered (offers : Move → Observation → Bool)
    (tree : LabeledTree Observation Move) (branch : Nat → Observation)
    (offered : ∀ n, offers (tree (branchNode branch n)) (branch n) = true) :
    ∀ n, publicSupport offers tree (branchNode branch n) = true := by
  intro n
  induction n with
  | zero => exact publicSupport_nil offers tree
  | succ n ih =>
    change publicSupport offers tree (branchNode branch n ++ [branch n]) = true
    simp only [publicSupport_append, ih, offered n, Bool.and_self]

end Support

section Monitor
variable {Observation Move : Type} [Fintype Observation] [Fintype Move]
variable (D : DetParityAutomaton (Move × Observation))
variable (offers : Move → Observation → Bool) (initial : Observation)
variable (Legal : Observation → Move → Prop) [DecidableRel Legal]

/-- Legality is checked before the observation is tested for support. The
sticky rejection bit cannot be repaired by choosing an empty offer set. -/
def supportedPublicTreeMonitor : DeterministicBlockMonitor Observation Move where
  branchFinite := inferInstance
  alphabetFinite := inferInstance
  State := Observation × D.State × Bool × Bool
  stateFinite := inferInstance
  initial := (initial, D.initial, true, true)
  step state move observation :=
    (observation, D.step state.2.1 (move, observation),
      state.2.2.1 && offers move observation,
      state.2.2.2 && (!state.2.2.1 || decide (Legal state.1 move)))
  priority state :=
    if state.2.2.2 then (if state.2.2.1 then D.priority state.2.1 + 2 else 0) else 1

theorem supportedPublicTreeMonitor_observation (tree : LabeledTree Observation Move) :
    ∀ node, ((supportedPublicTreeMonitor D offers initial Legal).control tree node).1 =
      observableAt initial node := by
  intro node
  cases node using List.reverseRecOn with
  | nil => rfl
  | append_singleton node observation =>
    rw [DeterministicBlockMonitor.control_append]
    simp [supportedPublicTreeMonitor, observableAt]

theorem supportedPublicTreeMonitor_support (tree : LabeledTree Observation Move) :
    ∀ node, ((supportedPublicTreeMonitor D offers initial Legal).control tree node).2.2.1 =
      publicSupport offers tree node := by
  intro node
  induction node using List.reverseRecOn with
  | nil => rw [publicSupport_nil]; rfl
  | append_singleton node observation ih =>
    rw [DeterministicBlockMonitor.control_append, publicSupport_append]
    change (_ && _) = (_ && _)
    rw [ih]

theorem supportedPublicTreeMonitor_bundle (tree : LabeledTree Observation Move)
    (branch : Nat → Observation) : ∀ n,
    ((supportedPublicTreeMonitor D offers initial Legal).control tree (branchNode branch n)).2.1 =
      D.run (observableThreadWord tree branch) n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    change ((supportedPublicTreeMonitor D offers initial Legal).control tree
      (branchNode branch n ++ [branch n])).2.1 = _
    rw [DeterministicBlockMonitor.control_append]
    change D.step _ _ = _
    rw [ih]
    rfl

theorem supportedPublicTreeMonitor_safe (tree : LabeledTree Observation Move)
    (legal : SupportedMovesValid offers initial Legal tree) :
    ∀ node, ((supportedPublicTreeMonitor D offers initial Legal).control tree node).2.2.2 = true := by
  intro node
  induction node using List.reverseRecOn with
  | nil => rfl
  | append_singleton node observation ih =>
    rw [DeterministicBlockMonitor.control_append]
    change (_ && (!_ || decide (Legal _ _))) = true
    rw [ih, supportedPublicTreeMonitor_support, supportedPublicTreeMonitor_observation]
    cases eq : publicSupport offers tree node with
    | false => rfl
    | true => simp only [Bool.not_true, Bool.false_or, Bool.true_and, decide_eq_true_eq]; exact legal node eq

theorem supportedPublicTreeMonitor_rejection_persists (tree : LabeledTree Observation Move)
    (node : List Observation)
    (bad : ((supportedPublicTreeMonitor D offers initial Legal).control tree node).2.2.2 = false) :
    ∀ suffix, ((supportedPublicTreeMonitor D offers initial Legal).control tree (node ++ suffix)).2.2.2 = false := by
  intro suffix
  induction suffix using List.reverseRecOn with
  | nil => simpa using bad
  | append_singleton suffix observation ih =>
    rw [← List.append_assoc, DeterministicBlockMonitor.control_append]
    change (_ && _) = false
    rw [ih]
    rfl

variable [Inhabited Observation]

private def extendingBranch (node : List Observation) : Nat → Observation :=
  fun n => node.getD n default

omit [Fintype Observation] in
private theorem extendingBranch_prefix (node : List Observation) :
    ∀ n, n ≤ node.length → branchNode (extendingBranch node) n = node.take n := by
  intro n bound
  induction n with
  | zero => rfl
  | succ n ih =>
    change branchNode (extendingBranch node) n ++ [node.getD n default] = _
    rw [ih (by omega), List.getD_eq_getElem node default (by omega),
      List.take_add_one, List.getElem?_eq_getElem (by omega)]
    rfl

theorem supportedPublicTreeMonitor_legal_of_winning (tree : LabeledTree Observation Move)
    (winning : (supportedPublicTreeMonitor D offers initial Legal).WinningTree tree) :
    SupportedMovesValid offers initial Legal tree := by
  intro node supported
  by_contra illegal
  let child := node ++ [(default : Observation)]
  have bad : ((supportedPublicTreeMonitor D offers initial Legal).control tree child).2.2.2 = false := by
    rw [DeterministicBlockMonitor.control_append]
    change (_ && (!_ || decide (Legal _ _))) = false
    rw [supportedPublicTreeMonitor_support, supportedPublicTreeMonitor_observation, supported,
      decide_eq_false illegal]
    exact Bool.and_false _
  let branch := extendingBranch child
  have atChild : branchNode branch child.length = child := by
    simpa [branch] using extendingBranch_prefix child child.length (Nat.le_refl _)
  have persists : ∀ k,
      ((supportedPublicTreeMonitor D offers initial Legal).control tree
        (branchNode branch (child.length + k))).2.2.2 = false := by
    intro k
    induction k with
    | zero => simpa [atChild] using bad
    | succ k ih =>
      rw [Nat.add_succ]
      change ((supportedPublicTreeMonitor D offers initial Legal).control tree
        (branchNode branch (child.length+k) ++ [branch (child.length+k)])).2.2.2 = false
      rw [DeterministicBlockMonitor.control_append]
      change (_ && _) = false
      rw [ih]
      rfl
  apply not_natSeqMinEvenParity_of_eventually_one _ child.length _ (winning branch)
  intro n bound
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le bound
  change (if _ then _ else 1) = 1
  rw [persists k]
  rfl

theorem supportedPublicTreeMonitor_parity_of_winning (tree : LabeledTree Observation Move)
    (winning : (supportedPublicTreeMonitor D offers initial Legal).WinningTree tree)
    (branch : Nat → Observation)
    (supported : ∀ n, publicSupport offers tree (branchNode branch n) = true) :
    D.Accepts (observableThreadWord tree branch) := by
  have safe := supportedPublicTreeMonitor_safe D offers initial Legal tree
    (supportedPublicTreeMonitor_legal_of_winning D offers initial Legal tree winning)
  have parity := winning branch
  have priorities : (fun n => (supportedPublicTreeMonitor D offers initial Legal).priority
      ((supportedPublicTreeMonitor D offers initial Legal).control tree (branchNode branch n))) =
      fun n => D.priority (D.run (observableThreadWord tree branch) n) + 2 := by
    funext n
    change (if _ then (if _ then _ else 0) else 1) = _
    rw [safe, supportedPublicTreeMonitor_support, supported n]
    simp only [↓reduceIte, supportedPublicTreeMonitor_bundle]
  rw [priorities] at parity
  exact (natSeqMinEvenParity_add_const (d := 2) ⟨1, rfl⟩).mp parity

omit [Inhabited Observation] in
theorem supportedPublicTreeMonitor_winning_of (tree : LabeledTree Observation Move)
    (legal : SupportedMovesValid offers initial Legal tree)
    (parity : ∀ branch : Nat → Observation,
      (∀ n, publicSupport offers tree (branchNode branch n) = true) →
      D.Accepts (observableThreadWord tree branch)) :
    (supportedPublicTreeMonitor D offers initial Legal).WinningTree tree := by
  intro branch
  have safe := supportedPublicTreeMonitor_safe D offers initial Legal tree legal
  by_cases supported : ∀ n, publicSupport offers tree (branchNode branch n) = true
  · have priorities : (fun n => (supportedPublicTreeMonitor D offers initial Legal).priority
        ((supportedPublicTreeMonitor D offers initial Legal).control tree (branchNode branch n))) =
        fun n => D.priority (D.run (observableThreadWord tree branch) n) + 2 := by
      funext n
      change (if _ then (if _ then _ else 0) else 1) = _
      rw [safe, supportedPublicTreeMonitor_support, supported n]
      simp only [↓reduceIte, supportedPublicTreeMonitor_bundle]
    rw [priorities]
    exact (natSeqMinEvenParity_add_const (d := 2) ⟨1, rfl⟩).mpr (parity branch supported)
  · push Not at supported
    obtain ⟨n, failed⟩ := supported
    have noSupport : publicSupport offers tree (branchNode branch n) = false :=
      Bool.eq_false_iff.mpr failed
    have persists : ∀ k, publicSupport offers tree (branchNode branch (n+k)) = false := by
      intro k
      induction k with
      | zero => simpa using noSupport
      | succ k ih =>
        rw [Nat.add_succ]
        change publicSupport offers tree (branchNode branch (n+k) ++ [branch (n+k)]) = false
        rw [publicSupport_append, ih]
        rfl
    refine ⟨0, ⟨0, rfl⟩, ?_, ?_⟩
    · intro base
      refine ⟨n+base, by omega, ?_⟩
      change (if _ then (if _ then _ else 0) else 1) = 0
      rw [safe, supportedPublicTreeMonitor_support, persists base]
      rfl
    · intro q _
      exact Nat.zero_le q

theorem supportedPublicTreeMonitor_winning_iff (tree : LabeledTree Observation Move) :
    (supportedPublicTreeMonitor D offers initial Legal).WinningTree tree ↔
      SupportedMovesValid offers initial Legal tree ∧
      ∀ branch : Nat → Observation,
        (∀ n, publicSupport offers tree (branchNode branch n) = true) →
        D.Accepts (observableThreadWord tree branch) := by
  exact ⟨fun win => ⟨supportedPublicTreeMonitor_legal_of_winning D offers initial Legal tree win,
      supportedPublicTreeMonitor_parity_of_winning D offers initial Legal tree win⟩,
    fun ⟨legal, parity⟩ => supportedPublicTreeMonitor_winning_of D offers initial Legal tree legal parity⟩

end Monitor
end Characterisation
