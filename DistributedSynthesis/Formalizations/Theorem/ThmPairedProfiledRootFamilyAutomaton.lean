/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemTwoSortedFamilyRun
import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledRootFamilyHandoff

/-!
# Concrete outer automaton for profiled root families

The outer descriptor remembers either a right recurrent macro, a left
recurrent macro, or the harmless wrong-orientation sink.  A live move is one
simultaneous two-root table.  Its validity is exactly the all-thread theorem
for the combined family monitor.  On a close, both member projections emit
certified opposite-orientation macros by
`ThmPairedProfiledRootFamilyHandoff`.

The anchor bit occurs only inside the proof-side family and the receiver
projection of the simultaneous table.  The shared sender table never receives
it.  Thus this automaton does not assume that a process knows the strict
leader.
-/

namespace DistributedSynthesis

universe u v x y s

namespace DetParityAutomaton

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable
  (A : DetParityAutomaton.{max u v x y, s}
    (RoundRecord In₁ In₂ Graph Out₁ Out₂))

section

noncomputable section

variable [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]
variable [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
variable [DecidableEq In₁] [DecidableEq In₂]

/-- Finite objective descriptor of the recursive root-family construction. -/
inductive ProfiledBankRootAnchor where
  | sink
  | right (source : ProfiledRightRestartRoot A)
  | left (source : ProfiledLeftRestartRoot A)

noncomputable instance : Fintype (ProfiledBankRootAnchor A) := by
  classical
  let Rep := Unit ⊕ ProfiledRightRestartRoot A ⊕ ProfiledLeftRestartRoot A
  let e : ProfiledBankRootAnchor A ≃ Rep :=
    { toFun := fun anchor =>
        match anchor with
        | .sink => .inl ()
        | .right source => .inr (.inl source)
        | .left source => .inr (.inr source)
      invFun := fun anchor =>
        match anchor with
        | .inl _ => .sink
        | .inr (.inl source) => .right source
        | .inr (.inr source) => .left source
      left_inv := by intro anchor; cases anchor <;> rfl
      right_inv := by
        intro anchor
        rcases anchor with empty | (right | left)
        · cases empty; rfl
        · rfl
        · rfl }
  exact Fintype.ofEquiv Rep e.symm

instance : Inhabited (ProfiledBankRootAnchor A) := ⟨.sink⟩

/-- Epoch priority of a live macro; the sink is accepting. -/
def profiledBankRootAnchorPriority : ProfiledBankRootAnchor A → Nat
  | .sink => 0
  | .right ⟨.inl key, _⟩ =>
      pairedProfiledEntryPriority A (.inr (.inl key.2.1))
  | .right ⟨.inr source, _⟩ =>
      pairedProfiledEntryPriority A (.inr (.inl source.2.1))
  | .left ⟨.inl key, _⟩ =>
      pairedProfiledEntryPriority A (.inr (.inr key.2.1))
  | .left ⟨.inr source, _⟩ =>
      pairedProfiledEntryPriority A (.inr (.inr source.2.1))

/-- The row bit is a proof-side selector for the actual objective anchor. -/
def pairedEntryRowAnchor : PairedEntryRow → Bool
  | .first => false
  | .both => true

/-- The two hidden right roots represented by one simultaneous table. -/
def profiledBankRightPairRoots
    (source : Bool → ProfiledRightRestartRoot A) :
    Finset (ProfiledBankRootAnchor A) := by
  classical
  exact { .right (source false), .right (source true) }

/-- Left mirror. -/
def profiledBankLeftPairRoots
    (source : Bool → ProfiledLeftRestartRoot A) :
    Finset (ProfiledBankRootAnchor A) := by
  classical
  exact { .left (source false), .left (source true) }

/-- Finite moves of the concrete outer automaton. -/
abbrev ProfiledBankRootMove :=
  Unit ⊕ (ProfiledRightFamilyPairMove A ⊕ ProfiledLeftFamilyPairMove A)

noncomputable instance : Fintype (ProfiledBankRootMove A) := by
  classical
  infer_instance

/-- A live move is valid exactly when its simultaneous table wins the
combined two-root monitor. -/
def ProfiledBankRootMove.Valid : ProfiledBankRootMove A → Prop
  | .inl _ => True
  | .inr (.inl move) =>
      NarrowedAllThreadsWin
        (finiteRootFamilyMonitor
          (profiledRightFamilyRootMonitors A move.1))
        move.2.toTransitionRationalTree.labeledTree
  | .inr (.inr move) =>
      NarrowedAllThreadsWin
        (finiteRootFamilyMonitor
          (profiledLeftFamilyRootMonitors A move.1))
        move.2.toTransitionRationalTree.labeledTree

/-- Root family consumed by a concrete outer move. -/
def ProfiledBankRootMove.roots : ProfiledBankRootMove A →
    Finset (ProfiledBankRootAnchor A)
  | .inl _ => {.sink}
  | .inr (.inl move) => profiledBankRightPairRoots A move.1
  | .inr (.inr move) => profiledBankLeftPairRoots A move.1

/-- Certified right-to-left child of one valid pair move. -/
noncomputable def profiledBankRightPairMoveChild
    (move : ProfiledRightFamilyPairMove A) (hvalid :
      ProfiledBankRootMove.Valid A (.inr (.inl move)))
    (anchor : Bool) (row : PairedEntryRow)
    (past : List (In₂ × In₁)) (input : In₂ × In₁) :
    ProfiledBankLeftMacro A :=
  profiledRightFamilyRootChild A move.1
    move.2.toTransitionRationalTree hvalid anchor
    (omegaOfList (past ++ [input])) past.length row

/-- Left-to-right mirror. -/
noncomputable def profiledBankLeftPairMoveChild
    (move : ProfiledLeftFamilyPairMove A) (hvalid :
      ProfiledBankRootMove.Valid A (.inr (.inr move)))
    (anchor : Bool) (row : PairedEntryRow)
    (past : List (In₁ × In₂)) (input : In₁ × In₂) :
    ProfiledBankRightMacro A :=
  profiledLeftFamilyRootChild A move.1
    move.2.toTransitionRationalTree hvalid anchor
    (omegaOfList (past ++ [input])) past.length row

/-- Complete successor assignment of a concrete move.  A wrong-orientation
direction goes to the accepting sink. -/
noncomputable def ProfiledBankRootMove.successor
    (move : ProfiledBankRootMove A) :
    TwoSortedFamilySuccessor (ProfiledBankRootAnchor A)
      (PairedEntryDirection (In₁ := In₁) (In₂ := In₂)) := by
  classical
  by_cases hvalid : move.Valid A
  · exact fun direction =>
      match move, direction with
      | .inl _, _ => (.sink, {.sink})
      | .inr (.inl right), .fromOne row past input =>
          let child := fun anchor =>
            profiledBankRightPairMoveChild A right hvalid anchor row past input
          (.right (right.1 (pairedEntryRowAnchor row)),
            {.left ⟨.inr (child false),
                (profiledBankLeftMonitor A (child false)).initial⟩,
              .left ⟨.inr (child true),
                (profiledBankLeftMonitor A (child true)).initial⟩})
      | .inr (.inl _), .fromTwo _ _ _ => (.sink, {.sink})
      | .inr (.inr left), .fromTwo row past input =>
          let child := fun anchor =>
            profiledBankLeftPairMoveChild A left hvalid anchor row past input
          (.left (left.1 (pairedEntryRowAnchor row)),
            {.right ⟨.inr (child false),
                (profiledBankRightMonitor A (child false)).initial⟩,
              .right ⟨.inr (child true),
                (profiledBankRightMonitor A (child true)).initial⟩})
      | .inr (.inr _), .fromOne _ _ _ => (.sink, {.sink})
  · exact fun _ => (.sink, {.sink})

/-- Concrete transition relation consumed by the two-sorted family
automaton.  The finite table is existential proof data recoverable at a
reachable outer state; it is not revealed to a process as a leader tag. -/
def ProfiledBankRootFamilyAllowed
    (roots : Finset (ProfiledBankRootAnchor A))
    (next : TwoSortedFamilySuccessor (ProfiledBankRootAnchor A)
      (PairedEntryDirection (In₁ := In₁) (In₂ := In₂))) : Prop :=
  ∃ move : ProfiledBankRootMove A,
    move.Valid A ∧ move.roots A = roots ∧ move.successor A = next

/-- The fully concrete finite-state outer run automaton. -/
noncomputable abbrev profiledBankRootFamilyRunAutomaton
    (initialRoots : Finset (ProfiledBankRootAnchor A)) :=
  twoSortedFamilyRunAutomaton (profiledBankRootAnchorPriority A) initialRoots
    (ProfiledBankRootFamilyAllowed A)

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- At a reachable family state of a rational outer policy, one valid finite
simultaneous table governs both hidden roots. -/
theorem exists_valid_rootFamilyMove_at_reachable
    (initialRoots : Finset (ProfiledBankRootAnchor A))
    (policy : InputFreeRunParityTreeAutomaton.RationalTransitionPolicy
      (profiledBankRootFamilyRunAutomaton A initialRoots))
    (roots : Finset (ProfiledBankRootAnchor A))
    (hreachable : TwoSortedFamilyPolicy.Reachable
      (profiledBankRootAnchorPriority A) initialRoots
      (ProfiledBankRootFamilyAllowed A) policy roots) :
    ∃ move : ProfiledBankRootMove A,
      move.Valid A ∧ move.roots A = roots ∧
      ∀ direction,
        policy.successor (TwoSortedFamilyState.family roots) direction =
          TwoSortedFamilyState.chosen (move.successor A direction).1
            (move.successor A direction).2 := by
  obtain ⟨next, hallowed, hnext⟩ :=
    TwoSortedFamilyPolicy.exists_shared_family_transition
      (profiledBankRootAnchorPriority A) initialRoots
      (ProfiledBankRootFamilyAllowed A) policy roots hreachable
  rcases hallowed with ⟨move, hvalid, hroots, rfl⟩
  exact ⟨move, hvalid, hroots, hnext⟩

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- Concrete rationalization endpoint for the recursive mixed-root
construction.  The raw transition may depend on the complete semantic
history.  Once its reachable family steps are witnessed by the finite moves
above and its selected epoch priorities accept, the standard input-free
rational-run basis replaces it by a finite outer policy.  No stabilization,
Nerode fixed point, leader bit, or state-based raw assignment is assumed. -/
theorem nonempty_profiledBankRootFamilyRationalPolicy_of_history
    (initialRoots : Finset (ProfiledBankRootAnchor A))
    (nextAt : TreeNode
        (PairedEntryDirection (In₁ := In₁) (In₂ := In₂)) →
      Finset (ProfiledBankRootAnchor A) →
      TwoSortedFamilySuccessor (ProfiledBankRootAnchor A)
        (PairedEntryDirection (In₁ := In₁) (In₂ := In₂)))
    (hallowed : ∀ node roots,
      TwoSortedFamilyPolicy.historyRun initialRoots nextAt node =
          .family roots →
        ProfiledBankRootFamilyAllowed A roots (nextAt node roots))
    (hparity : ∀ branch : Nat →
        PairedEntryDirection (In₁ := In₁) (In₂ := In₂),
      NatSeqMinEvenParity (fun n =>
        profiledBankRootAnchorPriority A
          (TwoSortedFamilyPolicy.historySelectedDescriptor initialRoots
            nextAt branch n)))
    (basis : InputFreeRunParityTreeAutomaton.RationalRunBasis
      (profiledBankRootFamilyRunAutomaton A initialRoots)) :
    Nonempty (InputFreeRunParityTreeAutomaton.RationalTransitionPolicy
      (profiledBankRootFamilyRunAutomaton A initialRoots)) := by
  exact TwoSortedFamilyPolicy.nonempty_rationalPolicy_of_historyAssignment
    (profiledBankRootAnchorPriority A) initialRoots
    (ProfiledBankRootFamilyAllowed A) nextAt hallowed hparity basis

end


end


end DetParityAutomaton

end DistributedSynthesis
