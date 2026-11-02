/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmPairedBoundaryProfile

/-!
# The boundary-profiled paired-entry automaton

The ordinary paired-entry automaton remembers the two DPA states and the
epoch minimum, but its transition does not relate the lambda chosen at a
parent to the lambda chosen at a child.  Independent later rationalization
can therefore destroy the output equality on an ambiguous `both` boundary.

The repair is finite.  A live state additionally stores only the first-row
informed action profile of its block.  A parent transition requires the child
profile to equal the parent's closing profile.  Both are functions between
finite types.  The raw strategy tree satisfies this strengthened transition
by `rightClosingProfile_lambdaOfStrategy` and its mirror.
-/

namespace DistributedSynthesis

universe u v x y s

namespace DetParityAutomaton

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable
  (A : DetParityAutomaton.{max u v x y, s}
    (RoundRecord In₁ In₂ Graph Out₁ Out₂))

/-- Initial action profile of a process-one-pending/right block. -/
abbrev RightInitialActionProfile := In₂ × In₁ → Out₂

/-- Initial action profile of a process-two-pending/left block. -/
abbrev LeftInitialActionProfile := In₁ × In₂ → Out₁

/-- Finite paired-entry state enriched by the one-round profile needed at the
next ambiguous boundary. -/
abbrev PairedProfiledTreeState :=
  PUnit.{1} ⊕
    (((A.State × A.State) × A.State) × RightInitialActionProfile
      (In₁ := In₁) (In₂ := In₂) (Out₂ := Out₂)) ⊕
    (((A.State × A.State) × A.State) × LeftInitialActionProfile
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁))

noncomputable instance
    [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂] :
    Fintype (PairedProfiledTreeState A) := by
  classical
  infer_instance

/-- Forget the finite boundary action profile. -/
def erasePairedProfiledState : PairedProfiledTreeState A → PairedEntryTreeState A
  | .inl _ => .inl PUnit.unit
  | .inr (.inl live) => .inr (.inl live.1)
  | .inr (.inr live) => .inr (.inr live.1)

/-- Profiled child of a process-one/right lambda. -/
def pairedProfiledOneChild
    (code : A.State × A.State)
    (lambda : ProcOnePairedRightLambda
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (row : PairedEntryRow) (past : List (In₂ × In₁))
    (move : In₂ × In₁) : PairedProfiledTreeState A :=
  let base := pairedOneChild A code lambda row past move
  match base with
  | .inr (.inr target) =>
      .inr (.inr (target, rightClosingProfile lambda row past move))
  | _ => .inl PUnit.unit

/-- Profiled child of a process-two/left lambda. -/
def pairedProfiledTwoChild
    (code : A.State × A.State)
    (lambda : ProcTwoPairedLeftLambda
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (row : PairedEntryRow) (past : List (In₁ × In₂))
    (move : In₁ × In₂) : PairedProfiledTreeState A :=
  let base := pairedTwoChild A code lambda row past move
  match base with
  | .inr (.inl target) =>
      .inr (.inl (target, leftClosingProfile lambda row past move))
  | _ => .inl PUnit.unit

@[simp] theorem erase_pairedProfiledOneChild
    (code : A.State × A.State)
    (lambda : ProcOnePairedRightLambda
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (row : PairedEntryRow) (past : List (In₂ × In₁))
    (move : In₂ × In₁) :
    erasePairedProfiledState A
        (pairedProfiledOneChild A code lambda row past move) =
      pairedOneChild A code lambda row past move := by
  cases row <;> rfl

@[simp] theorem erase_pairedProfiledTwoChild
    (code : A.State × A.State)
    (lambda : ProcTwoPairedLeftLambda
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (row : PairedEntryRow) (past : List (In₁ × In₂))
    (move : In₁ × In₂) :
    erasePairedProfiledState A
        (pairedProfiledTwoChild A code lambda row past move) =
      pairedTwoChild A code lambda row past move := by
  cases row <;> rfl

/-- Transition relation with the finite parent-to-child profile equality
built into the child state. -/
def pairedProfiledEntryDelta
    (state : PairedProfiledTreeState A)
    (_ : PUnit.{1})
    (children : PairedEntryDirection (In₁ := In₁) (In₂ := In₂) →
      PairedProfiledTreeState A) : Prop :=
  match state with
  | .inl _ => ∀ direction, children direction = .inl PUnit.unit
  | .inr (.inl live) =>
      ∃ lambda : ProcOnePairedRightLambda
          (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂),
        PairedRightForeverAccepts A live.1.1 lambda ∧
          rightInitialFirstProfile lambda = live.2 ∧
          ∀ direction, children direction =
            match direction with
            | .fromOne row past move =>
                pairedProfiledOneChild A live.1.1 lambda row past move
            | .fromTwo _ _ _ => .inl PUnit.unit
  | .inr (.inr live) =>
      ∃ lambda : ProcTwoPairedLeftLambda
          (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂),
        PairedLeftForeverAccepts A live.1.1 lambda ∧
          leftInitialFirstProfile lambda = live.2 ∧
          ∀ direction, children direction =
            match direction with
            | .fromOne _ _ _ => .inl PUnit.unit
            | .fromTwo row past move =>
                pairedProfiledTwoChild A live.1.1 lambda row past move

/-- The old epoch priority ignores the added finite action profile. -/
def pairedProfiledEntryPriority (state : PairedProfiledTreeState A) : Nat :=
  pairedEntryPriority A (erasePairedProfiledState A state)

/-- The strengthened input-free paired-entry automaton. -/
noncomputable def pairedProfiledEntryRunAutomaton
    [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
    (initialState : PairedProfiledTreeState A) :
    InputFreeRunParityTreeAutomaton.{max u v, max u v x y s}
      (PairedEntryDirection (In₁ := In₁) (In₂ := In₂)) where
  State := PairedProfiledTreeState A
  stateFinite := inferInstance
  initial := initialState
  delta := pairedProfiledEntryDelta A
  priority := pairedProfiledEntryPriority A

/-! ## The profiled run supplied by a raw distributed strategy -/

namespace PairedStrategyMemory

variable {A}
variable {strategy : StrategyPair In₁ In₂ Out₁ Out₂}

/-- Add the finite initial action profile to raw operational memory. -/
def toProfiledTreeState
    [Inhabited In₁] [Inhabited In₂] :
    PairedStrategyMemory A strategy → PairedProfiledTreeState A
  | .sink => .inl PUnit.unit
  | .processOne entry minimum =>
      .inr (.inl ((entry.code, minimum),
        rightInitialFirstProfile entry.lambdaOfStrategy))
  | .processTwo entry minimum =>
      .inr (.inr ((entry.code, minimum),
        leftInitialFirstProfile entry.lambdaOfStrategy))

@[simp] theorem erase_toProfiledTreeState
    [Inhabited In₁] [Inhabited In₂]
    (memory : PairedStrategyMemory A strategy) :
    erasePairedProfiledState A (toProfiledTreeState (A := A) memory) =
      memory.toTreeState := by
  cases memory <;> rfl

/-- The operational step preserves not only the old paired state but also the
finite boundary profile. -/
theorem toProfiledTreeState_step
    [Inhabited In₁] [Inhabited In₂]
    (memory : PairedStrategyMemory A strategy)
    (direction : PairedEntryDirection (In₁ := In₁) (In₂ := In₂)) :
    toProfiledTreeState (A := A) (memory.step (A := A) direction) =
      match memory with
      | .sink => .inl PUnit.unit
      | .processOne entry _ =>
          match direction with
          | .fromOne row past move =>
              pairedProfiledOneChild A entry.code entry.lambdaOfStrategy
                row past move
          | .fromTwo _ _ _ => .inl PUnit.unit
      | .processTwo entry _ =>
          match direction with
          | .fromOne _ _ _ => .inl PUnit.unit
          | .fromTwo row past move =>
              pairedProfiledTwoChild A entry.code entry.lambdaOfStrategy
                row past move := by
  cases memory with
  | sink => rfl
  | processOne entry minimum =>
      cases direction with
      | fromTwo row past move => rfl
      | fromOne row past move =>
          cases row <;>
            simp [step, toProfiledTreeState, pairedProfiledOneChild,
              pairedOneChild,
              pairedRightFreshChildCodeLeft_lambdaOfStrategy,
              pairedRightFreshChildCodeBoth_lambdaOfStrategy,
              rightClosingProfile_lambdaOfStrategy]
  | processTwo entry minimum =>
      cases direction with
      | fromOne row past move => rfl
      | fromTwo row past move =>
          cases row <;>
            simp [step, toProfiledTreeState, pairedProfiledTwoChild,
              pairedTwoChild,
              pairedLeftFreshChildCodeRight_lambdaOfStrategy,
              pairedLeftFreshChildCodeBoth_lambdaOfStrategy,
              leftClosingProfile_lambdaOfStrategy]

/-- The raw strategy run with its finite boundary profile retained. -/
def profiledRun
    [Inhabited In₁] [Inhabited In₂]
    (initial : PairedStrategyMemory A strategy) :
    TreeNode (PairedEntryDirection (In₁ := In₁) (In₂ := In₂)) →
      PairedProfiledTreeState A :=
  fun node => toProfiledTreeState (A := A) (atNode (A := A) initial node)

@[simp] theorem erase_profiledRun
    [Inhabited In₁] [Inhabited In₂]
    (initial : PairedStrategyMemory A strategy)
    (node : TreeNode (PairedEntryDirection (In₁ := In₁) (In₂ := In₂))) :
    erasePairedProfiledState A (profiledRun (A := A) initial node) =
      run (A := A) initial node := by
  simp [profiledRun, run]

/-- The strategy-generated run is legal for the strengthened profiled
automaton. -/
theorem profiledIsRun
    [Inhabited In₁] [Inhabited In₂]
    [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
    (initial : PairedStrategyMemory A strategy)
    (hforever : ForeverAccepts (A := A) initial) :
    (pairedProfiledEntryRunAutomaton A
      (toProfiledTreeState (A := A) initial)).IsRun
        InputFreeRunParityTreeAutomaton.uniqueTree
        (profiledRun (A := A) initial) := by
  constructor
  · rfl
  · intro node
    change pairedProfiledEntryDelta A
      (toProfiledTreeState (A := A) (atNode (A := A) initial node))
      (PUnit.unit : PUnit.{1})
      (fun direction => profiledRun (A := A) initial (node ++ [direction]))
    cases hmemory : atNode (A := A) initial node with
    | sink =>
        simp only [toProfiledTreeState, pairedProfiledEntryDelta]
        intro direction
        rw [profiledRun, atNode_append, hmemory, toProfiledTreeState_step]
    | processOne entry minimum =>
        simp only [toProfiledTreeState, pairedProfiledEntryDelta]
        refine ⟨entry.lambdaOfStrategy, ?_, rfl, ?_⟩
        · simpa [ForeverAccepts, hmemory] using hforever node
        · intro direction
          rw [profiledRun, atNode_append, toProfiledTreeState_step, hmemory]
    | processTwo entry minimum =>
        simp only [toProfiledTreeState, pairedProfiledEntryDelta]
        refine ⟨entry.lambdaOfStrategy, ?_, rfl, ?_⟩
        · simpa [ForeverAccepts, hmemory] using hforever node
        · intro direction
          rw [profiledRun, atNode_append, toProfiledTreeState_step, hmemory]

/-- The added profile does not change the priority sequence. -/
theorem profiledIsAcceptingRun
    [Inhabited In₁] [Inhabited In₂]
    [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
    (initial : PairedStrategyMemory A strategy)
    (hforever : ForeverAccepts (A := A) initial)
    (hswitching : SwitchingAccepts (A := A) initial) :
    (pairedProfiledEntryRunAutomaton A
      (toProfiledTreeState (A := A) initial)).IsAcceptingRun
        InputFreeRunParityTreeAutomaton.uniqueTree
        (profiledRun (A := A) initial) := by
  refine ⟨profiledIsRun (A := A) initial hforever, ?_⟩
  intro branch
  simpa [pairedProfiledEntryRunAutomaton, pairedProfiledEntryPriority,
    profiledRun, SwitchingAccepts, run] using hswitching branch

/-- Hence the strengthened input-free language is nonempty. -/
theorem profiledNonemptyLanguage
    [Inhabited In₁] [Inhabited In₂]
    [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
    (initial : PairedStrategyMemory A strategy)
    (hforever : ForeverAccepts (A := A) initial)
    (hswitching : SwitchingAccepts (A := A) initial) :
    (pairedProfiledEntryRunAutomaton A
      (toProfiledTreeState (A := A) initial)).NonemptyLanguage :=
  ⟨profiledRun (A := A) initial,
    profiledIsAcceptingRun (A := A) initial hforever hswitching⟩

/-- Apply the classical input-free rational-run basis after the finite profile
has been installed. -/
theorem profiledHasRationalRun
    [Inhabited In₁] [Inhabited In₂]
    [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
    (initial : PairedStrategyMemory A strategy)
    (basis : (pairedProfiledEntryRunAutomaton A
      (toProfiledTreeState (A := A) initial)).RationalRunBasis)
    (hforever : ForeverAccepts (A := A) initial)
    (hswitching : SwitchingAccepts (A := A) initial) :
    (pairedProfiledEntryRunAutomaton A
      (toProfiledTreeState (A := A) initial)).HasRationalRun :=
  basis (profiledNonemptyLanguage (A := A) initial hforever hswitching)

end PairedStrategyMemory

end DetParityAutomaton

end DistributedSynthesis
