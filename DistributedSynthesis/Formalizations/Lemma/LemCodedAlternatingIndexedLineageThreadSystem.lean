/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemIndexedLineageThreadSystem

/-!
# Coded alternating indexed-lineage monitor

This is the two-shadow form needed at delay-one hierarchy reversals.  The
finite monitor retains the public belief code and, invisibly to the
processes, one initial side and one persistent lineage.  A step from the
right shadow enters the left shadow and conversely.  Later hidden resolutions
are ignored, so neither an equal-root merge nor an arbitrary controller can
change the selected lineage.

The side is an objective-monitor coordinate only.  It is not an observation,
leader flag, or strategy input.  The public letter remains just
`Move × Direction`, exactly as required by the source-free belief-node
rationalization.
-/

namespace DistributedSynthesis

universe c i r m d

namespace DetParityAutomaton

/-- The two proof-side shadows of one alternating reversal construction. -/
inductive IndexedLineageSide where
  | right
  | left
deriving DecidableEq, Fintype

def IndexedLineageSide.other : IndexedLineageSide → IndexedLineageSide
  | .right => .left
  | .left => .right

@[simp] theorem IndexedLineageSide.other_other (side : IndexedLineageSide) :
    side.other.other = side := by
  cases side <;> rfl

/-- Hidden alternating-lineage coordinate.  The finite public belief code is
stored separately in the complete thread-system state. -/
inductive AlternatingIndexedLineageThreadState
    (I : Type i) (Root : Type r) where
  | initial
  | live (side : IndexedLineageSide) (lineage : I) (root : Root)
  | dead

noncomputable instance alternatingIndexedLineageThreadStateFintype
    {I : Type i} {Root : Type r} [Fintype I] [Fintype Root] :
    Fintype (AlternatingIndexedLineageThreadState I Root) := by
  classical
  let Rep := Bool ⊕ (IndexedLineageSide × I × Root)
  let e : AlternatingIndexedLineageThreadState I Root ≃ Rep :=
    { toFun := fun state =>
        match state with
        | .initial => .inl false
        | .dead => .inl true
        | .live side lineage root => .inr (side, lineage, root)
      invFun := fun state =>
        match state with
        | .inl false => .initial
        | .inl true => .dead
        | .inr value => .live value.1 value.2.1 value.2.2
      left_inv := by intro state; cases state <;> rfl
      right_inv := by
        intro state
        rcases state with bit | value
        · cases bit <;> rfl
        · rcases value with ⟨side, lineage, root⟩
          rfl }
  exact Fintype.ofEquiv Rep e.symm

/-- One coded alternating step.  `currentSlots` and `childCode` are total
finite functions.  Invalid or absent slots lead to the even dead state. -/
noncomputable def codedAlternatingIndexedLineageStep
    {Code : Type c} {I : Type i} {Root : Type r}
    {Move : Type m} {Direction : Type d}
    (next : Code → Move → Direction → Code)
    (currentSlots : IndexedLineageSide → Code → I → Option Root)
    (childCode : IndexedLineageSide → Code → Move → Direction →
      IndexedLineageChildCode I Root)
    (state : Code × AlternatingIndexedLineageThreadState I Root)
    (letter : Move × Direction)
    (resolution : IndexedLineageSide × I) :
    Code × AlternatingIndexedLineageThreadState I Root := by
  classical
  let nextBelief := next state.1 letter.1 letter.2
  let advance := fun (side : IndexedLineageSide) (lineage : I)
      (expected : Option Root) =>
    if currentSlots side state.1 lineage = expected then
      match childCode side state.1 letter.1 letter.2 lineage with
      | none => AlternatingIndexedLineageThreadState.dead
      | some (_, child) => .live side.other lineage child
    else .dead
  exact (nextBelief,
    match state.2 with
    | .initial =>
        match currentSlots resolution.1 state.1 resolution.2 with
        | none => .dead
        | some root => advance resolution.1 resolution.2 (some root)
    | .live side lineage root => advance side lineage (some root)
    | .dead => .dead)

/-- Finite thread system over the source-free public alphabet. -/
noncomputable def codedAlternatingIndexedLineageThreadSystem
    {Code : Type c} {I : Type i} {Root : Type r}
    {Move : Type m} {Direction : Type d}
    [Fintype Code] [Fintype I] [Fintype Root]
    (initialCode : Code)
    (next : Code → Move → Direction → Code)
    (currentSlots : IndexedLineageSide → Code → I → Option Root)
    (childCode : IndexedLineageSide → Code → Move → Direction →
      IndexedLineageChildCode I Root)
    (rootPriority : Root → Nat) : FiniteThreadSystem (Move × Direction) where
  State := Code × AlternatingIndexedLineageThreadState I Root
  stateFinite := inferInstance
  initial := (initialCode, .initial)
  Resolution := IndexedLineageSide × I
  step := codedAlternatingIndexedLineageStep next currentSlots childCode
  priority := fun state =>
    match state.2 with
    | .initial | .dead => 0
    | .live _ _ root => rootPriority root

/-- Both components start a present lineage and immediately enter the
opposite shadow. -/
theorem codedAlternatingIndexedLineageStep_initial_of
    {Code : Type c} {I : Type i} {Root : Type r}
    {Move : Type m} {Direction : Type d}
    (next : Code → Move → Direction → Code)
    (currentSlots : IndexedLineageSide → Code → I → Option Root)
    (childCode : IndexedLineageSide → Code → Move → Direction →
      IndexedLineageChildCode I Root)
    (code : Code) (move : Move) (direction : Direction)
    (side : IndexedLineageSide) (lineage : I)
    (root child : Root) (row : PairedEntryRow)
    (hcurrent : currentSlots side code lineage = some root)
    (hchild : childCode side code move direction lineage =
      some (row, child)) :
    codedAlternatingIndexedLineageStep next currentSlots childCode
        (code, .initial) (move, direction) (side, lineage) =
      (next code move direction, .live side.other lineage child) := by
  simp [codedAlternatingIndexedLineageStep, hcurrent, hchild]

/-- A live step retains the lineage and alternates the side. -/
theorem codedAlternatingIndexedLineageStep_live_of
    {Code : Type c} {I : Type i} {Root : Type r}
    {Move : Type m} {Direction : Type d}
    (next : Code → Move → Direction → Code)
    (currentSlots : IndexedLineageSide → Code → I → Option Root)
    (childCode : IndexedLineageSide → Code → Move → Direction →
      IndexedLineageChildCode I Root)
    (code : Code) (move : Move) (direction : Direction)
    (side : IndexedLineageSide) (lineage : I)
    (root child : Root) (row : PairedEntryRow)
    (resolution : IndexedLineageSide × I)
    (hcurrent : currentSlots side code lineage = some root)
    (hchild : childCode side code move direction lineage =
      some (row, child)) :
    codedAlternatingIndexedLineageStep next currentSlots childCode
        (code, .live side lineage root) (move, direction) resolution =
      (next code move direction, .live side.other lineage child) := by
  simp [codedAlternatingIndexedLineageStep, hcurrent, hchild]

/-- After the initial step the resolution cannot affect either the public
code or the hidden thread. -/
theorem codedAlternatingIndexedLineageStep_resolution_irrel_of_ne_initial
    {Code : Type c} {I : Type i} {Root : Type r}
    {Move : Type m} {Direction : Type d}
    (next : Code → Move → Direction → Code)
    (currentSlots : IndexedLineageSide → Code → I → Option Root)
    (childCode : IndexedLineageSide → Code → Move → Direction →
      IndexedLineageChildCode I Root)
    (state : Code × AlternatingIndexedLineageThreadState I Root)
    (letter : Move × Direction)
    (hne : state.2 ≠ .initial)
    (left right : IndexedLineageSide × I) :
    codedAlternatingIndexedLineageStep next currentSlots childCode state
        letter left =
      codedAlternatingIndexedLineageStep next currentSlots childCode state
        letter right := by
  cases hstate : state.2 with
  | initial => exact absurd hstate hne
  | live => simp [codedAlternatingIndexedLineageStep, hstate]
  | dead => simp [codedAlternatingIndexedLineageStep, hstate]

/-- Every step leaves the one-use hidden initial state. -/
theorem codedAlternatingIndexedLineageStep_thread_ne_initial
    {Code : Type c} {I : Type i} {Root : Type r}
    {Move : Type m} {Direction : Type d}
    (next : Code → Move → Direction → Code)
    (currentSlots : IndexedLineageSide → Code → I → Option Root)
    (childCode : IndexedLineageSide → Code → Move → Direction →
      IndexedLineageChildCode I Root)
    (state : Code × AlternatingIndexedLineageThreadState I Root)
    (letter : Move × Direction) (resolution : IndexedLineageSide × I) :
    (codedAlternatingIndexedLineageStep next currentSlots childCode state
      letter resolution).2 ≠ .initial := by
  classical
  cases hstate : state.2 with
  | initial =>
      rcases resolution with ⟨side, lineage⟩
      cases hcurrent : currentSlots side state.1 lineage with
      | none =>
          simp [codedAlternatingIndexedLineageStep, hstate, hcurrent]
      | some root =>
          cases hchild : childCode side state.1 letter.1 letter.2 lineage with
          | none =>
              simp [codedAlternatingIndexedLineageStep, hstate, hcurrent,
                hchild]
          | some value =>
              rcases value with ⟨row, child⟩
              simp [codedAlternatingIndexedLineageStep, hstate, hcurrent,
                hchild]
  | live side lineage root =>
      by_cases hcurrent : currentSlots side state.1 lineage = some root
      · cases hchild : childCode side state.1 letter.1 letter.2 lineage with
        | none =>
            simp [codedAlternatingIndexedLineageStep, hstate, hcurrent,
              hchild]
        | some value =>
            rcases value with ⟨row, child⟩
            simp [codedAlternatingIndexedLineageStep, hstate, hcurrent,
              hchild]
      · simp [codedAlternatingIndexedLineageStep, hstate, hcurrent]
  | dead => simp [codedAlternatingIndexedLineageStep, hstate]

/-- Canonical evolution for one initially selected side and lineage. -/
noncomputable def codedAlternatingIndexedLineageRun
    {Code : Type c} {I : Type i} {Root : Type r}
    {Move : Type m} {Direction : Type d}
    (initialCode : Code)
    (next : Code → Move → Direction → Code)
    (currentSlots : IndexedLineageSide → Code → I → Option Root)
    (childCode : IndexedLineageSide → Code → Move → Direction →
      IndexedLineageChildCode I Root)
    (word : OmegaWord (Move × Direction))
    (initialSide : IndexedLineageSide) (lineage : I) :
    Nat → Code × AlternatingIndexedLineageThreadState I Root
  | 0 => (initialCode, .initial)
  | n + 1 => codedAlternatingIndexedLineageStep next currentSlots childCode
      (codedAlternatingIndexedLineageRun initialCode next currentSlots
        childCode word initialSide lineage n)
      (word n) (initialSide, lineage)

@[simp] theorem codedAlternatingIndexedLineageRun_zero
    {Code : Type c} {I : Type i} {Root : Type r}
    {Move : Type m} {Direction : Type d}
    (initialCode : Code)
    (next : Code → Move → Direction → Code)
    (currentSlots : IndexedLineageSide → Code → I → Option Root)
    (childCode : IndexedLineageSide → Code → Move → Direction →
      IndexedLineageChildCode I Root)
    (word : OmegaWord (Move × Direction))
    (initialSide : IndexedLineageSide) (lineage : I) :
    codedAlternatingIndexedLineageRun initialCode next currentSlots childCode
        word initialSide lineage 0 =
      (initialCode, .initial) :=
  rfl

@[simp] theorem codedAlternatingIndexedLineageRun_succ
    {Code : Type c} {I : Type i} {Root : Type r}
    {Move : Type m} {Direction : Type d}
    (initialCode : Code)
    (next : Code → Move → Direction → Code)
    (currentSlots : IndexedLineageSide → Code → I → Option Root)
    (childCode : IndexedLineageSide → Code → Move → Direction →
      IndexedLineageChildCode I Root)
    (word : OmegaWord (Move × Direction))
    (initialSide : IndexedLineageSide) (lineage : I) (n : Nat) :
    codedAlternatingIndexedLineageRun initialCode next currentSlots childCode
        word initialSide lineage (n + 1) =
      codedAlternatingIndexedLineageStep next currentSlots childCode
        (codedAlternatingIndexedLineageRun initialCode next currentSlots
          childCode word initialSide lineage n)
        (word n) (initialSide, lineage) :=
  rfl

/-- Deterministic public-code evolution along a word. -/
def codedAlternatingBeliefCodeRun
    {Code : Type c} {Move : Type m} {Direction : Type d}
    (initialCode : Code)
    (next : Code → Move → Direction → Code)
    (word : OmegaWord (Move × Direction)) : Nat → Code
  | 0 => initialCode
  | n + 1 => next (codedAlternatingBeliefCodeRun initialCode next word n)
      (word n).1 (word n).2

@[simp] theorem codedAlternatingBeliefCodeRun_zero
    {Code : Type c} {Move : Type m} {Direction : Type d}
    (initialCode : Code)
    (next : Code → Move → Direction → Code)
    (word : OmegaWord (Move × Direction)) :
    codedAlternatingBeliefCodeRun initialCode next word 0 = initialCode :=
  rfl

@[simp] theorem codedAlternatingBeliefCodeRun_succ
    {Code : Type c} {Move : Type m} {Direction : Type d}
    (initialCode : Code)
    (next : Code → Move → Direction → Code)
    (word : OmegaWord (Move × Direction)) (n : Nat) :
    codedAlternatingBeliefCodeRun initialCode next word (n + 1) =
      next (codedAlternatingBeliefCodeRun initialCode next word n)
        (word n).1 (word n).2 :=
  rfl

/-- The public code carried by a hidden thread is independent of its hidden
initial side and lineage. -/
theorem codedAlternatingIndexedLineageRun_fst
    {Code : Type c} {I : Type i} {Root : Type r}
    {Move : Type m} {Direction : Type d}
    (initialCode : Code)
    (next : Code → Move → Direction → Code)
    (currentSlots : IndexedLineageSide → Code → I → Option Root)
    (childCode : IndexedLineageSide → Code → Move → Direction →
      IndexedLineageChildCode I Root)
    (word : OmegaWord (Move × Direction))
    (initialSide : IndexedLineageSide) (lineage : I) (n : Nat) :
    (codedAlternatingIndexedLineageRun initialCode next currentSlots childCode
      word initialSide lineage n).1 =
      codedAlternatingBeliefCodeRun initialCode next word n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [codedAlternatingIndexedLineageRun_succ,
        codedAlternatingBeliefCodeRun_succ]
      simp only [codedAlternatingIndexedLineageStep]
      rw [ih]

/-- An initially absent lineage enters the dead state on the first step and
can never be resurrected by later public codes. -/
theorem codedAlternatingIndexedLineageRun_dead_of_initial_none
    {Code : Type c} {I : Type i} {Root : Type r}
    {Move : Type m} {Direction : Type d}
    (initialCode : Code)
    (next : Code → Move → Direction → Code)
    (currentSlots : IndexedLineageSide → Code → I → Option Root)
    (childCode : IndexedLineageSide → Code → Move → Direction →
      IndexedLineageChildCode I Root)
    (word : OmegaWord (Move × Direction))
    (initialSide : IndexedLineageSide) (lineage : I)
    (hnone : currentSlots initialSide initialCode lineage = none) (n : Nat) :
    (codedAlternatingIndexedLineageRun initialCode next currentSlots childCode
      word initialSide lineage (n + 1)).2 = .dead := by
  induction n with
  | zero =>
      simp [codedAlternatingIndexedLineageRun_succ,
        codedAlternatingIndexedLineageStep, hnone]
  | succ n ih =>
      rw [codedAlternatingIndexedLineageRun_succ]
      cases hrun : codedAlternatingIndexedLineageRun initialCode next
          currentSlots childCode word initialSide lineage (n + 1) with
      | mk code thread =>
          have hthread : thread = .dead := by
            rw [hrun] at ih
            exact ih
          subst thread
          rfl

/-- Inactive padded slots are semantically harmless: their complete hidden
run has constant even priority zero. -/
theorem codedAlternatingIndexedLineageRun_minEven_of_initial_none
    {Code : Type c} {I : Type i} {Root : Type r}
    {Move : Type m} {Direction : Type d}
    [Fintype Code] [Fintype I] [Fintype Root]
    (initialCode : Code)
    (next : Code → Move → Direction → Code)
    (currentSlots : IndexedLineageSide → Code → I → Option Root)
    (childCode : IndexedLineageSide → Code → Move → Direction →
      IndexedLineageChildCode I Root)
    (rootPriority : Root → Nat)
    (word : OmegaWord (Move × Direction))
    (initialSide : IndexedLineageSide) (lineage : I)
    (hnone : currentSlots initialSide initialCode lineage = none) :
    NatSeqMinEvenParity (fun n =>
      (codedAlternatingIndexedLineageThreadSystem initialCode next currentSlots
        childCode rootPriority).priority
        (codedAlternatingIndexedLineageRun initialCode next currentSlots
          childCode word initialSide lineage n)) := by
  have hzero : ∀ n,
      (codedAlternatingIndexedLineageThreadSystem initialCode next currentSlots
        childCode rootPriority).priority
        (codedAlternatingIndexedLineageRun initialCode next currentSlots
          childCode word initialSide lineage n) = 0 := by
    intro n
    cases n with
    | zero => rfl
    | succ n =>
        change (match
          (codedAlternatingIndexedLineageRun initialCode next currentSlots
            childCode word initialSide lineage (n + 1)).2 with
          | .initial | .dead => 0
          | .live _ _ root => rootPriority root) = 0
        rw [codedAlternatingIndexedLineageRun_dead_of_initial_none initialCode
          next currentSlots childCode word initialSide lineage hnone n]
  refine ⟨0, ⟨0, rfl⟩, ?_, ?_⟩
  · intro base
    exact ⟨base, le_rfl, hzero base⟩
  · intro priority _
    exact Nat.zero_le priority

/-- Once a canonical lineage dies, later belief-code evolution cannot bring
it back. -/
theorem codedAlternatingIndexedLineageRun_dead_persists
    {Code : Type c} {I : Type i} {Root : Type r}
    {Move : Type m} {Direction : Type d}
    (initialCode : Code)
    (next : Code → Move → Direction → Code)
    (currentSlots : IndexedLineageSide → Code → I → Option Root)
    (childCode : IndexedLineageSide → Code → Move → Direction →
      IndexedLineageChildCode I Root)
    (word : OmegaWord (Move × Direction))
    (initialSide : IndexedLineageSide) (lineage : I)
    {n : Nat}
    (hdead : (codedAlternatingIndexedLineageRun initialCode next currentSlots
      childCode word initialSide lineage n).2 = .dead) (k : Nat) :
    (codedAlternatingIndexedLineageRun initialCode next currentSlots childCode
      word initialSide lineage (n + k)).2 = .dead := by
  induction k with
  | zero => simpa using hdead
  | succ k ih =>
      rw [Nat.add_succ, codedAlternatingIndexedLineageRun_succ]
      cases hrun : codedAlternatingIndexedLineageRun initialCode next
          currentSlots childCode word initialSide lineage (n + k) with
      | mk code thread =>
          have hthread : thread = .dead := by
            rw [hrun] at ih
            exact ih
          subst thread
          rfl

/-- A lineage that ever becomes inconsistent is automatically accepting,
because the dead suffix has priority zero forever. -/
theorem codedAlternatingIndexedLineageRun_minEven_of_eventually_dead
    {Code : Type c} {I : Type i} {Root : Type r}
    {Move : Type m} {Direction : Type d}
    [Fintype Code] [Fintype I] [Fintype Root]
    (initialCode : Code)
    (next : Code → Move → Direction → Code)
    (currentSlots : IndexedLineageSide → Code → I → Option Root)
    (childCode : IndexedLineageSide → Code → Move → Direction →
      IndexedLineageChildCode I Root)
    (rootPriority : Root → Nat)
    (word : OmegaWord (Move × Direction))
    (initialSide : IndexedLineageSide) (lineage : I)
    {n : Nat}
    (hdead : (codedAlternatingIndexedLineageRun initialCode next currentSlots
      childCode word initialSide lineage n).2 = .dead) :
    NatSeqMinEvenParity (fun k =>
      (codedAlternatingIndexedLineageThreadSystem initialCode next currentSlots
        childCode rootPriority).priority
        (codedAlternatingIndexedLineageRun initialCode next currentSlots
          childCode word initialSide lineage k)) := by
  let priorities := fun k =>
    (codedAlternatingIndexedLineageThreadSystem initialCode next currentSlots
      childCode rootPriority).priority
      (codedAlternatingIndexedLineageRun initialCode next currentSlots childCode
        word initialSide lineage k)
  have hzero : ∀ k, priorities (n + k) = 0 := by
    intro k
    have hpersist := codedAlternatingIndexedLineageRun_dead_persists
      initialCode next currentSlots childCode word initialSide lineage hdead k
    change (match
      (codedAlternatingIndexedLineageRun initialCode next currentSlots
        childCode word initialSide lineage (n + k)).2 with
      | .initial | .dead => 0
      | .live _ _ root => rootPriority root) = 0
    rw [hpersist]
  have hshift : NatSeqMinEvenParity (fun k => priorities (n + k)) := by
    refine ⟨0, ⟨0, rfl⟩, ?_, ?_⟩
    · intro base
      exact ⟨base, le_rfl, hzero base⟩
    · intro priority _
      exact Nat.zero_le priority
  exact (natSeqMinEvenParity_shift priorities n).mp hshift

/-- The canonical evolution is a hidden run. -/
theorem codedAlternatingIndexedLineageRun_isRun
    {Code : Type c} {I : Type i} {Root : Type r}
    {Move : Type m} {Direction : Type d}
    [Fintype Code] [Fintype I] [Fintype Root]
    (initialCode : Code)
    (next : Code → Move → Direction → Code)
    (currentSlots : IndexedLineageSide → Code → I → Option Root)
    (childCode : IndexedLineageSide → Code → Move → Direction →
      IndexedLineageChildCode I Root)
    (rootPriority : Root → Nat)
    (word : OmegaWord (Move × Direction))
    (initialSide : IndexedLineageSide) (lineage : I) :
    (codedAlternatingIndexedLineageThreadSystem initialCode next currentSlots
      childCode rootPriority).IsRun word
        (codedAlternatingIndexedLineageRun initialCode next currentSlots
          childCode word initialSide lineage) := by
  constructor
  · rfl
  · intro n
    exact ⟨(initialSide, lineage), rfl⟩

/-- Every hidden run is the canonical evolution of its first resolution. -/
theorem codedAlternatingIndexedLineageRun_eq_of_isRun
    {Code : Type c} {I : Type i} {Root : Type r}
    {Move : Type m} {Direction : Type d}
    [Fintype Code] [Fintype I] [Fintype Root]
    (initialCode : Code)
    (next : Code → Move → Direction → Code)
    (currentSlots : IndexedLineageSide → Code → I → Option Root)
    (childCode : IndexedLineageSide → Code → Move → Direction →
      IndexedLineageChildCode I Root)
    (rootPriority : Root → Nat)
    (word : OmegaWord (Move × Direction))
    (run : Nat → Code × AlternatingIndexedLineageThreadState I Root)
    (hrun : (codedAlternatingIndexedLineageThreadSystem initialCode next
      currentSlots childCode rootPriority).IsRun word run) :
    ∃ initialSide lineage,
      run = codedAlternatingIndexedLineageRun initialCode next currentSlots
        childCode word initialSide lineage := by
  rcases hrun.2 0 with ⟨⟨initialSide, lineage⟩, hfirst⟩
  refine ⟨initialSide, lineage, funext fun n => ?_⟩
  cases n with
  | zero => exact hrun.1
  | succ n =>
      induction n with
      | zero =>
          calc
            run (0 + 1) = codedAlternatingIndexedLineageStep next currentSlots
                childCode (run 0) (word 0) (initialSide, lineage) := hfirst
            _ = codedAlternatingIndexedLineageStep next currentSlots childCode
                (codedAlternatingIndexedLineageRun initialCode next
                  currentSlots childCode word initialSide lineage 0)
                (word 0) (initialSide, lineage) := by
                  rw [hrun.1,
                    codedAlternatingIndexedLineageRun_zero]
                  rfl
      | succ n ih =>
          rcases hrun.2 (n + 1) with ⟨resolution, hnext⟩
          rw [hnext, ih]
          apply codedAlternatingIndexedLineageStep_resolution_irrel_of_ne_initial
            next currentSlots childCode _ (word (n + 1))
          · exact codedAlternatingIndexedLineageStep_thread_ne_initial
              next currentSlots childCode
              (codedAlternatingIndexedLineageRun initialCode next currentSlots
                childCode word initialSide lineage n)
              (word n) (initialSide, lineage)

/-- The universal DPA checks exactly every persistent two-shadow lineage. -/
theorem codedAlternatingIndexedLineageThreadSystem_accepts_iff
    {Code : Type c} {I : Type i} {Root : Type r}
    {Move : Type m} {Direction : Type d}
    [Fintype Code] [Fintype I] [Fintype Root]
    (initialCode : Code)
    (next : Code → Move → Direction → Code)
    (currentSlots : IndexedLineageSide → Code → I → Option Root)
    (childCode : IndexedLineageSide → Code → Move → Direction →
      IndexedLineageChildCode I Root)
    (rootPriority : Root → Nat)
    (word : OmegaWord (Move × Direction)) :
    (codedAlternatingIndexedLineageThreadSystem initialCode next currentSlots
      childCode rootPriority).universalRunDPA.Accepts word ↔
      ∀ initialSide lineage,
        NatSeqMinEvenParity (fun n =>
          (codedAlternatingIndexedLineageThreadSystem initialCode next
            currentSlots childCode rootPriority).priority
            (codedAlternatingIndexedLineageRun initialCode next currentSlots
              childCode word initialSide lineage n)) := by
  rw [(codedAlternatingIndexedLineageThreadSystem initialCode next currentSlots
    childCode rootPriority).universalRunDPA_accepts_iff]
  constructor
  · intro hall initialSide lineage
    exact hall _ (codedAlternatingIndexedLineageRun_isRun initialCode next
      currentSlots childCode rootPriority word initialSide lineage)
  · intro hall run hrun
    rcases codedAlternatingIndexedLineageRun_eq_of_isRun initialCode next
      currentSlots childCode rootPriority word run hrun with
      ⟨initialSide, lineage, rfl⟩
    exact hall initialSide lineage

end DetParityAutomaton

end DistributedSynthesis
