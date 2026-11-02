/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledOpenProvenanceDistinguishedStreamAcceptance
import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledOpenIndexedBeliefThreadSystem

/-!
# Active-lineage persistence in the indexed code stream

The indexed successor never resurrects an absent lineage: after swapping
sides, the child's active-lineage carrier is a subset of the parent's carrier.
Conversely, an active reflexive pivot gives the raw gated child one root;
root deduplication may change its representative lineage but preserves that
root, so the opposite child carrier remains nonempty.

Along an alternating infinite stream these two facts give a descending chain
of nonempty finite lineage carriers.  Hence one fixed lineage belongs to every
carrier.  The pivot hypothesis is explicit.  In particular, query constructors
which currently use `(default, row)` do not by themselves prove that this
pivot is active; the final section names the proof-side selector obligation
needed to instantiate the theorem.  No process observes that selector.
-/

namespace DistributedSynthesis

universe i u v x y s

namespace DetParityAutomaton

variable {I : Type i}
variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable
  (A : DetParityAutomaton.{max u v x y, s}
    (RoundRecord In₁ In₂ Graph Out₁ Out₂))

noncomputable section

variable [Fintype I] [Inhabited I]
variable [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁]
  [Inhabited Out₂]
variable [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
variable [DecidableEq In₁] [DecidableEq In₂]

/-! ## Finite active carriers and no resurrection -/

/-- Active persistent lineage indices on one side of a finite code. -/
noncomputable def profiledOpenIndexedActiveLineageCarrier
    (side : IndexedLineageSide)
    (code : ProfiledOpenIndexedBiBeliefCode A (I := I)) : Finset I := by
  classical
  exact Finset.univ.filter fun lineage ↦
    profiledOpenIndexedBiBeliefCurrentSlots A side code lineage ≠ none

omit [Inhabited I] [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]
    [DecidableEq In₁] [DecidableEq In₂] in
@[simp] theorem mem_profiledOpenIndexedActiveLineageCarrier_iff
    (side : IndexedLineageSide)
    (code : ProfiledOpenIndexedBiBeliefCode A (I := I)) (lineage : I) :
    lineage ∈ profiledOpenIndexedActiveLineageCarrier A side code ↔
      profiledOpenIndexedBiBeliefCurrentSlots A side code lineage ≠ none := by
  classical
  simp [profiledOpenIndexedActiveLineageCarrier]

omit [Inhabited I] [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
/-- Code-level no-resurrection, in the carrier-inclusion form used by the
infinite argument. -/
theorem profiledOpenIndexedActiveLineageCarrier_next_other_subset
    (code : ProfiledOpenIndexedBiBeliefCode A (I := I))
    (move : ProfiledOpenIndexedBiBeliefMove A)
    (direction : ProfiledOpenIndexedBiBeliefDirection
      (I := I) (In₁ := In₁) (In₂ := In₂))
    (side : IndexedLineageSide) :
    profiledOpenIndexedActiveLineageCarrier A side.other
        (profiledOpenIndexedBiBeliefNext A code move direction) ⊆
      profiledOpenIndexedActiveLineageCarrier A side code := by
  intro lineage hchild
  rw [mem_profiledOpenIndexedActiveLineageCarrier_iff] at hchild ⊢
  cases side with
  | right =>
      simp only [IndexedLineageSide.other,
        profiledOpenIndexedBiBeliefCurrentSlots_left] at hchild
      simp only [profiledOpenIndexedBiBeliefCurrentSlots_right]
      intro hnone
      exact hchild
        (profiledOpenIndexedBiBeliefNext_left_none_of_right_none A code move
          direction lineage hnone)
  | left =>
      simp only [IndexedLineageSide.other,
        profiledOpenIndexedBiBeliefCurrentSlots_right] at hchild
      simp only [profiledOpenIndexedBiBeliefCurrentSlots_left]
      intro hnone
      exact hchild
        (profiledOpenIndexedBiBeliefNext_right_none_of_left_none A code move
          direction lineage hnone)

/-! ## Active reflexive pivots keep the child carrier nonempty -/

/-- Side-specific active-pivot condition on a candidate, independent of any
particular raw direction.  This is the proof-side selector interface used to
construct the next finite tag. -/
def ProfiledOpenIndexedActiveReflexivePivotAt
    (code : ProfiledOpenIndexedBiBeliefCode A (I := I))
    (side : IndexedLineageSide) (pivot : IndexedLineageCandidate I) : Prop :=
  match side with
  | .right =>
      code.rightSlots pivot.1 ≠ none ∧
        code.rightPattern.RowFunctionalAt pivot ∧
        code.rightPattern pivot pivot = true
  | .left =>
      code.leftSlots pivot.1 ≠ none ∧
        code.leftPattern.RowFunctionalAt pivot ∧
        code.leftPattern pivot pivot = true

/-- The exact source-side condition needed to keep one alternating carrier
alive.  Row-functionality handles the `.both` tie-break; reflexivity inserts
the pivot in its own gated class. -/
def ProfiledOpenIndexedActiveReflexivePivot
    (code : ProfiledOpenIndexedBiBeliefCode A (I := I))
    (side : IndexedLineageSide)
    (direction : ProfiledOpenIndexedBiBeliefDirection
      (I := I) (In₁ := In₁) (In₂ := In₂)) : Prop :=
  match side with
  | .right =>
      ProfiledOpenIndexedActiveReflexivePivotAt A code .right
        direction.rightPivot
  | .left =>
      ProfiledOpenIndexedActiveReflexivePivotAt A code .left
        direction.leftPivot

section
omit [Inhabited I] [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]

/-- An active reflexive right pivot produces a nonempty next left carrier.
The witness may use a different lineage after root deduplication. -/
theorem profiledOpenIndexed_next_leftCarrier_nonempty_of_activeRightPivot
    (code : ProfiledOpenIndexedBiBeliefCode A (I := I))
    (move : ProfiledOpenIndexedBiBeliefMove A)
    (direction : ProfiledOpenIndexedBiBeliefDirection
      (I := I) (In₁ := In₁) (In₂ := In₂))
    (hactive : ProfiledOpenIndexedActiveReflexivePivot A code .right
      direction) :
    (profiledOpenIndexedActiveLineageCarrier A .left
      (profiledOpenIndexedBiBeliefNext A code move direction)).Nonempty := by
  rcases hactive with ⟨hpivot, hfunctional, hreflexive⟩
  let raw := profiledOpenIndexedRightRawChildCode A code move direction
  let root := profiledOpenIndexedRightChildAnchor A code move direction
    direction.rightPivot
  have hraw : raw direction.rightPivot.1 =
      some (direction.rightPivot.2, root) := by
    change profiledOpenIndexedGatedChildCode A code.rightSlots
        code.rightPattern
        (profiledOpenIndexedRightChildAnchor A code move direction)
        direction.rightPivot direction.rightPivot.1 =
      some (direction.rightPivot.2,
        profiledOpenIndexedRightChildAnchor A code move direction
          direction.rightPivot)
    exact (profiledOpenIndexedGatedChildCode_eq_some_iff_of_active A
      code.rightSlots code.rightPattern
      (profiledOpenIndexedRightChildAnchor A code move direction)
      direction.rightPivot hfunctional direction.rightPivot.1
      direction.rightPivot.2 hpivot hpivot).2 hreflexive
  have hoccurs : raw.RootOccurs root :=
    ⟨direction.rightPivot.1, direction.rightPivot.2, hraw⟩
  obtain ⟨lineage, row, hslot⟩ := raw.rootOccurs_deduplicateRoots root
    hoccurs
  refine ⟨lineage, ?_⟩
  rw [mem_profiledOpenIndexedActiveLineageCarrier_iff]
  simp only [profiledOpenIndexedBiBeliefCurrentSlots_left,
    profiledOpenIndexedBiBeliefNext_leftSlots]
  have hrootSlot : raw.deduplicateRoots.rootSlots lineage = some root :=
    IndexedLineageChildCode.rootSlots_eq_some_of raw.deduplicateRoots hslot
  change raw.deduplicateRoots.rootSlots lineage ≠ none
  rw [hrootSlot]
  exact Option.some_ne_none _

/-- Left-to-right mirror. -/
theorem profiledOpenIndexed_next_rightCarrier_nonempty_of_activeLeftPivot
    (code : ProfiledOpenIndexedBiBeliefCode A (I := I))
    (move : ProfiledOpenIndexedBiBeliefMove A)
    (direction : ProfiledOpenIndexedBiBeliefDirection
      (I := I) (In₁ := In₁) (In₂ := In₂))
    (hactive : ProfiledOpenIndexedActiveReflexivePivot A code .left
      direction) :
    (profiledOpenIndexedActiveLineageCarrier A .right
      (profiledOpenIndexedBiBeliefNext A code move direction)).Nonempty := by
  rcases hactive with ⟨hpivot, hfunctional, hreflexive⟩
  let raw := profiledOpenIndexedLeftRawChildCode A code move direction
  let root := profiledOpenIndexedLeftChildAnchor A code move direction
    direction.leftPivot
  have hraw : raw direction.leftPivot.1 =
      some (direction.leftPivot.2, root) := by
    change profiledOpenIndexedGatedChildCode A code.leftSlots
        code.leftPattern
        (profiledOpenIndexedLeftChildAnchor A code move direction)
        direction.leftPivot direction.leftPivot.1 =
      some (direction.leftPivot.2,
        profiledOpenIndexedLeftChildAnchor A code move direction
          direction.leftPivot)
    exact (profiledOpenIndexedGatedChildCode_eq_some_iff_of_active A
      code.leftSlots code.leftPattern
      (profiledOpenIndexedLeftChildAnchor A code move direction)
      direction.leftPivot hfunctional direction.leftPivot.1
      direction.leftPivot.2 hpivot hpivot).2 hreflexive
  have hoccurs : raw.RootOccurs root :=
    ⟨direction.leftPivot.1, direction.leftPivot.2, hraw⟩
  obtain ⟨lineage, row, hslot⟩ := raw.rootOccurs_deduplicateRoots root
    hoccurs
  refine ⟨lineage, ?_⟩
  rw [mem_profiledOpenIndexedActiveLineageCarrier_iff]
  simp only [profiledOpenIndexedBiBeliefCurrentSlots_right,
    profiledOpenIndexedBiBeliefNext_rightSlots]
  have hrootSlot : raw.deduplicateRoots.rootSlots lineage = some root :=
    IndexedLineageChildCode.rootSlots_eq_some_of raw.deduplicateRoots hslot
  change raw.deduplicateRoots.rootSlots lineage ≠ none
  rw [hrootSlot]
  exact Option.some_ne_none _

/-- Side-generic nonemptiness of the cross-swapped next carrier. -/
theorem profiledOpenIndexedActiveLineageCarrier_next_other_nonempty
    (code : ProfiledOpenIndexedBiBeliefCode A (I := I))
    (move : ProfiledOpenIndexedBiBeliefMove A)
    (direction : ProfiledOpenIndexedBiBeliefDirection
      (I := I) (In₁ := In₁) (In₂ := In₂))
    (side : IndexedLineageSide)
    (hactive : ProfiledOpenIndexedActiveReflexivePivot A code side direction) :
    (profiledOpenIndexedActiveLineageCarrier A side.other
      (profiledOpenIndexedBiBeliefNext A code move direction)).Nonempty := by
  cases side with
  | right =>
      exact profiledOpenIndexed_next_leftCarrier_nonempty_of_activeRightPivot A
        code move direction hactive
  | left =>
      exact profiledOpenIndexed_next_rightCarrier_nonempty_of_activeLeftPivot A
        code move direction hactive

/-- Once one active pivot has produced the cross-swapped child, the successor
itself supplies an active reflexive pivot for the following alternating step.
This uses the crucial fact that every successor resets its patterns to the
active canonical row diagonal.  Thus activity does not require guessing a
distinguished leader: a proof-side candidate can be selected from the finite
nonempty carrier. -/
theorem exists_profiledOpenIndexedActiveReflexivePivotAt_next_other
    (code : ProfiledOpenIndexedBiBeliefCode A (I := I))
    (move : ProfiledOpenIndexedBiBeliefMove A)
    (direction : ProfiledOpenIndexedBiBeliefDirection
      (I := I) (In₁ := In₁) (In₂ := In₂))
    (side : IndexedLineageSide)
    (hactive : ProfiledOpenIndexedActiveReflexivePivot A code side direction) :
    ∃ pivot,
      ProfiledOpenIndexedActiveReflexivePivotAt A
        (profiledOpenIndexedBiBeliefNext A code move direction) side.other
          pivot := by
  let next := profiledOpenIndexedBiBeliefNext A code move direction
  obtain ⟨lineage, hlineage⟩ :=
    profiledOpenIndexedActiveLineageCarrier_next_other_nonempty A code move
      direction side hactive
  rw [mem_profiledOpenIndexedActiveLineageCarrier_iff] at hlineage
  cases side with
  | right =>
      have hslot : next.leftSlots lineage ≠ none := by
        simpa only [IndexedLineageSide.other,
          profiledOpenIndexedBiBeliefCurrentSlots_left] using hlineage
      refine ⟨(lineage, .first), ?_⟩
      change next.leftSlots lineage ≠ none ∧
        next.leftPattern.RowFunctionalAt (lineage, .first) ∧
        next.leftPattern (lineage, .first) (lineage, .first) = true
      refine ⟨hslot, ?_, ?_⟩
      · rw [profiledOpenIndexedBiBeliefNext_leftPattern]
        exact profiledOpenIndexedActiveCanonicalRowPattern_rowFunctionalAt A
          next.leftSlots (lineage, .first)
      · rw [profiledOpenIndexedBiBeliefNext_leftPattern]
        obtain ⟨root, hroot⟩ := Option.ne_none_iff_exists'.mp hslot
        dsimp only [next] at hroot
        simp [profiledOpenIndexedActiveCanonicalRowPattern, hroot]
  | left =>
      have hslot : next.rightSlots lineage ≠ none := by
        simpa only [IndexedLineageSide.other,
          profiledOpenIndexedBiBeliefCurrentSlots_right] using hlineage
      refine ⟨(lineage, .first), ?_⟩
      change next.rightSlots lineage ≠ none ∧
        next.rightPattern.RowFunctionalAt (lineage, .first) ∧
        next.rightPattern (lineage, .first) (lineage, .first) = true
      refine ⟨hslot, ?_, ?_⟩
      · rw [profiledOpenIndexedBiBeliefNext_rightPattern]
        exact profiledOpenIndexedActiveCanonicalRowPattern_rowFunctionalAt A
          next.rightSlots (lineage, .first)
      · rw [profiledOpenIndexedBiBeliefNext_rightPattern]
        obtain ⟨root, hroot⟩ := Option.ne_none_iff_exists'.mp hslot
        dsimp only [next] at hroot
        simp [profiledOpenIndexedActiveCanonicalRowPattern, hroot]

end

/-! ## A generic finite descending-chain lemma -/

omit [Inhabited I] in
/-- A descending sequence of nonempty finite subsets has one member common
to every level. -/
theorem exists_mem_all_of_finset_antitone_nonempty
    (carrier : Nat → Finset I)
    (hstep : ∀ n, carrier (n + 1) ⊆ carrier n)
    (hnonempty : ∀ n, (carrier n).Nonempty) :
    ∃ lineage, ∀ n, lineage ∈ carrier n := by
  classical
  by_contra hfixed
  push Not at hfixed
  choose cutoff hcutoff using hfixed
  obtain ⟨seed, hseed⟩ := hnonempty 0
  let cutoffs : Finset Nat := Finset.univ.image cutoff
  have hcutoffs : cutoffs.Nonempty := by
    refine ⟨cutoff seed, ?_⟩
    exact Finset.mem_image.2 ⟨seed, Finset.mem_univ seed, rfl⟩
  let bound := cutoffs.max' hcutoffs
  have hanti : Antitone carrier := antitone_nat_of_succ_le hstep
  have hnot : ∀ lineage, lineage ∉ carrier bound := by
    intro lineage hmem
    have hcutoffMem : cutoff lineage ∈ cutoffs :=
      Finset.mem_image.2 ⟨lineage, Finset.mem_univ lineage, rfl⟩
    have hle : cutoff lineage ≤ bound :=
      Finset.le_max' cutoffs (cutoff lineage) hcutoffMem
    exact hcutoff lineage ((hanti hle) hmem)
  obtain ⟨lineage, hlineage⟩ := hnonempty bound
  exact hnot lineage hlineage

/-! ## Alternating active streams -/

/-- One raw-direction code stream with an explicitly alternating proof-side
side and an active reflexive pivot at every step. -/
structure ProfiledOpenIndexedAlternatingActivePivotStream where
  code : Nat → ProfiledOpenIndexedBiBeliefCode A (I := I)
  move : Nat → ProfiledOpenIndexedBiBeliefMove A
  direction : Nat → ProfiledOpenIndexedBiBeliefDirection
    (I := I) (In₁ := In₁) (In₂ := In₂)
  side : Nat → IndexedLineageSide
  next : ∀ n,
    code (n + 1) = profiledOpenIndexedBiBeliefNext A (code n) (move n)
      (direction n)
  alternates : ∀ n, side (n + 1) = (side n).other
  active : ∀ n,
    ProfiledOpenIndexedActiveReflexivePivot A (code n) (side n) (direction n)

namespace ProfiledOpenIndexedAlternatingActivePivotStream

variable
  (stream : ProfiledOpenIndexedAlternatingActivePivotStream A (I := I)
    (In₁ := In₁) (In₂ := In₂))

/-- Carrier seen at one alternating stream level. -/
noncomputable def carrier (n : Nat) : Finset I :=
  profiledOpenIndexedActiveLineageCarrier A (stream.side n) (stream.code n)

section
omit [Inhabited I] [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]

/-- The alternating carriers form a descending chain. -/
theorem carrier_succ_subset (n : Nat) :
    stream.carrier A (n + 1) ⊆ stream.carrier A n := by
  rw [carrier, stream.next n, stream.alternates n]
  exact profiledOpenIndexedActiveLineageCarrier_next_other_subset A
    (stream.code n) (stream.move n) (stream.direction n) (stream.side n)

/-- Every level is nonempty.  Level zero is nonempty because its active pivot
belongs to the source carrier; positive levels use the preceding pivot and
the gated-child/deduplication theorem. -/
theorem carrier_nonempty (n : Nat) : (stream.carrier A n).Nonempty := by
  cases n with
  | zero =>
      cases hside : stream.side 0 with
      | right =>
          refine ⟨(stream.direction 0).rightPivot.1, ?_⟩
          rw [carrier, mem_profiledOpenIndexedActiveLineageCarrier_iff,
            hside]
          have hactive := stream.active 0
          simp only [ProfiledOpenIndexedActiveReflexivePivot, hside] at hactive
          simpa only [profiledOpenIndexedBiBeliefCurrentSlots_right] using
            hactive.1
      | left =>
          refine ⟨(stream.direction 0).leftPivot.1, ?_⟩
          rw [carrier, mem_profiledOpenIndexedActiveLineageCarrier_iff,
            hside]
          have hactive := stream.active 0
          simp only [ProfiledOpenIndexedActiveReflexivePivot, hside] at hactive
          simpa only [profiledOpenIndexedBiBeliefCurrentSlots_left] using
            hactive.1
  | succ n =>
      rw [carrier, stream.next n, stream.alternates n]
      exact profiledOpenIndexedActiveLineageCarrier_next_other_nonempty A
        (stream.code n) (stream.move n) (stream.direction n) (stream.side n)
        (stream.active n)

/-- One fixed persistent lineage remains active at every alternating level. -/
theorem exists_lineage_active_forever :
    ∃ lineage, ∀ n,
      profiledOpenIndexedBiBeliefCurrentSlots A (stream.side n)
        (stream.code n) lineage ≠ none := by
  obtain ⟨lineage, hlineage⟩ :=
    exists_mem_all_of_finset_antitone_nonempty (I := I)
      (stream.carrier A) (stream.carrier_succ_subset A)
      (stream.carrier_nonempty A)
  refine ⟨lineage, fun n ↦ ?_⟩
  exact (mem_profiledOpenIndexedActiveLineageCarrier_iff A
    (stream.side n) (stream.code n) lineage).1 (hlineage n)

end

end ProfiledOpenIndexedAlternatingActivePivotStream

/-! ## Finite-tag specialization

This is the interface used by the distinguished provenance stream.  The
`active` field is deliberately proof-side: it chooses no runtime action and
does not tell either process which side is currently informed.  Its remaining
model obligation is exactly that the raw representative selected by the
finite tag has an active reflexive pivot on the alternating source side. -/

/-- A finite-tag successor stream together with the proof-side alternating
active-pivot certificate needed by the carrier argument. -/
structure ProfiledOpenIndexedAlternatingActiveFiniteTagStream where
  code : Nat → ProfiledOpenIndexedBiBeliefCode A (I := I)
  move : Nat → ProfiledOpenIndexedBiBeliefMove A
  tag : Nat → ProfiledOpenIndexedFiniteDirectionTag A (I := I)
  side : Nat → IndexedLineageSide
  next : ∀ n,
    code (n + 1) = profiledOpenIndexedBiBeliefNextFiniteTag A (code n)
      (move n) (tag n)
  alternates : ∀ n, side (n + 1) = (side n).other
  active : ∀ n,
    ProfiledOpenIndexedActiveReflexivePivot A (code n) (side n)
      (profiledOpenIndexedRawDirectionOfFiniteTag A (code n) (move n) (tag n))

namespace ProfiledOpenIndexedAlternatingActiveFiniteTagStream

variable
  (stream : ProfiledOpenIndexedAlternatingActiveFiniteTagStream A (I := I)
    (In₁ := In₁) (In₂ := In₂))

/-- Forget only the finite tag and expose its selected raw representative.
No semantic information is lost from the persistence argument. -/
noncomputable def toRaw :
    ProfiledOpenIndexedAlternatingActivePivotStream A (I := I)
      (In₁ := In₁) (In₂ := In₂) where
  code := stream.code
  move := stream.move
  direction := fun n ↦ profiledOpenIndexedRawDirectionOfFiniteTag A
    (stream.code n) (stream.move n) (stream.tag n)
  side := stream.side
  next := by
    intro n
    rw [stream.next n]
    rfl
  alternates := stream.alternates
  active := stream.active

omit [Inhabited I] [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
/-- The finite-tag stream has one fixed lineage active at every alternating
level, provided its explicit active-pivot certificate is supplied. -/
theorem exists_lineage_active_forever :
    ∃ lineage, ∀ n,
      profiledOpenIndexedBiBeliefCurrentSlots A (stream.side n)
        (stream.code n) lineage ≠ none :=
  (stream.toRaw A).exists_lineage_active_forever A

end ProfiledOpenIndexedAlternatingActiveFiniteTagStream

end

end DetParityAutomaton

end DistributedSynthesis
