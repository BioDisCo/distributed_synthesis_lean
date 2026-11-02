/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemCarriedPointedSuccessorReceive
import DistributedSynthesis.Formalizations.Lemma.LemRelationalFamilySaturation

/-!
# Set-valued pointed successors at a receive

Exact pointed-query decoding is stronger than the operational handoff needs.
Instead of selecting the actual hidden descriptor, a process can carry a
finite set of tagged `(public family, hidden descriptor)` candidates and
advance every candidate through the same finite pointed table, public move,
and finite direction/tag.  The successor state is the set of every good table
answer obtained from a current candidate.

The family tag is retained with each descriptor, so the construction does not
perform the unsound coordinatewise two-fibre union.  One actual candidate is
preserved simply from its proof-side membership in the public set; no process
is told which member it is.

The local-summary wrapper in the second half carries this whole finite set.
At a literal `recv` it applies the fixed finite table to the partner's
delivered candidate set, using a move and direction computed from the two
finite summaries and current inputs.  Those readers have the ordinary
`PointedReceiveQueryReader` type and therefore receive no graph, lane,
orientation, strict-leader bit, or hidden descriptor.

The remaining mathematical premise is stated explicitly: the *one common
public move* selected at that node must be valid for every live candidate in
the carried set.  Set saturation removes descriptor recovery; it cannot turn
candidate-specific moves into one locally uniform distributed move.
-/

namespace DistributedSynthesis

universe u v m b o i j x

section PointedSet

variable {Code : Type u} {MoveIdentity : Type v}
variable (D : DetParityAutomaton.{u, x} Code)
variable {FamilyMove : Type m} {Direction : Type b}
variable [Fintype Code] [Fintype MoveIdentity]

/-- Public powerset atoms retain the provenance pairing between a family and
one descriptor represented by that family. -/
abbrev SetValuedPointedCandidate :=
  HiddenDescriptorTwoFibreFamily D (MoveIdentity := MoveIdentity) ×
    HiddenCodeControlDescriptor D (MoveIdentity := MoveIdentity)

/-- The pointed lookup query associated with one candidate and the one common
public move/direction. -/
def setValuedPointedQuery
    (source : SetValuedPointedCandidate D (MoveIdentity := MoveIdentity))
    (move : FamilyMove) (direction : Direction) :
    PointedSupportedSuccessorQuery D (MoveIdentity := MoveIdentity)
      (FamilyMove := FamilyMove) (Direction := Direction) :=
  { current := source.2
    currentFamily := source.1
    move := move
    direction := direction }

/-- Every good answer selected by the common pointed table from some current
candidate.  The filter checks the semantic table law rather than trusting an
arbitrary row. -/
noncomputable def setValuedPointedSuccessor
    (ExactEdge : HiddenCodeControlDescriptor D
        (MoveIdentity := MoveIdentity) → FamilyMove → Direction →
      HiddenDescriptorTwoFibreFamily D (MoveIdentity := MoveIdentity) →
      HiddenCodeControlDescriptor D (MoveIdentity := MoveIdentity) → Prop)
    (Supported : HiddenCodeControlDescriptor D
        (MoveIdentity := MoveIdentity) →
      HiddenDescriptorTwoFibreFamily D (MoveIdentity := MoveIdentity) →
      FamilyMove → Direction →
      HiddenDescriptorTwoFibreFamily D (MoveIdentity := MoveIdentity) → Prop)
    (table : PointedSupportedSuccessorTable D
      (MoveIdentity := MoveIdentity) (FamilyMove := FamilyMove)
      (Direction := Direction))
    (current : Finset
      (SetValuedPointedCandidate D (MoveIdentity := MoveIdentity)))
    (move : FamilyMove) (direction : Direction) :
    Finset (SetValuedPointedCandidate D (MoveIdentity := MoveIdentity)) := by
  classical
  exact Finset.univ.filter fun target =>
    ∃ source ∈ current,
      table (setValuedPointedQuery D source move direction) = some target ∧
        PointedSupportedSuccessorGood D ExactEdge Supported
          (setValuedPointedQuery D source move direction) target

/-- Exact membership characterization of the public successor set. -/
theorem mem_setValuedPointedSuccessor_iff
    (ExactEdge : HiddenCodeControlDescriptor D
        (MoveIdentity := MoveIdentity) → FamilyMove → Direction →
      HiddenDescriptorTwoFibreFamily D (MoveIdentity := MoveIdentity) →
      HiddenCodeControlDescriptor D (MoveIdentity := MoveIdentity) → Prop)
    (Supported : HiddenCodeControlDescriptor D
        (MoveIdentity := MoveIdentity) →
      HiddenDescriptorTwoFibreFamily D (MoveIdentity := MoveIdentity) →
      FamilyMove → Direction →
      HiddenDescriptorTwoFibreFamily D (MoveIdentity := MoveIdentity) → Prop)
    (table : PointedSupportedSuccessorTable D
      (MoveIdentity := MoveIdentity) (FamilyMove := FamilyMove)
      (Direction := Direction))
    (current : Finset
      (SetValuedPointedCandidate D (MoveIdentity := MoveIdentity)))
    (move : FamilyMove) (direction : Direction)
    (target : SetValuedPointedCandidate D
      (MoveIdentity := MoveIdentity)) :
    target ∈ setValuedPointedSuccessor D ExactEdge Supported table current
        move direction ↔
      ∃ source ∈ current,
        table (setValuedPointedQuery D source move direction) = some target ∧
          PointedSupportedSuccessorGood D ExactEdge Supported
            (setValuedPointedQuery D source move direction) target := by
  classical
  simp [setValuedPointedSuccessor]

/-- One public move is valid simultaneously for every live candidate.  This
is the exact common-move premise which powerset saturation does not create. -/
def SetValuedPointedCommonMoveValid
    (Live : HiddenCodeControlDescriptor D (MoveIdentity := MoveIdentity) →
      HiddenDescriptorTwoFibreFamily D (MoveIdentity := MoveIdentity) → Prop)
    (Valid : HiddenDescriptorTwoFibreFamily D
        (MoveIdentity := MoveIdentity) → FamilyMove → Prop)
    (current : Finset
      (SetValuedPointedCandidate D (MoveIdentity := MoveIdentity)))
    (move : FamilyMove) : Prop :=
  ∀ source ∈ current,
    Live source.2 source.1 → Valid source.1 move

/-- Every candidate in the public set is semantically live.  An application
may instead use the candidate-specific preservation theorem below. -/
def SetValuedPointedAllLive
    (Live : HiddenCodeControlDescriptor D (MoveIdentity := MoveIdentity) →
      HiddenDescriptorTwoFibreFamily D (MoveIdentity := MoveIdentity) → Prop)
    (current : Finset
      (SetValuedPointedCandidate D (MoveIdentity := MoveIdentity))) : Prop :=
  ∀ source ∈ current, Live source.2 source.1

/-- Every live candidate at which the common move is valid has one good
selected answer in the common public successor set. -/
theorem exists_mem_setValuedPointedSuccessor_of_live_valid
    (Live : HiddenCodeControlDescriptor D (MoveIdentity := MoveIdentity) →
      HiddenDescriptorTwoFibreFamily D (MoveIdentity := MoveIdentity) → Prop)
    (ExactEdge : HiddenCodeControlDescriptor D
        (MoveIdentity := MoveIdentity) → FamilyMove → Direction →
      HiddenDescriptorTwoFibreFamily D (MoveIdentity := MoveIdentity) →
      HiddenCodeControlDescriptor D (MoveIdentity := MoveIdentity) → Prop)
    (Valid : HiddenDescriptorTwoFibreFamily D
        (MoveIdentity := MoveIdentity) → FamilyMove → Prop)
    (Supported : HiddenCodeControlDescriptor D
        (MoveIdentity := MoveIdentity) →
      HiddenDescriptorTwoFibreFamily D (MoveIdentity := MoveIdentity) →
      FamilyMove → Direction →
      HiddenDescriptorTwoFibreFamily D (MoveIdentity := MoveIdentity) → Prop)
    (table : PointedSupportedSuccessorTable D
      (MoveIdentity := MoveIdentity) (FamilyMove := FamilyMove)
      (Direction := Direction))
    (hworks : PointedSupportedSuccessorTableWorks D Live ExactEdge Valid
      Supported table)
    (current : Finset
      (SetValuedPointedCandidate D (MoveIdentity := MoveIdentity)))
    (move : FamilyMove) (direction : Direction)
    (source : SetValuedPointedCandidate D (MoveIdentity := MoveIdentity))
    (hsource : source ∈ current)
    (hlive : Live source.2 source.1) (hvalid : Valid source.1 move) :
    ∃ target ∈ setValuedPointedSuccessor D ExactEdge Supported table
        current move direction,
      table (setValuedPointedQuery D source move direction) = some target ∧
        PointedSupportedSuccessorGood D ExactEdge Supported
          (setValuedPointedQuery D source move direction) target := by
  obtain ⟨target, htable, hgood⟩ :=
    hworks (setValuedPointedQuery D source move direction) hlive hvalid
  refine ⟨target, ?_, htable, hgood⟩
  exact (mem_setValuedPointedSuccessor_iff D ExactEdge Supported table current
    move direction target).2 ⟨source, hsource, htable, hgood⟩

/-- The actual represented candidate is preserved without decoding which
member it is.  It is used only as a proof-side membership witness. -/
theorem setValuedPointedSuccessor_preserves_actual
    (Live : HiddenCodeControlDescriptor D (MoveIdentity := MoveIdentity) →
      HiddenDescriptorTwoFibreFamily D (MoveIdentity := MoveIdentity) → Prop)
    (ExactEdge : HiddenCodeControlDescriptor D
        (MoveIdentity := MoveIdentity) → FamilyMove → Direction →
      HiddenDescriptorTwoFibreFamily D (MoveIdentity := MoveIdentity) →
      HiddenCodeControlDescriptor D (MoveIdentity := MoveIdentity) → Prop)
    (Valid : HiddenDescriptorTwoFibreFamily D
        (MoveIdentity := MoveIdentity) → FamilyMove → Prop)
    (Supported : HiddenCodeControlDescriptor D
        (MoveIdentity := MoveIdentity) →
      HiddenDescriptorTwoFibreFamily D (MoveIdentity := MoveIdentity) →
      FamilyMove → Direction →
      HiddenDescriptorTwoFibreFamily D (MoveIdentity := MoveIdentity) → Prop)
    (table : PointedSupportedSuccessorTable D
      (MoveIdentity := MoveIdentity) (FamilyMove := FamilyMove)
      (Direction := Direction))
    (hworks : PointedSupportedSuccessorTableWorks D Live ExactEdge Valid
      Supported table)
    (current : Finset
      (SetValuedPointedCandidate D (MoveIdentity := MoveIdentity)))
    (move : FamilyMove) (direction : Direction)
    (actual : SetValuedPointedCandidate D (MoveIdentity := MoveIdentity))
    (hactual : actual ∈ current) (hlive : Live actual.2 actual.1)
    (hcommon : SetValuedPointedCommonMoveValid D Live Valid current move) :
    ∃ nextActual ∈ setValuedPointedSuccessor D ExactEdge Supported table
        current move direction,
      PointedSupportedSuccessorGood D ExactEdge Supported
        (setValuedPointedQuery D actual move direction) nextActual := by
  obtain ⟨target, htarget, _, hgood⟩ :=
    exists_mem_setValuedPointedSuccessor_of_live_valid D Live ExactEdge Valid
      Supported table hworks current move direction actual hactual hlive
      (hcommon actual hactual hlive)
  exact ⟨target, htarget, hgood⟩

/-- Under all-live and common-move validity, every current candidate is
covered by the one successor set. -/
theorem setValuedPointedSuccessor_covers_all
    (Live : HiddenCodeControlDescriptor D (MoveIdentity := MoveIdentity) →
      HiddenDescriptorTwoFibreFamily D (MoveIdentity := MoveIdentity) → Prop)
    (ExactEdge : HiddenCodeControlDescriptor D
        (MoveIdentity := MoveIdentity) → FamilyMove → Direction →
      HiddenDescriptorTwoFibreFamily D (MoveIdentity := MoveIdentity) →
      HiddenCodeControlDescriptor D (MoveIdentity := MoveIdentity) → Prop)
    (Valid : HiddenDescriptorTwoFibreFamily D
        (MoveIdentity := MoveIdentity) → FamilyMove → Prop)
    (Supported : HiddenCodeControlDescriptor D
        (MoveIdentity := MoveIdentity) →
      HiddenDescriptorTwoFibreFamily D (MoveIdentity := MoveIdentity) →
      FamilyMove → Direction →
      HiddenDescriptorTwoFibreFamily D (MoveIdentity := MoveIdentity) → Prop)
    (table : PointedSupportedSuccessorTable D
      (MoveIdentity := MoveIdentity) (FamilyMove := FamilyMove)
      (Direction := Direction))
    (hworks : PointedSupportedSuccessorTableWorks D Live ExactEdge Valid
      Supported table)
    (current : Finset
      (SetValuedPointedCandidate D (MoveIdentity := MoveIdentity)))
    (move : FamilyMove) (direction : Direction)
    (hallLive : SetValuedPointedAllLive D Live current)
    (hcommon : SetValuedPointedCommonMoveValid D Live Valid current move) :
    ∀ source ∈ current,
      ∃ target ∈ setValuedPointedSuccessor D ExactEdge Supported table
          current move direction,
        PointedSupportedSuccessorGood D ExactEdge Supported
          (setValuedPointedQuery D source move direction) target := by
  intro source hsource
  obtain ⟨target, htarget, _, hgood⟩ :=
    exists_mem_setValuedPointedSuccessor_of_live_valid D Live ExactEdge Valid
      Supported table hworks current move direction source hsource
      (hallLive source hsource) (hcommon source hsource (hallLive source hsource))
  exact ⟨target, htarget, hgood⟩

/-- A public set containing one live actual candidate has a nonempty
successor. -/
theorem setValuedPointedSuccessor_nonempty_of_actual
    (Live : HiddenCodeControlDescriptor D (MoveIdentity := MoveIdentity) →
      HiddenDescriptorTwoFibreFamily D (MoveIdentity := MoveIdentity) → Prop)
    (ExactEdge : HiddenCodeControlDescriptor D
        (MoveIdentity := MoveIdentity) → FamilyMove → Direction →
      HiddenDescriptorTwoFibreFamily D (MoveIdentity := MoveIdentity) →
      HiddenCodeControlDescriptor D (MoveIdentity := MoveIdentity) → Prop)
    (Valid : HiddenDescriptorTwoFibreFamily D
        (MoveIdentity := MoveIdentity) → FamilyMove → Prop)
    (Supported : HiddenCodeControlDescriptor D
        (MoveIdentity := MoveIdentity) →
      HiddenDescriptorTwoFibreFamily D (MoveIdentity := MoveIdentity) →
      FamilyMove → Direction →
      HiddenDescriptorTwoFibreFamily D (MoveIdentity := MoveIdentity) → Prop)
    (table : PointedSupportedSuccessorTable D
      (MoveIdentity := MoveIdentity) (FamilyMove := FamilyMove)
      (Direction := Direction))
    (hworks : PointedSupportedSuccessorTableWorks D Live ExactEdge Valid
      Supported table)
    (current : Finset
      (SetValuedPointedCandidate D (MoveIdentity := MoveIdentity)))
    (move : FamilyMove) (direction : Direction)
    (actual : SetValuedPointedCandidate D (MoveIdentity := MoveIdentity))
    (hactual : actual ∈ current) (hlive : Live actual.2 actual.1)
    (hcommon : SetValuedPointedCommonMoveValid D Live Valid current move) :
    (setValuedPointedSuccessor D ExactEdge Supported table current move
      direction).Nonempty := by
  obtain ⟨target, htarget, _⟩ := setValuedPointedSuccessor_preserves_actual D
    Live ExactEdge Valid Supported table hworks current move direction actual
    hactual hlive hcommon
  exact ⟨target, htarget⟩

/-! ## Connection to the existing universal exact-thread saturation -/

/-- Every set-valued table successor is an edge of the larger relational
saturation.  Hence every thread through these public sets is one of the exact
threads quantified by `relationalFamilySaturation_universal_iff`; fixed-policy
parity may be applied universally without selecting the actual candidate. -/
theorem setValuedPointedSuccessor_subset_relationalFamilySaturation
    (ExactEdge : HiddenCodeControlDescriptor D
        (MoveIdentity := MoveIdentity) → FamilyMove → Direction →
      HiddenDescriptorTwoFibreFamily D (MoveIdentity := MoveIdentity) →
      HiddenCodeControlDescriptor D (MoveIdentity := MoveIdentity) → Prop)
    (Supported : HiddenCodeControlDescriptor D
        (MoveIdentity := MoveIdentity) →
      HiddenDescriptorTwoFibreFamily D (MoveIdentity := MoveIdentity) →
      FamilyMove → Direction →
      HiddenDescriptorTwoFibreFamily D (MoveIdentity := MoveIdentity) → Prop)
    (table : PointedSupportedSuccessorTable D
      (MoveIdentity := MoveIdentity) (FamilyMove := FamilyMove)
      (Direction := Direction))
    (current : Finset
      (SetValuedPointedCandidate D (MoveIdentity := MoveIdentity)))
    (move : FamilyMove) (direction : Direction) :
    setValuedPointedSuccessor D ExactEdge Supported table current move direction
      ⊆
    relationalFamilySaturation ExactEdge
      (fun source target =>
        target.control = D.step source.control target.code)
      current move direction := by
  intro target htarget
  obtain ⟨source, hsource, _, hgood⟩ :=
    (mem_setValuedPointedSuccessor_iff D ExactEdge Supported table current move
      direction target).1 htarget
  exact (mem_relationalFamilySaturation_iff ExactEdge
    (fun source target => target.control = D.step source.control target.code)
    current move direction target).2
      ⟨source, hsource, hgood.2.1, hgood.2.2⟩

end PointedSet

/-! ## Graph-blind carried candidate-set wrapper -/

section ReceiveWrapper

variable {In₁ : Type i} {In₂ : Type j}
variable {Code : Type u} {MoveIdentity : Type v}
variable (D : DetParityAutomaton.{u, x} Code)
variable {FamilyMove : Type m} {Direction : Type b}
variable [Fintype Code] [Fintype MoveIdentity]

/-- The underlying local state and the whole public candidate set.  No member
of the set is distinguished. -/
structure SetValuedPointedReceiveSummary
    (M : LocalSummaryAutomaton.{i, j, o} In₁ In₂) (d : Proc) where
  base : M.Summary d
  candidates : Finset
    (SetValuedPointedCandidate D (MoveIdentity := MoveIdentity))

noncomputable instance
    (M : LocalSummaryAutomaton.{i, j, o} In₁ In₂) (d : Proc) :
    Fintype (SetValuedPointedReceiveSummary
      (MoveIdentity := MoveIdentity) D M d) := by
  classical
  let encode : SetValuedPointedReceiveSummary
      (MoveIdentity := MoveIdentity) D M d →
      M.Summary d × Finset
        (SetValuedPointedCandidate D (MoveIdentity := MoveIdentity)) :=
    fun summary => (summary.base, summary.candidates)
  exact Fintype.ofInjective encode (by
    intro left right heq
    rcases left with ⟨leftBase, leftCandidates⟩
    rcases right with ⟨rightBase, rightCandidates⟩
    simp only [encode, Prod.mk.injEq] at heq
    rcases heq with ⟨rfl, rfl⟩
    rfl)

namespace LocalSummaryAutomaton

/-- At each receive, apply the one common finite table to the partner's
delivered public candidate set.  Move and direction are computed from the
ordinary joint receive data, never from a graph or selected hidden member. -/
noncomputable def withSetValuedPointedSuccessor
    (M : LocalSummaryAutomaton.{i, j, o} In₁ In₂)
    (ExactEdge : HiddenCodeControlDescriptor D
        (MoveIdentity := MoveIdentity) → FamilyMove → Direction →
      HiddenDescriptorTwoFibreFamily D (MoveIdentity := MoveIdentity) →
      HiddenCodeControlDescriptor D (MoveIdentity := MoveIdentity) → Prop)
    (Supported : HiddenCodeControlDescriptor D
        (MoveIdentity := MoveIdentity) →
      HiddenDescriptorTwoFibreFamily D (MoveIdentity := MoveIdentity) →
      FamilyMove → Direction →
      HiddenDescriptorTwoFibreFamily D (MoveIdentity := MoveIdentity) → Prop)
    (table : PointedSupportedSuccessorTable D
      (MoveIdentity := MoveIdentity) (FamilyMove := FamilyMove)
      (Direction := Direction))
    (initialCandidates : (d : Proc) → Finset
      (SetValuedPointedCandidate D (MoveIdentity := MoveIdentity)))
    (moveReader : PointedReceiveQueryReader M FamilyMove)
    (directionReader : PointedReceiveQueryReader M Direction) :
    LocalSummaryAutomaton In₁ In₂ where
  Summary d := SetValuedPointedReceiveSummary
    (MoveIdentity := MoveIdentity) D M d
  finite d := by
    classical
    infer_instance
  initial d :=
    { base := M.initial d
      candidates := initialCandidates d }
  stepNoRecv d self input :=
    { base := M.stepNoRecv d self.base input
      candidates := self.candidates }
  stepRecv d self inputSelf other inputOther :=
    { base := M.stepRecv d self.base inputSelf other.base inputOther
      candidates := setValuedPointedSuccessor D ExactEdge Supported table
        other.candidates
        (moveReader.recv d self.base inputSelf other.base inputOther)
        (directionReader.recv d self.base inputSelf other.base inputOther) }

@[simp] theorem withSetValuedPointedSuccessor_stepRecv_candidates
    (M : LocalSummaryAutomaton.{i, j, o} In₁ In₂)
    (ExactEdge : HiddenCodeControlDescriptor D
        (MoveIdentity := MoveIdentity) → FamilyMove → Direction →
      HiddenDescriptorTwoFibreFamily D (MoveIdentity := MoveIdentity) →
      HiddenCodeControlDescriptor D (MoveIdentity := MoveIdentity) → Prop)
    (Supported : HiddenCodeControlDescriptor D
        (MoveIdentity := MoveIdentity) →
      HiddenDescriptorTwoFibreFamily D (MoveIdentity := MoveIdentity) →
      FamilyMove → Direction →
      HiddenDescriptorTwoFibreFamily D (MoveIdentity := MoveIdentity) → Prop)
    (table : PointedSupportedSuccessorTable D
      (MoveIdentity := MoveIdentity) (FamilyMove := FamilyMove)
      (Direction := Direction))
    (initialCandidates : (d : Proc) → Finset
      (SetValuedPointedCandidate D (MoveIdentity := MoveIdentity)))
    (moveReader : PointedReceiveQueryReader M FamilyMove)
    (directionReader : PointedReceiveQueryReader M Direction)
    (d : Proc) (self : SetValuedPointedReceiveSummary
      (MoveIdentity := MoveIdentity) D M d)
    (inputSelf : PSum In₁ In₂)
    (other : SetValuedPointedReceiveSummary
      (MoveIdentity := MoveIdentity) D M d.other)
    (inputOther : PSum In₁ In₂) :
    ((M.withSetValuedPointedSuccessor D ExactEdge Supported table
      initialCandidates moveReader directionReader).stepRecv d self inputSelf
      other inputOther).candidates =
      setValuedPointedSuccessor D ExactEdge Supported table other.candidates
        (moveReader.recv d self.base inputSelf other.base inputOther)
        (directionReader.recv d self.base inputSelf other.base inputOther) :=
  rfl

@[simp] theorem withSetValuedPointedSuccessor_read_recv_candidates
    (M : LocalSummaryAutomaton.{i, j, o} In₁ In₂)
    (ExactEdge : HiddenCodeControlDescriptor D
        (MoveIdentity := MoveIdentity) → FamilyMove → Direction →
      HiddenDescriptorTwoFibreFamily D (MoveIdentity := MoveIdentity) →
      HiddenCodeControlDescriptor D (MoveIdentity := MoveIdentity) → Prop)
    (Supported : HiddenCodeControlDescriptor D
        (MoveIdentity := MoveIdentity) →
      HiddenDescriptorTwoFibreFamily D (MoveIdentity := MoveIdentity) →
      FamilyMove → Direction →
      HiddenDescriptorTwoFibreFamily D (MoveIdentity := MoveIdentity) → Prop)
    (table : PointedSupportedSuccessorTable D
      (MoveIdentity := MoveIdentity) (FamilyMove := FamilyMove)
      (Direction := Direction))
    (initialCandidates : (d : Proc) → Finset
      (SetValuedPointedCandidate D (MoveIdentity := MoveIdentity)))
    (moveReader : PointedReceiveQueryReader M FamilyMove)
    (directionReader : PointedReceiveQueryReader M Direction)
    (d : Proc) (previousSelf : View In₁ In₂ d)
    (inputSelf : PSum In₁ In₂)
    (previousOther : View In₁ In₂ d.other)
    (inputOther : PSum In₁ In₂) :
    ((M.withSetValuedPointedSuccessor D ExactEdge Supported table
      initialCandidates moveReader directionReader).read
        (.recv previousSelf inputSelf previousOther inputOther)).candidates =
      setValuedPointedSuccessor D ExactEdge Supported table
        ((M.withSetValuedPointedSuccessor D ExactEdge Supported table
          initialCandidates moveReader directionReader).read
            previousOther).candidates
        (moveReader.recv d
          ((M.withSetValuedPointedSuccessor D ExactEdge Supported table
            initialCandidates moveReader directionReader).read previousSelf).base
          inputSelf
          ((M.withSetValuedPointedSuccessor D ExactEdge Supported table
            initialCandidates moveReader directionReader).read previousOther).base
          inputOther)
        (directionReader.recv d
          ((M.withSetValuedPointedSuccessor D ExactEdge Supported table
            initialCandidates moveReader directionReader).read previousSelf).base
          inputSelf
          ((M.withSetValuedPointedSuccessor D ExactEdge Supported table
            initialCandidates moveReader directionReader).read previousOther).base
          inputOther) :=
  rfl

/-- Literal receive preservation of one proof-side actual candidate.  The
receiver advances the entire delivered public set; `actual` is never an input
to the executable transition. -/
theorem withSetValuedPointedSuccessor_read_recv_preserves_actual
    (M : LocalSummaryAutomaton.{i, j, o} In₁ In₂)
    (Live : HiddenCodeControlDescriptor D (MoveIdentity := MoveIdentity) →
      HiddenDescriptorTwoFibreFamily D (MoveIdentity := MoveIdentity) → Prop)
    (ExactEdge : HiddenCodeControlDescriptor D
        (MoveIdentity := MoveIdentity) → FamilyMove → Direction →
      HiddenDescriptorTwoFibreFamily D (MoveIdentity := MoveIdentity) →
      HiddenCodeControlDescriptor D (MoveIdentity := MoveIdentity) → Prop)
    (Valid : HiddenDescriptorTwoFibreFamily D
        (MoveIdentity := MoveIdentity) → FamilyMove → Prop)
    (Supported : HiddenCodeControlDescriptor D
        (MoveIdentity := MoveIdentity) →
      HiddenDescriptorTwoFibreFamily D (MoveIdentity := MoveIdentity) →
      FamilyMove → Direction →
      HiddenDescriptorTwoFibreFamily D (MoveIdentity := MoveIdentity) → Prop)
    (table : PointedSupportedSuccessorTable D
      (MoveIdentity := MoveIdentity) (FamilyMove := FamilyMove)
      (Direction := Direction))
    (hworks : PointedSupportedSuccessorTableWorks D Live ExactEdge Valid
      Supported table)
    (initialCandidates : (d : Proc) → Finset
      (SetValuedPointedCandidate D (MoveIdentity := MoveIdentity)))
    (moveReader : PointedReceiveQueryReader M FamilyMove)
    (directionReader : PointedReceiveQueryReader M Direction)
    (d : Proc) (previousSelf : View In₁ In₂ d)
    (inputSelf : PSum In₁ In₂)
    (previousOther : View In₁ In₂ d.other)
    (inputOther : PSum In₁ In₂)
    (actual : SetValuedPointedCandidate D (MoveIdentity := MoveIdentity))
    (hactual :
      actual ∈
        ((M.withSetValuedPointedSuccessor D ExactEdge Supported table
          initialCandidates moveReader directionReader).read
            previousOther).candidates)
    (hlive : Live actual.2 actual.1)
    (hcommon : SetValuedPointedCommonMoveValid D Live Valid
      ((M.withSetValuedPointedSuccessor D ExactEdge Supported table
        initialCandidates moveReader directionReader).read
          previousOther).candidates
      (moveReader.recv d
        ((M.withSetValuedPointedSuccessor D ExactEdge Supported table
          initialCandidates moveReader directionReader).read previousSelf).base
        inputSelf
        ((M.withSetValuedPointedSuccessor D ExactEdge Supported table
          initialCandidates moveReader directionReader).read previousOther).base
        inputOther)) :
    ∃ nextActual,
      nextActual ∈
        ((M.withSetValuedPointedSuccessor D ExactEdge Supported table
          initialCandidates moveReader directionReader).read
            (.recv previousSelf inputSelf previousOther inputOther)).candidates ∧
      PointedSupportedSuccessorGood D ExactEdge Supported
        (setValuedPointedQuery D actual
          (moveReader.recv d
            ((M.withSetValuedPointedSuccessor D ExactEdge Supported table
              initialCandidates moveReader directionReader).read
                previousSelf).base inputSelf
            ((M.withSetValuedPointedSuccessor D ExactEdge Supported table
              initialCandidates moveReader directionReader).read
                previousOther).base inputOther)
          (directionReader.recv d
            ((M.withSetValuedPointedSuccessor D ExactEdge Supported table
              initialCandidates moveReader directionReader).read
                previousSelf).base inputSelf
            ((M.withSetValuedPointedSuccessor D ExactEdge Supported table
              initialCandidates moveReader directionReader).read
                previousOther).base inputOther))
        nextActual := by
  let W := M.withSetValuedPointedSuccessor D ExactEdge Supported table
    initialCandidates moveReader directionReader
  let current := (W.read previousOther).candidates
  let move := moveReader.recv d (W.read previousSelf).base inputSelf
    (W.read previousOther).base inputOther
  let direction := directionReader.recv d (W.read previousSelf).base inputSelf
    (W.read previousOther).base inputOther
  obtain ⟨nextActual, hnext, hgood⟩ :=
    setValuedPointedSuccessor_preserves_actual D Live ExactEdge Valid Supported
      table hworks current move direction actual hactual hlive hcommon
  refine ⟨nextActual, ?_, hgood⟩
  change nextActual ∈ (W.read
    (.recv previousSelf inputSelf previousOther inputOther)).candidates
  rw [withSetValuedPointedSuccessor_read_recv_candidates]
  exact hnext

end LocalSummaryAutomaton

end ReceiveWrapper

end DistributedSynthesis
