/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemFixedPolicyRelationalCandidateTable

/-!
# Candidate-wide moves from two sidewise local-class banks

The complete-family move alphabet is too coarse for a candidate set whose
live members have different full family tags.  Distributed locality asks for
something weaker and asymmetric: process one must use one move on each of its
local information classes, and process two must do the same on its own local
classes.  The two partitions need not coincide and no candidate is selected.

This file gives the exact generic reduction.  Enrich every public family tag
with finite process-one and process-two class identifiers.  A public move is
then a pair of complete finite banks, one indexed by each class type.
Candidate-wide common validity is equivalent to the existence of a uniform
local move separately on every class of each partition.

The result is the interface consumed by the existing
`ProfiledOpenPairedFibreFamilyMove`: that construction supplies precisely one
shared sender controller per sidewise fibre.  This generic layer contains no
orientation, lane, graph, leader flag, or hidden-candidate selection.
-/

namespace DistributedSynthesis

universe oc tc f d om tm

/-- A full family tag retaining both finite local-class coordinates. -/
abbrev SidewiseTaggedFamily
    (OneClass : Type oc) (TwoClass : Type tc) (Family : Type f) :=
  (OneClass × TwoClass) × Family

/-- One finite public move contains a bank for every local class on each
side.  A process consults only its own class-indexed component. -/
abbrev SidewiseMoveBank
    (OneClass : Type oc) (TwoClass : Type tc)
    (OneMove : Type om) (TwoMove : Type tm) :=
  (OneClass → OneMove) × (TwoClass → TwoMove)

/-- Candidate validity for a sidewise bank.  The same hidden candidate may
belong to different class partitions on the two sides. -/
def SidewiseCandidateValid
    {OneClass : Type oc} {TwoClass : Type tc} {Family : Type f}
    {Descriptor : Type d} {OneMove : Type om} {TwoMove : Type tm}
    (OneValid : Descriptor → Family → OneMove → Prop)
    (TwoValid : Descriptor → Family → TwoMove → Prop)
    (descriptor : Descriptor)
    (family : SidewiseTaggedFamily OneClass TwoClass Family)
    (move : SidewiseMoveBank OneClass TwoClass OneMove TwoMove) : Prop :=
  OneValid descriptor family.2 (move.1 family.1.1) ∧
    TwoValid descriptor family.2 (move.2 family.1.2)

/-- The honest sidewise uniformity statement.  For every active finite
candidate set, each process-one class has one move valid for all live members
of that class, and independently every process-two class has one such move.
Empty classes merely require an arbitrary bank entry, which is harmless for
finite inhabited controller alphabets. -/
def SidewiseClasswiseMovesExist
    {OneClass : Type oc} {TwoClass : Type tc} {Family : Type f}
    {Descriptor : Type d} {OneMove : Type om} {TwoMove : Type tm}
    (Live : Descriptor → Family → Prop)
    (OneValid : Descriptor → Family → OneMove → Prop)
    (TwoValid : Descriptor → Family → TwoMove → Prop) : Prop :=
  ∀ candidates : Finset
      (RelationalFamilyCandidate
        (SidewiseTaggedFamily OneClass TwoClass Family) Descriptor),
    RelationalCandidateSetActive (fun descriptor family ↦
      Live descriptor family.2) candidates →
      (∀ oneClass : OneClass,
        ∃ move : OneMove,
          ∀ candidate ∈ candidates,
            Live candidate.2 candidate.1.2 →
              candidate.1.1.1 = oneClass →
                OneValid candidate.2 candidate.1.2 move) ∧
      (∀ twoClass : TwoClass,
        ∃ move : TwoMove,
          ∀ candidate ∈ candidates,
            Live candidate.2 candidate.1.2 →
              candidate.1.1.2 = twoClass →
                TwoValid candidate.2 candidate.1.2 move)

/-- Choosing the two finite class-indexed banks converts sidewise local
uniformity into the common public-move premise of the relational candidate
table. -/
theorem relationalCandidateCommonMoveExists_of_sidewiseClasswise
    {OneClass : Type oc} {TwoClass : Type tc} {Family : Type f}
    {Descriptor : Type d} {OneMove : Type om} {TwoMove : Type tm}
    (Live : Descriptor → Family → Prop)
    (OneValid : Descriptor → Family → OneMove → Prop)
    (TwoValid : Descriptor → Family → TwoMove → Prop)
    (hclasswise : SidewiseClasswiseMovesExist
      (OneClass := OneClass) (TwoClass := TwoClass)
      Live OneValid TwoValid) :
    RelationalCandidateCommonMoveExists
      (Family := SidewiseTaggedFamily OneClass TwoClass Family)
      (Descriptor := Descriptor)
      (Move := SidewiseMoveBank OneClass TwoClass OneMove TwoMove)
      (fun descriptor family ↦ Live descriptor family.2)
      (SidewiseCandidateValid (OneClass := OneClass) (TwoClass := TwoClass)
        OneValid TwoValid) := by
  intro candidates hactive
  obtain ⟨hone, htwo⟩ := hclasswise candidates hactive
  let oneBank : OneClass → OneMove := fun oneClass ↦
    Classical.choose (hone oneClass)
  let twoBank : TwoClass → TwoMove := fun twoClass ↦
    Classical.choose (htwo twoClass)
  refine ⟨(oneBank, twoBank), ?_⟩
  intro candidate hcandidate hlive
  constructor
  · exact Classical.choose_spec (hone candidate.1.1.1) candidate hcandidate
      hlive rfl
  · exact Classical.choose_spec (htwo candidate.1.1.2) candidate hcandidate
      hlive rfl

/-- Conversely, a candidate-wide sidewise bank immediately supplies the
local uniform move for each class by projection. -/
theorem sidewiseClasswiseMovesExist_of_relationalCandidateCommonMove
    {OneClass : Type oc} {TwoClass : Type tc} {Family : Type f}
    {Descriptor : Type d} {OneMove : Type om} {TwoMove : Type tm}
    (Live : Descriptor → Family → Prop)
    (OneValid : Descriptor → Family → OneMove → Prop)
    (TwoValid : Descriptor → Family → TwoMove → Prop)
    (hcommon : RelationalCandidateCommonMoveExists
      (Family := SidewiseTaggedFamily OneClass TwoClass Family)
      (Descriptor := Descriptor)
      (Move := SidewiseMoveBank OneClass TwoClass OneMove TwoMove)
      (fun descriptor family ↦ Live descriptor family.2)
      (SidewiseCandidateValid (OneClass := OneClass) (TwoClass := TwoClass)
        OneValid TwoValid)) :
    SidewiseClasswiseMovesExist (OneClass := OneClass) (TwoClass := TwoClass)
      Live OneValid TwoValid := by
  intro candidates hactive
  obtain ⟨bank, hbank⟩ := hcommon candidates hactive
  constructor
  · intro oneClass
    refine ⟨bank.1 oneClass, ?_⟩
    intro candidate hcandidate hlive hclass
    have hvalid := hbank candidate hcandidate hlive
    simpa only [SidewiseCandidateValid, hclass] using hvalid.1
  · intro twoClass
    refine ⟨bank.2 twoClass, ?_⟩
    intro candidate hcandidate hlive hclass
    have hvalid := hbank candidate hcandidate hlive
    simpa only [SidewiseCandidateValid, hclass] using hvalid.2

/-- Exact characterization of the common-move obligation after retaining the
two finite local-class tags.  This is the correct alternating/local-consistency
interface: global family tags may differ. -/
theorem relationalCandidateCommonMoveExists_sidewise_iff
    {OneClass : Type oc} {TwoClass : Type tc} {Family : Type f}
    {Descriptor : Type d} {OneMove : Type om} {TwoMove : Type tm}
    (Live : Descriptor → Family → Prop)
    (OneValid : Descriptor → Family → OneMove → Prop)
    (TwoValid : Descriptor → Family → TwoMove → Prop) :
    RelationalCandidateCommonMoveExists
        (Family := SidewiseTaggedFamily OneClass TwoClass Family)
        (Descriptor := Descriptor)
        (Move := SidewiseMoveBank OneClass TwoClass OneMove TwoMove)
        (fun descriptor family ↦ Live descriptor family.2)
        (SidewiseCandidateValid (OneClass := OneClass) (TwoClass := TwoClass)
          OneValid TwoValid) ↔
      SidewiseClasswiseMovesExist (OneClass := OneClass)
        (TwoClass := TwoClass) Live OneValid TwoValid := by
  constructor
  · exact sidewiseClasswiseMovesExist_of_relationalCandidateCommonMove
      Live OneValid TwoValid
  · exact relationalCandidateCommonMoveExists_of_sidewiseClasswise
      Live OneValid TwoValid

/-! ## Dependent class-indexed controller banks

The concrete fibre construction has a genuinely dependent controller type:
the root family and monitor stored at class `c` occur in the type of its
controller.  The following version therefore matches
`ProfiledOpenPairedFibreFamilyMove` definitionally, before any optional
fixed-alphabet reindexing.
-/

/-- A pair of dependent finite local-controller banks. -/
abbrev SidewiseDependentMoveBank
    {OneClass : Type oc} {TwoClass : Type tc}
    (OneMove : OneClass → Type om) (TwoMove : TwoClass → Type tm) :=
  (∀ oneClass, OneMove oneClass) × (∀ twoClass, TwoMove twoClass)

/-- Candidate validity for dependent sidewise controller families. -/
def SidewiseDependentCandidateValid
    {OneClass : Type oc} {TwoClass : Type tc} {Family : Type f}
    {Descriptor : Type d}
    {OneMove : OneClass → Type om} {TwoMove : TwoClass → Type tm}
    (OneValid : ∀ oneClass,
      Descriptor → Family → OneMove oneClass → Prop)
    (TwoValid : ∀ twoClass,
      Descriptor → Family → TwoMove twoClass → Prop)
    (descriptor : Descriptor)
    (family : SidewiseTaggedFamily OneClass TwoClass Family)
    (move : SidewiseDependentMoveBank OneMove TwoMove) : Prop :=
  OneValid family.1.1 descriptor family.2 (move.1 family.1.1) ∧
    TwoValid family.1.2 descriptor family.2 (move.2 family.1.2)

/-- Per-class local uniformity with the controller type allowed to depend on
the class. -/
def SidewiseDependentClasswiseMovesExist
    {OneClass : Type oc} {TwoClass : Type tc} {Family : Type f}
    {Descriptor : Type d}
    {OneMove : OneClass → Type om} {TwoMove : TwoClass → Type tm}
    (Live : Descriptor → Family → Prop)
    (OneValid : ∀ oneClass,
      Descriptor → Family → OneMove oneClass → Prop)
    (TwoValid : ∀ twoClass,
      Descriptor → Family → TwoMove twoClass → Prop) : Prop :=
  ∀ candidates : Finset
      (RelationalFamilyCandidate
        (SidewiseTaggedFamily OneClass TwoClass Family) Descriptor),
    RelationalCandidateSetActive (fun descriptor family ↦
      Live descriptor family.2) candidates →
      (∀ oneClass : OneClass,
        ∃ move : OneMove oneClass,
          ∀ candidate ∈ candidates,
            Live candidate.2 candidate.1.2 →
              candidate.1.1.1 = oneClass →
                OneValid oneClass candidate.2 candidate.1.2 move) ∧
      (∀ twoClass : TwoClass,
        ∃ move : TwoMove twoClass,
          ∀ candidate ∈ candidates,
            Live candidate.2 candidate.1.2 →
              candidate.1.1.2 = twoClass →
                TwoValid twoClass candidate.2 candidate.1.2 move)

theorem relationalCandidateCommonMoveExists_of_sidewiseDependentClasswise
    {OneClass : Type oc} {TwoClass : Type tc} {Family : Type f}
    {Descriptor : Type d}
    {OneMove : OneClass → Type om} {TwoMove : TwoClass → Type tm}
    (Live : Descriptor → Family → Prop)
    (OneValid : ∀ oneClass,
      Descriptor → Family → OneMove oneClass → Prop)
    (TwoValid : ∀ twoClass,
      Descriptor → Family → TwoMove twoClass → Prop)
    (hclasswise : SidewiseDependentClasswiseMovesExist
      (OneClass := OneClass) (TwoClass := TwoClass)
      Live OneValid TwoValid) :
    RelationalCandidateCommonMoveExists
      (Family := SidewiseTaggedFamily OneClass TwoClass Family)
      (Descriptor := Descriptor)
      (Move := SidewiseDependentMoveBank OneMove TwoMove)
      (fun descriptor family ↦ Live descriptor family.2)
      (SidewiseDependentCandidateValid
        (OneClass := OneClass) (TwoClass := TwoClass) OneValid TwoValid) := by
  intro candidates hactive
  obtain ⟨hone, htwo⟩ := hclasswise candidates hactive
  let oneBank : ∀ oneClass, OneMove oneClass := fun oneClass ↦
    Classical.choose (hone oneClass)
  let twoBank : ∀ twoClass, TwoMove twoClass := fun twoClass ↦
    Classical.choose (htwo twoClass)
  refine ⟨(oneBank, twoBank), ?_⟩
  intro candidate hcandidate hlive
  constructor
  · exact Classical.choose_spec (hone candidate.1.1.1) candidate hcandidate
      hlive rfl
  · exact Classical.choose_spec (htwo candidate.1.1.2) candidate hcandidate
      hlive rfl

theorem sidewiseDependentClasswiseMovesExist_of_commonMove
    {OneClass : Type oc} {TwoClass : Type tc} {Family : Type f}
    {Descriptor : Type d}
    {OneMove : OneClass → Type om} {TwoMove : TwoClass → Type tm}
    (Live : Descriptor → Family → Prop)
    (OneValid : ∀ oneClass,
      Descriptor → Family → OneMove oneClass → Prop)
    (TwoValid : ∀ twoClass,
      Descriptor → Family → TwoMove twoClass → Prop)
    (hcommon : RelationalCandidateCommonMoveExists
      (Family := SidewiseTaggedFamily OneClass TwoClass Family)
      (Descriptor := Descriptor)
      (Move := SidewiseDependentMoveBank OneMove TwoMove)
      (fun descriptor family ↦ Live descriptor family.2)
      (SidewiseDependentCandidateValid
        (OneClass := OneClass) (TwoClass := TwoClass) OneValid TwoValid)) :
    SidewiseDependentClasswiseMovesExist
      (OneClass := OneClass) (TwoClass := TwoClass)
      Live OneValid TwoValid := by
  intro candidates hactive
  obtain ⟨bank, hbank⟩ := hcommon candidates hactive
  constructor
  · intro oneClass
    refine ⟨bank.1 oneClass, ?_⟩
    intro candidate hcandidate hlive hclass
    have hvalid := hbank candidate hcandidate hlive
    subst oneClass
    exact hvalid.1
  · intro twoClass
    refine ⟨bank.2 twoClass, ?_⟩
    intro candidate hcandidate hlive hclass
    have hvalid := hbank candidate hcandidate hlive
    subst twoClass
    exact hvalid.2

/-- Dependent-bank form of the exact sidewise characterization. -/
theorem relationalCandidateCommonMoveExists_sidewiseDependent_iff
    {OneClass : Type oc} {TwoClass : Type tc} {Family : Type f}
    {Descriptor : Type d}
    {OneMove : OneClass → Type om} {TwoMove : TwoClass → Type tm}
    (Live : Descriptor → Family → Prop)
    (OneValid : ∀ oneClass,
      Descriptor → Family → OneMove oneClass → Prop)
    (TwoValid : ∀ twoClass,
      Descriptor → Family → TwoMove twoClass → Prop) :
    RelationalCandidateCommonMoveExists
        (Family := SidewiseTaggedFamily OneClass TwoClass Family)
        (Descriptor := Descriptor)
        (Move := SidewiseDependentMoveBank OneMove TwoMove)
        (fun descriptor family ↦ Live descriptor family.2)
        (SidewiseDependentCandidateValid
          (OneClass := OneClass) (TwoClass := TwoClass) OneValid TwoValid) ↔
      SidewiseDependentClasswiseMovesExist
        (OneClass := OneClass) (TwoClass := TwoClass)
        Live OneValid TwoValid := by
  constructor
  · exact sidewiseDependentClasswiseMovesExist_of_commonMove
      Live OneValid TwoValid
  · exact
      relationalCandidateCommonMoveExists_of_sidewiseDependentClasswise
        Live OneValid TwoValid

end DistributedSynthesis
