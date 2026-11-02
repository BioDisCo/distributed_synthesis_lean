/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPointedSupportedSuccessor
import DistributedSynthesis.Formalizations.Lemma.LemActualFullViewFamilyRecovery

/-!
# A carried pointed-successor plan at a full-view receive

The pointed construction supplies one finite table whose rows are indexed by
the current hidden descriptor.  This file records the operational handoff
which that table needs.  A local summary carries the whole table.  On a
`recv` step the receiver applies the *partner's delivered table* to one query
computed from the two delivered finite summaries and the two current inputs.

The query computation is graph-blind: it is a field of `stepRecv`, and hence
sees exactly the data of a literal local receive.  It receives no graph,
orientation, lane, or strict-leader bit.  Correctness is conditional only on
the explicitly named query-alignment equation saying that this finite joint
query is the actual live pointed query.  Under alignment and pointed
totality, evaluation cannot return `none`; its answer is supported, is an
exact semantic edge, and performs the required parity-control update.

The final section connects this evaluation to the existing end-to-end
receipt seam.  The present legacy receipt carrier stores one already-selected
family move rather than a descriptor-indexed table.  Accordingly its adapter
has one honest premise, `...SenderMatchesPointedPlanAt`, asserting that this
old slot contains the move obtained by evaluating the delivered table at the
aligned receive query.  Everything after that premise is proved here.  A
future concrete carrier which stores the table directly can use the generic
local-summary wrapper and does not need that legacy premise.
-/

namespace DistributedSynthesis

universe u v o q a t m c x y s

/-! ## A graph-blind local-summary wrapper carrying one finite plan -/

variable {In₁ : Type u} {In₂ : Type v}

/-- A base local summary, its finite outgoing plan, and the answer most
recently installed by a receive. -/
structure CarriedPointedSuccessorSummary
    (M : LocalSummaryAutomaton.{u, v, o} In₁ In₂)
    (Table : Type t) (Answer : Type a) (d : Proc) where
  base : M.Summary d
  carried : Table
  installed : Option Answer

noncomputable instance
    (M : LocalSummaryAutomaton.{u, v, o} In₁ In₂)
    (Table : Type t) (Answer : Type a) [Fintype Table] [Fintype Answer]
    (d : Proc) :
    Fintype (CarriedPointedSuccessorSummary M Table Answer d) := by
  classical
  let encode : CarriedPointedSuccessorSummary M Table Answer d →
      M.Summary d × Table × Option Answer :=
    fun summary => (summary.base, summary.carried, summary.installed)
  exact Fintype.ofInjective encode (by
    intro left right heq
    rcases left with ⟨leftBase, leftCarried, leftInstalled⟩
    rcases right with ⟨rightBase, rightCarried, rightInstalled⟩
    simp only [encode, Prod.mk.injEq] at heq
    rcases heq with ⟨rfl, rfl, rfl⟩
    rfl)

/-- The only query interface available at a receive.  Both summaries and
both current inputs are available because they are exactly the arguments of
`LocalSummaryAutomaton.stepRecv`; no graph or leader signal is present. -/
structure PointedReceiveQueryReader
    (M : LocalSummaryAutomaton.{u, v, o} In₁ In₂) (Query : Type q) where
  recv : (d : Proc) → M.Summary d → PSum In₁ In₂ →
    M.Summary d.other → PSum In₁ In₂ → Query

namespace LocalSummaryAutomaton

/-- Extend a local-summary automaton by a finite plan which is delivered at
receives.  The receiver keeps its own outgoing plan, and installs the result
of applying the partner's delivered plan to the joint receive query. -/
noncomputable def withCarriedPointedSuccessor
    (M : LocalSummaryAutomaton.{u, v, o} In₁ In₂)
    {Query : Type q} {Answer : Type a}
    [Fintype Query] [Fintype Answer]
    (initialTable : (d : Proc) → Query → Option Answer)
    (initialInstalled : (d : Proc) → Option Answer)
    (reader : PointedReceiveQueryReader M Query) :
    LocalSummaryAutomaton In₁ In₂ where
  Summary d := CarriedPointedSuccessorSummary M
    (Query → Option Answer) Answer d
  finite d := by
    classical
    infer_instance
  initial d :=
    { base := M.initial d
      carried := initialTable d
      installed := initialInstalled d }
  stepNoRecv d self input :=
    { base := M.stepNoRecv d self.base input
      carried := self.carried
      installed := self.installed }
  stepRecv d self inputSelf other inputOther :=
    { base := M.stepRecv d self.base inputSelf other.base inputOther
      carried := self.carried
      installed := other.carried
        (reader.recv d self.base inputSelf other.base inputOther) }

@[simp] theorem withCarriedPointedSuccessor_stepRecv_installed
    (M : LocalSummaryAutomaton.{u, v, o} In₁ In₂)
    {Query : Type q} {Answer : Type a}
    [Fintype Query] [Fintype Answer]
    (initialTable : (d : Proc) → Query → Option Answer)
    (initialInstalled : (d : Proc) → Option Answer)
    (reader : PointedReceiveQueryReader M Query)
    (d : Proc)
    (self : CarriedPointedSuccessorSummary M
      (Query → Option Answer) Answer d)
    (inputSelf : PSum In₁ In₂)
    (other : CarriedPointedSuccessorSummary M
      (Query → Option Answer) Answer d.other)
    (inputOther : PSum In₁ In₂) :
    ((M.withCarriedPointedSuccessor initialTable initialInstalled reader).stepRecv
      d self inputSelf other inputOther).installed =
      other.carried
        (reader.recv d self.base inputSelf other.base inputOther) :=
  rfl

@[simp] theorem withCarriedPointedSuccessor_read_recv_installed
    (M : LocalSummaryAutomaton.{u, v, o} In₁ In₂)
    {Query : Type q} {Answer : Type a}
    [Fintype Query] [Fintype Answer]
    (initialTable : (d : Proc) → Query → Option Answer)
    (initialInstalled : (d : Proc) → Option Answer)
    (reader : PointedReceiveQueryReader M Query)
    (d : Proc) (previousSelf : View In₁ In₂ d)
    (inputSelf : PSum In₁ In₂)
    (previousOther : View In₁ In₂ d.other)
    (inputOther : PSum In₁ In₂) :
    ((M.withCarriedPointedSuccessor initialTable initialInstalled reader).read
      (.recv previousSelf inputSelf previousOther inputOther)).installed =
      ((M.withCarriedPointedSuccessor initialTable initialInstalled reader).read
        previousOther).carried
        (reader.recv d
          ((M.withCarriedPointedSuccessor initialTable initialInstalled
            reader).read previousSelf).base inputSelf
          ((M.withCarriedPointedSuccessor initialTable initialInstalled
            reader).read previousOther).base inputOther) :=
  rfl

/-- The wrapper does not alter the underlying local-summary fold. -/
@[simp] theorem withCarriedPointedSuccessor_read_base
    (M : LocalSummaryAutomaton.{u, v, o} In₁ In₂)
    {Query : Type q} {Answer : Type a}
    [Fintype Query] [Fintype Answer]
    (initialTable : (d : Proc) → Query → Option Answer)
    (initialInstalled : (d : Proc) → Option Answer)
    (reader : PointedReceiveQueryReader M Query)
    {d : Proc} (view : View In₁ In₂ d) :
    ((M.withCarriedPointedSuccessor initialTable initialInstalled reader).read
      view).base = M.read view := by
  induction view with
  | empty p => rfl
  | noRecv previous input ih =>
      change M.stepNoRecv _ _ input = M.stepNoRecv _ _ input
      rw [ih]
  | recv previousSelf inputSelf previousOther inputOther ihSelf ihOther =>
      change M.stepRecv _ _ inputSelf _ inputOther =
        M.stepRecv _ _ inputSelf _ inputOther
      rw [ihSelf, ihOther]

/-- Until a later controller refresh replaces it, a process carries its own
initial finite plan through both blind and receive steps. -/
@[simp] theorem withCarriedPointedSuccessor_read_carried
    (M : LocalSummaryAutomaton.{u, v, o} In₁ In₂)
    {Query : Type q} {Answer : Type a}
    [Fintype Query] [Fintype Answer]
    (initialTable : (d : Proc) → Query → Option Answer)
    (initialInstalled : (d : Proc) → Option Answer)
    (reader : PointedReceiveQueryReader M Query)
    {d : Proc} (view : View In₁ In₂ d) :
    ((M.withCarriedPointedSuccessor initialTable initialInstalled reader).read
      view).carried = initialTable d := by
  induction view with
  | empty p => rfl
  | noRecv previous input ih => exact ih
  | recv previousSelf inputSelf previousOther inputOther ihSelf _ => exact ihSelf

end LocalSummaryAutomaton

/-! ## Exact alignment and evaluation -/

/-- The sole semantic recovery premise for a receive: the graph-blind joint
finite query computed by `stepRecv` is the actual pointed query. -/
def PointedReceiveQueryAligned
    {M : LocalSummaryAutomaton.{u, v, o} In₁ In₂} {Query : Type q}
    (reader : PointedReceiveQueryReader M Query) (d : Proc)
    (self : M.Summary d) (inputSelf : PSum In₁ In₂)
    (other : M.Summary d.other) (inputOther : PSum In₁ In₂)
    (actual : Query) : Prop :=
  reader.recv d self inputSelf other inputOther = actual

/-- At the unrestricted local-view level, the query-alignment decoder exists
for every pointed query defined from the settled history and both current
inputs.  This consumes the exact full-view recovery theorem and makes clear
what it does *not* prove: factorization through a chosen finite base summary
still needs a separate invariant. -/
theorem generatedReceiveOne_settledPointedQuery_partialFactorizes
    {Out₁ : Type x} {Out₂ : Type y}
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    {Query : Type q}
    (query : History In₁ In₂ Graph Out₁ Out₂ → In₁ → In₂ →
      Query) :
    QueryPartialFactorizes GeneratedReceiveOne.view
      (fun occurrence : GeneratedReceiveOne strategy =>
        query occurrence.history occurrence.environment.inputOne
          occurrence.environment.inputTwo) :=
  generatedReceiveOne_fixedFamily_fullView_partialFactorizes query

/-- Process-two mirror. -/
theorem generatedReceiveTwo_settledPointedQuery_partialFactorizes
    {Out₁ : Type x} {Out₂ : Type y}
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    {Query : Type q}
    (query : History In₁ In₂ Graph Out₁ Out₂ → In₁ → In₂ →
      Query) :
    QueryPartialFactorizes GeneratedReceiveTwo.view
      (fun occurrence : GeneratedReceiveTwo strategy =>
        query occurrence.history occurrence.environment.inputOne
          occurrence.environment.inputTwo) :=
  generatedReceiveTwo_fixedFamily_fullView_partialFactorizes query

section Pointed

variable {Code : Type c} {MoveIdentity : Type m}
variable (D : DetParityAutomaton.{c, s} Code)
variable {FamilyMove : Type x} {Direction : Type y}
variable [Fintype Code] [Fintype MoveIdentity]

/-- A finite pointed table is correct on every live and valid query. -/
def PointedSupportedSuccessorTableWorks
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
      (Direction := Direction)) : Prop :=
  ∀ query,
    Live query.current query.currentFamily →
    Valid query.currentFamily query.move →
    ∃ answer,
      table query = some answer ∧
        PointedSupportedSuccessorGood D ExactEdge Supported query answer

/-- Pointed totality materializes one correct finite table. -/
theorem pointedSupportedSuccessor?_works
    (Represented : HiddenCodeControlDescriptor D
        (MoveIdentity := MoveIdentity) →
      HiddenDescriptorTwoFibreFamily D (MoveIdentity := MoveIdentity) → Prop)
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
    (totality : PointedHiddenDescriptorFamilyTotality D Represented Live
      ExactEdge Valid Supported) :
    PointedSupportedSuccessorTableWorks D Live ExactEdge Valid Supported
      (pointedSupportedSuccessor? D ExactEdge Supported) := by
  intro query hlive hvalid
  exact pointedSupportedSuccessor?_spec D Represented Live ExactEdge Valid
    Supported totality query hlive hvalid

/-- Evaluation at an aligned receive query yields a supported exact answer.
This is the table-level core of the operational handoff. -/
theorem pointedTable_evaluates_good_of_aligned
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
    (computed actual : PointedSupportedSuccessorQuery D
      (MoveIdentity := MoveIdentity) (FamilyMove := FamilyMove)
      (Direction := Direction))
    (haligned : computed = actual)
    (hlive : Live actual.current actual.currentFamily)
    (hvalid : Valid actual.currentFamily actual.move) :
    ∃ answer,
      table computed = some answer ∧
        PointedSupportedSuccessorGood D ExactEdge Supported actual answer := by
  subst computed
  exact hworks actual hlive hvalid

variable [Fintype FamilyMove] [Fintype Direction]

/-- End-to-end read theorem for the carried-plan wrapper.  Once its joint
finite query aligns with the actual live query, the receive-installed answer
is nonempty and satisfies support, exactness, and the parity-control step. -/
theorem LocalSummaryAutomaton.read_recv_installs_good_pointedAnswer
    (M : LocalSummaryAutomaton.{u, v, o} In₁ In₂)
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
    (initialTable : (d : Proc) → PointedSupportedSuccessorTable D
      (MoveIdentity := MoveIdentity) (FamilyMove := FamilyMove)
      (Direction := Direction))
    (initialInstalled : (d : Proc) →
      Option (PointedSupportedSuccessorAnswer D
        (MoveIdentity := MoveIdentity)))
    (reader : PointedReceiveQueryReader M
      (PointedSupportedSuccessorQuery D (MoveIdentity := MoveIdentity)
        (FamilyMove := FamilyMove) (Direction := Direction)))
    (d : Proc) (previousSelf : View In₁ In₂ d)
    (inputSelf : PSum In₁ In₂)
    (previousOther : View In₁ In₂ d.other)
    (inputOther : PSum In₁ In₂)
    (actual : PointedSupportedSuccessorQuery D
      (MoveIdentity := MoveIdentity) (FamilyMove := FamilyMove)
      (Direction := Direction))
    (haligned :
      reader.recv d
        ((M.withCarriedPointedSuccessor initialTable initialInstalled reader).read
          previousSelf).base inputSelf
        ((M.withCarriedPointedSuccessor initialTable initialInstalled reader).read
          previousOther).base inputOther = actual)
    (hworks : PointedSupportedSuccessorTableWorks D Live ExactEdge Valid
      Supported
      ((M.withCarriedPointedSuccessor initialTable initialInstalled reader).read
        previousOther).carried)
    (hlive : Live actual.current actual.currentFamily)
    (hvalid : Valid actual.currentFamily actual.move) :
    ∃ answer,
      ((M.withCarriedPointedSuccessor initialTable initialInstalled reader).read
        (.recv previousSelf inputSelf previousOther inputOther)).installed =
          some answer ∧
        PointedSupportedSuccessorGood D ExactEdge Supported actual answer := by
  obtain ⟨answer, htable, hgood⟩ := hworks actual hlive hvalid
  refine ⟨answer, ?_, hgood⟩
  rw [LocalSummaryAutomaton.withCarriedPointedSuccessor_read_recv_installed]
  rw [haligned, htable]

/-- In particular the public successor family installed by the wrapper is
exactly the family component of its good relational answer. -/
theorem LocalSummaryAutomaton.read_recv_installs_good_pointedFamily
    (M : LocalSummaryAutomaton.{u, v, o} In₁ In₂)
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
    (initialTable : (d : Proc) → PointedSupportedSuccessorTable D
      (MoveIdentity := MoveIdentity) (FamilyMove := FamilyMove)
      (Direction := Direction))
    (initialInstalled : (d : Proc) →
      Option (PointedSupportedSuccessorAnswer D
        (MoveIdentity := MoveIdentity)))
    (reader : PointedReceiveQueryReader M
      (PointedSupportedSuccessorQuery D (MoveIdentity := MoveIdentity)
        (FamilyMove := FamilyMove) (Direction := Direction)))
    (d : Proc) (previousSelf : View In₁ In₂ d)
    (inputSelf : PSum In₁ In₂)
    (previousOther : View In₁ In₂ d.other)
    (inputOther : PSum In₁ In₂)
    (actual : PointedSupportedSuccessorQuery D
      (MoveIdentity := MoveIdentity) (FamilyMove := FamilyMove)
      (Direction := Direction))
    (haligned :
      reader.recv d
        ((M.withCarriedPointedSuccessor initialTable initialInstalled reader).read
          previousSelf).base inputSelf
        ((M.withCarriedPointedSuccessor initialTable initialInstalled reader).read
          previousOther).base inputOther = actual)
    (hworks : PointedSupportedSuccessorTableWorks D Live ExactEdge Valid
      Supported
      ((M.withCarriedPointedSuccessor initialTable initialInstalled reader).read
        previousOther).carried)
    (hlive : Live actual.current actual.currentFamily)
    (hvalid : Valid actual.currentFamily actual.move) :
    ∃ answer,
      Option.map Prod.fst
        ((M.withCarriedPointedSuccessor initialTable initialInstalled reader).read
          (.recv previousSelf inputSelf previousOther inputOther)).installed =
            some answer.1 ∧
        PointedSupportedSuccessorGood D ExactEdge Supported actual answer := by
  obtain ⟨answer, hinstalled, hgood⟩ :=
    M.read_recv_installs_good_pointedAnswer D Live ExactEdge Valid Supported
      initialTable initialInstalled reader d previousSelf inputSelf previousOther
      inputOther actual haligned hworks hlive hvalid
  refine ⟨answer, ?_, hgood⟩
  rw [hinstalled]
  rfl

end Pointed

/-! ## Adapter to the existing fixed-move receipt seam -/

namespace DetParityAutomaton

variable {Out₁ : Type x} {Out₂ : Type y}
variable
  (A : DetParityAutomaton.{max u v x y, s}
    (RoundRecord In₁ In₂ Graph Out₁ Out₂))

noncomputable section

variable [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁]
  [Inhabited Out₂]
variable [Fintype In₁] [Fintype In₂] [Fintype Out₁]
  [Fintype Out₂]
variable [DecidableEq In₁] [DecidableEq In₂]

open PairedStrategyMemory
open PairedStrategyMemory.PairedInitialProfiledRationalPackage

variable (package : PairedInitialProfiledRationalPackage A)

/-- Exact integration premise for the legacy process-one receipt carrier.
The old sender slot contains one fixed left-family move; this says it agrees
with the move selected by the delivered pointed plan at this receive query. -/
def EndToEndLeftSenderMatchesPointedPlanAt
    {Query : Type q} {Answer : Type a}
    (initialOne : EndToEndFamilyReceiptOneSummary A package)
    (initialTwo : EndToEndFamilyReceiptTwoSummary A package)
    (previousTwo : View In₁ In₂ .two)
    (table : Query → Option Answer) (query : Query)
    (moveOf : Answer → EndToEndLeftFamilyPairMove A package) : Prop :=
  ∀ answer, table query = some answer →
    let M := endToEndFamilyReceiptSummaryAutomaton A package initialOne initialTwo
      (endToEndFamilyReceiptSyncOrActivateReceivePairTable A package)
    (M.read previousTwo).1.1.leftSender.1 = moveOf answer

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
/-- Once the delivered plan has a good answer and the legacy carried-move
slot matches that evaluation, the existing receive seam installs exactly the
selected move. -/
theorem endToEndFamilyReceipt_read_recv_one_installs_evaluatedPointedPlan
    {Query : Type q} {Answer : Type a}
    (initialOne : EndToEndFamilyReceiptOneSummary A package)
    (initialTwo : EndToEndFamilyReceiptTwoSummary A package)
    (previousOne : View In₁ In₂ .one) (inputOne : In₁)
    (previousTwo : View In₁ In₂ .two) (inputTwo : In₂)
    (table : Query → Option Answer) (query : Query)
    (moveOf : Answer → EndToEndLeftFamilyPairMove A package)
    (Good : Query → Answer → Prop)
    (hlookup : ∃ answer, table query = some answer ∧ Good query answer)
    (hmatch : EndToEndLeftSenderMatchesPointedPlanAt A package initialOne
      initialTwo previousTwo table query moveOf) :
    ∃ answer,
      Good query answer ∧
        let M := endToEndFamilyReceiptSummaryAutomaton A package initialOne
          initialTwo
          (endToEndFamilyReceiptSyncOrActivateReceivePairTable A package)
        (M.read (.recv previousOne (.inl inputOne) previousTwo
          (.inr inputTwo))).1.1.leftReceiver.2.1 = moveOf answer := by
  obtain ⟨answer, htable, hgood⟩ := hlookup
  refine ⟨answer, hgood, ?_⟩
  exact endToEndFamilyReceipt_read_recv_one_follows_supported A package
    initialOne initialTwo previousOne inputOne previousTwo inputTwo
    (moveOf answer) (hmatch answer htable)

/-- Process-two mirror. -/
def EndToEndRightSenderMatchesPointedPlanAt
    {Query : Type q} {Answer : Type a}
    (initialOne : EndToEndFamilyReceiptOneSummary A package)
    (initialTwo : EndToEndFamilyReceiptTwoSummary A package)
    (previousOne : View In₁ In₂ .one)
    (table : Query → Option Answer) (query : Query)
    (moveOf : Answer → EndToEndRightFamilyPairMove A package) : Prop :=
  ∀ answer, table query = some answer →
    let M := endToEndFamilyReceiptSummaryAutomaton A package initialOne initialTwo
      (endToEndFamilyReceiptSyncOrActivateReceivePairTable A package)
    (M.read previousOne).1.1.rightSender.1 = moveOf answer

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
theorem endToEndFamilyReceipt_read_recv_two_installs_evaluatedPointedPlan
    {Query : Type q} {Answer : Type a}
    (initialOne : EndToEndFamilyReceiptOneSummary A package)
    (initialTwo : EndToEndFamilyReceiptTwoSummary A package)
    (previousTwo : View In₁ In₂ .two) (inputTwo : In₂)
    (previousOne : View In₁ In₂ .one) (inputOne : In₁)
    (table : Query → Option Answer) (query : Query)
    (moveOf : Answer → EndToEndRightFamilyPairMove A package)
    (Good : Query → Answer → Prop)
    (hlookup : ∃ answer, table query = some answer ∧ Good query answer)
    (hmatch : EndToEndRightSenderMatchesPointedPlanAt A package initialOne
      initialTwo previousOne table query moveOf) :
    ∃ answer,
      Good query answer ∧
        let M := endToEndFamilyReceiptSummaryAutomaton A package initialOne
          initialTwo
          (endToEndFamilyReceiptSyncOrActivateReceivePairTable A package)
        (M.read (.recv previousTwo (.inr inputTwo) previousOne
          (.inl inputOne))).1.1.rightReceiver.2.1 = moveOf answer := by
  obtain ⟨answer, htable, hgood⟩ := hlookup
  refine ⟨answer, hgood, ?_⟩
  exact endToEndFamilyReceipt_read_recv_two_follows_supported A package
    initialOne initialTwo previousTwo inputTwo previousOne inputOne
    (moveOf answer) (hmatch answer htable)

end

end DetParityAutomaton

end DistributedSynthesis
