/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Formalizations.Definition.DefHistory
import DistributedSynthesis.Formalizations.Definition.DefPathSummary

/-!
# Block, epoch, and handoff abstractions

This file formalizes the requested block-level and epoch-level definitions
from `real_model/paper.tex`.
-/

namespace DistributedSynthesis

universe u v w x y z

/-- The dominant one-way graph for a fixed real side. -/
def dominantGraph : Proc -> Graph
  | .one => .left
  | .two => .right

/-- The dominant process of a graph letter, with `none` for a synchronizing `both` round. -/
def dominantProcessOfGraph : Graph -> Option Proc
  | .left => some .one
  | .right => some .two
  | .both => none

/-- The dominant process of a non-empty graph word is determined by its last graph. -/
def dominantProcessOfWord (word : List Graph) : Option Proc :=
  word.getLast?.bind dominantProcessOfGraph

/-- A one-sided dominance block contains only repetitions of one dominant graph. -/
def IsOneSidedDominanceBlock (side : Proc) (block : List Graph) : Prop :=
  block ≠ [] ∧ ∀ graph ∈ block, graph = dominantGraph side

/--
Definition `def:dominanceepoch`: a dominance epoch is a maximal one-sided
block; maximality is represented relative to the surrounding left and right
context.
-/
structure DominanceEpochIn (word : List Graph) where
  side : Proc
  leftContext : List Graph
  epochBlock : List Graph
  rightContext : List Graph
  reconstruct : word = (leftContext ++ epochBlock ++ rightContext)
  oneSided : IsOneSidedDominanceBlock side epochBlock
  leftMaximal :
    ∀ leftPrefix graph, leftContext = (leftPrefix ++ [graph]) ->
      graph ≠ dominantGraph side
  rightMaximal :
    ∀ graph rightSuffix, rightContext = (graph :: rightSuffix) ->
      graph ≠ dominantGraph side

@[simp]
theorem dominantGraph_other (d : Proc) : dominantGraph d.other = match d with
  | .one => .right
  | .two => .left := by
  cases d <;> rfl

/-- The local outcome of one step in the block-decomposition scan. -/
inductive BlockStep where
  | sameSide
  | bidirectionalBoundary (nextSide : Option Proc)
  | directReversal
  deriving DecidableEq, Repr

/-- A block-decomposition scan records the current side, the current graph, and its scan case. -/
abbrev BlockRound := Proc × Graph × BlockStep

/-- Initial side selection for the deterministic block scan. -/
def initialBlockSide : Graph -> Proc
  | .left => .one
  | .right => .two
  | .both => .one

/-- The deterministic left-to-right scan from Definition `def:blockdecomposition`. -/
def blockDecompositionAux : Proc -> List Graph -> List BlockRound
  | _, [] => []
  | side, graph :: rest =>
      if graph = dominantGraph side then
        (side, graph, .sameSide) :: blockDecompositionAux side rest
      else
        match graph with
        | .both =>
            let nextSide := rest.head?.map initialBlockSide
            let tail :=
              match rest with
              | [] => []
              | nextGraph :: tailRest =>
                  blockDecompositionAux (initialBlockSide nextGraph) tailRest
            (side, graph, .bidirectionalBoundary nextSide) :: tail
        | _ =>
            (side, graph, .directReversal) :: blockDecompositionAux side.other rest

/-- The graph-word block decomposition induced by the deterministic scan. -/
def blockDecomposition (word : List Graph) : List BlockRound :=
  match word with
  | [] => []
  | graph :: _ => blockDecompositionAux (initialBlockSide graph) word

/-- A closing boundary letter packages the current inputs and outputs. -/
structure ClosingLetter (In₁ : Type u) (In₂ : Type v) (Out₁ : Type w) (Out₂ : Type x) where
  inputOne : In₁
  inputTwo : In₂
  outputOne : Out₁
  outputTwo : Out₂

/-- The two one-bit uncertainties tracked across a direct reversal. -/
structure DirectReversalBits where
  oldReceiverAmbiguity : Bool
  newReceiverAmbiguity : Bool
  deriving DecidableEq, Repr

/-- The finite tuple used by direct-reversal successor tests and handoff maps. -/
structure DirectReversalTuple
    (Atom : Proc -> Type y)
    (In₁ : Type u) (In₂ : Type v) (Out₁ : Type w) (Out₂ : Type x)
    (d : Proc) where
  atom : Atom d
  bits : DirectReversalBits
  letter : ClosingLetter In₁ In₂ Out₁ Out₂

/-- Side-local summary data for the one-directional fragment. -/
structure OneDirectionalSummaryData
    (boundary : Type u)
    (summary : Type v)
    (In₁ : Type w) (In₂ : Type x) (Out₁ : Type y) (Out₂ : Type z) where
  init : boundary -> summary
  update : summary -> In₁ -> In₂ -> Out₁ -> Out₂ -> summary
  close : summary -> ClosingLetter In₁ In₂ Out₁ Out₂ -> boundary

/-- Definition `def:uniformonedirectional`. -/
structure UniformOneDirectionalFiniteIndexLemma
    (Alphabet : Type u)
    (In₁ : Type v) (In₂ : Type w) (Out₁ : Type x) (Out₂ : Type y) where
  automaton : DetParityAutomaton.{u, z} Alphabet
  boundary : Type z
  boundaryFinite : Fintype boundary
  summary : Proc -> Type (max u v w x y z)
  summaryFinite : (d : Proc) -> Fintype (summary d)
  sideData : (d : Proc) -> OneDirectionalSummaryData boundary (summary d) In₁ In₂ Out₁ Out₂
  continuationInvariant : Prop
  regularRepresentation : Prop

/-- Direct-reversal successor tests `K_{τ,r}` over old-side typed paths. -/
structure HandoffTests
    (EdgeType : Proc -> Type u)
    (Atom : Proc -> Type v)
    (In₁ : Type w) (In₂ : Type x) (Out₁ : Type y) (Out₂ : Type z) where
  successorTest : (d : Proc) -> DirectReversalTuple Atom In₁ In₂ Out₁ Out₂ d -> Atom d.other -> Set (TypedPath (EdgeType d))

/--
Definition `def:endpointlocalclosure`: iterated direct-reversal successor tests
are determined by a synchronized atom and bounded endpoint windows of the old
typed path.
-/
structure EndpointLocalDirectReversalClosure
    (EdgeType : Proc -> Type u)
    (Atom : Proc -> Type v)
    (In₁ : Type w) (In₂ : Type x) (Out₁ : Type y) (Out₂ : Type z) where
  endpointWindowBound : Nat
  oldSynchronizedAtom : (d : Proc) -> TypedPath (EdgeType d) -> Atom d
  endpointSignature :
    (d : Proc) -> TypedPath (EdgeType d) ->
      Atom d × TypedPath (EdgeType d) × TypedPath (EdgeType d)
  endpointSignature_eq :
    ∀ d path,
      endpointSignature d path =
        (oldSynchronizedAtom d path,
          prefixAtMost endpointWindowBound path,
          suffixAtMost endpointWindowBound path)
  iteratedSuccessorTest : (d : Proc) -> Set (TypedPath (EdgeType d))
  determinedByEndpointSignature :
    ∀ d path₁ path₂,
      endpointSignature d path₁ = endpointSignature d path₂ ->
        (path₁ ∈ iteratedSuccessorTest d ↔ path₂ ∈ iteratedSuccessorTest d)

/-- Definition `def:functionaldirectclosing`. -/
structure FunctionalDirectClosingExtension
    (EdgeType : Proc -> Type u)
    (Atom : Proc -> Type v)
    (In₁ : Type w) (In₂ : Type x) (Out₁ : Type y) (Out₂ : Type z) where
  tests : HandoffTests EdgeType Atom In₁ In₂ Out₁ Out₂
  reachableTuples : (d : Proc) -> Set (DirectReversalTuple Atom In₁ In₂ Out₁ Out₂ d)
  functionalOnReachable : Prop

/-- The block-level epoch transformer from Definition `def:epochtransformer`. -/
structure FiniteEpochTransformer
    (Alphabet : Type u)
    (In₁ : Type v) (In₂ : Type w) (Out₁ : Type x) (Out₂ : Type y) where
  automaton : DetParityAutomaton.{u, z} Alphabet
  boundary : Type z
  boundaryFinite : Fintype boundary
  within : Proc -> Type (max u v w x y z)
  withinFinite : (d : Proc) -> Fintype (within d)
  init : (d : Proc) -> boundary -> within d
  update : (d : Proc) -> within d -> In₁ -> In₂ -> Out₁ -> Out₂ -> within d
  close : (d : Proc) -> within d -> Graph -> ClosingLetter In₁ In₂ Out₁ Out₂ -> boundary
  continuationInvariant : Prop

/-- Definition `def:epochcongruence`. -/
structure EpochCongruentPathSummaries
    (boundary : Type u)
    (EdgeType : Type v)
    (summaryData : PathSummarySemigroup EdgeType)
    (In₁ : Type w) (In₂ : Type x) (Out₁ : Type y) (Out₂ : Type z) where
  summary : Type (max u v w x y z)
  summaryFinite : Fintype summary
  init : boundary -> summary
  update : summary -> In₁ -> In₂ -> summary
  close : summary -> Graph -> ClosingLetter In₁ In₂ Out₁ Out₂ -> boundary
  determinesPathData : Prop
  rightCongruence : Prop

/-- Definition `def:regulartestbasis`. -/
structure FiniteRegularTestBasis
    (boundary : Type u)
    (EdgeType : Type v) where
  test : Type w
  testFinite : Fintype test
  language : test -> Set (TypedPath EdgeType)
  determinesPathData : Prop
  predecessorClosed : Prop
  boundaryClosed : boundary -> Prop
  continuationClosed : Prop
  determinesPathData_proof : determinesPathData
  predecessorClosed_proof : predecessorClosed
  boundaryClosed_proof : ∀ boundaryState, boundaryClosed boundaryState
  continuationClosed_proof : continuationClosed

/-- Regular languages over the typed-path alphabet used by regular-test bases. -/
abbrev TypedPathLanguage (EdgeType : Type u) := Set (TypedPath EdgeType)

/--
Definition `def:regulartestsaturation`: the staged finite Boolean-algebra
closure of a seed family under exact private-input predecessor steps.
-/
structure RegularTestSaturation
    (Alphabet : Type u)
    (EdgeType : Type v)
    (Boundary : Type w)
    (In₁ : Type x) (In₂ : Type y) where
  automaton : DetParityAutomaton.{u, z} Alphabet
  side : Proc
  edgeTypeFinite : Fintype EdgeType
  boundaryFinite : Fintype Boundary
  boundaryAccess : Set Boundary
  seed : Type (max u v w x y z)
  seedFinite : Fintype seed
  seedLanguage : seed -> TypedPathLanguage EdgeType
  seedReadsPathSummary : Prop
  seedReadsEndpointOwners : Prop
  seedReadsParityProgress : Prop
  seedContainsClosingTestsToBoundary : Prop
  stageTest : Nat -> Type (max u v w x y z)
  stageFinite : (n : Nat) -> Fintype (stageTest n)
  stageLanguage : (n : Nat) -> stageTest n -> TypedPathLanguage EdgeType
  stageBooleanAlgebra : (n : Nat) -> Prop
  seedAtZero : seed -> stageTest 0
  seedAtZero_semantics :
    ∀ seedTest, stageLanguage 0 (seedAtZero seedTest) = seedLanguage seedTest
  carry : (n : Nat) -> stageTest n -> stageTest (n + 1)
  carry_semantics :
    ∀ n test, stageLanguage (n + 1) (carry n test) = stageLanguage n test
  privateInputPredecessor :
    (n : Nat) -> ((In₁ × In₂) -> stageTest n) -> stageTest (n + 1)
  privateInputPredecessor_exact :
    ∀ (n : Nat) (_tuple : (In₁ × In₂) -> stageTest n), Prop
  successorGeneratedByCarryAndPredecessors : (n : Nat) -> Prop
  regularLanguageEquivalenceDecidable : (n : Nat) -> DecidableEq (stageTest n)

attribute [instance] RegularTestSaturation.edgeTypeFinite
attribute [instance] RegularTestSaturation.boundaryFinite
attribute [instance] RegularTestSaturation.seedFinite
attribute [instance] RegularTestSaturation.stageFinite
attribute [instance] RegularTestSaturation.regularLanguageEquivalenceDecidable

/-- Stabilization of the regular-test saturation sequence at a finite stage. -/
def RegularTestSaturation.StableAt
    {Alphabet : Type u}
    {EdgeType : Type v}
    {Boundary : Type w}
    {In₁ : Type x} {In₂ : Type y}
    (sat : RegularTestSaturation Alphabet EdgeType Boundary In₁ In₂)
    (n : Nat) : Prop :=
  (∀ testNext : sat.stageTest (n + 1),
    ∃ test : sat.stageTest n,
      sat.stageLanguage (n + 1) testNext = sat.stageLanguage n test) ∧
  (∀ test : sat.stageTest n,
    ∃ testNext : sat.stageTest (n + 1),
      sat.stageLanguage n test = sat.stageLanguage (n + 1) testNext)

/-- A configuration paired with the current automaton state. -/
structure ContinuationConfiguration
    (In₁ : Type u) (In₂ : Type v) (Out₁ : Type w) (Out₂ : Type x)
    (State : Type y) where
  history : History In₁ In₂ Graph Out₁ Out₂
  automatonState : State
  receiptOne : ReceiptTag
  receiptTwo : ReceiptTag

/-- The three cases of non-fringe containment order used in `def:Acontinuation`. -/
inductive NonFringeContainmentOrder where
  | secondInFirst
  | firstInSecond
  | equivalent
  deriving DecidableEq, Repr

instance : Fintype NonFringeContainmentOrder where
  elems :=
    {NonFringeContainmentOrder.secondInFirst,
      NonFringeContainmentOrder.firstInSecond,
      NonFringeContainmentOrder.equivalent}
  complete := by
    intro order
    cases order <;> simp

/-- Pending acknowledgement status for one process in a finite retraction candidate. -/
inductive PendingAcknowledgementStatus where
  | none
  | pending
  | resolved
  deriving DecidableEq, Repr

/-- The finite receipt/order component of candidate retraction data. -/
structure ReceiptOrderData where
  receiptOne : ReceiptTag
  receiptTwo : ReceiptTag
  containmentOrder : NonFringeContainmentOrder
  deriving DecidableEq, Repr

instance : Fintype ReceiptOrderData :=
  Fintype.ofEquiv
    (ReceiptTag × ReceiptTag × NonFringeContainmentOrder)
    {
      toFun := fun data => {
        receiptOne := data.1
        receiptTwo := data.2.1
        containmentOrder := data.2.2
      }
      invFun := fun data =>
        (data.receiptOne, data.receiptTwo, data.containmentOrder)
      left_inv := by
        intro data
        cases data with
        | mk receiptOne rest =>
            cases rest with
            | mk receiptTwo containmentOrder => rfl
      right_inv := by
        intro data
        cases data
        rfl
    }

/--
Definition `def:candidateretraction`: finite data proposed for a constructive
finite `A`-index proof.
-/
structure CandidateFiniteRetractionData
    (AutomatonProfile : Type u)
    (FixedInputPathSummary : Type v)
    (ParityProgress : Type w) where
  profileFinite : Fintype AutomatonProfile
  pathSummaryFinite : Fintype FixedInputPathSummary
  parityProgressFinite : Fintype ParityProgress
  automatonProfile : AutomatonProfile
  receiptOrder : ReceiptOrderData
  pendingOne : PendingAcknowledgementStatus
  pendingTwo : PendingAcknowledgementStatus
  fixedInputPathSummary : FixedInputPathSummary
  parityProgress : ParityProgress

attribute [instance] CandidateFiniteRetractionData.profileFinite
attribute [instance] CandidateFiniteRetractionData.pathSummaryFinite
attribute [instance] CandidateFiniteRetractionData.parityProgressFinite

/-- Definition `def:Acontinuation`. -/
def AContinuationEquivalent
    {In₁ : Type u} {In₂ : Type v} {Out₁ : Type w} {Out₂ : Type x} {State : Type y}
    (sameParityOutcomes :
      ContinuationConfiguration In₁ In₂ Out₁ Out₂ State ->
      ContinuationConfiguration In₁ In₂ Out₁ Out₂ State ->
      Prop)
    (containmentOrder :
      ContinuationConfiguration In₁ In₂ Out₁ Out₂ State -> NonFringeContainmentOrder)
    (c c' : ContinuationConfiguration In₁ In₂ Out₁ Out₂ State) : Prop :=
  c.automatonState = c'.automatonState ∧
    c.receiptOne = c'.receiptOne ∧
    c.receiptTwo = c'.receiptTwo ∧
    containmentOrder c = containmentOrder c' ∧
    sameParityOutcomes c c'

/-- Definition `def:finitehandoff`. -/
structure FiniteDirectReversalHandoff
    (Atom : Proc -> Type u)
    (In₁ : Type v) (In₂ : Type w) (Out₁ : Type x) (Out₂ : Type y) where
  handoff :
    (d : Proc) ->
      DirectReversalTuple Atom In₁ In₂ Out₁ Out₂ d ->
      Atom d.other
  invariant : Prop

end DistributedSynthesis
