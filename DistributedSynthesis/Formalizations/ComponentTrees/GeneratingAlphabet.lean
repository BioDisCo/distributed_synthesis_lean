/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Formalizations.ComponentTrees.SymbolicAlphabet
import DistributedSynthesis.Formalizations.ComponentTrees.FiniteRunMSOStar

/-! Node labels (K,q,r,λ,gen). The incoming table belongs to the child.
Its predecessor graph is recorded once, and each row stores a block scenario,
equivalently a predecessor edge and a length-D signal block. The root uses
none. No successor component or successor ordering is stored at the parent.
-/
namespace Characterisation.ComponentTrees.GeneratingAlphabet
open DistributedSynthesis Characterisation Characterisation.PeriodicBlocks
open Characterisation.ComponentGames
open scoped Characterisation.ComponentGames.Representation DistributedSynthesis.FiniteOrders
open scoped Characterisation.ComponentGames.FiniteEnumeration
open scoped Characterisation.ComponentGames.Representation.FiniteArena
set_option maxHeartbeats 2400000
set_option linter.unusedSectionVars false
variable {I₁ I₂ O₁ O₂ G : Type} {D capacity : Nat}
variable [Fintype I₁] [Fintype I₂] [DecidableEq I₁] [DecidableEq I₂]
variable [Fintype O₁] [Fintype O₂] [DecidableEq O₁] [DecidableEq O₂]
variable [LinearOrder I₁] [LinearOrder I₂] [LinearOrder O₁] [LinearOrder O₂]
variable (B : DetParityAutomaton (BlockWord (ContinuationLetter I₁ I₂ O₁ O₂) D))
variable [LinearOrder B.State]
variable (live : B.State → Bool) (bound : Nat) (positive : 0 < capacity)

abbrev Description := FinitePositions.Position B.State capacity
abbrev Extension (P : Description (capacity:=capacity) B) := ClosingLayer P.Root I₁ I₂ D
abbrev Incoming (P : Description (capacity:=capacity) B) :=
  Option ((previous : Description (capacity:=capacity) B) × (P.Root → Extension B previous))
abbrev Data := (current : SymbolicAlphabet.Data B live bound positive) × Incoming B current.val.source
abbrev Letter := Option (Data B live bound positive)
abbrev Frame := (P : Description (capacity:=capacity) B) × Incoming B P
abbrev Edge := (frame : Frame (capacity:=capacity) B) × frame.1.Root

instance letterFintype : Fintype (Letter B live bound positive) := inferInstance
instance letterDecidableEq : DecidableEq (Letter B live bound positive) := by
  unfold Letter Data Incoming SymbolicAlphabet.Data
  infer_instance
instance edgeFintype : Fintype (Edge (capacity:=capacity) B) := inferInstance
instance edgeDecidableEq : DecidableEq (Edge (capacity:=capacity) B) := inferInstance

def frame (current : Data B live bound positive) : Frame (capacity:=capacity) B :=
  ⟨current.1.val.source,current.2⟩

def edge (current : Data B live bound positive) (e : current.1.val.source.Root) : Edge (capacity:=capacity) B :=
  ⟨frame B live bound positive current,e⟩

def forgetEdge (e : Edge (capacity:=capacity) B) : FiniteAlphabet.Edge (capacity:=capacity) B :=
  ⟨e.1.1,e.2⟩

def backMap (m : FiniteAlphabet.Move (capacity:=capacity) B) (target : Frame (capacity:=capacity) B) :
    Option (target.1.Root → m.End) :=
  match target.2 with
  | none => none
  | some incoming =>
    if same : incoming.1 = m.source then
      some (cast (congrArg (fun P : Description (capacity:=capacity) B => target.1.Root → Extension B P) same) incoming.2)
    else none

def child (m : FiniteAlphabet.Move (capacity:=capacity) B) :
    Letter B live bound positive → Option (FiniteAlphabet.Child B m)
  | none => none
  | some current => (backMap B m (frame B live bound positive current)).map
      (fun gen => ⟨current.1.val.source,gen⟩)

def raw (current : Data B live bound positive) (children : Fin capacity → Letter B live bound positive) :
    FiniteAlphabet.Raw (capacity:=capacity) B :=
  ⟨current.1.val,fun dir => child B live bound positive current.1.val (children dir)⟩

/-- The existing component check supplies incidence, states, coverage, and
uniqueness. The final equality prevents a non-padding child from being ignored. -/
def StarLegal : Letter B live bound positive → (Fin capacity → Letter B live bound positive) → Prop
  | none,children => ∀ dir, children dir = none
  | some current,children =>
    FiniteAlphabet.Legal B live bound (raw B live bound positive current children) ∧
      ∀ dir, (child B live bound positive current.1.val (children dir)).isSome = (children dir).isSome

instance starLegalDecidable (current : Letter B live bound positive)
    (children : Fin capacity → Letter B live bound positive) :
    Decidable (StarLegal B live bound positive current children) := by
  cases current <;> unfold StarLegal <;> infer_instance

def starTest (current : Letter B live bound positive) (children : Fin capacity → Letter B live bound positive) : Bool :=
  decide (StarLegal B live bound positive current children)

def rootTest : Letter B live bound positive → Bool
  | none => false
  | some current => decide (current.1.val.source = FiniteAlphabet.initialPosition B positive ∧ current.2 = none)

def edgeTest : Letter B live bound positive → Edge (capacity:=capacity) B → Bool
  | none,_ => false
  | some current,e => decide (e.1 = frame B live bound positive current)

def Step (current : Data B live bound positive) (e e' : Edge (capacity:=capacity) B) : Prop :=
  ∃ origin : current.1.val.source.Root, e = edge B live bound positive current origin ∧
    ∃ gen, backMap B current.1.val e'.1 = some gen ∧
      closingLayerRoot D (gen e'.2) = current.1.val.replacement origin

instance stepDecidable (current : Data B live bound positive) (e e' : Edge (capacity:=capacity) B) :
    Decidable (Step B live bound positive current e e') := by
  unfold Step
  infer_instance

def stepTest : Letter B live bound positive → Fin capacity → Edge (capacity:=capacity) B → Edge (capacity:=capacity) B → Bool
  | none,_,_,_ => false
  | some current,_,e,e' => decide (Step B live bound positive current e e')

/-- The edge tag repeats the node's incoming table only inside the run
automaton. The allowed test forces it to be the table in the input label. -/
def tables : FiniteRunMSO.Tables (Fin capacity) (Letter B live bound positive) (Edge (capacity:=capacity) B) where
  initial := ⟨⟨FiniteAlphabet.initialPosition B positive,none⟩,⟨0,by change 0 < 1; omega⟩⟩
  root := rootTest B live bound positive
  child _ _ _ := true
  allowed := edgeTest B live bound positive
  step := stepTest B live bound positive
  priority _ e := B.priority (e.1.1.2.state e.2)

instance letterOrder : LinearOrder (Letter B live bound positive) := inferInstance
instance edgeOrder : LinearOrder (Edge (capacity:=capacity) B) := inferInstance

def edgeIndex : Edge (capacity:=capacity) B ≃ Fin (Fintype.card (Edge (capacity:=capacity) B)) :=
  (monoEquivOfFin (Edge (capacity:=capacity) B) rfl).toEquiv.symm

abbrev Local := FiniteRunMSO.Star.Local (tables B live bound positive) (starTest B live bound positive)
abbrev Accepting := FiniteRunMSO.Star.Accepting (tables B live bound positive) (starTest B live bound positive)

def sentence : MSO.Sentence (MSO.Tree.language (Fin capacity) (Letter B live bound positive)) :=
  FiniteRunMSO.Star.sentence (tables B live bound positive) (starTest B live bound positive) (edgeIndex B)

theorem sentence_correct (tree : LabeledTree (Fin capacity) (Letter B live bound positive)) :
    MSO.Tree.Satisfies tree (sentence B live bound positive) ↔ Accepting B live bound positive tree := by
  letI : Nonempty (Fin capacity) := ⟨⟨0,positive⟩⟩
  exact FiniteRunMSO.Star.sentence_correct _ _ _ tree

def satisfiable : Bool :=
  letI : Inhabited (Fin capacity) := ⟨⟨0,positive⟩⟩
  MSO.Tree.Executable.satisfiable (sentence B live bound positive)

theorem satisfiable_accepting_iff : satisfiable B live bound positive = true ↔
    ∃ tree, Accepting B live bound positive tree := by
  letI : Inhabited (Fin capacity) := ⟨⟨0,positive⟩⟩
  rw [satisfiable,MSO.Tree.Executable.satisfiable_correct]
  exact exists_congr (sentence_correct B live bound positive)

end Characterisation.ComponentTrees.GeneratingAlphabet
