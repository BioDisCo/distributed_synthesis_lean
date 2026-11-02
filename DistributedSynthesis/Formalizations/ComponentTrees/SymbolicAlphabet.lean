/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Formalizations.ComponentTrees.CanonicalEncodeTree
import DistributedSynthesis.Formalizations.ComponentTrees.ModelEquivalence

/-! Fixed-table intermediate encoding used in the completeness proof of
GeneratingAlphabet. A letter contains the current move (K,q,r,λ).
Successor components, their canonical representatives, and edge maps are
computed by complete. The full-source policy represents the rule on r(K);
only extensions starting in that image are used.

The recursive canonical encoder has exactly these computed successor data.
GeneratingEncode moves the resulting maps into the child labels of the
manuscript's alphabet. The public decision and synthesis functions use that
incoming-table alphabet, whose local checks allow arbitrary child orderings
and valid maps.
-/
namespace Characterisation.ComponentTrees.SymbolicAlphabet
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
variable (B : DetParityAutomaton (BlockWord (ContinuationLetter I₁ I₂ O₁ O₂) D))
variable [LinearOrder B.State]
variable (live : B.State → Bool) (bound : Nat) (positive : 0 < capacity)

/-- All conditions concern the current position, reduction and rule. -/
def MoveLegal (m : FiniteAlphabet.Move (capacity:=capacity) B) : Prop :=
  CanonicalPositions.normalizeWith (FiniteAlphabet.initialPosition B positive) m.source = m.source ∧
  0 < m.source.1.val ∧
  (∀ h, live (m.source.2.state h) = true) ∧
  FinitePositions.ReductionChecks m.source.2 bound m.replacement ∧
  ClosingPolicyCoherent m.source.2.shape m.rule

instance moveLegalDecidable (m : FiniteAlphabet.Move (capacity:=capacity) B) :
    Decidable (MoveLegal B live bound positive m) := by
  unfold MoveLegal
  infer_instance

abbrev Data := {m : FiniteAlphabet.Move (capacity:=capacity) B // MoveLegal B live bound positive m}
abbrev Letter := Option (Data B live bound positive)

instance letterFintype : Fintype (Letter B live bound positive) := inferInstance
instance letterDecidableEq : DecidableEq (Letter B live bound positive) := inferInstance

variable [LinearOrder I₁] [LinearOrder I₂]
variable (fits : bound * Nat.card (RoundRecord I₁ I₂ Graph Unit Unit) ^ D ≤ capacity)

/-- Compute every successor once, in the fixed component order, and choose
its fixed representative. No successor data are supplied in the input. -/
def completeData (a : Data B live bound positive) :
    {raw : FiniteAlphabet.Raw (capacity:=capacity) B // FiniteAlphabet.Legal B live bound raw} :=
  let checks := a.property.2.2.2.1
  CanonicalChildren.normalizeLetter B live bound (FiniteAlphabet.initialPosition B positive)
    ⟨⟨a.val, FiniteAlphabet.children B live bound a.val checks.2.2.2 fits⟩,
      FiniteAlphabet.raw_legal B live bound a.val checks.2.2.2 fits
        a.property.2.1 a.property.2.2.1 checks a.property.2.2.2.2⟩

def complete : Letter B live bound positive → FiniteAlphabet.Letter (capacity:=capacity) B live bound
  | none => none
  | some a => some (completeData B live bound positive fits a)

/-- Next and the compatible-edge relations are finite tests computed
from the parent letter. The child contributes only its own position. -/
def tables :
    FiniteRunMSO.Tables (Fin capacity) (Letter B live bound positive)
      (FiniteAlphabet.Edge (capacity:=capacity) B) where
  initial := (FiniteAlphabet.tables B live bound positive).initial
  root a := (FiniteAlphabet.tables B live bound positive).root (complete B live bound positive fits a)
  child a d b := (FiniteAlphabet.tables B live bound positive).child
    (complete B live bound positive fits a) d (complete B live bound positive fits b)
  allowed a e := (FiniteAlphabet.tables B live bound positive).allowed (complete B live bound positive fits a) e
  step a d e f := (FiniteAlphabet.tables B live bound positive).step (complete B live bound positive fits a) d e f
  priority a e := (FiniteAlphabet.tables B live bound positive).priority (complete B live bound positive fits a) e

theorem local_iff (code : LabeledTree (Fin capacity) (Letter B live bound positive)) :
    FiniteRunMSO.Local (tables B live bound positive fits) code ↔
      FiniteRunMSO.Local (FiniteAlphabet.tables B live bound positive)
        (fun x => complete B live bound positive fits (code x)) := Iff.rfl

theorem run_iff (code : LabeledTree (Fin capacity) (Letter B live bound positive))
    (branch : Nat → Fin capacity) (edges : Nat → FiniteAlphabet.Edge (capacity:=capacity) B) :
    FiniteRunMSO.Run (tables B live bound positive fits) code branch edges ↔
      FiniteRunMSO.Run (FiniteAlphabet.tables B live bound positive)
        (fun x => complete B live bound positive fits (code x)) branch edges := Iff.rfl

/-- Completion preserves every compatible run and its priorities. -/
theorem accepting_iff (code : LabeledTree (Fin capacity) (Letter B live bound positive)) :
    FiniteRunMSO.Accepting (tables B live bound positive fits) code ↔
      FiniteRunMSO.Accepting (FiniteAlphabet.tables B live bound positive)
        (fun x => complete B live bound positive fits (code x)) := Iff.rfl

def SourceCanonical : FiniteAlphabet.Letter (capacity:=capacity) B live bound → Prop
  | none => True
  | some a =>
    CanonicalPositions.normalizeWith (FiniteAlphabet.initialPosition B positive) a.val.1.source = a.val.1.source

/-- Forget the computed successor fields of an already normalized letter. -/
def erase : (a : FiniteAlphabet.Letter (capacity:=capacity) B live bound) →
    SourceCanonical B live bound positive a → Letter B live bound positive
  | none, _ => none
  | some a, normalized =>
    some ⟨a.val.1, normalized, a.property.1, a.property.2.1,
      a.property.2.2.1, a.property.2.2.2.1⟩

variable (M : Recognizer Graph G) [DecidablePred (· ∈ M.accept)]
variable (liveCorrect : ∀ h q, StateReachable B h q →
  (live q = true ↔ M.eval (History.graphSequence h) ∈ M.accept))
variable (original : CompressedTree B M bound) (valid : original.Valid)

include liveCorrect in
theorem encoded_source (address : List (Fin capacity)) :
    SourceCanonical B live bound positive
      (CanonicalModelEncode.code B M live liveCorrect positive fits original valid address) := by
  have normalized := CanonicalModelEncode.code_normalized B M live liveCorrect positive fits original valid address
  cases h : CanonicalModelEncode.code B M live liveCorrect positive fits original valid address with
  | none => trivial
  | some a =>
    rw [h] at normalized
    exact normalized.1

noncomputable def encode : LabeledTree (Fin capacity) (Letter B live bound positive) :=
  fun address => erase B live bound positive
    (CanonicalModelEncode.code B M live liveCorrect positive fits original valid address)
    (encoded_source B live bound positive fits M liveCorrect original valid address)

/-- The canonical recursive encoder already computes the same children
from its current move. Its choices are independent of future node labels. -/
theorem complete_encode :
    (fun x => complete B live bound positive fits
      (encode B live bound positive fits M liveCorrect original valid x)) =
      CanonicalModelEncode.code B M live liveCorrect positive fits original valid := by
  funext address
  unfold encode CanonicalModelEncode.code
  generalize_proofs normalized
  revert normalized
  cases h : CanonicalModelEncode.atState B M live liveCorrect positive fits original valid address with
  | none => intro normalized; rfl
  | some s => intro normalized; rfl

include liveCorrect in
theorem model_tree_iff (initialLive : M.eval [] ∈ M.accept) :
    (∃ code, FiniteRunMSO.Accepting (tables B live bound positive fits) code) ↔
      ∃ tree : CompressedTree B M bound, tree.Accepting := by
  constructor
  · rintro ⟨code, accepted⟩
    exact (ComponentTrees.model_tree_iff B M live liveCorrect positive initialLive fits).mp
      ⟨_, (accepting_iff B live bound positive fits code).mp accepted⟩
  · rintro ⟨tree, accepted⟩
    refine ⟨encode B live bound positive fits M liveCorrect tree accepted.1,
      (accepting_iff B live bound positive fits _).mpr ?_⟩
    rw [complete_encode]
    have checked := CanonicalModelEncode.code_accepting B M live liveCorrect positive fits tree accepted.1 accepted
    have sameDecider : (fun a b : B.State => Classical.propDecidable (a = b)) =
        (inferInstance : DecidableEq B.State) := Subsingleton.elim _ _
    rw [sameDecider] at checked
    exact checked

/-- Executable readback computes the successor tables before applying
the existing decoder; no isomorphism choices are requested from the caller. -/
def decode (initialLive : M.eval [] ∈ M.accept)
    (code : LabeledTree (Fin capacity) (Letter B live bound positive))
    (valid : FiniteRunMSO.Local (tables B live bound positive fits) code) : CompressedTree B M bound :=
  ModelDecode.tree B M live liveCorrect positive initialLive
    (fun x => complete B live bound positive fits (code x)) valid

include liveCorrect in
theorem decode_accepting (initialLive : M.eval [] ∈ M.accept)
    (code : LabeledTree (Fin capacity) (Letter B live bound positive))
    (accepted : FiniteRunMSO.Accepting (tables B live bound positive fits) code) :
    (decode B live bound positive fits M liveCorrect initialLive code accepted.1).Accepting :=
  ModelDecode.tree_accepting B M live liveCorrect positive initialLive
    (fun x => complete B live bound positive fits (code x)) accepted.1
    ((accepting_iff B live bound positive fits code).mp accepted)

variable [LinearOrder O₁] [LinearOrder O₂]
instance letterOrder : LinearOrder (Letter B live bound positive) := inferInstance

def sentence : MSO.Sentence (MSO.Tree.language (Fin capacity) (Letter B live bound positive)) :=
  letI : Nonempty (Fin capacity) := ⟨⟨0,positive⟩⟩
  FiniteRunMSO.acceptanceFormula (tables B live bound positive fits) (FiniteAlphabet.edgeIndex B)

theorem sentence_correct (code : LabeledTree (Fin capacity) (Letter B live bound positive)) :
    MSO.Tree.Satisfies code (sentence B live bound positive fits) ↔
      FiniteRunMSO.Accepting (tables B live bound positive fits) code := by
  letI : Nonempty (Fin capacity) := ⟨⟨0,positive⟩⟩
  exact FiniteRunMSO.acceptanceFormula_correct (tables B live bound positive fits) (FiniteAlphabet.edgeIndex B) code

include liveCorrect in
theorem mso_compressed_iff (initialLive : M.eval [] ∈ M.accept) :
    (∃ code, MSO.Tree.Satisfies code (sentence B live bound positive fits)) ↔
      ∃ tree : CompressedTree B M bound, tree.Accepting :=
  (exists_congr (sentence_correct B live bound positive fits)).trans
    (model_tree_iff B live bound positive fits M liveCorrect initialLive)

def satisfiable : Bool :=
  letI : Inhabited (Fin capacity) := ⟨⟨0,positive⟩⟩
  MSO.Tree.Executable.satisfiable (sentence B live bound positive fits)

theorem satisfiable_accepting_iff :
    satisfiable B live bound positive fits = true ↔
      ∃ code, FiniteRunMSO.Accepting (tables B live bound positive fits) code := by
  letI : Inhabited (Fin capacity) := ⟨⟨0,positive⟩⟩
  rw [satisfiable, MSO.Tree.Executable.satisfiable_correct]
  exact exists_congr (sentence_correct B live bound positive fits)

include liveCorrect in
theorem satisfiable_correct (initialLive : M.eval [] ∈ M.accept) :
    satisfiable B live bound positive fits = true ↔
      ∃ tree : CompressedTree B M bound, tree.Accepting :=
  (satisfiable_accepting_iff B live bound positive fits).trans
    (model_tree_iff B live bound positive fits M liveCorrect initialLive)

end Characterisation.ComponentTrees.SymbolicAlphabet
