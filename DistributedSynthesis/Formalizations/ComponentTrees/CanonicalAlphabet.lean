/- Project authors: see AUTHORS.md at the repository root. -/
import DistributedSynthesis.Formalizations.ComponentTrees.CanonicalEncodeTree
import DistributedSynthesis.Formalizations.ComponentTrees.ModelEquivalence

namespace Characterisation.ComponentTrees.CanonicalAlphabet
open DistributedSynthesis Characterisation Characterisation.PeriodicBlocks
open Characterisation.ComponentGames
open scoped Characterisation.ComponentGames.Representation DistributedSynthesis.FiniteOrders
open scoped Characterisation.ComponentGames.FiniteEnumeration
open scoped Characterisation.ComponentGames.Representation.FiniteArena
set_option maxHeartbeats 1800000
set_option linter.unusedSectionVars false
variable {I₁ I₂ O₁ O₂ G : Type} {D capacity : Nat}
variable [Fintype I₁] [Fintype I₂] [DecidableEq I₁] [DecidableEq I₂]
variable [Fintype O₁] [Fintype O₂] [DecidableEq O₁] [DecidableEq O₂]
variable (B : DetParityAutomaton (BlockWord (ContinuationLetter I₁ I₂ O₁ O₂) D))
variable [LinearOrder B.State]
variable (live : B.State → Bool) (bound : Nat) (positive : 0 < capacity)

def Canonical : FiniteAlphabet.Letter (capacity:=capacity) B live bound → Prop
  | none => True
  | some a =>
    CanonicalPositions.normalizeWith (FiniteAlphabet.initialPosition B positive) a.val.1.source = a.val.1.source ∧
    (∀ d c, a.val.2 d = some c →
      CanonicalPositions.normalizeWith (FiniteAlphabet.initialPosition B positive) c.1 = c.1) ∧
    ∃ k : Fin (capacity+1), ∀ d : Fin capacity, (a.val.2 d).isSome = decide (d.val < k.val)

instance canonicalDecidable (a : FiniteAlphabet.Letter (capacity:=capacity) B live bound) :
    Decidable (Canonical B live bound positive a) := by
  cases a <;> unfold Canonical <;> infer_instance

/-- The same finite moves and block witnesses, restricted to a single
representative per isomorphism class at sources and named children. -/
abbrev Letter := {a : FiniteAlphabet.Letter (capacity:=capacity) B live bound // Canonical B live bound positive a}
instance letterFintype : Fintype (Letter B live bound positive) := inferInstance
instance letterDecidableEq : DecidableEq (Letter B live bound positive) := inferInstance

def tables : FiniteRunMSO.Tables (Fin capacity) (Letter B live bound positive) (FiniteAlphabet.Edge (capacity:=capacity) B) where
  initial := (FiniteAlphabet.tables B live bound positive).initial
  root a := (FiniteAlphabet.tables B live bound positive).root a.val
  child a d b := (FiniteAlphabet.tables B live bound positive).child a.val d b.val
  allowed a e := (FiniteAlphabet.tables B live bound positive).allowed a.val e
  step a d e f := (FiniteAlphabet.tables B live bound positive).step a.val d e f
  priority a e := (FiniteAlphabet.tables B live bound positive).priority a.val e

/-- Forgetting the canonicality proofs preserves every run and priority,
not just the existence of an accepting run. -/
theorem accepting_iff (code : LabeledTree (Fin capacity) (Letter B live bound positive)) :
    FiniteRunMSO.Accepting (tables B live bound positive) code ↔
      FiniteRunMSO.Accepting (FiniteAlphabet.tables B live bound positive) (fun x => (code x).val) := Iff.rfl

variable (M : Recognizer Graph G) [DecidablePred (· ∈ M.accept)]
variable (liveCorrect : ∀ h q, StateReachable B h q →
  (live q = true ↔ M.eval (History.graphSequence h) ∈ M.accept))
variable [LinearOrder I₁] [LinearOrder I₂]

include liveCorrect in
/-- Recursive normalization preserves all compatible runs. The reverse
construction is the existing executable decoder applied to the same letters. -/
theorem model_tree_iff (initialLive : M.eval [] ∈ M.accept)
    (fits : bound * Nat.card (RoundRecord I₁ I₂ Graph Unit Unit) ^ D ≤ capacity) :
    (∃ code, FiniteRunMSO.Accepting (tables B live bound positive) code) ↔
      ∃ tree : CompressedTree B M bound, tree.Accepting := by
  constructor
  · rintro ⟨code,accepted⟩
    exact (ComponentTrees.model_tree_iff B M live liveCorrect positive initialLive fits).mp
      ⟨fun x => (code x).val,(accepting_iff B live bound positive code).mp accepted⟩
  · rintro ⟨tree,accepted⟩
    let code : LabeledTree (Fin capacity) (Letter B live bound positive) := fun address =>
      ⟨CanonicalModelEncode.code B M live liveCorrect positive fits tree accepted.1 address,
       by
         have normalized := CanonicalModelEncode.code_normalized B M live liveCorrect positive fits tree accepted.1 address
         have packed := CanonicalModelEncode.code_packed B M live liveCorrect positive fits tree accepted.1 address
         cases h : CanonicalModelEncode.code B M live liveCorrect positive fits tree accepted.1 address with
         | none => trivial
         | some a =>
           rw [h] at normalized packed
           exact ⟨normalized.1,normalized.2,packed⟩⟩
    have checked := CanonicalModelEncode.code_accepting B M live liveCorrect positive fits tree accepted.1 accepted
    have sameDecider : (fun a b : B.State => Classical.propDecidable (a = b)) =
        (inferInstance : DecidableEq B.State) := Subsingleton.elim _ _
    rw [sameDecider] at checked
    exact ⟨code,(accepting_iff B live bound positive code).mpr checked⟩

/-- Executable readback from a canonical labelled tree. It reuses the
existing decoder without asking for a numbering or isomorphism oracle. -/
def decode (initialLive : M.eval [] ∈ M.accept)
    (code : LabeledTree (Fin capacity) (Letter B live bound positive))
    (valid : FiniteRunMSO.Local (tables B live bound positive) code) : CompressedTree B M bound :=
  ModelDecode.tree B M live liveCorrect positive initialLive (fun x => (code x).val) valid

include liveCorrect in
theorem decode_accepting (initialLive : M.eval [] ∈ M.accept)
    (code : LabeledTree (Fin capacity) (Letter B live bound positive))
    (accepted : FiniteRunMSO.Accepting (tables B live bound positive) code) :
    (decode B live bound positive M liveCorrect initialLive code accepted.1).Accepting :=
  ModelDecode.tree_accepting B M live liveCorrect positive initialLive (fun x => (code x).val)
    accepted.1 ((accepting_iff B live bound positive code).mp accepted)

variable [LinearOrder O₁] [LinearOrder O₂]
instance letterOrder : LinearOrder (Letter B live bound positive) := inferInstance

def sentence : MSO.Sentence (MSO.Tree.language (Fin capacity) (Letter B live bound positive)) :=
  letI : Nonempty (Fin capacity) := ⟨⟨0,positive⟩⟩
  FiniteRunMSO.acceptanceFormula (tables B live bound positive) (FiniteAlphabet.edgeIndex B)

theorem sentence_correct (code : LabeledTree (Fin capacity) (Letter B live bound positive)) :
    MSO.Tree.Satisfies code (sentence B live bound positive) ↔
      FiniteRunMSO.Accepting (tables B live bound positive) code := by
  letI : Nonempty (Fin capacity) := ⟨⟨0,positive⟩⟩
  exact FiniteRunMSO.acceptanceFormula_correct (tables B live bound positive) (FiniteAlphabet.edgeIndex B) code

include liveCorrect in
/-- MSO characterization instantiated on the canonical representative alphabet. -/
theorem mso_compressed_iff (initialLive : M.eval [] ∈ M.accept)
    (fits : bound * Nat.card (RoundRecord I₁ I₂ Graph Unit Unit) ^ D ≤ capacity) :
    (∃ code, MSO.Tree.Satisfies code (sentence B live bound positive)) ↔
      ∃ tree : CompressedTree B M bound, tree.Accepting :=
  (exists_congr (sentence_correct B live bound positive)).trans
    (model_tree_iff B live bound positive M liveCorrect initialLive fits)

/-- Finite enumeration and the existing executable MSO decision procedure. -/
def satisfiable : Bool :=
  letI : Inhabited (Fin capacity) := ⟨⟨0,positive⟩⟩
  MSO.Tree.Executable.satisfiable (sentence B live bound positive)

include liveCorrect in
theorem satisfiable_correct (initialLive : M.eval [] ∈ M.accept)
    (fits : bound * Nat.card (RoundRecord I₁ I₂ Graph Unit Unit) ^ D ≤ capacity) :
    satisfiable B live bound positive = true ↔
      ∃ tree : CompressedTree B M bound, tree.Accepting := by
  letI : Inhabited (Fin capacity) := ⟨⟨0,positive⟩⟩
  rw [satisfiable,MSO.Tree.Executable.satisfiable_correct]
  exact mso_compressed_iff B live bound positive M liveCorrect initialLive fits

end Characterisation.ComponentTrees.CanonicalAlphabet
