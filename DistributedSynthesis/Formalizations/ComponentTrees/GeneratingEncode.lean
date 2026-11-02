/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Formalizations.ComponentTrees.GeneratingDecode

/-! Completeness of the incoming-table alphabet. The existing canonical
encoder supplies one choice of child order and identifications. We move each
identification into its child's label. The alphabet and decoder themselves
allow every order and every valid identification.
-/
namespace Characterisation.ComponentTrees.GeneratingAlphabet
open DistributedSynthesis Characterisation Characterisation.PeriodicBlocks
open Characterisation.ComponentGames
open scoped Characterisation.ComponentGames.Representation DistributedSynthesis.FiniteOrders
open scoped Characterisation.ComponentGames.FiniteEnumeration
open scoped Characterisation.ComponentGames.Representation.FiniteArena
set_option maxHeartbeats 200000
set_option linter.unusedSectionVars false
variable {I₁ I₂ O₁ O₂ G : Type} {D capacity : Nat}
variable [Fintype I₁] [Fintype I₂] [DecidableEq I₁] [DecidableEq I₂]
variable [Fintype O₁] [Fintype O₂] [DecidableEq O₁] [DecidableEq O₂]
variable [LinearOrder I₁] [LinearOrder I₂] [LinearOrder O₁] [LinearOrder O₂]
variable (B : DetParityAutomaton (BlockWord (ContinuationLetter I₁ I₂ O₁ O₂) D))
variable [LinearOrder B.State]
variable (live : B.State → Bool) (bound : Nat) (positive : 0 < capacity)
variable (fits : bound * Nat.card (RoundRecord I₁ I₂ Graph Unit Unit) ^ D ≤ capacity)

/-- Transport a computed correspondence to the actual child's source. -/
def fromChild (m : FiniteAlphabet.Move (capacity:=capacity) B)
    (current : SymbolicAlphabet.Data B live bound positive) (c : FiniteAlphabet.Child B m) :
    Incoming B current.val.source :=
  if same : c.1 = current.val.source then
    some ⟨m.source, cast (congrArg (fun P : Description (capacity:=capacity) B => P.Root → m.End) same) c.2⟩
  else none

theorem child_fromChild (m : FiniteAlphabet.Move (capacity:=capacity) B)
    (current : SymbolicAlphabet.Data B live bound positive) (c : FiniteAlphabet.Child B m)
    (same : c.1 = current.val.source) :
    child B live bound positive m (some ⟨current,fromChild B live bound positive m current c⟩) = some c := by
  rcases c with ⟨P,gen⟩
  dsimp only at same
  subst P
  simp [child,backMap,frame,fromChild]

def incoming (parent : SymbolicAlphabet.Letter B live bound positive)
    (dir : Fin capacity) (current : SymbolicAlphabet.Data B live bound positive) : Incoming B current.val.source :=
  match parent with
  | none => none
  | some previous =>
    match (SymbolicAlphabet.completeData B live bound positive fits previous).val.2 dir with
    | none => none
    | some c => fromChild B live bound positive previous.val current c

/-- Attach to each non-root node the correspondence computed at its parent. -/
def encode (code : LabeledTree (Fin capacity) (SymbolicAlphabet.Letter B live bound positive))
    (node : List (Fin capacity)) : Letter B live bound positive :=
  match node.reverse with
  | [] => (code node).map (fun current => ⟨current,none⟩)
  | dir :: reversedParent => (code node).map (fun current =>
      ⟨current,incoming B live bound positive fits (code reversedParent.reverse) dir current⟩)

theorem encode_nil (code : LabeledTree (Fin capacity) (SymbolicAlphabet.Letter B live bound positive)) :
    encode B live bound positive fits code [] = (code []).map (fun current => ⟨current,none⟩) := rfl

theorem encode_append (code : LabeledTree (Fin capacity) (SymbolicAlphabet.Letter B live bound positive))
    (node : List (Fin capacity)) (dir : Fin capacity) :
    encode B live bound positive fits code (node ++ [dir]) =
      (code (node ++ [dir])).map (fun current => ⟨current,incoming B live bound positive fits (code node) dir current⟩) := by
  simp [encode,List.reverse_append]

def strip (letter : Letter B live bound positive) : SymbolicAlphabet.Letter B live bound positive :=
  letter.map Sigma.fst

theorem strip_encode (code : LabeledTree (Fin capacity) (SymbolicAlphabet.Letter B live bound positive))
    (node : List (Fin capacity)) :
    strip B live bound positive (encode B live bound positive fits code node) = code node := by
  unfold encode
  split <;> simp [strip,Option.map_map,Function.comp_def]

theorem isSome_encode (code : LabeledTree (Fin capacity) (SymbolicAlphabet.Letter B live bound positive))
    (node : List (Fin capacity)) :
    (encode B live bound positive fits code node).isSome = (code node).isSome := by
  unfold encode
  split <;> simp

variable (code : LabeledTree (Fin capacity) (SymbolicAlphabet.Letter B live bound positive))
variable (valid : FiniteRunMSO.Local (SymbolicAlphabet.tables B live bound positive fits) code)

include valid in
theorem children_encode (node : List (Fin capacity)) (current : SymbolicAlphabet.Data B live bound positive)
    (present : code node = some current) (dir : Fin capacity) :
    child B live bound positive current.val (encode B live bound positive fits code (node ++ [dir])) =
      (SymbolicAlphabet.completeData B live bound positive fits current).val.2 dir := by
  have next := valid.2 node dir
  simp only [SymbolicAlphabet.tables,SymbolicAlphabet.complete,present,
    FiniteAlphabet.tables,FiniteAlphabet.childTest] at next
  rw [encode_append,present]
  cases chosen : (SymbolicAlphabet.completeData B live bound positive fits current).val.2 dir with
  | none =>
    rw [chosen] at next
    cases target : code (node ++ [dir]) with
    | none => rfl
    | some other => simp [target] at next
  | some c =>
    rw [chosen] at next
    cases target : code (node ++ [dir]) with
    | none => simp [target] at next
    | some other =>
      have source : c.1 = other.val.source := by
        have same : other.val.source = c.1 := by
          simpa only [target,SymbolicAlphabet.complete,decide_eq_true_eq] using next
        exact same.symm
      simp only [Option.map_some,incoming,chosen]
      exact child_fromChild B live bound positive current.val other c source

include valid in
theorem raw_encode (node : List (Fin capacity)) (current : Data B live bound positive)
    (present : encode B live bound positive fits code node = some current) :
    raw B live bound positive current (fun dir => encode B live bound positive fits code (node ++ [dir])) =
      (SymbolicAlphabet.completeData B live bound positive fits current.1).val := by
  have source : code node = some current.1 := by
    rw [← strip_encode B live bound positive fits code node,present]
    rfl
  apply congrArg (Sigma.mk current.1.val)
  funext dir
  exact children_encode B live bound positive fits code valid node current.1 source dir

include valid in
theorem encode_local : Local B live bound positive (encode B live bound positive fits code) := by
  refine ⟨?_,?_,fun _ _ => rfl⟩
  · intro node
    apply decide_eq_true
    cases present : encode B live bound positive fits code node with
    | none =>
      have source : code node = none := by
        rw [← strip_encode B live bound positive fits code node,present]
        rfl
      intro dir
      have next := valid.2 node dir
      have absent : code (node ++ [dir]) = none := by
        cases target : code (node ++ [dir]) with
        | none => rfl
        | some other => simp [SymbolicAlphabet.tables,SymbolicAlphabet.complete,source,target,
            FiniteAlphabet.tables,FiniteAlphabet.childTest] at next
      simp [encode_append,absent]
    | some current =>
      have source : code node = some current.1 := by
        rw [← strip_encode B live bound positive fits code node,present]
        rfl
      refine ⟨?_,?_⟩
      · rw [raw_encode B live bound positive fits code valid node current present]
        exact (SymbolicAlphabet.completeData B live bound positive fits current.1).property
      · intro dir
        rw [children_encode B live bound positive fits code valid node current.1 source dir,isSome_encode]
        have next := valid.2 node dir
        cases chosen : (SymbolicAlphabet.completeData B live bound positive fits current.1).val.2 dir <;>
          cases target : code (node ++ [dir]) <;>
          simp_all [SymbolicAlphabet.tables,SymbolicAlphabet.complete,FiniteAlphabet.tables,FiniteAlphabet.childTest] <;> rfl
  · have root := valid.1
    cases source : code [] with
    | none => simp [SymbolicAlphabet.tables,SymbolicAlphabet.complete,source,FiniteAlphabet.tables,FiniteAlphabet.rootTest] at root
    | some current =>
      have same : current.val.source = FiniteAlphabet.initialPosition B positive := by
        simpa only [SymbolicAlphabet.tables,SymbolicAlphabet.complete,source,
          FiniteAlphabet.tables,FiniteAlphabet.rootTest,decide_eq_true_eq] using root
      simp [tables,rootTest,encode_nil,source,same]

include valid in
theorem complete_encode :
    complete B live bound positive (encode B live bound positive fits code)
      (encode_local B live bound positive fits code valid) =
      fun node => SymbolicAlphabet.complete B live bound positive fits (code node) := by
  funext node
  cases present : encode B live bound positive fits code node with
  | none =>
    rw [complete_none B live bound positive _ _ node present]
    have source : code node = none := by rw [← strip_encode B live bound positive fits code node,present]; rfl
    rw [source]
    rfl
  | some current =>
    have legal := legalAt B live bound positive _ (encode_local B live bound positive fits code valid) node
    rw [present] at legal
    rw [complete_some B live bound positive _ _ node current present legal.1]
    have source : code node = some current.1 := by rw [← strip_encode B live bound positive fits code node,present]; rfl
    rw [source]
    apply congrArg some
    apply Subtype.ext
    exact raw_encode B live bound positive fits code valid node current present

include valid in
theorem encode_accepting (accepted : FiniteRunMSO.Accepting (SymbolicAlphabet.tables B live bound positive fits) code) :
    Accepting B live bound positive (encode B live bound positive fits code) := by
  apply (complete_accepting_iff B live bound positive _ (encode_local B live bound positive fits code valid)).mp
  rw [complete_encode B live bound positive fits code valid]
  exact (SymbolicAlphabet.accepting_iff B live bound positive fits code).mp accepted

variable (M : Recognizer Graph G) [DecidablePred (· ∈ M.accept)]
variable (liveCorrect : ∀ h q, StateReachable B h q →
  (live q = true ↔ M.eval (History.graphSequence h) ∈ M.accept))

include fits liveCorrect in
theorem model_tree_iff (initialLive : M.eval [] ∈ M.accept) :
    (∃ code, Accepting B live bound positive code) ↔
      ∃ tree : CompressedTree B M bound, tree.Accepting := by
  constructor
  · rintro ⟨code,accepted⟩
    exact ⟨decode B live bound positive M liveCorrect initialLive code accepted.1,
      decode_accepting B live bound positive M liveCorrect initialLive code accepted⟩
  · intro tree
    obtain ⟨code,accepted⟩ := (SymbolicAlphabet.model_tree_iff B live bound positive fits M liveCorrect initialLive).mpr tree
    exact ⟨encode B live bound positive fits code,
      encode_accepting B live bound positive fits code accepted.1 accepted⟩

include fits liveCorrect in
theorem mso_compressed_iff (initialLive : M.eval [] ∈ M.accept) :
    (∃ code, MSO.Tree.Satisfies code (sentence B live bound positive)) ↔
      ∃ tree : CompressedTree B M bound, tree.Accepting :=
  (exists_congr (sentence_correct B live bound positive)).trans
    (model_tree_iff B live bound positive fits M liveCorrect initialLive)

include fits liveCorrect in
theorem satisfiable_correct (initialLive : M.eval [] ∈ M.accept) :
    satisfiable B live bound positive = true ↔
      ∃ tree : CompressedTree B M bound, tree.Accepting :=
  (satisfiable_accepting_iff B live bound positive).trans
    (model_tree_iff B live bound positive fits M liveCorrect initialLive)

end Characterisation.ComponentTrees.GeneratingAlphabet
