/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Formalizations.ComponentTrees.CanonicalEncodeNode
import DistributedSynthesis.Formalizations.ComponentTrees.EncodeTree
import DistributedSynthesis.Formalizations.ComponentTrees.DecodeTree
import DistributedSynthesis.Formalizations.ComponentGames.ExecutableIsomorphisms

/-! Normalize each child before continuing the existing recursive encoder.
The state, root, casts, finite positions and run semantics are reused; only
the chosen child representatives differ from the numbered encoding. -/
namespace Characterisation.ComponentTrees.CanonicalModelEncode
open DistributedSynthesis Characterisation Characterisation.PeriodicBlocks
open Characterisation.ComponentTrees.FiniteTransport
open Characterisation.ComponentTrees.FiniteDecode
open Characterisation.ComponentGames Characterisation.ComponentGames.HistoryGame
open scoped Characterisation.ComponentGames.Representation DistributedSynthesis.FiniteOrders
open scoped Characterisation.ComponentGames.FiniteEnumeration
noncomputable section
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 2400000
set_option linter.unusedSectionVars false
variable {I₁ I₂ O₁ O₂ G : Type} {D capacity : Nat}
variable [Fintype I₁] [Fintype I₂] [DecidableEq I₁] [DecidableEq I₂]
variable [Fintype O₁] [Fintype O₂] [DecidableEq O₁] [DecidableEq O₂]
variable (B : DetParityAutomaton (BlockWord (ContinuationLetter I₁ I₂ O₁ O₂) D))
variable [LinearOrder B.State]
variable (M : Recognizer Graph G) [DecidablePred (· ∈ M.accept)]
variable (live : B.State → Bool)
variable (liveCorrect : ∀ h q, StateReachable B h q →
  (live q = true ↔ M.eval (History.graphSequence h) ∈ M.accept))
variable {bound : Nat}
variable [LinearOrder I₁] [LinearOrder I₂]
variable (positive : 0 < capacity)
variable (fits : bound * Nat.card (RoundRecord I₁ I₂ Graph Unit Unit) ^ D ≤ capacity)
variable (original : CompressedTree B M bound) (valid : original.Valid)

abbrev State := ModelEncode.State (capacity:=capacity) B M original

def action (s : State (capacity:=capacity) B M original) :=
  CanonicalEncode.letter B M live liveCorrect positive fits (original s.address) s.encoded s.iso

abbrev start : State (capacity:=capacity) B M original := ModelEncode.start B M positive original valid

def child (s : State (capacity:=capacity) B M original) (d : Fin capacity)
    (c : FiniteAlphabet.Child B (action B M live liveCorrect positive fits original s).val.1)
    (entry : (action B M live liveCorrect positive fits original s).val.2 d = some c) : Position I₁ I₂ B.State D :=
  CanonicalEncode.child B M live liveCorrect positive fits (original s.address) s.encoded s.iso d c entry

def advance (s : State (capacity:=capacity) B M original) (d : Fin capacity)
    (c : FiniteAlphabet.Child B (action B M live liveCorrect positive fits original s).val.1)
    (entry : (action B M live liveCorrect positive fits original s).val.2 d = some c) : State (capacity:=capacity) B M original := by
  let Q := child B M live liveCorrect positive fits original s d c entry
  have next := CanonicalEncode.child_next B M live liveCorrect positive fits (original s.address) s.encoded s.iso d c entry
  have support : publicSupport CompressedNode.offers original (s.address ++ [Q]) = true := by
    rw [publicSupport_append,s.supported,Bool.true_and]
    exact decide_eq_true next
  have source : (original (s.address ++ [Q])).position = Q := by
    have source := valid _ support
    simpa only [observableAt,List.getLast?_concat,Option.getD_some] using source
  exact ⟨s.address ++ [Q],support,c.1,
    FiniteDecode.castPositionIso B
      (CanonicalEncode.childIso B M live liveCorrect positive fits (original s.address) s.encoded s.iso d c entry) source.symm⟩

def stepState : Option (State (capacity:=capacity) B M original) → Fin capacity → Option (State (capacity:=capacity) B M original)
  | none,_ => none
  | some s,d => match entry : (action B M live liveCorrect positive fits original s).val.2 d with
    | none => none
    | some c => some (advance B M live liveCorrect positive fits original valid s d c entry)

def atState (address : List (Fin capacity)) : Option (State (capacity:=capacity) B M original) :=
  address.foldl (stepState B M live liveCorrect positive fits original valid) (some (start B M positive original valid))

def code : LabeledTree (Fin capacity) (FiniteAlphabet.Letter (capacity:=capacity) B live bound) :=
  fun address => (atState B M live liveCorrect positive fits original valid address).map
    (action B M live liveCorrect positive fits original)

theorem at_append (address : List (Fin capacity)) (d : Fin capacity) :
    atState B M live liveCorrect positive fits original valid (address ++ [d]) =
      stepState B M live liveCorrect positive fits original valid
        (atState B M live liveCorrect positive fits original valid address) d := by
  simp only [atState,List.foldl_append,List.foldl_cons,List.foldl_nil]

theorem code_local : FiniteRunMSO.Local (FiniteAlphabet.tables B live bound positive)
    (code B M live liveCorrect positive fits original valid) := by
  constructor
  · change decide (FiniteAlphabet.initialPosition B positive = FiniteAlphabet.initialPosition B positive) = true
    exact decide_eq_true rfl
  · intro address d
    change FiniteAlphabet.childTest B live bound _ d _ = true
    simp only [code,at_append]
    cases state : atState B M live liveCorrect positive fits original valid address with
    | none => rfl
    | some s =>
      simp only [Option.map_some]
      simp only [stepState]
      split
      · rename_i entry
        simp only [Option.map_none,FiniteAlphabet.childTest,entry]
      · rename_i c entry
        simp only [Option.map_some,FiniteAlphabet.childTest,entry]
        change decide (c.1 = c.1) = true
        exact decide_eq_true rfl

/-- Padding cannot hide any finite run: a state is available at every
node of any run admitted by the finite table. -/
def liveState (address : List (Fin capacity))
    (nonempty : code B M live liveCorrect positive fits original valid address ≠ none) :
    {s // atState B M live liveCorrect positive fits original valid address = some s} := by
  cases h : atState B M live liveCorrect positive fits original valid address with
  | none => exact False.elim (nonempty (by simp only [code,h,Option.map_none]))
  | some s => exact ⟨s,rfl⟩

theorem step_present (s after : State (capacity:=capacity) B M original) (d : Fin capacity)
    (present : stepState B M live liveCorrect positive fits original valid (some s) d = some after) :
    ∃ c, ∃ (entry : (action B M live liveCorrect positive fits original s).val.2 d = some c),
      after = advance B M live liveCorrect positive fits original valid s d c entry := by
  simp only [stepState] at present
  split at present
  · cases present
  · rename_i c entry
    exact ⟨c,entry,(Option.some.inj present).symm⟩

/-- The finite edge code determines exactly one concrete edge at this node. -/
theorem edge_exists (s : State (capacity:=capacity) B M original) (x : FiniteAlphabet.Edge (capacity:=capacity) B)
    (allowed : FiniteAlphabet.edgeTest B live bound (some (action B M live liveCorrect positive fits original s)) x = true) :
    ∃ h : (original s.address).position.Root, x = ⟨s.encoded,s.iso.toEquiv h⟩ := by
  have same : x.1 = s.encoded := of_decide_eq_true allowed
  rcases x with ⟨A,j⟩
  dsimp only at same
  subst A
  exact ⟨s.iso.toEquiv.symm j,by rw [s.iso.toEquiv.apply_symm_apply]⟩

theorem advance_trace (s : State (capacity:=capacity) B M original) (d : Fin capacity)
    (c : FiniteAlphabet.Child B (action B M live liveCorrect positive fits original s).val.1)
    (entry : (action B M live liveCorrect positive fits original s).val.2 d = some c)
    (h : (original s.address).position.Root) (k : c.1.Root) (u : BlockInput I₁ I₂ D)
    (endpoint : c.2 k = wordScenario
      ((action B M live liveCorrect positive fits original s).val.1.replacement (s.iso.toEquiv h)) u) :
    (((advance B M live liveCorrect positive fits original valid s d c entry).iso).toEquiv.symm k).val =
      ((original s.address).reduction.map.edge h).val ++ u.val := by
  unfold advance
  rw [FiniteDecode.castPositionIso_history]
  exact CanonicalEncode.child_trace B M live liveCorrect positive fits (original s.address) s.encoded s.iso d c entry k h u endpoint

theorem advance_compatible (s after : State (capacity:=capacity) B M original) (d : Fin capacity)
    (c : FiniteAlphabet.Child B (action B M live liveCorrect positive fits original s).val.1)
    (entry : (action B M live liveCorrect positive fits original s).val.2 d = some c)
    (same : after = advance B M live liveCorrect positive fits original valid s d c entry)
    (h : (original s.address).position.Root) (k : (original after.address).position.Root)
    (step : FiniteAlphabet.Step B live bound (action B M live liveCorrect positive fits original s) d
      ⟨s.encoded,s.iso.toEquiv h⟩ ⟨after.encoded,after.iso.toEquiv k⟩) :
    ∃ u : BlockInput I₁ I₂ D, k.val = ((original s.address).reduction.map.edge h).val ++ u.val := by
  subst after
  obtain ⟨i,old,c',entry',j,new,u,endpoint⟩ := (FiniteAlphabet.step_word B live bound _ _ _ _).mp step
  have childEq : c' = c := Option.some.inj (entry'.symm.trans entry)
  subst c'
  have oldIndex : s.iso.toEquiv h = i := eq_of_heq (Sigma.mk.inj old).2
  have newIndex : (advance B M live liveCorrect positive fits original valid s d c entry).iso.toEquiv k = j :=
    eq_of_heq (Sigma.mk.inj new).2
  rw [← oldIndex,← newIndex] at endpoint
  have trace := advance_trace B M live liveCorrect positive fits original valid s d c entry h _ u endpoint
  rw [Equiv.symm_apply_apply] at trace
  exact ⟨u,trace⟩

open ModelEncode (castRoot castRoot_val castRoot_state castRoot_reduction)

/-- Every finite-table run lifts to a run of the original compressed tree,
with unchanged priorities; all directions use the same node rule. -/
theorem code_accepting (accepting : original.Accepting) :
    FiniteRunMSO.Accepting (FiniteAlphabet.tables B live bound positive)
      (code B M live liveCorrect positive fits original valid) := by
  refine ⟨code_local B M live liveCorrect positive fits original valid,?_⟩
  intro branch edges run
  let chosen n := liveState B M live liveCorrect positive fits original valid (branchNode branch n)
    (FiniteAlphabet.padding_has_no_run B live bound positive _ branch edges run n)
  let st n := (chosen n).val
  have stateEq n : atState B M live liveCorrect positive fits original valid (branchNode branch n) = some (st n) :=
    (chosen n).property
  have startEq : st 0 = start B M positive original valid := (Option.some.inj (stateEq 0)).symm
  have advanceExists n : ∃ c, ∃ entry : (action B M live liveCorrect positive fits original (st n)).val.2 (branch n) = some c,
      st (n+1) = advance B M live liveCorrect positive fits original valid (st n) (branch n) c entry := by
    apply step_present B M live liveCorrect positive fits original valid
    have eq := stateEq (n+1)
    change atState B M live liveCorrect positive fits original valid (branchNode branch n ++ [branch n]) = _ at eq
    rw [at_append,stateEq n] at eq
    exact eq
  let component n := (advanceExists n).choose
  let entry n := (advanceExists n).choose_spec.choose
  have advanceEq n : st (n+1) = advance B M live liveCorrect positive fits original valid (st n) (branch n) (component n) (entry n) :=
    (advanceExists n).choose_spec.choose_spec
  let target n := child B M live liveCorrect positive fits original (st n) (branch n) (component n) (entry n)
  have addresses n : (st n).address = branchNode target n := by
    induction n with
    | zero => rw [startEq]; rfl
    | succ n ih => rw [advanceEq n]; change (st n).address ++ [target n] = _; rw [ih]; rfl
  have labels n : code B M live liveCorrect positive fits original valid (branchNode branch n) =
      some (action B M live liveCorrect positive fits original (st n)) := by
    simp only [code,stateEq n,Option.map_some]
  have edgeExists n : ∃ h : (original (st n).address).position.Root, edges n = ⟨(st n).encoded,(st n).iso.toEquiv h⟩ := by
    apply edge_exists B M live liveCorrect positive fits original
    have allowed := run.2.1 n
    change FiniteAlphabet.edgeTest B live bound _ (edges n) = true at allowed
    rwa [labels n] at allowed
  let history n := (edgeExists n).choose
  have edgeEq n : edges n = ⟨(st n).encoded,(st n).iso.toEquiv (history n)⟩ := (edgeExists n).choose_spec
  have words n : ∃ u : BlockInput I₁ I₂ D,
      (history (n+1)).val = ((original (st n).address).reduction.map.edge (history n)).val ++ u.val := by
    apply advance_compatible B M live liveCorrect positive fits original valid (st n) (st (n+1)) (branch n)
      (component n) (entry n) (advanceEq n)
    have step := run.2.2 n
    change FiniteAlphabet.stepTest B live bound _ _ _ _ = true at step
    rw [labels n,edgeEq n,edgeEq (n+1)] at step
    exact of_decide_eq_true step
  let actualHistory n := castRoot B (congrArg (fun address => (original address).position) (addresses n)) (history n)
  let actualRun : original.Run target :=
    { history := actualHistory
      word := fun n => (words n).choose
      initial := by
        have root := valid [] (publicSupport_nil _ _)
        change (original []).position = Position.initial B.initial at root
        have member := (actualHistory 0).property
        change (actualHistory 0).val ∈ (original []).position.histories at member
        rw [root] at member
        exact Finset.mem_singleton.mp member
      next := by
        intro n
        change (actualHistory (n+1)).val = ((original (branchNode target n)).reduction.map.edge (actualHistory n)).val ++ _
        rw [castRoot_val,castRoot_reduction B M _ _ (congrArg original (addresses n))]
        exact (words n).choose_spec }
  have support n : publicSupport CompressedNode.offers original (branchNode target n) = true :=
    addresses n ▸ (st n).supported
  have parity := accepting.2 target support actualRun
  have priorities n : (FiniteAlphabet.tables B live bound positive).priority
      (code B M live liveCorrect positive fits original valid (branchNode branch n)) (edges n) =
      B.priority ((original (branchNode target n)).position.state (actualRun.history n)) := by
    rw [edgeEq n]
    change B.priority ((st n).encoded.2.state ((st n).iso.toEquiv (history n))) = _
    rw [(st n).iso.state_same]
    exact congrArg B.priority (castRoot_state B _ (history n)).symm
  simpa only [← priorities] using parity

/-- Every used source and every named child is the chosen representative.
The initial representative is kept exactly, not merely up to isomorphism. -/
theorem code_normalized (address : List (Fin capacity)) :
    match code B M live liveCorrect positive fits original valid address with
    | none => True
    | some a =>
      CanonicalPositions.normalizeWith (FiniteAlphabet.initialPosition B positive) a.val.1.source = a.val.1.source ∧
      ∀ d c, a.val.2 d = some c →
        CanonicalPositions.normalizeWith (FiniteAlphabet.initialPosition B positive) c.1 = c.1 := by
  have states (xs : List (Fin capacity)) (s : State (capacity:=capacity) B M original)
      (present : atState B M live liveCorrect positive fits original valid xs = some s) :
      CanonicalPositions.normalizeWith (FiniteAlphabet.initialPosition B positive) s.encoded = s.encoded := by
    induction xs using List.reverseRecOn generalizing s with
    | nil =>
      have same : start B M positive original valid = s := Option.some.inj present
      subst s
      exact CanonicalPositions.normalizeWith_root _
    | append_singleton xs d ih =>
      rw [at_append] at present
      cases old : atState B M live liveCorrect positive fits original valid xs with
      | none => simp only [old,stepState] at present; contradiction
      | some before =>
        rw [old] at present
        obtain ⟨c,entry,rfl⟩ := step_present B M live liveCorrect positive fits original valid before s d present
        exact CanonicalEncode.child_normalized B M live liveCorrect positive fits
          (original before.address) before.encoded before.iso d c entry
  unfold code
  cases state : atState B M live liveCorrect positive fits original valid address with
  | none => trivial
  | some s =>
    refine ⟨states address s state,?_⟩
    intro d c entry
    exact CanonicalEncode.child_normalized B M live liveCorrect positive fits
      (original s.address) s.encoded s.iso d c entry

theorem code_packed (address : List (Fin capacity)) :
    match code B M live liveCorrect positive fits original valid address with
    | none => True
    | some a => ∃ k : Fin (capacity+1), ∀ d : Fin capacity,
      (a.val.2 d).isSome = decide (d.val < k.val) := by
  unfold code
  cases state : atState B M live liveCorrect positive fits original valid address with
  | none => trivial
  | some s =>
    exact CanonicalEncode.children_packed B M live liveCorrect positive fits
      (original s.address) s.encoded s.iso

end
end Characterisation.ComponentTrees.CanonicalModelEncode
