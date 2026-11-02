/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Formalizations.ComponentTrees.DecodeNode
import DistributedSynthesis.Formalizations.ComponentGames.ExecutableIsomorphisms

/-! Reconstruct one entire concrete child from its finite numbering.
The map is a finite bijection preserving all vertices and block states.
-/
namespace Characterisation.ComponentTrees.ModelDecode
open DistributedSynthesis Characterisation Characterisation.PeriodicBlocks
open Characterisation.ComponentTrees.FiniteTransport
open Characterisation.ComponentTrees.FiniteDecode
open Characterisation.ComponentGames Characterisation.ComponentGames.HistoryGame
open scoped Characterisation.ComponentGames.Representation DistributedSynthesis.FiniteOrders
open scoped Characterisation.ComponentGames.FiniteEnumeration
set_option maxHeartbeats 1800000
set_option linter.unusedSectionVars false
variable {I₁ I₂ O₁ O₂ G : Type} {D capacity : Nat}
variable [Fintype I₁] [Fintype I₂] [DecidableEq I₁] [DecidableEq I₂]
variable [Fintype O₁] [Fintype O₂] [DecidableEq O₁] [DecidableEq O₂]
variable (B : DetParityAutomaton (BlockWord (ContinuationLetter I₁ I₂ O₁ O₂) D))
variable [DecidableEq B.State]
variable (M : Recognizer Graph G) [DecidablePred (· ∈ M.accept)]
variable (live : B.State → Bool)
variable (liveCorrect : ∀ h q, StateReachable B h q →
  (live q = true ↔ M.eval (History.graphSequence h) ∈ M.accept))
variable {bound : Nat}
variable (positive : 0 < capacity)
variable (initialLive : M.eval [] ∈ M.accept)
variable (code : LabeledTree (Fin capacity) (FiniteAlphabet.Letter (capacity:=capacity) B live bound))
variable (localCorrect : FiniteRunMSO.Local (FiniteAlphabet.tables B live bound positive) code)

def initialIso : Representation.Iso
    (FinitePositions.historyData (Position.initial (I₁:=I₁) (I₂:=I₂) (D:=D) B.initial))
    (FiniteAlphabet.initialPosition B positive).2 := by
  let P := Position.initial (I₁:=I₁) (I₂:=I₂) (D:=D) B.initial
  have empty (h : P.Root) : h.val = [] := Finset.mem_singleton.mp h.property
  let e : P.Root ≃ Fin 1 :=
    {toFun := fun _ => 0, invFun := fun _ => ⟨[],Finset.mem_singleton_self _⟩
     left_inv := fun h => Subtype.ext (empty h).symm
     right_inv := fun h => Subsingleton.elim _ _}
  refine {toEquiv := e,shape_same := ?_,graph_same := fun _ => rfl,state_same := fun _ => rfl}
  intro p h k
  apply Bool.eq_iff_iff.mpr
  simp only [FinitePositions.historyData,ExecutableHistories.shape_eq]
  change true = true ↔ extractInputShape P.past p h k = true
  rw [extractInputShape_exact]
  change true = true ↔ currentView p h.val = currentView p k.val
  rw [empty h,empty k]
  simp

def castTargetIso {P : Position I₁ I₂ B.State D} {A C : FinitePositions.Position B.State capacity}
    (e : Representation.Iso (FinitePositions.historyData P) A.2) (same : A = C) :
    Representation.Iso (FinitePositions.historyData P) C.2 := same ▸ e

theorem castTargetIso_edge {P : Position I₁ I₂ B.State D} {A C : FinitePositions.Position B.State capacity}
    (e : Representation.Iso (FinitePositions.historyData P) A.2) (same : A = C) (h : P.Root) :
    (⟨C,(castTargetIso B e same).toEquiv h⟩ : FiniteAlphabet.Edge B) = ⟨A,e.toEquiv h⟩ := by
  cases same; rfl

structure State where
  real : Position I₁ I₂ B.State D
  valid : PositionValid B M real
  address : List (Fin capacity)
  letter : {raw : FiniteAlphabet.Raw (capacity:=capacity) B // FiniteAlphabet.Legal B live bound raw}
  label : code address = some letter
  iso : Representation.Iso (FinitePositions.historyData real) letter.val.1.source.2

def action (s : State B M live code) : CompressedNode B M bound :=
  FiniteDecode.node B M live s.real s.valid s.letter s.iso

def edge (s : State B M live code) (h : s.real.Root) : FiniteAlphabet.Edge (capacity:=capacity) B :=
  ⟨s.letter.val.1.source,s.iso.toEquiv h⟩

def readLetter (address : List (Fin capacity)) (nonempty : code address ≠ none) :
    {a // code address = some a} :=
  match label : code address with
  | none => False.elim (nonempty label)
  | some a => ⟨a,rfl⟩

include localCorrect in
theorem root_nonempty : code [] ≠ none := by
  intro empty
  have root := localCorrect.1
  change FiniteAlphabet.rootTest B live bound positive (code []) = true at root
  simp only [empty,FiniteAlphabet.rootTest,Bool.false_eq_true] at root

def start : State B M live code := by
  let a := readLetter B live code [] (root_nonempty B live positive code localCorrect)
  have same : a.val.val.1.source = FiniteAlphabet.initialPosition B positive := by
    have root := localCorrect.1
    change FiniteAlphabet.rootTest B live bound positive (code []) = true at root
    rw [a.property] at root
    exact of_decide_eq_true root
  exact ⟨Position.initial B.initial,initial_position_valid B M initialLive,[],a.val,a.property,
    castTargetIso B (initialIso B positive) same.symm⟩

@[simp] theorem start_real : (start B M live positive initialLive code localCorrect).real =
    Position.initial B.initial := rfl
@[simp] theorem start_address : (start B M live positive initialLive code localCorrect).address = [] := rfl

theorem start_edge (h : (start B M live positive initialLive code localCorrect).real.Root) :
    edge B M live code (start B M live positive initialLive code localCorrect) h =
      FiniteAlphabet.initialEdge B positive := by
  unfold start edge
  rw [castTargetIso_edge]
  rfl

def data (s : State B M live code) (Q : Position I₁ I₂ B.State D)
    (next : (action B M live code s).Successor Q) :
    FiniteDecode.ChildData B live s.real s.letter s.iso Q :=
  childData B M live liveCorrect s.real s.valid s.letter s.iso Q next

include localCorrect in
theorem child_nonempty (s : State B M live code) (Q : Position I₁ I₂ B.State D)
    (next : (action B M live code s).Successor Q) :
    code (s.address ++ [(data B M live liveCorrect code s Q next).direction]) ≠ none := by
  intro empty
  let found := data B M live liveCorrect code s Q next
  change code (s.address ++ [found.direction]) = none at empty
  have test := localCorrect.2 s.address found.direction
  change FiniteAlphabet.childTest B live bound (code s.address) found.direction
    (code (s.address ++ [found.direction])) = true at test
  simp only [s.label,empty,FiniteAlphabet.childTest,found.entry,Bool.false_eq_true] at test

def advance (s : State B M live code) (Q : Position I₁ I₂ B.State D)
    (next : (action B M live code s).Successor Q) : State B M live code := by
  let found := data B M live liveCorrect code s Q next
  let a := readLetter B live code (s.address ++ [found.direction])
    (child_nonempty B M live liveCorrect positive code localCorrect s Q next)
  have same : a.val.val.1.source = found.encoded.1 := by
    have test := localCorrect.2 s.address found.direction
    change FiniteAlphabet.childTest B live bound (code s.address) found.direction
      (code (s.address ++ [found.direction])) = true at test
    simpa only [s.label,a.property,FiniteAlphabet.childTest,found.entry,decide_eq_true_eq] using test
  exact ⟨Q,ComponentSuccessor.valid B M
    ((FiniteDecode.node_next B M live s.real s.valid s.letter s.iso Q).mp next) s.valid,
    s.address ++ [found.direction],a.val,a.property,castTargetIso B found.iso same.symm⟩

@[simp] theorem advance_real (s : State B M live code) (Q : Position I₁ I₂ B.State D)
    (next : (action B M live code s).Successor Q) :
    (advance B M live liveCorrect positive code localCorrect s Q next).real = Q := rfl

@[simp] theorem advance_address (s : State B M live code) (Q : Position I₁ I₂ B.State D)
    (next : (action B M live code s).Successor Q) :
    (advance B M live liveCorrect positive code localCorrect s Q next).address =
      s.address ++ [(data B M live liveCorrect code s Q next).direction] := rfl

theorem advance_step (s : State B M live code) (Q : Position I₁ I₂ B.State D)
    (next : (action B M live code s).Successor Q)
    (h : Q.Root) (k : s.real.Root) (u : BlockInput I₁ I₂ D)
    (history : h.val = ((action B M live code s).reduction.map.edge k).val ++ u.val) :
    FiniteAlphabet.Step B live bound s.letter (data B M live liveCorrect code s Q next).direction
      (edge B M live code s k)
      (edge B M live code (advance B M live liveCorrect positive code localCorrect s Q next) h) := by
  let found := data B M live liveCorrect code s Q next
  have edgeEq : edge B M live code (advance B M live liveCorrect positive code localCorrect s Q next) h =
      ⟨found.encoded.1,found.iso.toEquiv h⟩ := by
    unfold advance edge
    rw [castTargetIso_edge]
  rw [edgeEq,FiniteAlphabet.step_word]
  exact ⟨s.iso.toEquiv k,rfl,found.encoded,found.entry,found.iso.toEquiv h,rfl,u,
    childData_trace B M live liveCorrect s.real s.valid s.letter s.iso Q next h k u history⟩

private theorem advance_step_eq (s after : State B M live code) (Q : Position I₁ I₂ B.State D)
    (next : (action B M live code s).Successor Q)
    (same : after = advance B M live liveCorrect positive code localCorrect s Q next)
    (h : after.real.Root) (k : s.real.Root) (u : BlockInput I₁ I₂ D)
    (history : h.val = ((action B M live code s).reduction.map.edge k).val ++ u.val) :
    FiniteAlphabet.Step B live bound s.letter (data B M live liveCorrect code s Q next).direction
      (edge B M live code s k) (edge B M live code after h) := by
  subst after
  exact advance_step B M live liveCorrect positive code localCorrect s Q next h k u history

instance nextDecidable (s : State B M live code) (Q : Position I₁ I₂ B.State D) :
    Decidable ((action B M live code s).Successor Q) :=
  decidable_of_iff _ (FiniteDecode.node_next B M live s.real s.valid s.letter s.iso Q).symm

def stepState (s : State B M live code) (Q : Position I₁ I₂ B.State D) : State B M live code :=
  if next : (action B M live code s).Successor Q then
    advance B M live liveCorrect positive code localCorrect s Q next else s

def atState (address : List (Position I₁ I₂ B.State D)) : State B M live code :=
  address.foldl (stepState B M live liveCorrect positive code localCorrect)
    (start B M live positive initialLive code localCorrect)

def tree : CompressedTree B M bound := fun address =>
  action B M live code (atState B M live liveCorrect positive initialLive code localCorrect address)

theorem at_append (address : List (Position I₁ I₂ B.State D)) (Q : Position I₁ I₂ B.State D) :
    atState B M live liveCorrect positive initialLive code localCorrect (address ++ [Q]) =
      stepState B M live liveCorrect positive code localCorrect
        (atState B M live liveCorrect positive initialLive code localCorrect address) Q := by
  simp only [atState,List.foldl_append,List.foldl_cons,List.foldl_nil]

theorem step_of_next (s : State B M live code) (Q : Position I₁ I₂ B.State D)
    (next : (action B M live code s).Successor Q) :
    stepState B M live liveCorrect positive code localCorrect s Q =
      advance B M live liveCorrect positive code localCorrect s Q next := by
  simp only [stepState,dif_pos next]

theorem at_real (address : List (Position I₁ I₂ B.State D))
    (supported : publicSupport CompressedNode.offers
      (tree B M live liveCorrect positive initialLive code localCorrect) address = true) :
    (atState B M live liveCorrect positive initialLive code localCorrect address).real =
      observableAt (Position.initial B.initial) address := by
  cases address using List.reverseRecOn with
  | nil => rfl
  | append_singleton address Q =>
    have both := supported
    rw [publicSupport_append,Bool.and_eq_true] at both
    have next : (action B M live code
      (atState B M live liveCorrect positive initialLive code localCorrect address)).Successor Q :=
      @of_decide_eq_true _ (Classical.propDecidable _) both.2
    rw [at_append,step_of_next B M live liveCorrect positive code localCorrect _ _ next,advance_real]
    simp [observableAt]

theorem tree_valid : (tree B M live liveCorrect positive initialLive code localCorrect).Valid := by
  intro address supported
  exact at_real B M live liveCorrect positive initialLive code localCorrect address supported

/-- Decode one tree and preserve every compatible run and all its priorities.
All searches and recursive state updates in `tree` are executable. -/
theorem tree_accepting
    (accepting : FiniteRunMSO.Accepting (FiniteAlphabet.tables B live bound positive) code) :
    (tree B M live liveCorrect positive initialLive code localCorrect).Accepting := by
  refine ⟨tree_valid B M live liveCorrect positive initialLive code localCorrect,?_⟩
  intro branch supported run
  let st n := atState B M live liveCorrect positive initialLive code localCorrect (branchNode branch n)
  have next n : (action B M live code (st n)).Successor (branch n) := by
    have both := supported (n+1)
    change publicSupport CompressedNode.offers (tree B M live liveCorrect positive initialLive code localCorrect)
      (branchNode branch n ++ [branch n]) = true at both
    rw [publicSupport_append,Bool.and_eq_true] at both
    exact @of_decide_eq_true _ (Classical.propDecidable _) both.2
  have advanceEq n : st (n+1) = advance B M live liveCorrect positive code localCorrect (st n) (branch n) (next n) := by
    change atState B M live liveCorrect positive initialLive code localCorrect (branchNode branch n ++ [branch n]) = _
    rw [at_append,step_of_next B M live liveCorrect positive code localCorrect _ _ (next n)]
  let target n := (data B M live liveCorrect code (st n) (branch n) (next n)).direction
  have addresses n : (st n).address = branchNode target n := by
    induction n with
    | zero => rfl
    | succ n ih => rw [advanceEq n,advance_address,ih]; rfl
  let edges n := edge B M live code (st n) (run.history n)
  have finiteRun : FiniteRunMSO.Run (FiniteAlphabet.tables B live bound positive) code target edges := by
    refine ⟨start_edge B M live positive initialLive code localCorrect _,?_,?_⟩
    · intro n
      change FiniteAlphabet.edgeTest B live bound (code (branchNode target n)) (edges n) = true
      rw [← addresses n,(st n).label]
      change decide ((st n).letter.val.1.source = (st n).letter.val.1.source) = true
      exact decide_eq_true rfl
    · intro n
      change FiniteAlphabet.stepTest B live bound (code (branchNode target n)) (target n) (edges n) (edges (n+1)) = true
      rw [← addresses n,(st n).label]
      apply decide_eq_true
      exact advance_step_eq B M live liveCorrect positive code localCorrect (st n) (st (n+1)) (branch n)
        (next n) (advanceEq n) (run.history (n+1)) (run.history n) (run.word n) (run.next n)
  have parity := accepting.2 target edges finiteRun
  have priorities n : (FiniteAlphabet.tables B live bound positive).priority (code (branchNode target n)) (edges n) =
      B.priority ((tree B M live liveCorrect positive initialLive code localCorrect (branchNode branch n)).position.state
        (run.history n)) := congrArg B.priority ((st n).iso.state_same (run.history n))
  simpa only [priorities] using parity

end Characterisation.ComponentTrees.ModelDecode
