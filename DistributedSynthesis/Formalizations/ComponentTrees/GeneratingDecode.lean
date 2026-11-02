/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Formalizations.ComponentTrees.GeneratingAlphabet

/-! Reassemble the existing decoder's successor records from the actual
child labels. The records are computed locally and are not input fields.
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
variable (code : LabeledTree (Fin capacity) (Letter B live bound positive))
variable (valid : Local B live bound positive code)

include valid in
theorem legalAt (node : List (Fin capacity)) :
    StarLegal B live bound positive (code node) (fun dir => code (node ++ [dir])) :=
  of_decide_eq_true (valid.1 node)

def complete (node : List (Fin capacity)) : FiniteAlphabet.Letter (capacity:=capacity) B live bound :=
  match present : code node with
  | none => none
  | some current => some ⟨raw B live bound positive current (fun dir => code (node ++ [dir])),by
      have legal := legalAt B live bound positive code valid node
      rw [present] at legal
      exact legal.1⟩

theorem complete_none (node : List (Fin capacity)) (absent : code node = none) :
    complete B live bound positive code valid node = none := by
  unfold complete
  split
  · rfl
  · rename_i current present
    rw [absent] at present
    cases present

theorem complete_some (node : List (Fin capacity)) (current : Data B live bound positive)
    (present : code node = some current)
    (legal : FiniteAlphabet.Legal B live bound (raw B live bound positive current (fun dir => code (node ++ [dir])))) :
    complete B live bound positive code valid node = some ⟨raw B live bound positive current (fun dir => code (node ++ [dir])),legal⟩ := by
  unfold complete
  split
  · rename_i absent
    rw [present] at absent
    cases absent
  · rename_i other found
    have same : other = current := Option.some.inj (found.symm.trans present)
    subst other
    rfl

theorem complete_local : FiniteRunMSO.Local (FiniteAlphabet.tables B live bound positive)
    (complete B live bound positive code valid) := by
  constructor
  · have root := valid.2.1
    cases present : code [] with
    | none => simp [tables,rootTest,present] at root
    | some current =>
      have source : current.1.val.source = FiniteAlphabet.initialPosition B positive := by
        have both : current.1.val.source = FiniteAlphabet.initialPosition B positive ∧ current.2 = none := by
          simpa only [tables,rootTest,present,decide_eq_true_eq] using root
        exact both.1
      have checked := legalAt B live bound positive code valid []
      rw [present] at checked
      have legal := checked.1
      rw [complete_some B live bound positive code valid [] current present legal]
      simp [FiniteAlphabet.tables,FiniteAlphabet.rootTest,raw,source]
  · intro node dir
    have legal := legalAt B live bound positive code valid node
    cases parent : code node with
    | none =>
      rw [parent] at legal
      have next : code (node ++ [dir]) = none := legal dir
      rw [complete_none B live bound positive code valid node parent,
        complete_none B live bound positive code valid (node ++ [dir]) next]
      rfl
    | some current =>
      rw [parent] at legal
      rw [complete_some B live bound positive code valid node current parent legal.1]
      cases next : code (node ++ [dir]) with
      | none =>
        rw [complete_none B live bound positive code valid (node ++ [dir]) next]
        simp [FiniteAlphabet.tables,FiniteAlphabet.childTest,raw,child,next]
      | some target =>
        have present := legal.2 dir
        simp only [next] at present
        cases back : backMap B current.1.val (frame B live bound positive target) with
        | none =>
          simp only [child,back,Option.isSome_some] at present
          cases present
        | some gen =>
          have nextLegal := legalAt B live bound positive code valid (node ++ [dir])
          rw [next] at nextLegal
          rw [complete_some B live bound positive code valid (node ++ [dir]) target next nextLegal.1]
          simp only [FiniteAlphabet.tables,FiniteAlphabet.childTest,raw,child,next,back]
          exact decide_eq_true rfl

theorem edge_injective (current : Data B live bound positive) :
    Function.Injective (edge B live bound positive current) := by
  intro e e' equal
  simpa only [edge,Sigma.mk.inj_iff,heq_eq_eq,true_and] using equal

theorem edgeTest_some (current : Data B live bound positive) (e : Edge (capacity:=capacity) B) :
    edgeTest B live bound positive (some current) e = true ↔
      ∃ origin, e = edge B live bound positive current origin := by
  rcases e with ⟨F,origin⟩
  change decide (F = frame B live bound positive current) = true ↔ _
  rw [decide_eq_true_eq]
  constructor
  · intro same
    subst F
    exact ⟨origin,rfl⟩
  · rintro ⟨e,equal⟩
    exact congrArg Sigma.fst equal

theorem step_edge_iff (current target : Data B live bound positive)
    (e : current.1.val.source.Root) (e' : target.1.val.source.Root) :
    Step B live bound positive current (edge B live bound positive current e) (edge B live bound positive target e') ↔
      ∃ gen, backMap B current.1.val (frame B live bound positive target) = some gen ∧
        closingLayerRoot D (gen e') = current.1.val.replacement e := by
  constructor
  · rintro ⟨origin,equal,gen,present,root⟩
    have same := edge_injective B live bound positive current equal
    subst origin
    exact ⟨gen,present,root⟩
  · rintro ⟨gen,present,root⟩
    exact ⟨e,rfl,gen,present,root⟩

theorem step_iff (current target : Data B live bound positive)
    (children : Fin capacity → Letter B live bound positive)
    (legal : FiniteAlphabet.Legal B live bound (raw B live bound positive current children))
    (dir : Fin capacity) (next : children dir = some target)
    (e : current.1.val.source.Root) (e' : target.1.val.source.Root) :
    FiniteAlphabet.Step B live bound ⟨raw B live bound positive current children,legal⟩ dir
      ⟨current.1.val.source,e⟩ ⟨target.1.val.source,e'⟩ ↔
      Step B live bound positive current (edge B live bound positive current e) (edge B live bound positive target e') := by
  rw [step_edge_iff]
  cases back : backMap B current.1.val (frame B live bound positive target) with
  | none => simp [FiniteAlphabet.Step,raw,child,next,back]
  | some gen =>
    simp only [FiniteAlphabet.Step,raw,child,next,back,
      Sigma.mk.inj_iff,heq_eq_eq,true_and,Option.some.injEq,exists_eq_left']
    change (∃ c : FiniteAlphabet.Child B current.1.val,
      some ⟨target.1.val.source,gen⟩ = some c ∧ ∃ k,
        (target.1.val.source = c.1 ∧ HEq e' k) ∧
          closingLayerRoot D (c.2 k) = current.1.val.replacement e) ↔ _
    constructor
    · rintro ⟨c,same,k,equal,root⟩
      cases Option.some.inj same
      have eq : e' = k := eq_of_heq equal.2
      exact eq.symm ▸ root
    · intro root
      exact ⟨⟨target.1.val.source,gen⟩,rfl,e',⟨rfl,HEq.rfl⟩,root⟩

theorem run_edge (branch : Nat → Fin capacity) (edges : Nat → Edge (capacity:=capacity) B)
    (run : FiniteRunMSO.Run (tables B live bound positive) code branch edges) (n : Nat) :
    ∃ current, code (branchNode branch n) = some current ∧
      ∃ origin, edges n = edge B live bound positive current origin := by
  have allowed := run.2.1 n
  cases present : code (branchNode branch n) with
  | none => simp [tables,edgeTest,present] at allowed
  | some current =>
    obtain ⟨origin,equal⟩ := (edgeTest_some B live bound positive current (edges n)).mp
      (by simpa only [tables,present] using allowed)
    exact ⟨current,rfl,origin,equal⟩

theorem run_forget (branch : Nat → Fin capacity) (edges : Nat → Edge (capacity:=capacity) B)
    (run : FiniteRunMSO.Run (tables B live bound positive) code branch edges) :
    FiniteRunMSO.Run (FiniteAlphabet.tables B live bound positive)
      (complete B live bound positive code valid) branch (fun n => forgetEdge B (edges n)) := by
  refine ⟨congrArg (forgetEdge B) run.1,?_,?_⟩
  · intro n
    obtain ⟨current,present,origin,equal⟩ := run_edge B live bound positive code branch edges run n
    have legal := legalAt B live bound positive code valid (branchNode branch n)
    rw [present] at legal
    rw [complete_some B live bound positive code valid _ current present legal.1]
    dsimp only
    rw [equal]
    exact decide_eq_true rfl
  · intro n
    obtain ⟨current,present,origin,equal⟩ := run_edge B live bound positive code branch edges run n
    obtain ⟨target,next,endpoint,equal'⟩ := run_edge B live bound positive code branch edges run (n+1)
    have incoming : Step B live bound positive current (edge B live bound positive current origin)
        (edge B live bound positive target endpoint) := by
      have step := run.2.2 n
      simpa only [tables,stepTest,present,equal,equal',decide_eq_true_eq] using step
    have legal := legalAt B live bound positive code valid (branchNode branch n)
    rw [present] at legal
    have outgoing := (step_iff B live bound positive current target
      (fun dir => code (branchNode branch n ++ [dir])) legal.1 (branch n) next origin endpoint).mpr incoming
    rw [complete_some B live bound positive code valid _ current present legal.1]
    dsimp only
    rw [equal,equal']
    exact decide_eq_true outgoing

theorem old_run_edge (branch : Nat → Fin capacity)
    (edges : Nat → FiniteAlphabet.Edge (capacity:=capacity) B)
    (run : FiniteRunMSO.Run (FiniteAlphabet.tables B live bound positive)
      (complete B live bound positive code valid) branch edges) (n : Nat) :
    ∃ current, code (branchNode branch n) = some current ∧
      ∃ origin, edges n = ⟨current.1.val.source,origin⟩ := by
  have allowed := run.2.1 n
  cases present : code (branchNode branch n) with
  | none =>
    rw [complete_none B live bound positive code valid _ present] at allowed
    contradiction
  | some current =>
    have legal := legalAt B live bound positive code valid (branchNode branch n)
    rw [present] at legal
    rw [complete_some B live bound positive code valid _ current present legal.1] at allowed
    cases selected : edges n with
    | mk P origin =>
      have same : P = current.1.val.source := by
        simpa only [FiniteAlphabet.tables,FiniteAlphabet.edgeTest,selected,raw,decide_eq_true_eq] using allowed
      subst P
      exact ⟨current,rfl,origin,rfl⟩

theorem run_lift (branch : Nat → Fin capacity)
    (edges : Nat → FiniteAlphabet.Edge (capacity:=capacity) B)
    (run : FiniteRunMSO.Run (FiniteAlphabet.tables B live bound positive)
      (complete B live bound positive code valid) branch edges) :
    ∃ lifted, FiniteRunMSO.Run (tables B live bound positive) code branch lifted ∧
      ∀ n, forgetEdge B (lifted n) = edges n := by
  classical
  choose current present origin selected using old_run_edge B live bound positive code valid branch edges run
  let lifted n := edge B live bound positive (current n) (origin n)
  refine ⟨lifted,⟨?_,?_,?_⟩,fun n => (selected n).symm⟩
  · have root := valid.2.1
    have dummy : (current 0).2 = none := by
      have both : (current 0).1.val.source = FiniteAlphabet.initialPosition B positive ∧ (current 0).2 = none := by
        simpa only [tables,rootTest,show code [] = some (current 0) from present 0,decide_eq_true_eq] using root
      exact both.2
    let tag (e : FiniteAlphabet.Edge (capacity:=capacity) B) : Edge (capacity:=capacity) B := ⟨⟨e.1,none⟩,e.2⟩
    calc
      lifted 0 = tag ⟨(current 0).1.val.source,origin 0⟩ := by
        change (⟨⟨_,(current 0).2⟩,_⟩ : Edge B) = _
        exact congrArg (fun incoming : Incoming B (current 0).1.val.source =>
          (⟨⟨(current 0).1.val.source,incoming⟩,origin 0⟩ : Edge B)) dummy
      _ = tag (edges 0) := congrArg tag (selected 0).symm
      _ = (tables B live bound positive).initial := congrArg tag run.1
  · intro n
    simp only [tables,edgeTest,present n,lifted,edge,decide_eq_true_eq]
  · intro n
    have legal := legalAt B live bound positive code valid (branchNode branch n)
    rw [present n] at legal
    have step := run.2.2 n
    rw [complete_some B live bound positive code valid _ (current n) (present n) legal.1] at step
    have outgoing : FiniteAlphabet.Step B live bound
        ⟨raw B live bound positive (current n) (fun dir => code (branchNode branch n ++ [dir])),legal.1⟩
        (branch n) ⟨(current n).1.val.source,origin n⟩ ⟨(current (n+1)).1.val.source,origin (n+1)⟩ := by
      simpa only [FiniteAlphabet.tables,FiniteAlphabet.stepTest,
        selected n,selected (n+1),decide_eq_true_eq] using step
    have incoming := (step_iff B live bound positive (current n) (current (n+1))
      (fun dir => code (branchNode branch n ++ [dir])) legal.1 (branch n) (present (n+1)) (origin n) (origin (n+1))).mp outgoing
    simpa only [tables,stepTest,present n,lifted,decide_eq_true_eq] using incoming

theorem complete_accepting_iff :
    FiniteRunMSO.Accepting (FiniteAlphabet.tables B live bound positive)
      (complete B live bound positive code valid) ↔ Accepting B live bound positive code := by
  constructor
  · intro accepted
    refine ⟨valid,fun branch edges run => ?_⟩
    exact accepted.2 branch (fun n => forgetEdge B (edges n))
      (run_forget B live bound positive code valid branch edges run)
  · intro accepted
    refine ⟨complete_local B live bound positive code valid,?_⟩
    intro branch edges run
    obtain ⟨lifted,compatible,forgotten⟩ := run_lift B live bound positive code valid branch edges run
    have parity := accepted.2 branch lifted compatible
    have same : (fun n => (tables B live bound positive).priority (code (branchNode branch n)) (lifted n)) =
        (fun n => (FiniteAlphabet.tables B live bound positive).priority
          (complete B live bound positive code valid (branchNode branch n)) (edges n)) := by
      funext n
      exact congrArg (fun e : FiniteAlphabet.Edge (capacity:=capacity) B => B.priority (e.1.2.state e.2)) (forgotten n)
    exact same ▸ parity

variable (M : Recognizer DistributedSynthesis.Graph G) [DecidablePred (· ∈ M.accept)]
variable (liveCorrect : ∀ h q, StateReachable B h q →
  (live q = true ↔ M.eval (History.graphSequence h) ∈ M.accept))

def decode (initialLive : M.eval [] ∈ M.accept)
    (code : LabeledTree (Fin capacity) (Letter B live bound positive))
    (valid : Local B live bound positive code) : CompressedTree B M bound :=
  ModelDecode.tree B M live liveCorrect positive initialLive
    (complete B live bound positive code valid) (complete_local B live bound positive code valid)

include liveCorrect in
theorem decode_accepting (initialLive : M.eval [] ∈ M.accept)
    (code : LabeledTree (Fin capacity) (Letter B live bound positive))
    (accepted : Accepting B live bound positive code) :
    (decode B live bound positive M liveCorrect initialLive code accepted.1).Accepting :=
  ModelDecode.tree_accepting B M live liveCorrect positive initialLive
    (complete B live bound positive code accepted.1) (complete_local B live bound positive code accepted.1)
    ((complete_accepting_iff B live bound positive code accepted.1).mpr accepted)

end Characterisation.ComponentTrees.GeneratingAlphabet
