/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemFinitePairedStateEncoding

/-!
# Exact automaton-state tracking without changing the distributed outputs

For every finite paired controller and finite deterministic parity automaton,
add a finite correlated state encoding to the two endpoints. The four local
maps preserve the original outputs, while the joint decoder follows the
automaton on the actual physical word. Receive maps need no current graph.

This closes finite tracking of the actual automaton state. It does not make
that state available to a blind endpoint, construct a winning base controller,
or re-anchor arbitrary strategy-history families.
-/

namespace DistributedSynthesis
namespace FinitePairedMealyController
open FinitePairedStateEncoding DetParityAutomaton

universe u v x y c₁ c₂ s
variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable (C : FinitePairedMealyController.{u,v,x,y,c₁,c₂} In₁ In₂ Out₁ Out₂)
variable (A : DetParityAutomaton.{max u v x y,s}
  (RoundRecord In₁ In₂ Graph Out₁ Out₂))

/-- Evaluate each possible physical successor from the same pre-round
controls and decoded actual state. The receive maps store both relevant
possibilities rather than selecting the actual graph. -/
def monitoredSuccessor
    (one : C.OneControl × Control A.State) (two : C.TwoControl × Control A.State)
    (i : In₁) (j : In₂) (g : Graph) : A.State :=
  A.step (decode one.2 two.2) (C.semanticRecord (one.1,two.1) ⟨i,j,g⟩)

def withAutomatonMonitor : FinitePairedMealyController In₁ In₂ Out₁ Out₂ where
  OneControl := C.OneControl × Control A.State
  TwoControl := C.TwoControl × Control A.State
  oneFinite := inferInstance
  twoFinite := inferInstance
  initialOne := (C.initialOne, initial A.initial)
  initialTwo := (C.initialTwo, initial A.initial)
  noRecvOne := fun one i ↦ (((C.noRecvOne one.1 i).1, one.2), (C.noRecvOne one.1 i).2)
  noRecvTwo := fun two j ↦ (((C.noRecvTwo two.1 j).1, two.2), (C.noRecvTwo two.1 j).2)
  recvOne := fun one i two j ↦
    (((C.recvOne one.1 i two.1 j).1,
      receiveOne one.2 two.2 (C.monitoredSuccessor A one two i j .left)
        (C.monitoredSuccessor A one two i j .both)),
      (C.recvOne one.1 i two.1 j).2)
  recvTwo := fun two j one i ↦
    (((C.recvTwo two.1 j one.1 i).1,
      receiveTwo one.2 two.2 (C.monitoredSuccessor A one two i j .right)
        (C.monitoredSuccessor A one two i j .both)),
      (C.recvTwo two.1 j one.1 i).2)

theorem withAutomatonMonitor_step_base
    (s : (C.withAutomatonMonitor A).OneControl × (C.withAutomatonMonitor A).TwoControl)
    (e : EnvironmentRound In₁ In₂) :
    let t := (C.withAutomatonMonitor A).semanticAdvanceControls s e
    (t.1.1,t.2.1) = C.semanticAdvanceControls (s.1.1,s.2.1) e := by
  cases hg : e.graph <;> simp [semanticAdvanceControls, withAutomatonMonitor, hg]

theorem withAutomatonMonitor_record
    (s : (C.withAutomatonMonitor A).OneControl × (C.withAutomatonMonitor A).TwoControl)
    (e : EnvironmentRound In₁ In₂) :
    (C.withAutomatonMonitor A).semanticRecord s e = C.semanticRecord (s.1.1,s.2.1) e := by
  cases hg : e.graph <;> simp [semanticRecord, withAutomatonMonitor, hg]

/-- Exact successor alignment for every pair of local controls, not merely
reachable controls. The same receive updates satisfy all three graph cases. -/
theorem withAutomatonMonitor_step_state
    (s : (C.withAutomatonMonitor A).OneControl × (C.withAutomatonMonitor A).TwoControl)
    (e : EnvironmentRound In₁ In₂) :
    let t := (C.withAutomatonMonitor A).semanticAdvanceControls s e
    decode t.1.2 t.2.2 =
      A.step (decode s.1.2 s.2.2) ((C.withAutomatonMonitor A).semanticRecord s e) := by
  rw [withAutomatonMonitor_record]
  rcases e with ⟨i,j,g⟩
  cases g <;> simp [semanticAdvanceControls, withAutomatonMonitor,
    decode_left, decode_right, decode_both, monitoredSuccessor]

theorem withAutomatonMonitor_trace_base (env : EnvironmentSequence In₁ In₂) (n : Nat) :
    let s := (C.withAutomatonMonitor A).semanticControlTrace env n
    (s.1.1,s.2.1) = C.semanticControlTrace env n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [semanticControlTrace]
    rw [withAutomatonMonitor_step_base, ih]

theorem withAutomatonMonitor_word (env : EnvironmentSequence In₁ In₂) :
    (C.withAutomatonMonitor A).semanticWord env = C.semanticWord env := by
  funext n
  unfold semanticWord
  rw [withAutomatonMonitor_record, withAutomatonMonitor_trace_base]

theorem withAutomatonMonitor_trace_state (env : EnvironmentSequence In₁ In₂) (n : Nat) :
    let s := (C.withAutomatonMonitor A).semanticControlTrace env n
    decode s.1.2 s.2.2 = A.run (C.semanticWord env) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [semanticControlTrace]
    rw [withAutomatonMonitor_step_state, ih]
    change A.step (A.run (C.semanticWord env) n)
      ((C.withAutomatonMonitor A).semanticWord env n) = _
    rw [withAutomatonMonitor_word]
    rfl

noncomputable section
variable [Fintype In₁] [Fintype In₂]
variable [Fintype Out₁] [Fintype Out₂] [Inhabited Out₁] [Inhabited Out₂]

omit [Fintype In₁] [Fintype In₂] in
/-- Literal equality of the actual physical words, including both outputs. -/
theorem withAutomatonMonitor_physical_word (env : EnvironmentSequence In₁ In₂) :
    let P := (C.withAutomatonMonitor A).mooreize
    P.globalMachine.globalMachineTraceWord P.globalOutputOne P.globalOutputTwo env =
      C.mooreize.globalMachine.globalMachineTraceWord
        C.mooreize.globalOutputOne C.mooreize.globalOutputTwo env := by
  dsimp only
  rw [mooreize_word_eq_semanticWord, mooreize_word_eq_semanticWord,
    withAutomatonMonitor_word]

omit [Fintype In₁] [Fintype In₂] in
/-- The encoded state tracks the actual physical word, with pre-round
indexing. No acceptance hypothesis or perfect-recall strategy occurs here. -/
theorem withAutomatonMonitor_physical_state (env : EnvironmentSequence In₁ In₂) (n : Nat) :
    let P := (C.withAutomatonMonitor A).mooreize
    let s := P.globalMachine.globalStateTrace env n
    decode s.1.1.2 s.2.1.2 =
      A.run (P.globalMachine.globalMachineTraceWord P.globalOutputOne P.globalOutputTwo env) n := by
  dsimp only
  rw [mooreize_word_eq_semanticWord, withAutomatonMonitor_word]
  have h := (C.withAutomatonMonitor A).mooreize_globalStateTrace_underlying env n
  have h' := congrArg (fun pair ↦ decode pair.1.2 pair.2.2) h
  exact h'.trans (C.withAutomatonMonitor_trace_state A env n)

end
end FinitePairedMealyController
end DistributedSynthesis
