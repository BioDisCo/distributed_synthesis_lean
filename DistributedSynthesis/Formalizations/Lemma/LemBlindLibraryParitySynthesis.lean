/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemParityTreePositionalization
import DistributedSynthesis.Formalizations.Lemma.LemFiniteReceiveStateAwareController

/-!
# Joint parity synthesis for a fixed finite blind library

A library fixes the two blind transition/output maps, but leaves all receive
choices open. One prescription chooses both receive outputs and successor
controls for every input pair, before the current graph is selected. An
accepting prescription tree may depend on the entire environment history.
If the library is finite, joint parity positionalization and state-aware
compilation produce a finite distributed winner, with no additional common
choice, rank, or observation-uniformity premise.

The library definition deliberately does not assert finiteness. Proving that
some finite library has an accepting tree is the remaining completeness task.
-/

namespace DistributedSynthesis

universe u v x y c₁ c₂ s

structure BlindControllerLibrary (In₁ : Type u) (In₂ : Type v)
    (Out₁ : Type x) (Out₂ : Type y) where
  OneControl : Type c₁
  TwoControl : Type c₂
  initialOne : OneControl
  initialTwo : TwoControl
  noRecvOne : OneControl → In₁ → OneControl × Out₁
  noRecvTwo : TwoControl → In₂ → TwoControl × Out₂

namespace BlindControllerLibrary
open DetParityAutomaton FinitePairedMealyController

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable (L : BlindControllerLibrary.{u,v,x,y,c₁,c₂} In₁ In₂ Out₁ Out₂)
variable (A : DetParityAutomaton.{max u v x y,s}
  (RoundRecord In₁ In₂ Graph Out₁ Out₂))

abbrev State := (L.OneControl × L.TwoControl) × A.State
abbrev Move := In₁ → In₂ → (L.OneControl × Out₁) × (L.TwoControl × Out₂)

def initial : L.State A := ((L.initialOne,L.initialTwo),A.initial)

/-- Literal transition results. The two receive choices are shared between
strict and simultaneous branches; only blind choices use the fixed library. -/
def responses (s : L.State A) (move : L.Move) (e : EnvironmentRound In₁ In₂) :
    (L.OneControl × Out₁) × (L.TwoControl × Out₂) :=
  match e.graph with
  | .left => ((move e.inputOne e.inputTwo).1, L.noRecvTwo s.1.2 e.inputTwo)
  | .right => (L.noRecvOne s.1.1 e.inputOne, (move e.inputOne e.inputTwo).2)
  | .both => move e.inputOne e.inputTwo

def record (s : L.State A) (move : L.Move) (e : EnvironmentRound In₁ In₂) :
    RoundRecord In₁ In₂ Graph Out₁ Out₂ :=
  ⟨e.inputOne,e.inputTwo,e.graph,(L.responses A s move e).1.2,(L.responses A s move e).2.2⟩

def next (s : L.State A) (move : L.Move) (e : EnvironmentRound In₁ In₂) : L.State A :=
  (((L.responses A s move e).1.1,(L.responses A s move e).2.1),
    A.step s.2 (L.record A s move e))

/-- Infinite semantic witnesses are allowed here. Finiteness is imposed only
in the extraction theorem, not hidden inside this premise. -/
def HasAcceptingTree : Prop :=
  ∃ tree : LabeledTree (EnvironmentRound In₁ In₂) L.Move,
    ∃ run : List (EnvironmentRound In₁ In₂) → L.State A,
      (run [] = L.initial A ∧
      (∀ node e, run (node ++ [e]) = L.next A (run node) (tree node) e)) ∧
      ∀ env : EnvironmentSequence In₁ In₂,
        NatSeqMinEvenParity (fun n ↦ A.priority (run (branchNode env n)).2)

section Finite
variable [Fintype L.OneControl] [Fintype L.TwoControl]
variable [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]

noncomputable instance moveFinite : Fintype L.Move := by
  classical
  exact inferInstanceAs (Fintype (In₁ → In₂ → (L.OneControl × Out₁) × (L.TwoControl × Out₂)))

/-- One finite parity automaton checks all graph words jointly, rather than
checking each homogeneous direction in a separate monitor. -/
def automaton : RunParityTreeAutomaton (EnvironmentRound In₁ In₂) L.Move :=
  ParityPrescription.automaton (L.initial A) (L.next A) (fun s ↦ A.priority s.2)

omit [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂] in
theorem hasAcceptingTree_iff : L.HasAcceptingTree A ↔
    ∃ tree, (L.automaton A).acceptsTree tree := by
  rfl

def policy (choose : L.State A → L.Move) :
    FiniteReceiveStateAwareController In₁ In₂ Out₁ Out₂ A.State where
  OneControl := L.OneControl
  TwoControl := L.TwoControl
  oneFinite := inferInstance
  twoFinite := inferInstance
  initialOne := L.initialOne
  initialTwo := L.initialTwo
  noRecvOne := L.noRecvOne
  noRecvTwo := L.noRecvTwo
  recvOne := fun q one i two j ↦ (choose ((one,two),q) i j).1
  recvTwo := fun q two j one i ↦ (choose ((one,two),q) i j).2

omit [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂] in
theorem policy_step (choose : L.State A → L.Move) (s : L.State A)
    (e : EnvironmentRound In₁ In₂) :
    (L.policy A choose).globalStep A s e = L.next A s (choose s) e := by
  cases hg : e.graph <;>
    simp [FiniteReceiveStateAwareController.globalStep,
      FiniteReceiveStateAwareController.atState, semanticAdvanceControls,
      semanticRecord, policy, next, record, responses, hg]

omit [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂] in
theorem policy_trace (choose : L.State A → L.Move)
    (env : EnvironmentSequence In₁ In₂) (n : Nat) :
    (L.policy A choose).globalTrace A env n =
      ParityPrescription.stateAt (L.initial A) (L.next A) choose (branchNode env n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [FiniteReceiveStateAwareController.globalTrace, ih, policy_step]
    exact (ParityPrescription.stateAt_append (L.initial A) (L.next A) choose
      (branchNode env n) (env n)).symm

/-- Joint uniformity and all-branch parity are extracted, not assumed as
extra certificates. The sole substantive premise is an accepting tree over
this fixed finite blind library. The original tree's labels may be replaced. -/
theorem exists_winning_policy (h : L.HasAcceptingTree A) :
    ∃ choose : L.State A → L.Move, ∀ env,
      A.Accepts ((L.policy A choose).word A env) := by
  obtain ⟨choose, hparity⟩ := ParityPrescription.exists_positional
    (L.initial A) (L.next A) (fun s ↦ A.priority s.2)
    ((L.hasAcceptingTree_iff A).mp h)
  refine ⟨choose, ?_⟩
  intro env
  change NatSeqMinEvenParity
    (fun n ↦ A.priority (A.run ((L.policy A choose).word A env) n))
  have heq : (fun n ↦ A.priority (A.run ((L.policy A choose).word A env) n)) =
      (fun n ↦ A.priority
        (ParityPrescription.stateAt (L.initial A) (L.next A) choose (branchNode env n)).2) := by
    funext n
    rw [← (L.policy A choose).globalTrace_state A env n, policy_trace]
  rw [heq]
  exact hparity env

variable [Inhabited Out₁] [Inhabited Out₂]

theorem exists_winning_physical_controller (h : L.HasAcceptingTree A) :
    ∃ C : FinitePairedPhysicalController.{u,v,x,y,max (max c₁ s) x,max (max c₂ s) y}
      In₁ In₂ Out₁ Out₂, ∀ env,
      A.Accepts (C.globalMachine.globalMachineTraceWord C.globalOutputOne C.globalOutputTwo env) := by
  obtain ⟨choose,hwin⟩ := L.exists_winning_policy A h
  exact ⟨((L.policy A choose).compile A).mooreize,
    (L.policy A choose).compile_physical_accepts A hwin⟩

end Finite
end BlindControllerLibrary
end DistributedSynthesis
