/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemFinitePairedStateEncoding

/-!
# Compiling finite policies with exact state access on receipt

A receive-state-aware policy may use the true pre-round automaton state on
receive, including when updating its future blind control. A blind map may
not use that state. The finite correlated encoding compiles every such policy
to an ordinary finite paired Mealy controller with exactly the same trace.

The compiler requires a finite policy; it does not synthesize that policy
from a perfect-recall winning strategy.
-/

namespace DistributedSynthesis
open FinitePairedStateEncoding

universe u v x y s c₁ c₂

structure FiniteReceiveStateAwareController
    (In₁ : Type u) (In₂ : Type v) (Out₁ : Type x) (Out₂ : Type y)
    (State : Type s) where
  OneControl : Type c₁
  TwoControl : Type c₂
  oneFinite : Fintype OneControl
  twoFinite : Fintype TwoControl
  initialOne : OneControl
  initialTwo : TwoControl
  noRecvOne : OneControl → In₁ → OneControl × Out₁
  noRecvTwo : TwoControl → In₂ → TwoControl × Out₂
  recvOne : State → OneControl → In₁ → TwoControl → In₂ → OneControl × Out₁
  recvTwo : State → TwoControl → In₂ → OneControl → In₁ → TwoControl × Out₂

attribute [instance] FiniteReceiveStateAwareController.oneFinite
  FiniteReceiveStateAwareController.twoFinite

namespace FiniteReceiveStateAwareController
open FinitePairedMealyController DetParityAutomaton

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable (A : DetParityAutomaton.{max u v x y,s}
  (RoundRecord In₁ In₂ Graph Out₁ Out₂))
variable (P : FiniteReceiveStateAwareController.{u,v,x,y,s,c₁,c₂}
  In₁ In₂ Out₁ Out₂ A.State)

/-- Fixing the pre-round state gives four ordinary local maps for that round.
Only the receive maps depend on it. This is a specification, not the compiler. -/
def atState (q : A.State) : FinitePairedMealyController In₁ In₂ Out₁ Out₂ where
  OneControl := P.OneControl
  TwoControl := P.TwoControl
  oneFinite := inferInstance
  twoFinite := inferInstance
  initialOne := P.initialOne
  initialTwo := P.initialTwo
  noRecvOne := P.noRecvOne
  noRecvTwo := P.noRecvTwo
  recvOne := P.recvOne q
  recvTwo := P.recvTwo q

abbrev GlobalState := (P.OneControl × P.TwoControl) × A.State

def globalStep (s : P.GlobalState A) (e : EnvironmentRound In₁ In₂) : P.GlobalState A :=
  ((P.atState A s.2).semanticAdvanceControls s.1 e,
    A.step s.2 ((P.atState A s.2).semanticRecord s.1 e))

def globalTrace (env : EnvironmentSequence In₁ In₂) : Nat → P.GlobalState A
  | 0 => ((P.initialOne,P.initialTwo), A.initial)
  | n + 1 => P.globalStep A (globalTrace env n) (env n)

def word (env : EnvironmentSequence In₁ In₂) (n : Nat) :
    RoundRecord In₁ In₂ Graph Out₁ Out₂ :=
  let s := P.globalTrace A env n
  (P.atState A s.2).semanticRecord s.1 (env n)

def successor (one : P.OneControl × Control A.State)
    (two : P.TwoControl × Control A.State) (i : In₁) (j : In₂) (g : Graph) : A.State :=
  let q := decode one.2 two.2
  A.step q ((P.atState A q).semanticRecord (one.1,two.1) ⟨i,j,g⟩)

/-- No graph or global-state oracle appears in the four runtime maps. -/
def compile : FinitePairedMealyController In₁ In₂ Out₁ Out₂ where
  OneControl := P.OneControl × Control A.State
  TwoControl := P.TwoControl × Control A.State
  oneFinite := inferInstance
  twoFinite := inferInstance
  initialOne := (P.initialOne, initial A.initial)
  initialTwo := (P.initialTwo, initial A.initial)
  noRecvOne := fun one i ↦ (((P.noRecvOne one.1 i).1, one.2), (P.noRecvOne one.1 i).2)
  noRecvTwo := fun two j ↦ (((P.noRecvTwo two.1 j).1, two.2), (P.noRecvTwo two.1 j).2)
  recvOne := fun one i two j ↦
    let next := P.recvOne (decode one.2 two.2) one.1 i two.1 j
    ((next.1, receiveOne one.2 two.2 (P.successor A one two i j .left)
      (P.successor A one two i j .both)), next.2)
  recvTwo := fun two j one i ↦
    let next := P.recvTwo (decode one.2 two.2) two.1 j one.1 i
    ((next.1, receiveTwo one.2 two.2 (P.successor A one two i j .right)
      (P.successor A one two i j .both)), next.2)

def project (s : (P.compile A).OneControl × (P.compile A).TwoControl) : P.GlobalState A :=
  ((s.1.1,s.2.1), decode s.1.2 s.2.2)

theorem compile_record (s : (P.compile A).OneControl × (P.compile A).TwoControl)
    (e : EnvironmentRound In₁ In₂) :
    (P.compile A).semanticRecord s e =
      (P.atState A (P.project A s).2).semanticRecord (P.project A s).1 e := by
  cases hg : e.graph <;> simp [semanticRecord, compile, project, atState, hg]

/-- One invariant covers the base control updates, the new automaton state,
and the correlation of the two encodings, for all three graphs. -/
theorem compile_step (s : (P.compile A).OneControl × (P.compile A).TwoControl)
    (e : EnvironmentRound In₁ In₂) :
    P.project A ((P.compile A).semanticAdvanceControls s e) =
      P.globalStep A (P.project A s) e := by
  rcases e with ⟨i,j,g⟩
  cases g <;> simp [project, globalStep, semanticAdvanceControls, compile,
    atState, decode_left, decode_right, decode_both, successor]

theorem compile_trace (env : EnvironmentSequence In₁ In₂) (n : Nat) :
    P.project A ((P.compile A).semanticControlTrace env n) = P.globalTrace A env n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [semanticControlTrace, compile_step, ih]
    rfl

theorem compile_word (env : EnvironmentSequence In₁ In₂) :
    (P.compile A).semanticWord env = P.word A env := by
  funext n
  unfold semanticWord word
  rw [compile_record, compile_trace]

theorem globalTrace_state (env : EnvironmentSequence In₁ In₂) (n : Nat) :
    (P.globalTrace A env n).2 = A.run (P.word A env) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change A.step (P.globalTrace A env n).2 (P.word A env n) = _
    rw [ih]
    rfl

theorem compile_state (env : EnvironmentSequence In₁ In₂) (n : Nat) :
    let s := (P.compile A).semanticControlTrace env n
    decode s.1.2 s.2.2 = A.run ((P.compile A).semanticWord env) n := by
  rw [compile_word]
  exact (congrArg Prod.snd (P.compile_trace A env n)).trans
    (P.globalTrace_state A env n)

noncomputable section
variable [Fintype In₁] [Fintype In₂]
variable [Fintype Out₁] [Fintype Out₂] [Inhabited Out₁] [Inhabited Out₂]

omit [Fintype In₁] [Fintype In₂] in
theorem compile_physical_word (env : EnvironmentSequence In₁ In₂) :
    let C := (P.compile A).mooreize
    C.globalMachine.globalMachineTraceWord C.globalOutputOne C.globalOutputTwo env = P.word A env := by
  dsimp only
  rw [mooreize_word_eq_semanticWord, compile_word]

omit [Fintype In₁] [Fintype In₂] in
/-- Acceptance transfer is unconditional once a finite state-aware winning
policy has been supplied. Constructing that policy remains a separate task. -/
theorem compile_physical_accepts
    (hwin : ∀ env, A.Accepts (P.word A env)) (env : EnvironmentSequence In₁ In₂) :
    let C := (P.compile A).mooreize
    A.Accepts (C.globalMachine.globalMachineTraceWord C.globalOutputOne C.globalOutputTwo env) := by
  dsimp only
  rw [compile_physical_word]
  exact hwin env

end
end FiniteReceiveStateAwareController
end DistributedSynthesis
