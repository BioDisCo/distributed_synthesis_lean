/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemFinitePairedMealyControllerTrace

/-!
# Receipt-aware local control and its physical trace

The extension below adds one receipt bit to each local state. Its Boolean
outputs replace, rather than preserve, the base controller's outputs. The
base control trace is preserved. Thus this is a runtime regression repair,
not an acceptance-preserving transformation for an arbitrary specification.
-/

namespace DistributedSynthesis
namespace FinitePairedMealyController

universe u v x y c₁ c₂
variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable (C : FinitePairedMealyController.{u,v,x,y,c₁,c₂} In₁ In₂ Out₁ Out₂)

/-- Whether each process receives in the current physical round. -/
def receiptBits : Graph → Bool × Bool
  | .left => (true, false)
  | .right => (false, true)
  | .both => (true, true)

/-- Receipt bits before round `n`; initially neither process has received. -/
def previousReceiptBits (env : EnvironmentSequence In₁ In₂) : Nat → Bool × Bool
  | 0 => (false, false)
  | n + 1 => receiptBits (env n).graph

/-- The old bit is emitted, and the current local event determines the new
bit. In particular, neither receive map distinguishes strict from simultaneous
receipt, nor does a blind map inspect the partner's state. -/
def withReceiptMemory : FinitePairedMealyController In₁ In₂ Bool Bool where
  OneControl := C.OneControl × Bool
  TwoControl := C.TwoControl × Bool
  oneFinite := inferInstance
  twoFinite := inferInstance
  initialOne := (C.initialOne, false)
  initialTwo := (C.initialTwo, false)
  noRecvOne := fun s i ↦ (((C.noRecvOne s.1 i).1, false), s.2)
  noRecvTwo := fun s i ↦ (((C.noRecvTwo s.1 i).1, false), s.2)
  recvOne := fun s i t j ↦ (((C.recvOne s.1 i t.1 j).1, true), s.2)
  recvTwo := fun t j s i ↦ (((C.recvTwo t.1 j s.1 i).1, true), t.2)

/-- One physical transition preserves the underlying transition and records
exactly the local receipt events, in all three graph cases. -/
theorem withReceiptMemory_advance
    (s : C.withReceiptMemory.OneControl × C.withReceiptMemory.TwoControl)
    (e : EnvironmentRound In₁ In₂) :
    C.withReceiptMemory.semanticAdvanceControls s e =
      (((C.semanticAdvanceControls (s.1.1, s.2.1) e).1, (receiptBits e.graph).1),
       ((C.semanticAdvanceControls (s.1.1, s.2.1) e).2, (receiptBits e.graph).2)) := by
  cases h : e.graph <;> simp [semanticAdvanceControls, withReceiptMemory, receiptBits, h]

/-- Exact invariant, with no reachability or certificate premise on the base
controller. This also covers an acknowledged relay used as the base. -/
theorem withReceiptMemory_trace (env : EnvironmentSequence In₁ In₂) (n : Nat) :
    C.withReceiptMemory.semanticControlTrace env n =
      (((C.semanticControlTrace env n).1, (previousReceiptBits env n).1),
       ((C.semanticControlTrace env n).2, (previousReceiptBits env n).2)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [semanticControlTrace, withReceiptMemory_advance, ih]
    rfl

/-- Literal Mealy record, including outputs emitted during this transition. -/
def semanticRecord
    (s : C.OneControl × C.TwoControl) (e : EnvironmentRound In₁ In₂) :
    RoundRecord In₁ In₂ Graph Out₁ Out₂ where
  inputOne := e.inputOne
  inputTwo := e.inputTwo
  graph := e.graph
  outputOne := match e.graph with
    | .right => (C.noRecvOne s.1 e.inputOne).2
    | _ => (C.recvOne s.1 e.inputOne s.2 e.inputTwo).2
  outputTwo := match e.graph with
    | .left => (C.noRecvTwo s.2 e.inputTwo).2
    | _ => (C.recvTwo s.2 e.inputTwo s.1 e.inputOne).2

def semanticWord (env : EnvironmentSequence In₁ In₂) (n : Nat) :=
  C.semanticRecord (C.semanticControlTrace env n) (env n)

theorem withReceiptMemory_record_outputs
    (s : C.withReceiptMemory.OneControl × C.withReceiptMemory.TwoControl)
    (e : EnvironmentRound In₁ In₂) :
    let r := C.withReceiptMemory.semanticRecord s e
    (r.outputOne, r.outputTwo) = (s.1.2, s.2.2) := by
  cases h : e.graph <;> simp [semanticRecord, withReceiptMemory, h]

theorem withReceiptMemory_word_outputs (env : EnvironmentSequence In₁ In₂) (n : Nat) :
    let r := C.withReceiptMemory.semanticWord env n
    (r.outputOne, r.outputTwo) = previousReceiptBits env n := by
  dsimp only [semanticWord]
  rw [withReceiptMemory_record_outputs, withReceiptMemory_trace]

/-- Entry variant: initialize each endpoint with its own actual receipt bit.
The transition maps are unchanged, and no endpoint reads the other bit. -/
def withReceiptMemoryFrom (bits : Bool × Bool) :
    FinitePairedMealyController In₁ In₂ Bool Bool :=
  { C.withReceiptMemory with
    initialOne := (C.initialOne, bits.1)
    initialTwo := (C.initialTwo, bits.2) }

def receiptBitsFrom (bits : Bool × Bool) (env : EnvironmentSequence In₁ In₂) :
    Nat → Bool × Bool
  | 0 => bits
  | n + 1 => receiptBits (env n).graph

theorem withReceiptMemoryFrom_trace (bits : Bool × Bool)
    (env : EnvironmentSequence In₁ In₂) (n : Nat) :
    (C.withReceiptMemoryFrom bits).semanticControlTrace env n =
      (((C.semanticControlTrace env n).1, (receiptBitsFrom bits env n).1),
       ((C.semanticControlTrace env n).2, (receiptBitsFrom bits env n).2)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [semanticControlTrace]
    change C.withReceiptMemory.semanticAdvanceControls
      ((C.withReceiptMemoryFrom bits).semanticControlTrace env n) (env n) = _
    rw [withReceiptMemory_advance, ih]
    rfl

theorem withReceiptMemoryFrom_word_outputs (bits : Bool × Bool)
    (env : EnvironmentSequence In₁ In₂) (n : Nat) :
    let r := (C.withReceiptMemoryFrom bits).semanticWord env n
    (r.outputOne, r.outputTwo) = receiptBitsFrom bits env n := by
  have h := C.withReceiptMemory_record_outputs
    ((C.withReceiptMemoryFrom bits).semanticControlTrace env n) (env n)
  simpa only [semanticWord, withReceiptMemoryFrom_trace] using h

noncomputable section
variable [Fintype In₁] [Fintype In₂]
variable [Fintype Out₁] [Fintype Out₂] [Inhabited Out₁] [Inhabited Out₂]

omit [Fintype In₁] [Fintype In₂] in
/-- The semantic word is the actual word of the finite physical controller,
not merely an auxiliary global trace. -/
theorem mooreize_word_eq_semanticWord (env : EnvironmentSequence In₁ In₂) :
    C.mooreize.globalMachine.globalMachineTraceWord
      C.mooreize.globalOutputOne C.mooreize.globalOutputTwo env = C.semanticWord env := by
  funext n
  have h := C.mooreize_globalStateTrace_underlying env n
  have h₁ := congrArg Prod.fst h
  have h₂ := congrArg Prod.snd h
  cases hg : (env n).graph <;>
    simp [FiniteGlobalRoundMachine.globalMachineTraceWord,
      FiniteGlobalRoundMachine.globalStateTrace_succ,
      FinitePairedPhysicalController.globalMachine,
      FinitePairedPhysicalController.globalOutputOne,
      FinitePairedPhysicalController.globalOutputTwo,
      FinitePairedPhysicalController.advanceControls,
      mooreize, semanticWord, semanticRecord, hg] at h₁ h₂ ⊢ <;>
    simp only [h₁, h₂, and_self]

end
end FinitePairedMealyController
end DistributedSynthesis
