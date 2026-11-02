/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.PrivateInputs.Model
import DistributedSynthesis.Library.Distributed.PrivateInputs.Paths

/-! # Local two-round coding of private inputs

This coding never transmits an input to the other process. The first process
has a data bit and a clock bit; the second has one data bit.
-/

namespace DistributedSynthesis.PrivateInputs.Binary

def bits : Symbol → Bool × Bool
  | none => (false, false)
  | some true => (false, true)
  | some false => (true, false)

def unbits : Bool → Bool → Symbol
  | false, false => none
  | false, true => some true
  | true, false => some false
  | true, true => none

@[simp] theorem unbits_bits (a : Symbol) : unbits (bits a).1 (bits a).2 = a := by
  cases a with
  | none => rfl
  | some a => cases a <;> rfl

def encodeWord (w : List Symbol) : List Bool := w.flatMap fun a ↦ [(bits a).1, (bits a).2]
def decodeWord : List Bool → List Symbol
  | a :: b :: w => unbits a b :: decodeWord w
  | _ => []

theorem decodeWord_snoc (w : List Bool) (hw : w.length % 2 = 0) (a b : Bool) :
    decodeWord (w ++ [a,b]) = decodeWord w ++ [unbits a b] := by
  induction w using List.twoStepInduction with
  | nil => rfl
  | singleton x => simp at hw
  | cons_cons x y w ih _ =>
    have hh : w.length % 2 = 0 := by simp only [List.length_cons] at hw; omega
    simpa only [List.cons_append, decodeWord] using congrArg (List.cons (unbits x y)) (ih hh)

@[simp] theorem decode_encodeWord (w : List Symbol) : decodeWord (encodeWord w) = w := by
  induction w with
  | nil => rfl
  | cons a w ih => simpa [encodeWord, decodeWord] using ih

def encodeStream (x : Nat → Symbol) (t : Nat) : Bool :=
  if t % 2 = 0 then (bits (x (t/2))).1 else (bits (x (t/2))).2

@[simp] theorem encodeStream_even (x : Nat → Symbol) (t : Nat) :
    encodeStream x (2*t) = (bits (x t)).1 := by simp [encodeStream]
@[simp] theorem encodeStream_odd (x : Nat → Symbol) (t : Nat) :
    encodeStream x (2*t+1) = (bits (x t)).2 := by
  have ht : (2*t+1)/2 = t := by omega
  simp [encodeStream, ht]

theorem prefix_two {I : Type*} (x : Nat → I) (t : Nat) :
    inputPrefix x (2*(t+1)) = inputPrefix x (2*t) ++ [x (2*t), x (2*t+1)] := by
  rw [show 2*(t+1) = (2*t+1)+1 by omega]
  simp only [inputPrefix, List.append_assoc, List.singleton_append]

theorem encoded_prefix (x : Nat → Symbol) (t : Nat) :
    inputPrefix (encodeStream x) (2*t) = encodeWord (inputPrefix x t) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [prefix_two, ih]
    simp [inputPrefix, encodeWord]

theorem decoded_prefix (x : Nat → Bool) (t : Nat) :
    decodeWord (inputPrefix x (2*t)) = inputPrefix (fun n ↦ unbits (x (2*n)) (x (2*n+1))) t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [prefix_two, decodeWord_snoc _ (by simp) _ _, ih]
    rfl

def encodeEnvironment (env : EnvironmentSequence Symbol Symbol) : EnvironmentSequence Bool Bool :=
  fun t ↦ ⟨encodeStream (fun k ↦ (env k).inputOne) t,
    encodeStream (fun k ↦ (env k).inputTwo) t⟩

def decodeEnvironment (env : EnvironmentSequence Bool Bool) : EnvironmentSequence Symbol Symbol :=
  fun t ↦ ⟨unbits (env (2*t)).inputOne (env (2*t+1)).inputOne,
    unbits (env (2*t)).inputTwo (env (2*t+1)).inputTwo⟩

@[simp] theorem decode_encodeEnvironment (env : EnvironmentSequence Symbol Symbol) :
    decodeEnvironment (encodeEnvironment env) = env := by
  funext t
  simp only [decodeEnvironment, encodeEnvironment, encodeStream_even, encodeStream_odd, unbits_bits]

def encodeStrategy (σ : StrategyPair Symbol Symbol Bool Bool) : StrategyPair Bool Bool (Bool × Bool) Bool :=
  ⟨fun w ↦ (σ.one (decodeWord w), decide (w.length % 2 = 1)), fun w ↦ σ.two (decodeWord w)⟩

def decodeStrategy (τ : StrategyPair Bool Bool (Bool × Bool) Bool) : StrategyPair Symbol Symbol Bool Bool :=
  ⟨fun w ↦ (τ.one (encodeWord w)).1, fun w ↦ τ.two (encodeWord w)⟩

abbrev Atom := (Bool × Bool) × (Bool × Bool) × Bool

def raw (r : Letter Bool Bool (Bool × Bool) Bool) : Atom :=
  ((r.inputOne, r.inputTwo), r.outputOne, r.outputTwo)

def blockLetter (a b : Atom) : Input × Bool × Bool :=
  ((unbits a.1.1 b.1.1, unbits a.1.2 b.1.2), b.2.1.1, b.2.2)

def sample (w : OmegaWord Atom) : OmegaWord (Input × Bool × Bool) :=
  fun t ↦ blockLetter (w (2*t)) (w (2*t+1))

theorem encode_sample (σ : StrategyPair Symbol Symbol Bool Bool) (env : EnvironmentSequence Bool Bool) :
    sample (fun t ↦ raw (execution (encodeStrategy σ) env t)) =
      fun t ↦ (( (execution σ (decodeEnvironment env) t).inputOne,
        (execution σ (decodeEnvironment env) t).inputTwo),
        (execution σ (decodeEnvironment env) t).outputOne,
        (execution σ (decodeEnvironment env) t).outputTwo) := by
  funext t
  simp only [sample, blockLetter, raw, execution, encodeStrategy, decodeEnvironment]
  rw [show 2*t+1+1 = 2*(t+1) by omega, decoded_prefix, decoded_prefix]

theorem decode_sample (τ : StrategyPair Bool Bool (Bool × Bool) Bool)
    (env : EnvironmentSequence Symbol Symbol) :
    sample (fun t ↦ raw (execution τ (encodeEnvironment env) t)) =
      fun t ↦ (((execution (decodeStrategy τ) env t).inputOne,
        (execution (decodeStrategy τ) env t).inputTwo),
        (execution (decodeStrategy τ) env t).outputOne,
        (execution (decodeStrategy τ) env t).outputTwo) := by
  funext t
  simp only [sample, blockLetter, raw, execution, decodeStrategy, encodeEnvironment]
  rw [show 2*t+1+1 = 2*(t+1) by omega]
  simp only [encoded_prefix, encodeStream_even, encodeStream_odd, unbits_bits]

end DistributedSynthesis.PrivateInputs.Binary
