/-
Lean adaptation and development: the paper authors listed in AUTHORS.md
at the repository root. The credits below refer to upstream formalizations,
not authorship of this Lean implementation; see the CounterMachines README.md.
-/

/-
SPDX-License-Identifier: MPL-2.0
Control macros for the Lean adaptation of Dominique Larchey-Wendling's BSM.v.
These macros and exact step-count proofs are additions of this project.
See README.md and LICENSE-MPL-2.0 in this directory.
-/
import DistributedSynthesis.Library.Computability.CounterMachines.BSM

/-! # BSM control macros with strict progress

An unconditional jump pushes false and immediately pops it. Thus it uses an
existing stack, preserves all its contents, and needs no empty auxiliary stack.
A dispatching peek restores a popped bit before jumping to the selected target;
the empty branch changes no stack. `Placed` makes the code-placement assumptions
explicit. These are local block proofs, not a whole-program compiler.
-/
namespace DistributedSynthesis.CounterMachine.BSM

variable {n : Nat}

def runSteps (P : Program n) (base : Nat) : Nat → Cfg n → Option (Cfg n)
  | 0, x => some x
  | t+1, x => (step P base x).bind (runSteps P base t)

theorem runSteps_reaches (P : Program n) (base t : Nat) (x y : Cfg n)
    (h : runSteps P base t x = some y) : Reaches P base x y := by
  induction t generalizing x with
  | zero => cases h; exact .refl
  | succ t ih =>
    cases hs : step P base x with
    | none => simp [runSteps,hs] at h
    | some z =>
      exact Relation.ReflTransGen.head (by simp [hs]) (ih z (by simpa [runSteps,hs] using h))

theorem runSteps_reaches₁ (P : Program n) (base t : Nat) (x y : Cfg n)
    (ht : 0 < t) (h : runSteps P base t x = some y) : Reaches₁ P base x y := by
  cases t with
  | zero => cases ht
  | succ t =>
    cases hs : step P base x with
    | none => simp [runSteps,hs] at h
    | some z =>
      exact Relation.TransGen.head' (by simp [hs])
        (runSteps_reaches P base t z y (by simpa [runSteps,hs] using h))

def Placed (P : Program n) (base i : Nat) (code : Program n) : Prop :=
  ∀ j, j < code.length → lookup P base (i+j) = code[j]?

theorem placed_self (code : Program n) (base : Nat) : Placed code base base code := by
  intro j hj
  simp [lookup]

def jump (k : Fin n) (target : Nat) : Program n :=
  [push k false,pop k target target]

theorem jump_correct (P : Program n) (base i target : Nat) (k : Fin n)
    (s : Stacks n) (h₀ : lookup P base i = some (push k false))
    (h₁ : lookup P base (i+1) = some (pop k target target)) :
    runSteps P base 2 (i,s) = some (target,s) := by
  simp [runSteps,step,h₀,h₁,next,push,pop]

theorem jump_placed (P : Program n) (base i target : Nat) (k : Fin n)
    (s : Stacks n) (h : Placed P base i (jump k target)) :
    runSteps P base 2 (i,s) = some (target,s) := by
  apply jump_correct
  · simpa [jump] using h 0 (by simp [jump])
  · simpa [jump] using h 1 (by simp [jump])

theorem jump_progress (P : Program n) (base i target : Nat) (k : Fin n)
    (s : Stacks n) (h : Placed P base i (jump k target)) :
    Reaches₁ P base (i,s) (target,s) :=
  runSteps_reaches₁ P base 2 _ _ (by decide) (jump_placed P base i target k s h)

def pushTo (k : Fin n) (b : Bool) (target : Nat) : Program n :=
  [push k b,push k false,pop k target target]

theorem pushTo_correct (P : Program n) (base i target : Nat) (k : Fin n)
    (b : Bool) (s : Stacks n) (h : Placed P base i (pushTo k b target)) :
    runSteps P base 3 (i,s) = some (target,Function.update s k (b :: s k)) := by
  have h₀ : lookup P base i = some (push k b) := by
    simpa [pushTo] using h 0 (by simp [pushTo])
  have h₁ : lookup P base (i+1) = some (push k false) := by
    simpa [pushTo] using h 1 (by simp [pushTo])
  have h₂ : lookup P base (i+2) = some (pop k target target) := by
    simpa [pushTo] using h 2 (by simp [pushTo])
  simp [runSteps,step,h₀,h₁,h₂,next,push,pop,Nat.add_assoc]

def popTo (k : Fin n) (jt jf je : Nat) : Program n :=
  [pop k jf je,push k false,pop k jt jt]

theorem popTo_empty (P : Program n) (base i jt jf je : Nat) (k : Fin n)
    (s : Stacks n) (hs : s k = []) (h : Placed P base i (popTo k jt jf je)) :
    runSteps P base 1 (i,s) = some (je,s) := by
  have h₀ : lookup P base i = some (pop k jf je) := by
    simpa [popTo] using h 0 (by simp [popTo])
  simp [runSteps,step,h₀,next,pop,hs]

theorem popTo_false (P : Program n) (base i jt jf je : Nat) (k : Fin n)
    (s : Stacks n) (l : List Bool) (hs : s k = false :: l)
    (h : Placed P base i (popTo k jt jf je)) :
    runSteps P base 1 (i,s) = some (jf,Function.update s k l) := by
  have h₀ : lookup P base i = some (pop k jf je) := by
    simpa [popTo] using h 0 (by simp [popTo])
  simp [runSteps,step,h₀,next,pop,hs]

theorem popTo_true (P : Program n) (base i jt jf je : Nat) (k : Fin n)
    (s : Stacks n) (l : List Bool) (hs : s k = true :: l)
    (h : Placed P base i (popTo k jt jf je)) :
    runSteps P base 3 (i,s) = some (jt,Function.update s k l) := by
  have h₀ : lookup P base i = some (pop k jf je) := by
    simpa [popTo] using h 0 (by simp [popTo])
  have h₁ : lookup P base (i+1) = some (push k false) := by
    simpa [popTo] using h 1 (by simp [popTo])
  have h₂ : lookup P base (i+2) = some (pop k jt jt) := by
    simpa [popTo] using h 2 (by simp [popTo])
  simp [runSteps,step,h₀,h₁,h₂,next,push,pop,hs,Nat.add_assoc]

/-- Seven instructions: true and false paths restore the bit, then jump.
The empty path jumps immediately without modifying any stack. -/
def peek (k : Fin n) (i jt jf je : Nat) : Program n :=
  [pop k (i+4) je,push k true,push k false,pop k jt jt,
    push k false,push k false,pop k jf jf]

theorem peek_empty (P : Program n) (base i jt jf je : Nat) (k : Fin n)
    (s : Stacks n) (hs : s k = []) (h : Placed P base i (peek k i jt jf je)) :
    runSteps P base 1 (i,s) = some (je,s) := by
  have h₀ : lookup P base i = some (pop k (i+4) je) := by
    simpa [peek] using h 0 (by simp [peek])
  simp [runSteps,step,h₀,next,pop,hs]

theorem peek_true (P : Program n) (base i jt jf je : Nat) (k : Fin n)
    (s : Stacks n) (l : List Bool) (hs : s k = true :: l)
    (h : Placed P base i (peek k i jt jf je)) :
    runSteps P base 4 (i,s) = some (jt,s) := by
  have h₀ : lookup P base i = some (pop k (i+4) je) := by
    simpa [peek] using h 0 (by simp [peek])
  have h₁ : lookup P base (i+1) = some (push k true) := by
    simpa [peek] using h 1 (by simp [peek])
  have h₂ : lookup P base (i+2) = some (push k false) := by
    simpa [peek] using h 2 (by simp [peek])
  have h₃ : lookup P base (i+3) = some (pop k jt jt) := by
    simpa [peek] using h 3 (by simp [peek])
  have hu : Function.update s k (true :: l) = s := Function.update_eq_self_iff.mpr hs.symm
  simp [runSteps,step,h₀,h₁,h₂,h₃,next,push,pop,hs,hu,Nat.add_assoc]

theorem peek_false (P : Program n) (base i jt jf je : Nat) (k : Fin n)
    (s : Stacks n) (l : List Bool) (hs : s k = false :: l)
    (h : Placed P base i (peek k i jt jf je)) :
    runSteps P base 4 (i,s) = some (jf,s) := by
  have h₀ : lookup P base i = some (pop k (i+4) je) := by
    simpa [peek] using h 0 (by simp [peek])
  have h₄ : lookup P base (i+4) = some (push k false) := by
    simpa [peek] using h 4 (by simp [peek])
  have h₅ : lookup P base (i+5) = some (push k false) := by
    simpa [peek] using h 5 (by simp [peek])
  have h₆ : lookup P base (i+6) = some (pop k jf jf) := by
    simpa [peek] using h 6 (by simp [peek])
  have hu : Function.update s k (false :: l) = s := Function.update_eq_self_iff.mpr hs.symm
  simp [runSteps,step,h₀,h₄,h₅,h₆,next,push,pop,hs,hu,Nat.add_assoc]

def peekTarget (jt jf je : Nat) : Option Bool → Nat
  | none => je
  | some false => jf
  | some true => jt

theorem peek_progress (P : Program n) (base i jt jf je : Nat) (k : Fin n)
    (s : Stacks n) (h : Placed P base i (peek k i jt jf je)) :
    Reaches₁ P base (i,s) (peekTarget jt jf je (s k).head?,s) := by
  cases hs : s k with
  | nil =>
    exact runSteps_reaches₁ P base 1 _ _ (by decide)
      (by simpa [hs,peekTarget] using peek_empty P base i jt jf je k s hs h)
  | cons b l =>
    cases b with
    | false =>
      exact runSteps_reaches₁ P base 4 _ _ (by decide)
        (by simpa [hs,peekTarget] using peek_false P base i jt jf je k s l hs h)
    | true =>
      exact runSteps_reaches₁ P base 4 _ _ (by decide)
        (by simpa [hs,peekTarget] using peek_true P base i jt jf je k s l hs h)

end DistributedSynthesis.CounterMachine.BSM
