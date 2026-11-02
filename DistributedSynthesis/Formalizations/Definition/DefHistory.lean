/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Basic

/-!
# Histories

This file formalizes Definition `def:history` from `paper.tex`.

A round record is a five-component tuple containing both process inputs, the
communication graph, and both process outputs. A finite history is a finite
sequence of such round records, represented as a Lean list.
-/

namespace DistributedSynthesis

universe u v w x y

/--
A round record is a tuple `(x₁, x₂, g, y₁, y₂) ∈ In₁ × In₂ × G × Out₁ × Out₂`.
-/
structure RoundRecord (In₁ : Type u) (In₂ : Type v) (G : Type w)
    (Out₁ : Type x) (Out₂ : Type y) where
  /-- The input of process 1 in this round. -/
  inputOne : In₁
  /-- The input of process 2 in this round. -/
  inputTwo : In₂
  /-- The communication graph in this round. -/
  graph : G
  /-- The output of process 1 in this round. -/
  outputOne : Out₁
  /-- The output of process 2 in this round. -/
  outputTwo : Out₂
  deriving Repr

namespace RoundRecord

variable {In₁ : Type u} {In₂ : Type v} {G : Type w} {Out₁ : Type x} {Out₂ : Type y}

/-- The input component belonging to a process. -/
def input (p : Proc) (r : RoundRecord In₁ In₂ G Out₁ Out₂) : PSum In₁ In₂ :=
  match p with
  | Proc.one => .inl r.inputOne
  | Proc.two => .inr r.inputTwo

@[simp]
theorem input_one (r : RoundRecord In₁ In₂ G Out₁ Out₂) :
    r.input Proc.one = PSum.inl r.inputOne := rfl

@[simp]
theorem input_two (r : RoundRecord In₁ In₂ G Out₁ Out₂) :
    r.input Proc.two = PSum.inr r.inputTwo := rfl

end RoundRecord

/-- A finite history is a finite sequence of round records. -/
abbrev History (In₁ : Type u) (In₂ : Type v) (G : Type w) (Out₁ : Type x) (Out₂ : Type y) :=
  List (RoundRecord In₁ In₂ G Out₁ Out₂)

namespace History

variable {In₁ : Type u} {In₂ : Type v} {G : Type w} {Out₁ : Type x} {Out₂ : Type y}

/-- The length `|h|` of a history. -/
def length (h : History In₁ In₂ G Out₁ Out₂) : Nat :=
  List.length h

/-- The empty history `ε`, of length zero. -/
def empty : History In₁ In₂ G Out₁ Out₂ :=
  []

/-- Append one round record to the end of a history, written `h · r` in the paper. -/
def append (h : History In₁ In₂ G Out₁ Out₂) (r : RoundRecord In₁ In₂ G Out₁ Out₂) :
    History In₁ In₂ G Out₁ Out₂ :=
  h ++ [r]

/-- The graph sequence `(g⁰, …, gᵗ⁻¹)` of a history. -/
def graphSequence (h : History In₁ In₂ G Out₁ Out₂) : List G :=
  h.map RoundRecord.graph

/-- The input sequence `(xₚ⁰, …, xₚᵗ⁻¹)` of process `p`. -/
def inputSequence (p : Proc) (h : History In₁ In₂ G Out₁ Out₂) :
    PSum (List In₁) (List In₂) :=
  match p with
  | Proc.one => .inl (h.map RoundRecord.inputOne)
  | Proc.two => .inr (h.map RoundRecord.inputTwo)

/-- The output sequence `(yₚ⁰, …, yₚᵗ⁻¹)` of process `p`. -/
def outputSequence (p : Proc) (h : History In₁ In₂ G Out₁ Out₂) :
    PSum (List Out₁) (List Out₂) :=
  match p with
  | Proc.one => .inl (h.map RoundRecord.outputOne)
  | Proc.two => .inr (h.map RoundRecord.outputTwo)

@[simp]
theorem length_empty : length (empty : History In₁ In₂ G Out₁ Out₂) = 0 :=
  rfl

@[simp]
theorem length_append (h : History In₁ In₂ G Out₁ Out₂)
    (r : RoundRecord In₁ In₂ G Out₁ Out₂) :
    length (append h r) = length h + 1 := by
  simp [length, append, List.length_append]

@[simp]
theorem graphSequence_empty :
    graphSequence (empty : History In₁ In₂ G Out₁ Out₂) = [] :=
  rfl

@[simp]
theorem graphSequence_append (h : History In₁ In₂ G Out₁ Out₂)
    (r : RoundRecord In₁ In₂ G Out₁ Out₂) :
    graphSequence (append h r) = graphSequence h ++ [r.graph] := by
  simp [graphSequence, append]

@[simp]
theorem inputSequence_one_empty :
    inputSequence Proc.one (empty : History In₁ In₂ G Out₁ Out₂) = PSum.inl [] :=
  rfl

@[simp]
theorem inputSequence_two_empty :
    inputSequence Proc.two (empty : History In₁ In₂ G Out₁ Out₂) = PSum.inr [] :=
  rfl

@[simp]
theorem inputSequence_one_append (h : History In₁ In₂ G Out₁ Out₂)
    (r : RoundRecord In₁ In₂ G Out₁ Out₂) :
    inputSequence Proc.one (append h r) =
      PSum.inl ((h.map RoundRecord.inputOne) ++ [r.inputOne]) := by
  simp [inputSequence, append]

@[simp]
theorem inputSequence_two_append (h : History In₁ In₂ G Out₁ Out₂)
    (r : RoundRecord In₁ In₂ G Out₁ Out₂) :
    inputSequence Proc.two (append h r) =
      PSum.inr ((h.map RoundRecord.inputTwo) ++ [r.inputTwo]) := by
  simp [inputSequence, append]

@[simp]
theorem outputSequence_one_empty :
    outputSequence Proc.one (empty : History In₁ In₂ G Out₁ Out₂) = PSum.inl [] :=
  rfl

@[simp]
theorem outputSequence_two_empty :
    outputSequence Proc.two (empty : History In₁ In₂ G Out₁ Out₂) = PSum.inr [] :=
  rfl

@[simp]
theorem outputSequence_one_append (h : History In₁ In₂ G Out₁ Out₂)
    (r : RoundRecord In₁ In₂ G Out₁ Out₂) :
    outputSequence Proc.one (append h r) =
      PSum.inl ((h.map RoundRecord.outputOne) ++ [r.outputOne]) := by
  simp [outputSequence, append]

@[simp]
theorem outputSequence_two_append (h : History In₁ In₂ G Out₁ Out₂)
    (r : RoundRecord In₁ In₂ G Out₁ Out₂) :
    outputSequence Proc.two (append h r) =
      PSum.inr ((h.map RoundRecord.outputTwo) ++ [r.outputTwo]) := by
  simp [outputSequence, append]

end History

end DistributedSynthesis
