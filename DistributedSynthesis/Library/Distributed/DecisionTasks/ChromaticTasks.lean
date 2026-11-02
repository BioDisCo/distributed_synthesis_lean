/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.DecisionTasks.IISParticipation

/-! # Chromatic task carriers and the inactive-input table

A chromatic simplex is a partial assignment: at most one value for each
process. Taking a face deletes some entries. This representation preserves
all input faces and all partially decided output faces in the table reduction.
-/

namespace DistributedSynthesis.DecisionTasks.ChromaticTasks

open IISParticipation

variable {P : Type} {I O : P → Type}

def Face {V : P → Type} (s t : Assignment P V) : Prop :=
  ∀ p v, s p = some v → t p = some v

theorem Face.refl {V : P → Type} (s : Assignment P V) : Face s s := fun _ _ h => h

theorem Face.trans {V : P → Type} {s t u : Assignment P V}
    (h : Face s t) (h' : Face t u) : Face s u := fun p v hv => h' p v (h p v hv)

def empty {V : P → Type} : Assignment P V := fun _ => none

theorem empty_face {V : P → Type} (s : Assignment P V) : Face empty s := by
  intro p v h
  cases h

/-- An abstract chromatic complex represented by partial assignments. -/
structure Complex (P : Type) (V : P → Type) where
  faces : Set (Assignment P V)
  empty_mem : empty ∈ faces
  face_closed : ∀ {s t}, Face s t → t ∈ faces → s ∈ faces

/-- The usual input complex, output complex, and monotone carrier map. -/
structure Task (P : Type) (I O : P → Type) where
  input : Complex P I
  output : Complex P O
  carrier : Assignment P I → Complex P O
  carrier_output : ∀ x, x ∈ input.faces → (carrier x).faces ⊆ output.faces
  carrier_support : ∀ x, x ∈ input.faces → ∀ o, o ∈ (carrier x).faces →
    ∀ p, (o p).isSome = true → (x p).isSome = true
  carrier_mono : ∀ {s t}, Face s t → t ∈ input.faces →
    (carrier s).faces ⊆ (carrier t).faces

/-- All input faces are rows of the participation table. -/
def Task.toParticipation (T : Task P I O) : IISParticipation.Task P I O where
  legal x := x ∈ T.input.faces
  allows x o := o ∈ (T.carrier x).faces

/-- Every finite chromatic task has exactly the padded table described in the manuscript. -/
def Task.padded (T : Task P I O) : DecisionTasks.Task P
    (fun p => Option (I p)) (fun p => Option (O p)) := T.toParticipation.padded

theorem Task.padded_legal (T : Task P I O) (x : Assignment P I) (o : Assignment P O)
    (hx : x ∈ T.input.faces) :
    T.padded.allows x o ↔ sameSupport x o ∧ o ∈ (T.carrier x).faces := by
  exact ⟨fun h => h hx, fun h _ => h⟩

theorem Task.padded_illegal (T : Task P I O) (x : Assignment P I)
    (hx : x ∉ T.input.faces) (o : Assignment P O) : T.padded.allows x o :=
  fun h => False.elim (hx h)

/-- The all-inactive input admits exactly the all-inactive output. -/
theorem Task.padded_empty (T : Task P I O) (o : Assignment P O) :
    T.padded.allows empty o ↔ o = empty := by
  rw [T.padded_legal empty o T.input.empty_mem]
  constructor
  · intro h
    funext p
    have hp := h.1 p
    cases ho : o p <;> simp_all [empty]
  · rintro rfl
    exact ⟨fun _ => rfl, (T.carrier empty).empty_mem⟩

/-- Any subset of the decisions remains valid in the original task carrier. -/
theorem Task.partial_outputs_valid (T : Task P I O)
    {x : Assignment P I} {o o' : Assignment P O} (hx : x ∈ T.input.faces)
    (ho : T.padded.allows x o) (hface : Face o' o) :
    o' ∈ (T.carrier x).faces ∧ o' ∈ T.output.faces := by
  have h := (T.carrier x).face_closed hface ((T.padded_legal x o hx).mp ho).2
  exact ⟨h, T.carrier_output x hx h⟩

/-- Enlarging the legal input face preserves a carried partial output. -/
theorem Task.input_face_valid (T : Task P I O)
    {s t : Assignment P I} {o : Assignment P O}
    (hst : Face s t) (ht : t ∈ T.input.faces) (ho : T.padded.allows s o) :
    o ∈ (T.carrier t).faces :=
  T.carrier_mono hst ht (ho (T.input.face_closed hst ht)).2

/-- Graph solvability preserves the complete collection of participating input faces. -/
theorem Task.solvable_iff_bounded {I O : Fin 3 → Type} [∀ p, Finite (I p)]
    (T : Task (Fin 3) I O) :
    T.padded.Solvable (Source.advIIS (Fin 3)) ↔ T.toParticipation.BoundedSolvable :=
  T.toParticipation.solvable_iff_bounded

end DistributedSynthesis.DecisionTasks.ChromaticTasks
