/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.DecisionTasks.IISBoundedProtocol

/-! # Participation and the complete-input IIS graph model

`none` is an inactive input/output value, distinct from an undecided output.
A task lists legal partial input assignments and permitted joint outputs.
All input faces are retained by the complete-table translation.

The two simulations below are explicit state-machine constructions. Filtering
removes inactive senders; completion places inactive processes after all active
processes. The latter preserves every active local state for every protocol.
-/

namespace DistributedSynthesis.DecisionTasks.IISParticipation

variable {P : Type} {I O : P → Type} {St : Type}

abbrev Assignment (P : Type) (I : P → Type) := ∀ p, Option (I p)

def active (x : Assignment P I) (p : P) : Bool := (x p).isSome

/-- Restrict a round to the active processes; an inactive process only hears itself. -/
def restrict (a : P → Bool) (G : Source.Event P) : Source.Event P where
  inN p := if a p then {q | a q = true ∧ q ∈ G.inN p} else {p}
  self_mem p := by cases h : a p <;> simp [h, G.self_mem]

/-- Complete a partial round by a final block of all inactive processes. -/
def complete (a : P → Bool) (G : Source.Event P) : Source.Event P where
  inN p := if a p then {q | a q = true ∧ q ∈ G.inN p} else Set.univ
  self_mem p := by cases h : a p <;> simp [h, G.self_mem]

theorem complete_mem_DIIS [Finite P] (a : P → Bool) {G : Source.Event P}
    (hG : G ∈ Source.DIIS P) : complete a G ∈ Source.DIIS P := by
  obtain ⟨hi, hn⟩ := Source.mem_DIIS_iff.mp hG
  apply Source.mem_DIIS_iff.mpr
  constructor
  · intro p q hq z hz
    by_cases hp : a p = true
    · have hq' : a q = true ∧ q ∈ G.inN p := by simpa [complete, hp] using hq
      have hz' : a z = true ∧ z ∈ G.inN q := by simpa [complete, hq'.1] using hz
      simpa [complete, hp] using And.intro hz'.1 (hi p q hq'.2 hz'.2)
    · simp [complete, hp]
  · intro p q
    by_cases hp : a p = true
    · by_cases hq : a q = true
      · rcases hn p q with h | h
        · exact Or.inl (by simpa [complete, hp, hq] using
            (show {z | a z = true ∧ z ∈ G.inN p} ⊆ {z | a z = true ∧ z ∈ G.inN q}
              from fun _ hz => ⟨hz.1, h hz.2⟩))
        · exact Or.inr (by simpa [complete, hp, hq] using
            (show {z | a z = true ∧ z ∈ G.inN q} ⊆ {z | a z = true ∧ z ∈ G.inN p}
              from fun _ hz => ⟨hz.1, h hz.2⟩))
      · exact Or.inl (by simp [complete, hq])
    · exact Or.inr (by simp [complete, hp])

/-- Completing every round yields a full IIS execution. -/
theorem complete_admissible [Finite P] (a : P → Bool)
    {σ : ℕ → Source.Event P} (hσ : σ ∈ Source.advIIS P) :
    (fun r => complete a (σ r)) ∈ Source.advIIS P :=
  fun r => complete_mem_DIIS a (hσ r)

/-- No active process can distinguish a restricted execution from its completion. -/
theorem run_complete_eq (A : Protocol P (fun p => Option (I p)) St)
    (a : P → Bool) (σ : ℕ → Source.Event P) (x : Assignment P I)
    (r : ℕ) (p : P) (hp : a p = true) :
    A.run (fun n => complete a (σ n)) x r p =
      A.run (fun n => restrict a (σ n)) x r p := by
  induction r generalizing p with
  | zero => rfl
  | succ r ih =>
    simp only [Protocol.run, ih p hp]
    congr 1
    have hN : (complete a (σ r)).inN p = (restrict a (σ r)).inN p := by
      simp [complete, restrict, hp]
    rw [← hN]
    apply Set.image_congr
    intro q hq
    have hqa : a q = true := (by simpa [complete, hp] using hq :
      a q = true ∧ q ∈ (σ r).inN p).1
    rw [ih q hqa]

private theorem filtered_messages (a : P → Bool) (f : P → St) (N : Set P) :
    {z : P × St | (z.1, (true, z.2)) ∈ (fun q => (q, (a q, f q))) '' N} =
      (fun q => (q, f q)) '' {q | a q = true ∧ q ∈ N} := by
  ext ⟨q, s⟩
  simp only [Set.mem_setOf_eq, Set.mem_image, Prod.mk.injEq]
  constructor
  · rintro ⟨q', hq', rfl, ha, hs⟩
    exact ⟨q', ⟨ha, hq'⟩, rfl, hs⟩
  · rintro ⟨q', ⟨ha, hq'⟩, rfl, hs⟩
    exact ⟨q', hq', rfl, ha, hs⟩

/-- A process retains its participation flag and simulates the restricted round. -/
def filterInactive (A : Protocol P (fun p => Option (I p)) St) :
    Protocol P (fun p => Option (I p)) (Bool × St) where
  init p x := (x.isSome, A.init p x)
  trans p s messages := (s.1, A.trans p s.2
    (if s.1 then {z | (z.1, (true, z.2)) ∈ messages} else {(p, s.2)}))

theorem filterInactive_run (A : Protocol P (fun p => Option (I p)) St)
    (σ : ℕ → Source.Event P) (x : Assignment P I) (r : ℕ) (p : P) :
    (filterInactive A).run σ x r p =
      (active x p, A.run (fun n => restrict (active x) (σ n)) x r p) := by
  induction r generalizing p with
  | zero => rfl
  | succ r ih =>
    simp only [Protocol.run, ih]
    change (active x p, A.trans p _
      (if active x p then {z | (z.1, (true, z.2)) ∈
          (fun q => (q, (active x q,
            A.run (fun n => restrict (active x) (σ n)) x r q))) '' (σ r).inN p}
        else {(p, A.run (fun n => restrict (active x) (σ n)) x r p)})) = _
    rw [filtered_messages]
    cases hp : active x p <;> simp [restrict, hp]

/-- Finite tables of legal partial inputs and permitted outputs on those inputs.
For a chromatic task these are its input simplices and carrier relation. -/
structure Task (P : Type) (I O : P → Type) where
  legal : Assignment P I → Prop
  allows : Assignment P I → Assignment P O → Prop

def sameSupport (x : Assignment P I) (o : Assignment P O) : Prop :=
  ∀ p, (o p).isSome = (x p).isSome

/-- Illegal inputs impose no validity condition. Termination is still required. -/
def Task.padded (T : Task P I O) : DecisionTasks.Task P
    (fun p => Option (I p)) (fun p => Option (O p)) where
  allows x o := T.legal x → sameSupport x o ∧ T.allows x o

instance [Fintype P] (T : Task P I O) [∀ x, Decidable (T.legal x)]
    [∀ x o, Decidable (T.allows x o)] (x : Assignment P I) (o : Assignment P O) :
    Decidable (T.padded.allows x o) := by
  change Decidable (T.legal x → (∀ p, (o p).isSome = (x p).isSome) ∧ T.allows x o)
  infer_instance

/-- The complete output table is computed entry by entry from the two source tables. -/
def Task.paddedTable [Fintype P] (T : Task P I O) [∀ x, Decidable (T.legal x)]
    [∀ x o, Decidable (T.allows x o)] (x : Assignment P I) (o : Assignment P O) : Bool :=
  decide (T.padded.allows x o)

theorem Task.paddedTable_correct [Fintype P] (T : Task P I O)
    [∀ x, Decidable (T.legal x)] [∀ x o, Decidable (T.allows x o)]
    (x : Assignment P I) (o : Assignment P O) :
    T.paddedTable x o = true ↔ T.padded.allows x o := by simp [paddedTable]

/-- The total output assignment of a finite-round partial-participation protocol. -/
def outputs (A : Protocol P (fun p => Option (I p)) St)
    (out : ∀ p, St → Option (O p)) (k : ℕ)
    (σ : ℕ → Source.Event P) (x : Assignment P I) : Assignment P O :=
  fun p => if active x p then
    out p (A.run (fun n => restrict (active x) (σ n)) x k p) else none

/-- One finite-depth local rule, valid simultaneously on every legal input face. -/
def Task.BoundedSolvable (T : Task P I O) : Prop :=
  ∃ (k : ℕ) (St : Type) (A : Protocol P (fun p => Option (I p)) St)
    (out : ∀ p, St → Option (O p)),
    ∀ σ ∈ Source.advIIS P, ∀ x, T.legal x →
      sameSupport x (outputs A out k σ x) ∧ T.allows x (outputs A out k σ x)

/-- Exact transfer, with the same decision depth in each direction. -/
theorem Task.bounded_transfer [Finite P] (T : Task P I O) :
    T.BoundedSolvable ↔ T.padded.BoundedSolvable (Source.advIIS P) := by
  constructor
  · rintro ⟨k, St, A, out, h⟩
    refine ⟨k, Bool × St, filterInactive A,
      fun p s => if s.1 then out p s.2 else none, ?_⟩
    intro σ hσ x hx
    simpa only [filterInactive_run] using h σ hσ x hx
  · rintro ⟨k, St, A, out, h⟩
    refine ⟨k, St, A, out, ?_⟩
    intro σ hσ x hx
    have hc := h (fun n => complete (active x) (σ n))
      (complete_admissible (active x) hσ) x hx
    have heq : outputs A out k σ x =
        fun p => out p (A.run (fun n => complete (active x) (σ n)) x k p) := by
      funext p
      by_cases hp : active x p = true
      · simp [outputs, hp, run_complete_eq A (active x) σ x k p hp]
      · have hs := hc.1 p
        have hxp : (x p).isSome = false := by simpa [active] using hp
        have ho : out p (A.run (fun n => complete (active x) (σ n)) x k p) = none := by
          simpa only [Option.isSome_eq_false_iff, Option.isNone_iff_eq_none] using hs.trans hxp
        simp [outputs, hp, ho]
    rw [heq]
    exact hc

/-- Arbitrary-state graph solvability is equivalent to a bounded protocol on
all participating subsets. The finite bound is a conclusion of compactness. -/
theorem Task.solvable_iff_bounded {I O : Fin 3 → Type} [∀ p, Finite (I p)]
    (T : Task (Fin 3) I O) :
    T.padded.Solvable (Source.advIIS (Fin 3)) ↔ T.BoundedSolvable :=
  (IISGraphs.solvable_iff_bounded T.padded).trans T.bounded_transfer.symm

end DistributedSynthesis.DecisionTasks.IISParticipation
