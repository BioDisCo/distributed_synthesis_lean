/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.DecisionTasks.Source.Model

/-! # Decision tasks with a separate alphabet for each process

Packing each alphabet into the product of all alphabets reduces this model to
the common-alphabet backend. Only the diagonal coordinates affect the task.
The converse simulation fixes the other coordinates locally, so packing does
not give the original processes access to one another's inputs.
-/

namespace DistributedSynthesis.DecisionTasks

universe u v w z

variable {P : Type u} {I : P → Type v} {O : P → Type w}

def Task.packed (T : Task P I O) : Source.Task P (∀ p, I p) (∀ p, O p) where
  allows x o := T.allows (fun p => x p p) (fun p => o p p)

def Protocol.packed {St : Type z} (A : Protocol P I St) :
    Source.Algorithm P (∀ p, I p) St where
  init p x := A.init p (x p)
  trans := A.trans

theorem Protocol.packed_run {St : Type z} (A : Protocol P I St)
    (σ : ℕ → Source.Event P) (x : P → ∀ p, I p) (r : ℕ) (p : P) :
    A.packed.run σ x r p = A.run σ (fun q => x q q) r p := by
  induction r generalizing p with
  | zero => rfl
  | succ r ih => simp only [Source.Algorithm.run, Protocol.run, ih]; rfl

def Protocol.unpacked [DecidableEq P] {St : Type z}
    (A : Source.Algorithm P (∀ p, I p) St) (d : ∀ p, I p) : Protocol P I St where
  init p x := A.init p (Function.update d p x)
  trans := A.trans

theorem Protocol.unpacked_run [DecidableEq P] {St : Type z}
    (A : Source.Algorithm P (∀ p, I p) St) (d : ∀ p, I p)
    (σ : ℕ → Source.Event P) (x : ∀ p, I p) (r : ℕ) (p : P) :
    (Protocol.unpacked A d).run σ x r p =
      A.run σ (fun q => Function.update d q (x q)) r p := by
  induction r generalizing p with
  | zero => rfl
  | succ r ih => simp only [Source.Algorithm.run, Protocol.run, ih]; rfl

/-- The alphabet reduction preserves arbitrary-state task solvability. -/
theorem Task.packed_solvable_iff [DecidableEq P]
    [∀ p, Nonempty (I p)] [∀ p, Nonempty (O p)]
    (T : Task P I O) (adv : Set (ℕ → Source.Event P)) :
    (∃ (St : Type (max u v)) (A : Source.Algorithm P (∀ p, I p) St)
      (out : P → St → Option (∀ p, O p)), A.SolvesTask out T.packed adv) ↔
      T.Solvable adv := by
  classical
  let di : ∀ p, I p := fun p => Classical.choice (inferInstance : Nonempty (I p))
  let dout : ∀ p, O p := fun p => Classical.choice (inferInstance : Nonempty (O p))
  constructor
  · rintro ⟨St, A, out, h⟩
    refine ⟨St, Protocol.unpacked A di, fun p s => (out p s).map (fun y => y p), ?_⟩
    constructor
    · intro σ hσ x p
      obtain ⟨r, y, hy⟩ := h.term σ hσ (fun q => Function.update di q (x q)) p
      exact ⟨r, y p, by rw [Protocol.unpacked_run, hy]; rfl⟩
    · intro σ hσ x p r r' hrr o ho
      rw [Protocol.unpacked_run, Option.map_eq_some_iff] at ho
      obtain ⟨y, hy, hyo⟩ := ho
      rw [Protocol.unpacked_run,
        h.irrev σ hσ _ p r r' hrr y hy, Option.map_some, hyo]
    · intro σ hσ x o ho
      have hh : ∀ p, ∃ r y, out p (A.run σ (fun q => Function.update di q (x q)) r p) =
          some y ∧ y p = o p := by
        intro p
        obtain ⟨r, hr⟩ := ho p
        rw [Protocol.unpacked_run, Option.map_eq_some_iff] at hr
        obtain ⟨y, hy, hyo⟩ := hr
        exact ⟨r, y, hy, hyo⟩
      choose r y hy hyo using hh
      have ht := h.allows σ hσ (fun q => Function.update di q (x q)) y
        (fun p => ⟨r p, hy p⟩)
      simpa only [Task.packed, Function.update_self, hyo] using ht
  · rintro ⟨St, A, out, h⟩
    let packedOut : P → St → Option (∀ p, O p) :=
      fun p s => (out p s).map (Function.update dout p)
    refine ⟨St, A.packed, packedOut, ?_⟩
    constructor
    · intro σ hσ x p
      obtain ⟨r, o, ho⟩ := h.term σ hσ (fun q => x q q) p
      refine ⟨r, Function.update dout p o, ?_⟩
      simp only [packedOut, Protocol.packed_run, ho, Option.map_some]
    · intro σ hσ x p r r' hrr o ho
      change (out p (A.packed.run σ x r p)).map (Function.update dout p) = some o at ho
      rw [Protocol.packed_run, Option.map_eq_some_iff] at ho
      obtain ⟨y, hy, hyo⟩ := ho
      change (out p (A.packed.run σ x r' p)).map (Function.update dout p) = some o
      rw [Protocol.packed_run, h.irrev σ hσ _ p r r' hrr y hy, Option.map_some, hyo]
    · intro σ hσ x o ho
      apply h.allows σ hσ (fun q => x q q) (fun q => o q q)
      intro p
      obtain ⟨r, hr⟩ := ho p
      change (out p (A.packed.run σ x r p)).map (Function.update dout p) = some (o p) at hr
      rw [Protocol.packed_run, Option.map_eq_some_iff] at hr
      obtain ⟨y, hy, hyo⟩ := hr
      have heq : y = o p p := by simpa using congrFun hyo p
      exact ⟨r, heq ▸ hy⟩

end DistributedSynthesis.DecisionTasks
