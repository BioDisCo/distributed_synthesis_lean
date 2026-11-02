/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.DecisionTasks.Model
import Mathlib.Logic.Equiv.Basic

/-! # Renaming processes in decision tasks

A process equivalence changes sender identities consistently in events,
protocols and task tables. It preserves finite executions and solvability.
-/

namespace DistributedSynthesis.DecisionTasks

namespace ProcessTransport

variable {P Q V O St : Type}

def event (e : P ≃ Q) (g : Event P) : Event Q where
  inN q := {p | e.symm p ∈ g.inN (e.symm q)}
  self_mem q := g.self_mem (e.symm q)

private theorem event_ext {g h : Event P} (he : g.inN = h.inN) : g = h := by
  cases g
  cases h
  cases he
  rfl

@[simp] theorem event_inverse (e : P ≃ Q) (g : Event P) :
    event e.symm (event e g) = g := by
  have hn : (event e.symm (event e g)).inN = g.inN := by
    funext p
    ext q
    simp [event]
  exact event_ext hn

@[simp] theorem event_inverse_symm (e : P ≃ Q) (g : Event Q) :
    event e (event e.symm g) = g := event_inverse e.symm g

def algorithm (e : P ≃ Q) (A : Protocol P (fun _ => V) St) : Protocol Q (fun _ => V) St where
  init q x := A.init (e.symm q) x
  trans q s messages := A.trans (e.symm q) s
    ((fun m : Q × St => (e.symm m.1, m.2)) '' messages)

theorem run (e : P ≃ Q) (A : Protocol P (fun _ => V) St)
    (σ : ℕ → Event P) (x : Q → V) (r : ℕ) (q : Q) :
    (algorithm e A).run (event e ∘ σ) x r q = A.run σ (x ∘ e) r (e.symm q) := by
  induction r generalizing q with
  | zero => simp [Protocol.run, algorithm]
  | succ r ih =>
      change A.trans (e.symm q) ((algorithm e A).run (event e ∘ σ) x r q)
        ((fun m : Q × St => (e.symm m.1, m.2)) ''
          ((fun p => (p, (algorithm e A).run (event e ∘ σ) x r p)) ''
            (event e (σ r)).inN q)) = _
      simp only [ih, Protocol.run]
      congr 1
      ext m
      constructor
      · rintro ⟨_, ⟨p, hp, rfl⟩, rfl⟩
        exact ⟨e.symm p, hp, rfl⟩
      · rintro ⟨p, hp, rfl⟩
        refine ⟨(e p, A.run σ (x ∘ e) r p), ?_, by simp⟩
        refine ⟨e p, ?_, ?_⟩
        · simpa [event] using hp
        · simp

def task (e : P ≃ Q) (T : Task P (fun _ => V) (fun _ => O)) : Task Q (fun _ => V) (fun _ => O) where
  allows x o := T.allows (x ∘ e) (o ∘ e)

def adversary (e : P ≃ Q) (adv : Set (ℕ → Event P)) :
    Set (ℕ → Event Q) := {τ | (event e.symm ∘ τ) ∈ adv}

theorem solvable_iff (e : P ≃ Q) (T : Task P (fun _ => V) (fun _ => O))
    (adv : Set (ℕ → Event P)) :
    (∃ (St : Type) (A : Protocol Q (fun _ => V) St) (out : Q → St → Option O),
      A.Solves out (task e T) (adversary e adv)) ↔
    ∃ (St : Type) (A : Protocol P (fun _ => V) St) (out : P → St → Option O),
      A.Solves out T adv := by
  constructor
  · rintro ⟨St, A, out, h⟩
    refine ⟨St, algorithm e.symm A, fun p s => out (e p) s, ?_⟩
    have hr (σ : ℕ → Event P) (x : P → V) (r : ℕ) (p : P) :
        (algorithm e.symm A).run σ x r p =
          A.run (event e ∘ σ) (x ∘ e.symm) r (e p) := by
      have hh := run e.symm A (event e ∘ σ) x r p
      simpa only [Function.comp_def, event_inverse, event_inverse_symm, Equiv.symm_symm] using hh
    constructor
    · intro σ hσ x p
      have hm : event e ∘ σ ∈ adversary e adv := by simpa [adversary, Function.comp_def]
      obtain ⟨r, o, ho⟩ := h.term _ hm (x ∘ e.symm) (e p)
      exact ⟨r, o, by rw [hr]; exact ho⟩
    · intro σ hσ x p r r' hrr o ho
      have hm : event e ∘ σ ∈ adversary e adv := by simpa [adversary, Function.comp_def]
      rw [hr] at ho ⊢
      exact h.irrev _ hm _ _ _ _ hrr _ ho
    · intro σ hσ x o ho
      have hm : event e ∘ σ ∈ adversary e adv := by simpa [adversary, Function.comp_def]
      have hh := h.allows _ hm (x ∘ e.symm) (o ∘ e.symm) (fun q => by
        obtain ⟨r, hh⟩ := ho (e.symm q)
        refine ⟨r, ?_⟩
        simpa only [hr, Equiv.apply_symm_apply, Function.comp_apply] using hh)
      change T.allows (fun p => x (e.symm (e p))) (fun p => o (e.symm (e p))) at hh
      have hx : (fun p => x (e.symm (e p))) = x := by
        funext p
        exact congrArg x (e.symm_apply_apply p)
      have ho : (fun p => o (e.symm (e p))) = o := by
        funext p
        exact congrArg o (e.symm_apply_apply p)
      rw [hx, ho] at hh
      exact hh
  · rintro ⟨St, A, out, h⟩
    refine ⟨St, algorithm e A, fun q s => out (e.symm q) s, ?_⟩
    have hr (τ : ℕ → Event Q) (x : Q → V) (r : ℕ) (q : Q) :
        (algorithm e A).run τ x r q =
          A.run (event e.symm ∘ τ) (x ∘ e) r (e.symm q) := by
      have hh := run e A (event e.symm ∘ τ) x r q
      simpa only [Function.comp_def, event_inverse, event_inverse_symm, Equiv.symm_symm] using hh
    constructor
    · intro τ hτ x q
      obtain ⟨r, o, ho⟩ := h.term _ hτ (x ∘ e) (e.symm q)
      exact ⟨r, o, by rw [hr]; exact ho⟩
    · intro τ hτ x q r r' hrr o ho
      rw [hr] at ho ⊢
      exact h.irrev _ hτ _ _ _ _ hrr _ ho
    · intro τ hτ x o ho
      apply h.allows _ hτ (x ∘ e) (o ∘ e)
      intro p
      obtain ⟨r, hh⟩ := ho (e p)
      refine ⟨r, ?_⟩
      simpa only [hr, Equiv.symm_apply_apply, Function.comp_apply] using hh

end ProcessTransport

end DistributedSynthesis.DecisionTasks
