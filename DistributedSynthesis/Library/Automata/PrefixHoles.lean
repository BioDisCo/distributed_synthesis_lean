/- Project authors: see AUTHORS.md at the repository root. -/

import Mathlib.Tactic

/-! Finite-state prefix languages: holes at every node have a uniform depth.
This file proves a combinatorial part of the proposed characterization. It
does not assume or assert a distributed synthesis theorem. -/

namespace Characterisation

variable {α Q : Type*}

/-- A finite-state recognizer; the finite-state hypothesis is supplied to the
theorems as `Fintype Q`. Kept local to avoid building additional dependencies. -/
structure Recognizer (α Q : Type*) where
  step : Q → α → Q
  start : Q
  accept : Set Q

namespace Recognizer

def evalFrom (M : Recognizer α Q) (q : Q) (w : List α) : Q :=
  w.foldl M.step q

def eval (M : Recognizer α Q) (w : List α) : Q := M.evalFrom M.start w

theorem evalFrom_of_append (M : Recognizer α Q) (q : Q) (u v : List α) :
    M.evalFrom q (u ++ v) = M.evalFrom (M.evalFrom q u) v :=
  List.foldl_append

end Recognizer

def PrefixClosed (P : List α → Prop) : Prop :=
  ∀ h u, P (h ++ u) → P h

def HasPrefixHoles (P : List α → Prop) : Prop :=
  ∀ h, P h → ∃ u, ¬ P (h ++ u)

def HasUniformPrefixHoles (P : List α → Prop) : Prop :=
  ∃ k, ∀ h, P h → ∃ u, u.length ≤ k ∧ ¬ P (h ++ u)

def FullCone (P : List α → Prop) (h : List α) : Prop :=
  ∀ u, P (h ++ u)

theorem prefixHoles_iff_no_fullCone (P : List α → Prop) :
    HasPrefixHoles P ↔ ¬ ∃ h, FullCone P h := by
  classical
  constructor
  · rintro holes ⟨h, cone⟩
    obtain ⟨u, hu⟩ := holes h (by simpa using cone [])
    exact hu (cone u)
  · intro noCone h _
    by_contra hn
    apply noCone
    exact ⟨h, by simpa only [not_exists, not_not] using hn⟩

theorem uniformPrefixHoles_of_finite_dfa [Fintype Q]
    (M : Recognizer α Q) (P : List α → Prop)
    (recognizes : ∀ w, P w ↔ M.eval w ∈ M.accept)
    (holes : HasPrefixHoles P) : HasUniformPrefixHoles P := by
  classical
  let bad : Q → Prop := fun q => ∃ u, M.evalFrom q u ∉ M.accept
  let witness : Q → List α := fun q =>
    if h : bad q then Classical.choose h else []
  let k := Finset.univ.sup (fun q => (witness q).length)
  refine ⟨k, fun h hh => ?_⟩
  obtain ⟨u, hu⟩ := holes h hh
  have hb : bad (M.eval h) := by
    refine ⟨u, ?_⟩
    intro ha
    apply hu
    apply (recognizes _).mpr
    simpa only [Recognizer.eval, Recognizer.evalFrom_of_append] using ha
  refine ⟨witness (M.eval h), Finset.le_sup (f := fun q => (witness q).length)
    (Finset.mem_univ _), ?_⟩
  intro hp
  have hw : M.evalFrom (M.eval h) (witness (M.eval h)) ∉ M.accept := by
    dsimp [witness]
    rw [dif_pos hb]
    exact Classical.choose_spec hb
  apply hw
  simpa only [Recognizer.eval, Recognizer.evalFrom_of_append] using (recognizes _).mp hp

theorem finite_dfa_holes_iff_uniform [Fintype Q]
    (M : Recognizer α Q) (P : List α → Prop)
    (recognizes : ∀ w, P w ↔ M.eval w ∈ M.accept) :
    HasPrefixHoles P ↔ HasUniformPrefixHoles P := by
  constructor
  · exact uniformPrefixHoles_of_finite_dfa M P recognizes
  · rintro ⟨k, hk⟩ h hh
    obtain ⟨u, _, hu⟩ := hk h hh
    exact ⟨u, hu⟩

/-- A rejected prefix stays rejected under extension. -/
theorem rejected_append (P : List α → Prop) (closed : PrefixClosed P)
    {h : List α} (hh : ¬ P h) (u : List α) : ¬ P (h ++ u) :=
  fun hp => hh (closed h u hp)

/-- Uniform holes may be placed at exactly the common depth by padding. -/
theorem uniform_holes_exact_depth [Nonempty α]
    (P : List α → Prop) (closed : PrefixClosed P)
    (holes : HasUniformPrefixHoles P) :
    ∃ k, ∀ h, ∃ u, u.length = k ∧ ¬ P (h ++ u) := by
  classical
  obtain ⟨k, hk⟩ := holes
  let a : α := Classical.choice inferInstance
  refine ⟨k, fun h => ?_⟩
  by_cases hh : P h
  · obtain ⟨u, hlen, hu⟩ := hk h hh
    refine ⟨u ++ List.replicate (k - u.length) a, ?_, ?_⟩
    · simp only [List.length_append, List.length_replicate]
      omega
    · simpa only [List.append_assoc] using
        rejected_append P closed hu (List.replicate (k - u.length) a)
  · exact ⟨List.replicate k a, by simp, rejected_append P closed hh _⟩

end Characterisation
