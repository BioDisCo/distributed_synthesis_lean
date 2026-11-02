/- Extracted from consensusLTL/lean/ConsensusLTL/IIS.lean.
Only decision-task dependencies are retained; see ../SOURCE.md. -/

import DistributedSynthesis.Library.Distributed.DecisionTasks.Source.Model

-- Preserve the source section contexts on Lean 4.30.
set_option linter.unusedSectionVars false

namespace DistributedSynthesis.DecisionTasks.Source

universe u

variable {Proc : Type u}

/-- The event of an ordered partition, presented by a rank function: `p` hears exactly the
processes whose rank is at most its own. -/
def isEvent (rk : Proc → ℕ) : Event Proc where
  inN p := {q | rk q ≤ rk p}
  self_mem p := show rk p ≤ rk p from le_rfl

@[simp] theorem isEvent_inN (rk : Proc → ℕ) (p : Proc) :
    (isEvent rk).inN p = {q | rk q ≤ rk p} := rfl

/-- The immediate snapshot events. -/
def DIIS (Proc : Type u) : Set (Event Proc) := Set.range isEvent

/-- Two events with the same in-neighbourhoods are equal. -/
theorem event_ext {G H : Event Proc} (h : G.inN = H.inN) : G = H := by
  cases G; cases H; cases h; rfl

/-- **Immediacy.**  Everything heard by a process one hears is itself heard. -/
def Immediate (G : Event Proc) : Prop := ∀ p q, q ∈ G.inN p → G.inN q ⊆ G.inN p

/-- **Nesting.**  Any two in-neighbourhoods are comparable. -/
def Nested (G : Event Proc) : Prop := ∀ p q, G.inN p ⊆ G.inN q ∨ G.inN q ⊆ G.inN p

theorem immediate_isEvent (rk : Proc → ℕ) : Immediate (isEvent rk) := by
  intro p q hq z hz
  have h₁ : rk q ≤ rk p := hq
  have h₂ : rk z ≤ rk q := hz
  exact le_trans h₂ h₁

theorem nested_isEvent (rk : Proc → ℕ) : Nested (isEvent rk) := by
  intro p q
  rcases le_total (rk p) (rk q) with h | h
  · exact Or.inl fun z hz => le_trans (show rk z ≤ rk p from hz) h
  · exact Or.inr fun z hz => le_trans (show rk z ≤ rk q from hz) h

/-- **The immediate snapshot events are exactly the immediate nested ones.**  This is the
combinatorial definition of an immediate-snapshot round, so it identifies `Obl DIIS` with the
iterated immediate snapshot model. -/
theorem mem_DIIS_iff [Finite Proc] {G : Event Proc} :
    G ∈ DIIS Proc ↔ Immediate G ∧ Nested G := by
  classical
  constructor
  · rintro ⟨rk, rfl⟩
    exact ⟨immediate_isEvent rk, nested_isEvent rk⟩
  · rintro ⟨himm, hnest⟩
    refine ⟨fun p => (G.inN p).ncard, ?_⟩
    have hfin : ∀ p : Proc, (G.inN p).Finite := fun p => Set.toFinite _
    refine event_ext (funext fun p => ?_)
    ext q
    simp only [isEvent_inN, Set.mem_setOf_eq]
    constructor
    · intro hcard
      rcases hnest p q with h | h
      · have heq : G.inN p = G.inN q := Set.eq_of_subset_of_ncard_le h hcard (hfin q)
        rw [heq]
        exact G.self_mem q
      · exact h (G.self_mem q)
    · intro hq
      exact Set.ncard_le_ncard (himm p q hq) (hfin p)

/-- The iterated immediate snapshot adversary: every round is an immediate snapshot.  It is
oblivious, hence closed, and it is the LTL formula asserting that the event of every round lies
in the finite set `DIIS`. -/
def advIIS (Proc : Type u) : Set (ℕ → Event Proc) := Obl (DIIS Proc)

theorem mem_advIIS_iff {σ : ℕ → Event Proc} : σ ∈ advIIS Proc ↔ ∀ r, σ r ∈ DIIS Proc := Iff.rfl

variable {V O : Type}

end DistributedSynthesis.DecisionTasks.Source
