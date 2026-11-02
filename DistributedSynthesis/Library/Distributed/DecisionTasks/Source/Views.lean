/- Decision-task excerpts from consensusLTL.
Source declarations and hashes are recorded in ../source-manifest.json. -/

import DistributedSynthesis.Library.Distributed.DecisionTasks.Source.Model

set_option linter.unusedSectionVars false

/- From View.lean. -/
namespace DistributedSynthesis.DecisionTasks.Source

universe u v w

variable {Proc : Type u} {V : Type v} {St : Type w}

/-- **View bisimulation.**  If the marked process-time pairs have matching inputs and matching
in-neighbourhoods at earlier rounds, and the mark passes to in-neighbours, the marked states
agree.  Taking `R p r := p ∈ S` recovers `run_congr`. -/
theorem run_eq_of_bisim (A : Algorithm Proc V St) {σ τ : ℕ → Event Proc} {I J : Proc → V}
    (R : Proc → ℕ → Prop)
    (hI : ∀ p r, R p r → I p = J p)
    (hN : ∀ p r, R p r → ∀ i, i < r → (σ i).inN p = (τ i).inN p)
    (hstep : ∀ p r, R p r → ∀ i, i < r → ∀ q ∈ (σ i).inN p, R q i) :
    ∀ r p, R p r → A.run σ I r p = A.run τ J r p := by
  intro r
  induction r using Nat.strong_induction_on with
  | _ r ih =>
      intro p hp
      match r with
      | 0 => simp only [Algorithm.run, Protocol.run, hI p 0 hp]
      | k + 1 =>
          have hk : k < k + 1 := Nat.lt_succ_self k
          have hnb : (σ k).inN p = (τ k).inN p := hN p (k + 1) hp k hk
          have hpk : R p k := hstep p (k + 1) hp k hk p ((σ k).self_mem p)
          have hmsg : (fun q => (q, A.run σ I k q)) '' (σ k).inN p
                    = (fun q => (q, A.run τ J k q)) '' (τ k).inN p := by
            rw [← hnb]
            exact Set.image_congr fun q hq => by
              rw [ih k hk q (hstep p (k + 1) hp k hk q hq)]
          simp only [Algorithm.run, Protocol.run, ih k hk p hpk, hmsg]

theorem Bool.eq_or_eq_not (q p : Bool) : q = p ∨ q = !p := by
  cases q <;> cases p <;> simp

/-- `p` hears the other process in round `r`. -/
def Hears (p : Bool) (σ : ℕ → Event Bool) (r : ℕ) : Prop := (!p) ∈ (σ r).inN p

end DistributedSynthesis.DecisionTasks.Source

/- From TwoHard.lean. -/
namespace DistributedSynthesis.DecisionTasks.Source

universe u v w

variable {Proc : Type u} {V : Type v} {St : Type w}

theorem inN_eq_self_of_not_hears {p : Bool} {σ : ℕ → Event Bool} {i : ℕ}
    (h : ¬ Hears p σ i) : (σ i).inN p = {p} := by
  ext z
  constructor
  · intro hz
    rcases Bool.eq_or_eq_not z p with rfl | rfl
    · rfl
    · exact absurd hz h
  · intro hz
    rw [show z = p from hz]
    exact (σ i).self_mem p

end DistributedSynthesis.DecisionTasks.Source

/- From Leader.lean. -/
namespace DistributedSynthesis.DecisionTasks.Source

universe v w

variable {V : Type v} {St : Type w}

/-- `p` never hears the other process. -/
def Muted (p : Bool) (σ : ℕ → Event Bool) : Prop := ∀ r, ¬ Hears p σ r

/-- `σ` and `τ` give `p` the same view at time `r`: `p`'s own receptions agree over `[0, r)`,
and for every round `i < r` at which `p` hears, the other process's receptions agree over
`[0, i)`. -/
def ViewEq (p : Bool) (r : ℕ) (σ τ : ℕ → Event Bool) : Prop :=
  (∀ i, i < r → (σ i).inN p = (τ i).inN p) ∧
  (∀ i, i < r → Hears p σ i → ∀ j, j < i → (σ j).inN (!p) = (τ j).inN (!p))

theorem ViewEq.mono {p : Bool} {r r' : ℕ} {σ τ : ℕ → Event Bool} (h : ViewEq p r' σ τ)
    (hle : r ≤ r') : ViewEq p r σ τ :=
  ⟨fun i hi => h.1 i (lt_of_lt_of_le hi hle),
   fun i hi hh j hj => h.2 i (lt_of_lt_of_le hi hle) hh j hj⟩

/-- **The view lemma, as a congruence.**  A process's state is a function of its view and of
the inputs it can see: its own, and the other's if it has heard. -/
theorem run_eq_of_viewEq (A : Algorithm Bool V St) {σ τ : ℕ → Event Bool} {I J : Bool → V}
    {p : Bool} {r : ℕ} (h : ViewEq p r σ τ) (hI : I p = J p)
    (hI' : (∃ i, i < r ∧ Hears p σ i) → I (!p) = J (!p)) :
    A.run σ I r p = A.run τ J r p := by
  refine run_eq_of_bisim A
    (fun q i => (q = p ∧ i ≤ r) ∨ (q = !p ∧ ∃ i', i ≤ i' ∧ i' < r ∧ Hears p σ i'))
    ?_ ?_ ?_ r p (Or.inl ⟨rfl, le_rfl⟩)
  · rintro q i (⟨rfl, -⟩ | ⟨rfl, i', -, hi', hh⟩)
    · exact hI
    · exact hI' ⟨i', hi', hh⟩
  · rintro q i (⟨rfl, hi⟩ | ⟨rfl, i', hii', hi', hh⟩) j hj
    · exact h.1 j (lt_of_lt_of_le hj hi)
    · exact h.2 i' hi' hh j (lt_of_lt_of_le hj hii')
  · rintro q i hq j hj z hz
    have hjr : j < r := by
      rcases hq with ⟨-, hi⟩ | ⟨-, i', hii', hi', -⟩ <;> omega
    rcases Bool.eq_or_eq_not z p with rfl | rfl
    · exact Or.inl ⟨rfl, Nat.le_of_lt hjr⟩
    · refine Or.inr ⟨rfl, ?_⟩
      rcases hq with ⟨hqp, -⟩ | ⟨-, i', hii', hi', hh⟩
      · subst hqp
        exact ⟨j, le_rfl, hjr, hz⟩
      · exact ⟨i', le_trans (Nat.le_of_lt hj) hii', hi', hh⟩

theorem inN_eq_of_hears {p : Bool} {σ : ℕ → Event Bool} {i : ℕ} (h : Hears p σ i) :
    (σ i).inN p = {p, !p} := by
  ext z
  constructor
  · intro _
    rcases Bool.eq_or_eq_not z p with hz | hz <;> simp [hz]
  · intro _
    rcases Bool.eq_or_eq_not z p with hz | hz
    · rw [hz]; exact (σ i).self_mem p
    · rw [hz]; exact h

/-- On two processes an in-neighbourhood is determined by whether the process hears. -/
theorem inN_eq_of_hears_iff {p : Bool} {σ τ : ℕ → Event Bool} {i : ℕ}
    (h : Hears p σ i ↔ Hears p τ i) : (σ i).inN p = (τ i).inN p := by
  by_cases hσ : Hears p σ i
  · rw [inN_eq_of_hears hσ, inN_eq_of_hears (h.mp hσ)]
  · rw [inN_eq_self_of_not_hears hσ, inN_eq_self_of_not_hears (fun ht => hσ (h.mpr ht))]

/-- Internal two-process encoding of a local history: an initial state, then one
round at a time, carrying the other process's history whenever it was received.
This is a proof representation for the shared `Protocol` model, not another
execution semantics. `historyAlg_run` identifies it with a protocol run;
`run_eq_of_viewEq` and the input-aware bridge in `TaskColouring` establish locality. -/
inductive Hist (V : Type v) : Type v
  | init (p : Bool) (x : V) : Hist V
  | step (h : Hist V) (m : Option (Hist V)) : Hist V

namespace Hist

variable {V : Type v}

/-- The process whose history this is. -/
def proc : Hist V → Bool
  | init p _ => p
  | step h _ => h.proc

/-- The process's own input. -/
def own : Hist V → V
  | init _ x => x
  | step h _ => h.own

/-- The other process's input, if it has ever been heard. -/
def other : Hist V → Option V
  | init _ _ => none
  | step h none => h.other
  | step _ (some h') => some h'.own

/-- The number of rounds. -/
def depth : Hist V → ℕ
  | init _ _ => 0
  | step h _ => h.depth + 1

end Hist

section Hist

open Classical

/-- The history of `p` after `r` rounds of `σ` on inputs `I`. -/
noncomputable def hist (σ : ℕ → Event Bool) (I : Bool → V) : ℕ → Bool → Hist V
  | 0, p => .init p (I p)
  | r + 1, p => .step (hist σ I r p) (if Hears p σ r then some (hist σ I r (!p)) else none)

variable {σ τ : ℕ → Event Bool} {I J : Bool → V}

theorem hist_zero (p : Bool) : hist σ I 0 p = .init p (I p) := rfl

theorem hist_succ (r : ℕ) (p : Bool) :
    hist σ I (r + 1) p =
      .step (hist σ I r p) (if Hears p σ r then some (hist σ I r (!p)) else none) := rfl

theorem hist_own (r : ℕ) (p : Bool) : (hist σ I r p).own = I p := by
  induction r with
  | zero => rfl
  | succ r ih => rw [hist_succ]; exact ih

theorem hist_depth (r : ℕ) (p : Bool) : (hist σ I r p).depth = r := by
  induction r with
  | zero => rfl
  | succ r ih =>
      rw [hist_succ]
      show (hist σ I r p).depth + 1 = r + 1
      rw [ih]

/-- After a reception the other process's input is recorded. -/
theorem hist_other_of_heard {s : ℕ} {p : Bool} (hs : Hears p σ s) :
    ∀ r, s < r → (hist σ I r p).other = some (I (!p)) := by
  intro r
  induction r with
  | zero => intro h; exact absurd h (Nat.not_lt_zero s)
  | succ r ih =>
      intro hsr
      rw [hist_succ]
      by_cases hh : Hears p σ r
      · rw [if_pos hh]
        show some (hist σ I r (!p)).own = some (I (!p))
        rw [hist_own]
      · rw [if_neg hh]
        show (hist σ I r p).other = some (I (!p))
        have hne : s ≠ r := fun h => hh (h ▸ hs)
        exact ih (by omega)

/-- **The view lemma, converse direction.**  Equal histories have equal views and equal own
inputs. -/
theorem viewEq_of_hist_eq :
    ∀ (r : ℕ) (p : Bool), hist σ I r p = hist τ J r p → ViewEq p r σ τ ∧ I p = J p := by
  intro r
  induction r with
  | zero =>
      intro p h
      rw [hist_zero, hist_zero] at h
      exact ⟨⟨fun i hi => absurd hi (Nat.not_lt_zero i),
        fun i hi => absurd hi (Nat.not_lt_zero i)⟩, (Hist.init.inj h).2⟩
  | succ r ih =>
      intro p h
      rw [hist_succ, hist_succ] at h
      obtain ⟨h₁, h₂⟩ := Hist.step.inj h
      obtain ⟨hv, hI⟩ := ih p h₁
      have hiff : Hears p σ r ↔ Hears p τ r := by
        constructor
        · intro hσ
          by_contra hτ
          rw [if_pos hσ, if_neg hτ] at h₂
          exact Option.some_ne_none _ h₂
        · intro hτ
          by_contra hσ
          rw [if_neg hσ, if_pos hτ] at h₂
          exact Option.some_ne_none _ h₂.symm
      refine ⟨⟨fun i hi => ?_, fun i hi hh j hj => ?_⟩, hI⟩
      · rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | hi
        · exact hv.1 i hi
        · rw [hi]
          exact inN_eq_of_hears_iff hiff
      · rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | hi
        · exact hv.2 i hi hh j hj
        · rw [hi] at hh hj
          rw [if_pos hh, if_pos (hiff.mp hh)] at h₂
          exact ((ih (!p) (Option.some_inj.mp h₂)).1).1 j hj

end Hist

/-- Store the complete history; task outputs are supplied separately. -/
noncomputable def historyAlg (V : Type v) : Algorithm Bool V (Hist V) where
  init p x := .init p x
  trans p st msgs := .step st (lookup msgs (!p))

/-- The algorithm's state is the history. -/
theorem historyAlg_run (σ : ℕ → Event Bool) (I : Bool → V) :
    ∀ (r : ℕ) (p : Bool), (historyAlg V).run σ I r p = hist σ I r p := by
  intro r
  induction r with
  | zero => intro p; rfl
  | succ r ih =>
      intro p
      show Hist.step ((historyAlg V).run σ I r p)
        (lookup ((fun q => (q, (historyAlg V).run σ I r q)) '' (σ r).inN p) (!p)) = _
      rw [hist_succ, lookup_image, ih p]
      unfold Hears
      by_cases hh : (!p) ∈ (σ r).inN p
      · rw [if_pos hh, if_pos hh, ih (!p)]
      · rw [if_neg hh, if_neg hh]

end DistributedSynthesis.DecisionTasks.Source
