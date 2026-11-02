/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.DecisionTasks.BoundedProtocol

/-! # Finite local views at a fixed depth

These are the recursive views of the TeX model: the own previous view and
the sender-indexed received views. All protocols factor through them, and
the canonical full-information protocol implements them. For finite alphabets
each level is finite. Consequently the bounded criterion quantifies over
finite local output tables, even when the original protocol has arbitrary states.
IIS and participation specializations are in `IISFiniteViews`.
-/

namespace DistributedSynthesis.DecisionTasks.FiniteViews

universe u

variable {P : Type} {I O : P → Type} {St : Type u}

/-- The tag at each level records the receiving process. -/
def View (P : Type) (I : P → Type) : ℕ → Type
  | 0 => Σ p, I p
  | r + 1 => P × View P I r × (P → Option (View P I r))

instance [Fintype P] [DecidableEq P] [∀ p, DecidableEq (I p)] (r : ℕ) :
    DecidableEq (View P I r) := by
  induction r with
  | zero => exact inferInstanceAs (DecidableEq (Σ p, I p))
  | succ r ih =>
    exact inferInstanceAs (DecidableEq (P × View P I r × (P → Option (View P I r))))

instance [Fintype P] [DecidableEq P] [∀ p, Fintype (I p)] (r : ℕ) :
    Fintype (View P I r) := by
  induction r with
  | zero => exact inferInstanceAs (Fintype (Σ p, I p))
  | succ r ih =>
    exact inferInstanceAs (Fintype (P × View P I r × (P → Option (View P I r))))

instance [Finite P] [∀ p, Finite (I p)] (r : ℕ) : Finite (View P I r) := by
  induction r with
  | zero => exact inferInstanceAs (Finite (Σ p, I p))
  | succ r ih => exact inferInstanceAs (Finite (P × View P I r × (P → Option (View P I r))))

noncomputable def view (σ : ℕ → Event P) (x : ∀ p, I p) :
    (r : ℕ) → P → View P I r
  | 0, p => ⟨p, x p⟩
  | r + 1, p => (p, view σ x r p,
      fun q => @ite _ (q ∈ (σ r).inN p) (Classical.propDecidable _)
        (some (view σ x r q)) none)

def eval (A : Protocol P I St) : (r : ℕ) → View P I r → St
  | 0, v => A.init v.1 v.2
  | r + 1, v => A.trans v.1 (eval A r v.2.1)
      {z | (v.2.2 z.1).map (eval A r) = some z.2}

/-- Equal local views imply equal states in every deterministic protocol. -/
theorem eval_view (A : Protocol P I St) (σ : ℕ → Event P)
    (x : ∀ p, I p) (r : ℕ) (p : P) :
    eval A r (view σ x r p) = A.run σ x r p := by
  classical
  induction r generalizing p with
  | zero => rfl
  | succ r ih =>
    simp only [view, eval, Protocol.run, ih]
    congr 1
    ext ⟨q, s⟩
    by_cases hq : q ∈ (σ r).inN p <;> simp [hq, ih, Set.mem_image]

abbrev State (P : Type) (I : P → Type) := Σ r, View P I r

/-- Read a sender's previous-round state. Real executions contain one such state. -/
noncomputable def receive (r : ℕ) (messages : Set (P × State P I)) (q : P) :
    Option (View P I r) := by
  classical
  exact if h : ∃ v, (q, ⟨r, v⟩) ∈ messages then some (Classical.choose h) else none

theorem receive_image (r : ℕ) (v : P → View P I r) (N : Set P) (q : P) :
    receive r ((fun p => (p, ⟨r, v p⟩)) '' N) q =
      @ite _ (q ∈ N) (Classical.propDecidable _) (some (v q)) none := by
  classical
  have hmem (u : View P I r) :
      (q, (⟨r, u⟩ : State P I)) ∈ (fun p => (p, (⟨r, v p⟩ : State P I))) '' N ↔
        q ∈ N ∧ u = v q := by
    simp [Set.mem_image, eq_comm]
  unfold receive
  split_ifs with h hq hq
  · have hc := (hmem _).mp (Classical.choose_spec h)
    exact congrArg some hc.2
  · exact False.elim (hq ((hmem _).mp (Classical.choose_spec h)).1)
  · exact False.elim (h ⟨v q, (hmem _).mpr ⟨hq, rfl⟩⟩)
  · rfl

/-- The state contains exactly the current round and its full local view. -/
noncomputable def protocol : Protocol P I (State P I) where
  init p x := ⟨0, ⟨p, x⟩⟩
  trans p s messages := ⟨s.1 + 1, (p, s.2, receive s.1 messages)⟩

theorem protocol_run (σ : ℕ → Event P) (x : ∀ p, I p) (r : ℕ) (p : P) :
    (protocol (P := P) (I := I)).run σ x r p = ⟨r, view σ x r p⟩ := by
  induction r generalizing p with
  | zero => rfl
  | succ r ih =>
    simp only [Protocol.run, ih]
    change (⟨r + 1, (p, view σ x r p,
      receive r ((fun q => (q, ⟨r, view σ x r q⟩)) '' (σ r).inN p))⟩ : State P I) = _
    congr 3
    funext q
    exact receive_image r (view σ x r) ((σ r).inN p) q

/-- The canonical view protocol simulates the decisions of a solving protocol
whose state type may lie in any universe. No finite-state or uniform-time
assumption is needed. -/
theorem protocol_solves (A : Protocol P I St) (out : ∀ p, St → Option (O p))
    (T : DecisionTasks.Task P I O) (adv : Set (ℕ → Event P))
    (h : A.Solves out T adv) :
    (protocol (P := P) (I := I)).Solves
      (fun p s => out p (eval A s.1 s.2)) T adv := by
  have heval (σ : ℕ → Event P) (x : ∀ p, I p) (r : ℕ) (p : P) :
      eval A ((protocol (P := P) (I := I)).run σ x r p).1
        ((protocol (P := P) (I := I)).run σ x r p).2 = A.run σ x r p :=
    (congrArg (fun s : State P I => eval A s.1 s.2)
      (protocol_run σ x r p)).trans (eval_view A σ x r p)
  constructor
  · intro σ hσ x p
    simpa only [heval] using h.term σ hσ x p
  · intro σ hσ x p r r' hrr o ho
    simp only [heval] at ho ⊢
    exact h.irrev σ hσ x p r r' hrr o ho
  · intro σ hσ x o ho
    apply h.allows σ hσ x o
    simpa only [heval] using ho

/-- Restricting the existential state type to `Type` does not restrict task
solvability: every solver, even in a larger universe, factors through the
shared `Type`-valued full-information protocol. -/
theorem solvable_of_solves (A : Protocol P I St) (out : ∀ p, St → Option (O p))
    (T : DecisionTasks.Task P I O) (adv : Set (ℕ → Event P))
    (h : A.Solves out T adv) : T.Solvable adv :=
  ⟨State P I, protocol, fun p s => out p (eval A s.1 s.2),
    protocol_solves A out T adv h⟩

/-- An arbitrary finite-round protocol can be replaced by a finite local view table. -/
theorem bounded_iff_view_maps [∀ p, Nonempty (O p)] (T : DecisionTasks.Task P I O)
    (adv : Set (ℕ → Event P)) :
    T.BoundedSolvable adv ↔
      ∃ (k : ℕ) (d : ∀ p, View P I k → O p),
        ∀ σ ∈ adv, ∀ x, T.allows x (fun p => d p (view σ x k p)) := by
  classical
  constructor
  · rintro ⟨k, St, A, out, h⟩
    exact ⟨k, fun p v => out p (eval A k v), by simpa only [eval_view] using h⟩
  · rintro ⟨k, d, h⟩
    let decision : ∀ p, State P I → O p := fun p s =>
      if hr : s.1 = k then d p (hr ▸ s.2) else Classical.choice inferInstance
    refine ⟨k, State P I, protocol, decision, ?_⟩
    intro σ hσ x
    simpa only [protocol_run, decision, dite_true] using h σ hσ x


end DistributedSynthesis.DecisionTasks.FiniteViews
