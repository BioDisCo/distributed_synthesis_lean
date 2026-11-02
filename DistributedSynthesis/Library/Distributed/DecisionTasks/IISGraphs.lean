/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.DecisionTasks.Source.IIS
import DistributedSynthesis.Library.Distributed.DecisionTasks.CompactTermination
import DistributedSynthesis.Library.Logic.LTL

/-!
# The fixed three-process IIS graph formula

Processes `0,1,2` represent the paper's `1,2,3`. The six atoms are,
in order, `e₁₂, e₁₃, e₂₁, e₂₃, e₃₁, e₃₂`. Graphs always include
self-loops. The finite enumeration below is checked by kernel reduction.
This file proves the graph-language identification, not task undecidability.
-/

namespace DistributedSynthesis.DecisionTasks.IISGraphs

abbrev Graph := Fin 6 → Bool

/-- Sender and receiver of each cross-edge atom. -/
def edge : Fin 6 → Fin 3 × Fin 3
  | 0 => (0, 1)
  | 1 => (0, 2)
  | 2 => (1, 0)
  | 3 => (1, 2)
  | 4 => (2, 0)
  | 5 => (2, 1)

/-- Decode the six bits, adding the mandatory self-loops. -/
def event (g : Graph) : Source.Event (Fin 3) where
  inN p := {q | q = p ∨ ∃ a, edge a = (q, p) ∧ g a = true}
  self_mem _ := Or.inl rfl

private theorem edge_complete :
    ∀ p q : Fin 3, q ≠ p → ∃ a : Fin 6, edge a = (q, p) := by decide

private theorem edge_injective : Function.Injective edge := by decide

private theorem edge_distinct (a : Fin 6) : (edge a).1 ≠ (edge a).2 := by
  fin_cases a <;> decide

/-- Every event is represented by its six cross-edge bits. -/
noncomputable def encode (G : Source.Event (Fin 3)) : Graph :=
  fun a => @decide ((edge a).1 ∈ G.inN (edge a).2) (Classical.propDecidable _)

theorem event_encode (G : Source.Event (Fin 3)) : event (encode G) = G := by
  apply Source.event_ext
  funext p
  ext q
  change (q = p ∨ ∃ a, edge a = (q, p) ∧ encode G a = true) ↔ q ∈ G.inN p
  constructor
  · rintro (rfl | ⟨a, ha, hb⟩)
    · exact G.self_mem _
    · simpa [encode, ha] using hb
  · intro h
    by_cases heq : q = p
    · exact Or.inl heq
    · obtain ⟨a, ha⟩ := edge_complete p q heq
      exact Or.inr ⟨a, ha, by simpa [encode, ha] using h⟩

theorem encode_event (g : Graph) : encode (event g) = g := by
  funext a
  simp [encode, event, edge_distinct, edge_injective.eq_iff]

instance (g : Graph) (p q : Fin 3) : Decidable (q ∈ (event g).inN p) :=
  inferInstanceAs (Decidable (q = p ∨ ∃ a, edge a = (q, p) ∧ g a = true))

instance (g : Graph) : Decidable (Source.Immediate (event g)) := by
  change Decidable (∀ p q, q ∈ (event g).inN p →
    ∀ r, r ∈ (event g).inN q → r ∈ (event g).inN p)
  infer_instance

instance (g : Graph) : Decidable (Source.Nested (event g)) := by
  change Decidable (∀ p q,
    (∀ r, r ∈ (event g).inN p → r ∈ (event g).inN q) ∨
    (∀ r, r ∈ (event g).inN q → r ∈ (event g).inN p))
  infer_instance

/-- The graph of an ordered partition given by ranks. -/
def rankGraph (rank : Fin 3 → Fin 3) : Graph :=
  fun a => decide (rank (edge a).1 ≤ rank (edge a).2)

/-- All rank functions on three processes, in a concrete finite order. -/
def ranks : List (Fin 3 → Fin 3) :=
  (List.finRange 3).flatMap fun a =>
    (List.finRange 3).flatMap fun b =>
      (List.finRange 3).map fun c => ![a, b, c]

/-- Repeated ranks and rank gaps yield duplicates, which are removed. -/
def graphs : List Graph := (ranks.map rankGraph).eraseDups

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem graph_count : graphs.length = 13 := by decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem enumeration_correct :
    ∀ g : Graph, g ∈ graphs ↔ Source.Immediate (event g) ∧ Source.Nested (event g) := by
  decide

/-- The list contains exactly the immediate-snapshot graphs. -/
theorem mem_graphs_iff (g : Graph) : g ∈ graphs ↔ event g ∈ Source.DIIS (Fin 3) :=
  (enumeration_correct g).trans Source.mem_DIIS_iff.symm

/-- Conjunction of a finite list of formulas. -/
def conjunction : List (LTL (Fin 6)) → LTL (Fin 6)
  | [] => .verum
  | φ :: rest => .conj φ (conjunction rest)

/-- Disjunction of a finite list of formulas. -/
def disjunction : List (LTL (Fin 6)) → LTL (Fin 6)
  | [] => .falsum
  | φ :: rest => .disj φ (disjunction rest)

def interp (a : Fin 6) (g : Graph) : Prop := g a = true

theorem satisfies_conjunction (xs : List (LTL (Fin 6))) (w : OmegaWord Graph) :
    LTL.Satisfies interp w (conjunction xs) ↔ ∀ φ ∈ xs, LTL.Satisfies interp w φ := by
  induction xs with
  | nil => simp [conjunction, LTL.Satisfies]
  | cons φ xs ih => simp [conjunction, LTL.Satisfies, ih]

theorem satisfies_disjunction (xs : List (LTL (Fin 6))) (w : OmegaWord Graph) :
    LTL.Satisfies interp w (disjunction xs) ↔ ∃ φ ∈ xs, LTL.Satisfies interp w φ := by
  induction xs with
  | nil => simp [disjunction, LTL.Satisfies]
  | cons φ xs ih => simp [disjunction, LTL.Satisfies, ih]

/-- An exact graph test uses a positive or negative literal for every edge. -/
def graphTest (g : Graph) : LTL (Fin 6) :=
  conjunction ((List.finRange 6).map fun a => if g a then .atom a else .neg (.atom a))

theorem satisfies_graphTest (g : Graph) (w : OmegaWord Graph) :
    LTL.Satisfies interp w (graphTest g) ↔ w 0 = g := by
  rw [graphTest, satisfies_conjunction]
  simp only [List.forall_mem_map, List.mem_finRange, forall_const]
  have hbit (a : Fin 6) :
      LTL.Satisfies interp w (if g a then .atom a else .neg (.atom a)) ↔ w 0 a = g a := by
    cases hg : g a <;> cases hw : w 0 a <;> simp [hg, hw, LTL.Satisfies, interp]
  simp only [hbit, funext_iff]

/-- The same formula is used for every task instance. -/
def formula : LTL (Fin 6) := .always (disjunction (graphs.map graphTest))

theorem formula_correct (w : OmegaWord Graph) :
    LTL.Satisfies interp w formula ↔
      (fun r => event (w r)) ∈ Source.advIIS (Fin 3) := by
  rw [formula, LTL.satisfies_always, Source.mem_advIIS_iff]
  apply forall_congr'
  intro r
  rw [satisfies_disjunction]
  simp only [List.mem_map, exists_exists_and_eq_and, satisfies_graphTest,
    OmegaWord.drop_apply, Nat.add_zero]
  exact (show (∃ g ∈ graphs, w r = g) ↔ w r ∈ graphs by simp).trans (mem_graphs_iff _)

/-- The graph formula also characterizes IIS directly on the event model. -/
theorem formula_on_events (σ : ℕ → Source.Event (Fin 3)) :
    LTL.Satisfies interp (encode ∘ σ) formula ↔ σ ∈ Source.advIIS (Fin 3) := by
  simpa only [Function.comp_apply, event_encode] using formula_correct (encode ∘ σ)

/-- Every terminating IIS task solver has a bound uniform over all inputs,
processes, and admissible infinite executions. -/
theorem uniform_bound {I O : Fin 3 → Type} [∀ p, Finite (I p)] {St : Type}
    (A : Protocol (Fin 3) I St) (out : ∀ p, St → Option (O p))
    (T : DecisionTasks.Task (Fin 3) I O) (h : A.Solves out T (Source.advIIS (Fin 3))) :
    ∃ r, ∀ σ ∈ Source.advIIS (Fin 3), ∀ x p,
      ∃ o, out p (A.run σ x r p) = some o := by
  classical
  let G := {g : Graph // g ∈ graphs}
  let decode : G → Source.Event (Fin 3) := fun g => event g.val
  have admissible (w : ℕ → G) : decode ∘ w ∈ Source.advIIS (Fin 3) :=
    fun r => (mem_graphs_iff _).mp (w r).property
  obtain ⟨r, hr⟩ := A.uniform_bound out decode
    (fun w => h.term (decode ∘ w) (admissible w))
    (fun w => h.irrev (decode ∘ w) (admissible w))
  refine ⟨r, fun σ hσ x p => ?_⟩
  let w : ℕ → G := fun n => ⟨encode (σ n),
    (mem_graphs_iff _).mpr (by rw [event_encode]; exact hσ n)⟩
  have hw : decode ∘ w = σ := funext fun n => event_encode (σ n)
  simpa only [hw] using hr w x p

end DistributedSynthesis.DecisionTasks.IISGraphs
