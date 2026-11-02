/- Project authors: see AUTHORS.md at the repository root. -/

import Mathlib.Data.Set.Image

/-! # Decision tasks and synchronous message-passing protocols

This is the shared model for both task proofs. Unlike reactive synthesis,
inputs are supplied once, before communication, and outputs are irrevocable
decisions. The process set and the input/output alphabets are parameters.
There is no finite-state restriction on protocols.

An event specifies incoming deliveries and includes every self-loop. The
existing three-graph model embeds into this representation; arbitrary process
sets and the silent event are also needed for the task results.
-/

namespace DistributedSynthesis.DecisionTasks

universe u v w z

/-- A communication graph, represented by its incoming neighborhoods. -/
structure Event (P : Type u) where
  inN : P → Set P
  self_mem : ∀ p, p ∈ inN p

/-- Every round belongs to the given graph alphabet. -/
def Obl {P : Type u} (D : Set (Event P)) : Set (ℕ → Event P) :=
  {σ | ∀ r, σ r ∈ D}

/-- The graph in which each process receives only its own message. -/
def silentEvent {P : Type u} : Event P where
  inN p := {p}
  self_mem _ := rfl

@[simp] theorem silentEvent_inN {P : Type u} (p : P) :
    (silentEvent : Event P).inN p = {p} := rfl

/-- The permitted joint output assignments for each initial input assignment. -/
structure Task (P : Type u) (I : P → Type v) (O : P → Type w) where
  allows : (∀ p, I p) → (∀ p, O p) → Prop

/-- A deterministic protocol. A transition sees the old local state and
incoming pairs of sender identities and their old states. -/
structure Protocol (P : Type u) (I : P → Type v) (St : Type z) where
  init : ∀ p, I p → St
  trans : P → St → Set (P × St) → St

variable {P : Type u} {I : P → Type v} {O : P → Type w}

/-- State after `r` rounds. Event `σ r` is used in round `r + 1`. -/
def Protocol.run {St : Type z} (A : Protocol P I St)
    (σ : ℕ → Event P) (x : ∀ p, I p) : ℕ → P → St
  | 0, p => A.init p (x p)
  | r + 1, p => A.trans p (A.run σ x r p)
      ((fun q => (q, A.run σ x r q)) '' (σ r).inN p)

/-- Termination, irrevocability, and task validity on every admissible word
and every initial input assignment. Decision times need not be uniform. -/
structure Protocol.Solves {St : Type z} (A : Protocol P I St)
    (out : ∀ p, St → Option (O p)) (T : Task P I O)
    (adv : Set (ℕ → Event P)) : Prop where
  term : ∀ σ ∈ adv, ∀ x p, ∃ r o, out p (A.run σ x r p) = some o
  irrev : ∀ σ ∈ adv, ∀ x p r r', r ≤ r' → ∀ o,
    out p (A.run σ x r p) = some o → out p (A.run σ x r' p) = some o
  allows : ∀ σ ∈ adv, ∀ x o,
    (∀ p, ∃ r, out p (A.run σ x r p) = some (o p)) → T.allows x o

/-- One protocol and output map, chosen before the inputs and graph word.
State types range over the universe containing the process and input types,
which includes full histories; their cardinality is unrestricted. -/
def Task.Solvable (T : Task P I O) (adv : Set (ℕ → Event P)) : Prop :=
  ∃ (St : Type (max u v)) (A : Protocol P I St) (out : ∀ p, St → Option (O p)),
    A.Solves out T adv

end DistributedSynthesis.DecisionTasks
