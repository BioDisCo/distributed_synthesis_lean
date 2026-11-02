/- Decision-task excerpts from consensusLTL.
Source declarations and hashes are recorded in ../source-manifest.json. -/

import Mathlib
import DistributedSynthesis.Library.Distributed.DecisionTasks.Model

set_option linter.unusedSectionVars false

/- From Model.lean. -/
namespace DistributedSynthesis.DecisionTasks.Source

universe u v w

variable {Proc : Type u} {V : Type v} {St : Type w}

/-- Compatibility name for the shared communication-graph model. -/
abbrev Event (Proc : Type u) := DecisionTasks.Event Proc

/-- The oblivious message adversary: only events of `D`, in every round. -/
abbrev Obl (D : Set (Event Proc)) : Set (ℕ → Event Proc) := DecisionTasks.Obl D

/-- The source's common input alphabet is a constant family in the shared model. -/
abbrev Algorithm (Proc : Type u) (V : Type v) (St : Type w) :=
  DecisionTasks.Protocol Proc (fun _ => V) St

/-- The state of each process after `r` rounds, running `A` on event sequence `σ`
with input assignment `I`.  Round `r + 1` uses the event `σ r`. -/
abbrev Algorithm.run (A : Algorithm Proc V St) (σ : ℕ → Event Proc) (I : Proc → V) :
    ℕ → Proc → St := DecisionTasks.Protocol.run A σ I

open Classical in
/-- The state received from `q`, if `q` sent one. -/
noncomputable def lookup {S : Type*} (msgs : Set (Proc × S)) (q : Proc) : Option S :=
  if h : ∃ s, (q, s) ∈ msgs then some (Classical.choose h) else none

open Classical in
theorem lookup_image {S : Type*} (f : Proc → S) (T : Set Proc) (q : Proc) :
    lookup ((fun p => (p, f p)) '' T) q = if q ∈ T then some (f q) else none := by
  classical
  by_cases hq : q ∈ T
  · have hex : ∃ s, (q, s) ∈ (fun p => (p, f p)) '' T := ⟨f q, ⟨q, hq, rfl⟩⟩
    rw [lookup, dif_pos hex, if_pos hq]
    obtain ⟨p', _, hp⟩ := Classical.choose_spec hex
    have h1 : p' = q := congrArg Prod.fst hp
    have h2 : f p' = Classical.choose hex := congrArg Prod.snd hp
    rw [← h2, h1]
  · have hex : ¬ ∃ s, (q, s) ∈ (fun p => (p, f p)) '' T := by
      rintro ⟨s, p, hp, hps⟩
      exact hq ((Prod.mk.inj hps).1 ▸ hp)
    rw [lookup, dif_neg hex, if_neg hq]

end DistributedSynthesis.DecisionTasks.Source

/- From Task.lean. -/
namespace DistributedSynthesis.DecisionTasks.Source

universe u v w x

variable {Proc : Type u} {V : Type v} {St : Type w} {O : Type x}

/-- The source task table is the constant-alphabet instance of the shared task. -/
abbrev Task (Proc : Type u) (V : Type v) (O : Type x) :=
  DecisionTasks.Task Proc (fun _ => V) (fun _ => O)

/-- `A`, reading outputs through `out`, solves the task `T` under `adv`. -/
abbrev Algorithm.SolvesTask (A : Algorithm Proc V St) (out : Proc → St → Option O)
    (T : Task Proc V O) (adv : Set (ℕ → Event Proc)) : Prop :=
  DecisionTasks.Protocol.Solves A out T adv

end DistributedSynthesis.DecisionTasks.Source

/- From TwoProcess.lean. -/
namespace DistributedSynthesis.DecisionTasks.Source

universe v w

/-- `u` is `false` and `v` is `true`. -/
abbrev U : Bool := false
abbrev W : Bool := true

variable {V : Type v} {σ : ℕ → Event Bool} {I : Bool → V}

end DistributedSynthesis.DecisionTasks.Source

/- From Stutter.lean. -/
namespace DistributedSynthesis.DecisionTasks.Source

universe u v w

variable {Proc : Type u} {V : Type v} {St : Type w}

/-- Nobody hears anyone but themselves. -/
abbrev silentEvent : Event Proc := DecisionTasks.silentEvent

@[simp] theorem silentEvent_inN (p : Proc) : (silentEvent (Proc := Proc)).inN p = {p} := rfl

end DistributedSynthesis.DecisionTasks.Source
