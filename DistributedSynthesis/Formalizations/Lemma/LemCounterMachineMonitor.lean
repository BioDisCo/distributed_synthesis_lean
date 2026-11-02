/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/
import DistributedSynthesis.Formalizations.Lemma.LemTernaryCounterSoundness
import DistributedSynthesis.Formalizations.Lemma.LemScalingLTLWinner

namespace DistributedSynthesis.CounterMachine
open TernaryCounter

inductive Instruction (Q : Type*) where
  | inc (counter : Fin 2) (target : Q)
  | dec (counter : Fin 2) (zeroTarget positiveTarget : Q)
deriving DecidableEq

structure Machine (Q : Type*) where
  initial : Q
  code : Q → Option (Instruction Q)

variable {Q : Type*}

def Machine.next (M : Machine Q) (q : Q) (z : Fin 2 → Bool) : Q :=
  match M.code q with
  | none => q
  | some (.inc _ p) => p
  | some (.dec r pz pp) => if z r then pz else pp

def Machine.op (M : Machine Q) (q : Q) (z : Fin 2 → Bool) (r : Fin 2) : Operation :=
  match M.code q with
  | none => .idle
  | some (.inc s _) => if r = s then .increment else .idle
  | some (.dec s _ _) => if r = s ∧ z s = false then .decrement else .idle

theorem Machine.op_decrement (M : Machine Q) (q : Q) (z : Fin 2 → Bool) (r : Fin 2)
    (h : M.op q z r = .decrement) : z r = false := by
  unfold Machine.op at h
  split at h
  · cases h
  · split at h <;> cases h
  · split at h
    · rename_i hh
      exact hh.1 ▸ hh.2
    · cases h

def flags (c : Fin 2 → Nat) : Fin 2 → Bool := fun r ↦ decide (c r = 0)
def Machine.advance (M : Machine Q) (s : Q × (Fin 2 → Nat)) : Q × (Fin 2 → Nat) :=
  (M.next s.1 (flags s.2),fun r ↦ (M.op s.1 (flags s.2) r).applyCount (s.2 r))
def Machine.run (M : Machine Q) : Nat → Q × (Fin 2 → Nat)
  | 0 => (M.initial,fun _ ↦ 0)
  | n+1 => M.advance (M.run n)
def Machine.Nonhalting (M : Machine Q) : Prop := ∀ n, M.code (M.run n).1 ≠ none

structure Plan where
  weight : Fin 2
  child : Fin 3 → Fin 2
deriving DecidableEq, Fintype
def Plan.promised (p : Plan) : Nat := (p.child 0).val + (p.child 1).val + (p.child 2).val

structure Label (Q : Type*) where
  control : Q
  zero : Fin 2 → Bool
  carry : Fin 2 → Fin 9
  right : Fin 2 → Plan
deriving DecidableEq

instance [Fintype Q] : Fintype (Label Q) := Fintype.ofEquiv
  (Q × (Fin 2 → Bool) × (Fin 2 → Fin 9) × (Fin 2 → Plan))
  ⟨fun p ↦ ⟨p.1,p.2.1,p.2.2.1,p.2.2.2⟩,
    fun l ↦ (l.control,l.zero,l.carry,l.right),fun _ ↦ rfl,fun _ ↦ rfl⟩

structure Snapshot (Q : Type*) where
  control : Q
  zero : Fin 2 → Bool
  plans : Fin 2 → Plan
deriving DecidableEq, Fintype
def Label.snapshot (l : Label Q) : Snapshot Q := ⟨l.control,l.zero,l.right⟩

structure State (Q : Type*) where
  oneLeft : Bool
  leftBoundary : Bool
  rightBoundary : Bool
  previous : Option (Snapshot Q)
  good : Bool
deriving DecidableEq, Fintype

structure Valid (M : Machine Q) (lb rb : Bool) (prev : Option (Snapshot Q))
    (d : Fin 3) (l r : Label Q) : Prop where
  control : l.control = r.control
  zero : l.zero = r.zero
  live : M.code l.control ≠ none
  balance : ∀ k, (l.right k).promised + (l.carry k).val =
    (M.op l.control l.zero k).factor * (l.right k).weight.val + (r.carry k).val
  zeroWeight : ∀ k, l.zero k = true → (l.right k).weight.val = 1
  leftCarry : lb = true → ∀ k, (l.carry k).val = 0
  leftWeight : lb = true → ∀ k, l.zero k = false → (l.right k).weight.val = 0
  rightCarry : rb = true → ∀ k, (r.carry k).val = 0
  initial : prev = none → l.control = M.initial ∧ ∀ k, l.zero k = true
  next : ∀ old, prev = some old → l.control = M.next old.control old.zero ∧
    ∀ k, (l.right k).weight = (old.plans k).child d
variable [DecidableEq Q] [Fintype Q]

instance (M : Machine Q) (lb rb : Bool) (prev : Option (Snapshot Q))
    (d : Fin 3) (l r : Label Q) : Decidable (Valid M lb rb prev d l r) :=
  decidable_of_iff
    (l.control = r.control ∧ l.zero = r.zero ∧
      M.code l.control ≠ none ∧
      (∀ k, (l.right k).promised + (l.carry k).val =
        (M.op l.control l.zero k).factor * (l.right k).weight.val + (r.carry k).val) ∧
      (∀ k, l.zero k = true → (l.right k).weight.val = 1) ∧
      (lb = true → ∀ k, (l.carry k).val = 0) ∧
      (lb = true → ∀ k, l.zero k = false → (l.right k).weight.val = 0) ∧
      (rb = true → ∀ k, (r.carry k).val = 0) ∧
      (prev = none → l.control = M.initial ∧ ∀ k, l.zero k = true) ∧
      (∀ old, prev = some old → l.control = M.next old.control old.zero ∧
        ∀ k, (l.right k).weight = (old.plans k).child d))
    (by constructor <;> rintro ⟨a,b,c,d,e,f,g,h,i,j⟩ <;> exact ⟨a,b,c,d,e,f,g,h,i,j⟩)

def step (M : Machine Q) (s : State Q)
    (r : RoundRecord Unit Unit Graph (Label Q) (Label Q)) : State Q :=
  let d := ScalingSafety.digit s.oneLeft r.graph
  let t := ScalingSafety.Source.turn s.oneLeft r.graph
  let lb := s.leftBoundary && decide (d = 0)
  let rb := s.rightBoundary && decide (d = 2)
  let l := if t then r.outputOne else r.outputTwo
  let r := if t then r.outputTwo else r.outputOne
  ⟨t,lb,rb,some l.snapshot,s.good && decide (Valid M lb rb s.previous d l r)⟩

def objective (M : Machine Q) :
    DetParityAutomaton (RoundRecord Unit Unit Graph (Label Q) (Label Q)) where
  State := State Q
  stateFinite := inferInstance
  initial := ⟨true,true,true,none,true⟩
  step := step M
  priority := fun s ↦ if s.good then 0 else 1

theorem accepts_iff_good (M : Machine Q) (word) :
    (objective M).Accepts word ↔ ∀ n, ((objective M).run word n).good = true := by
  constructor
  · intro h n
    by_contra hn
    have hf : ((objective M).run word n).good = false := Bool.eq_false_iff.mpr hn
    have hpersist : ∀ k, ((objective M).run word (n+k)).good = false := by
      intro k
      induction k with
      | zero => simpa using hf
      | succ k ih =>
        rw [Nat.add_succ,(objective M).run_succ]
        change (step M _ _).good = false
        simp [step,ih]
    apply not_natSeqMinEvenParity_of_eventually_one _ n _ h
    intro k hk
    have hp := hpersist (k-n)
    rw [Nat.add_sub_of_le hk] at hp
    change (if ((objective M).run word k).good then 0 else 1) = 1
    simp [hp]
  · intro h
    change NatSeqMinEvenParity (fun n ↦ (objective M).priority ((objective M).run word n))
    refine ⟨0,⟨0,rfl⟩,?_,fun q _ ↦ Nat.zero_le q⟩
    intro n
    refine ⟨n,le_rfl,?_⟩
    change (if ((objective M).run word n).good then 0 else 1) = 0
    simp [h n]

end DistributedSynthesis.CounterMachine
