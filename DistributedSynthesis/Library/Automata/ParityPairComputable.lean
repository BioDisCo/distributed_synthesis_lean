/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Automata.UniversalThreadsComputable
import DistributedSynthesis.Formalizations.Theorem.ThmParityBlockPasting

/-! # Executable conjunction of two priority streams

A finite thread chooses one component at its first step and then follows that
component. Universal-thread determinization checks both choices.
-/
namespace DistributedSynthesis.ParityPairComputable

variable {Q R : Type*} [Fintype Q] [Fintype R]
variable (p : Q → Nat) (r : R → Nat)

def threads : FiniteThreadSystem (Q × R) where
  State := Option (Q ⊕ R)
  stateFinite := inferInstance
  initial := none
  Resolution := Bool
  step q a choose := match q with
    | none => some (if choose then Sum.inl a.1 else Sum.inr a.2)
    | some (.inl _) => some (.inl a.1)
    | some (.inr _) => some (.inr a.2)
  priority q := match q with
    | none => 0
    | some (.inl q) => p q
    | some (.inr q) => r q

instance resolutionDecidableEq : DecidableEq (threads p r).Resolution :=
  inferInstanceAs (DecidableEq Bool)

theorem universal_iff (word : OmegaWord (Q × R)) :
    (∀ q, (threads p r).IsRun word q →
      NatSeqMinEvenParity (fun n => (threads p r).priority (q n))) ↔
    NatSeqMinEvenParity (fun n => p (word n).1) ∧
      NatSeqMinEvenParity (fun n => r (word n).2) := by
  constructor
  · intro h
    have component (side : Bool) : NatSeqMinEvenParity (fun n =>
        if side = true then p (word n).1 else r (word n).2) := by
      let run : Nat → (threads p r).State := fun n => match n with
        | 0 => none
        | k+1 => some (if side = true then Sum.inl (word k).1 else Sum.inr (word k).2)
      have legal : (threads p r).IsRun word run := by
        refine ⟨rfl,fun n => ⟨side,?_⟩⟩
        cases n <;> cases side <;> rfl
      have parity := h run legal
      rw [← natSeqMinEvenParity_shift _ 1] at parity
      cases side <;> simpa [run,threads,Nat.add_comm] using parity
    exact ⟨by simpa using component true,by simpa using component false⟩
  · rintro ⟨left,right⟩ q ⟨initial,steps⟩
    obtain ⟨side,first⟩ := steps 0
    have path (n : Nat) : q (n+1) =
        some (if side = true then Sum.inl (word n).1 else Sum.inr (word n).2) := by
      induction n with
      | zero => simpa only [initial,threads] using first
      | succ n ih =>
        obtain ⟨choice,next⟩ := steps (n+1)
        rw [ih] at next
        cases side <;> exact next
    rw [← natSeqMinEvenParity_shift _ 1]
    simp only [Nat.add_comm 1, path]
    cases side
    · exact right
    · exact left

instance resolutionFintype : Fintype (threads p r).Resolution := inferInstanceAs (Fintype Bool)

variable [DecidableEq Q] [DecidableEq R]

instance threadStateDecidableEq : DecidableEq (threads p r).State :=
  inferInstanceAs (DecidableEq (Option (Q ⊕ R)))

def automaton : DetParityAutomaton (Q × R) :=
  FiniteThreadSystem.Computable.universalDPA (threads p r)

instance stateDecidableEq : DecidableEq (automaton p r).State :=
  FiniteThreadSystem.Computable.universalStateDecidableEq (threads p r)

theorem accepts_iff (word : OmegaWord (Q × R)) :
    (automaton p r).Accepts word ↔
      NatSeqMinEvenParity (fun n => p (word n).1) ∧
      NatSeqMinEvenParity (fun n => r (word n).2) :=
  (FiniteThreadSystem.Computable.universalDPA_correct (threads p r) word).trans (universal_iff p r word)

end DistributedSynthesis.ParityPairComputable
