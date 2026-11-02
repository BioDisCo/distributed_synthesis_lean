/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Automata.MiyanoHayashiComputable
import DistributedSynthesis.Library.Automata.PitermanComputable
import DistributedSynthesis.Formalizations.Theorem.ThmWeakAlternationRemoval

/-! # Certified executable compilation of weak alternating automata

Recolor by priority parity, apply the executable breakpoint construction, and
determinize. The supplied decreasing measure is used only by the language proof.
-/

namespace DistributedSynthesis.AlternatingParityAutomaton.WeakComputable

variable {Alphabet : Type*} (A : AlternatingParityAutomaton Alphabet)
variable [DecidableEq A.State]

def recolor : AlternatingParityAutomaton Alphabet where
  State := A.State
  stateFinite := A.stateFinite
  initial := A.initial
  step := A.step
  priority := fun q => if A.priority q % 2 = 0 then 0 else 1

omit [DecidableEq A.State] in
theorem recolor_eq : recolor A = AlternatingParityAutomaton.recolor A := by
  have heven (p : Nat) : (p % 2 = 0) ↔ DetParityAutomaton.NatEven p := by
    constructor
    · intro hp; exact ⟨p / 2, by omega⟩
    · rintro ⟨k, rfl⟩; omega
  unfold recolor AlternatingParityAutomaton.recolor
  congr 1
  funext q
  by_cases h : A.priority q % 2 = 0
  · rw [if_pos h, if_pos ((heven _).mp h)]
  · rw [if_neg h, if_neg (fun h' => h ((heven _).mpr h'))]

local instance : DecidableEq (recolor A).State := inferInstanceAs (DecidableEq A.State)

def buchi := MiyanoHayashi.Computable.buchi (recolor A)

@[reducible] def buchiStateDecidableEq : DecidableEq (buchi A).State :=
  MiyanoHayashi.Computable.stateDecidableEq (recolor A)

def buchiStepDecidable : ∀ q a q', Decidable ((buchi A).step q a q') :=
  MiyanoHayashi.Computable.stepDecidable (recolor A)

@[reducible] def buchiAcceptingDecidable : DecidablePred (buchi A).accepting :=
  MiyanoHayashi.Computable.acceptingDecidable (recolor A)

omit [DecidableEq A.State] in
theorem buchi_accepts_iff (μ : A.State → Nat) (hweak : SelfOrDecreasing A μ)
    (word : OmegaWord Alphabet) : (buchi A).Accepts word ↔ A.Accepts word := by
  unfold buchi
  rw [MiyanoHayashi.Computable.buchi_eq, recolor_eq]
  exact (MiyanoHayashi.buchiCore_accepts_iff_accepts (recolor_buchiShaped A)).trans
    (recolor_accepts_iff hweak)

def dpa : DetParityAutomaton Alphabet :=
  letI := buchiStateDecidableEq A
  (NondetBuchiAutomaton.Piterman.Computable.compilation
    (buchi A) (buchiStepDecidable A) (buchiAcceptingDecidable A)).dpa

@[reducible] def stateDecidableEq : DecidableEq (dpa A).State :=
  letI := buchiStateDecidableEq A
  NondetBuchiAutomaton.Piterman.Computable.stateDecidableEq (buchi A)

theorem accepts_iff (μ : A.State → Nat) (hweak : SelfOrDecreasing A μ)
    (word : OmegaWord Alphabet) : (dpa A).Accepts word ↔ A.Accepts word :=
  letI := buchiStateDecidableEq A
  (NondetBuchiAutomaton.Piterman.Computable.accepts_iff (buchi A)
    (buchiStepDecidable A) (buchiAcceptingDecidable A) word).trans
    (buchi_accepts_iff A μ hweak word)

def compilation (μ : A.State → Nat) (hweak : SelfOrDecreasing A μ) :
    APARunToDPACompilation A where
  dpa := dpa A
  correct := accepts_iff A μ hweak

end DistributedSynthesis.AlternatingParityAutomaton.WeakComputable
