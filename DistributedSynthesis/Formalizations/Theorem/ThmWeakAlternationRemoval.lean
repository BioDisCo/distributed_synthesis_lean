/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmMiyanoHayashiEquivalence
import DistributedSynthesis.Library.Automata.AlternatingSupport

/-!
# Alternation removal for weak alternating parity automata

A weak alternating automaton is witnessed here by a `SelfOrDecreasing`
transition measure: every transition atom is the source state itself or
strictly smaller in the measure.  Along any thread of a positional run DAG
the measure is antitone, so the thread is eventually constant, and the
min-even parity condition reduces to the parity of the limit state's
priority.  Consequently `recolor`, which replaces every priority by its
parity (`0` for even, `1` for odd), preserves the accepted language:
`recolor_accepts_iff`.

Composing with the Miyano-Hayashi breakpoint equivalence for the
Büchi-shaped recolored automaton yields the unconditional
alternation-removal compilation for weak automata,
`weakAPAToNBACompilation`, which plugs into the checked Piterman
determinization through `APARunToDPACompilation` interfaces.
-/

namespace DistributedSynthesis

universe u v

namespace AlternatingParityAutomaton

variable {Alphabet : Type u}

/--
A self-or-decreasing transition measure: the weakness witness.  Every
transition atom is the source itself or strictly smaller.
-/
def SelfOrDecreasing (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (μ : A.State -> Nat) : Prop :=
  ∀ (s : A.State) (letter : Alphabet) (s' : A.State),
    s' ∈ (A.step s letter).atoms -> s' = s ∨ μ s' < μ s

/-- Recoloring priorities to their parity. -/
noncomputable def recolor (A : AlternatingParityAutomaton.{u, v} Alphabet) :
    AlternatingParityAutomaton.{u, v} Alphabet where
  State := A.State
  stateFinite := A.stateFinite
  initial := A.initial
  step := A.step
  priority := fun s => by
    classical
    exact if DetParityAutomaton.NatEven (A.priority s) then 0 else 1

/-- The recolored automaton is Büchi-shaped. -/
theorem recolor_buchiShaped (A : AlternatingParityAutomaton.{u, v} Alphabet) :
    MiyanoHayashi.BuchiShaped (recolor A) := by
  classical
  intro s
  show (if DetParityAutomaton.NatEven (A.priority s) then 0 else 1) = 0 ∨
    (if DetParityAutomaton.NatEven (A.priority s) then 0 else 1) = 1
  by_cases h : DetParityAutomaton.NatEven (A.priority s)
  · exact Or.inl (if_pos h)
  · exact Or.inr (if_neg h)

theorem recolor_priority_even (A : AlternatingParityAutomaton.{u, v} Alphabet)
    {s : A.State} (h : DetParityAutomaton.NatEven (A.priority s)) :
    (recolor A).priority s = 0 := by
  classical
  show (if DetParityAutomaton.NatEven (A.priority s) then 0 else 1) = 0
  exact if_pos h

theorem recolor_priority_odd (A : AlternatingParityAutomaton.{u, v} Alphabet)
    {s : A.State} (h : ¬ DetParityAutomaton.NatEven (A.priority s)) :
    (recolor A).priority s = 1 := by
  classical
  show (if DetParityAutomaton.NatEven (A.priority s) then 0 else 1) = 1
  exact if_neg h

/-- Self-or-decreasing threads are eventually constant. -/
theorem thread_eventually_constant
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {μ : A.State -> Nat}
    {s : Nat -> A.State}
    (hstep : ∀ n : Nat, s (n + 1) = s n ∨ μ (s (n + 1)) < μ (s n)) :
    ∃ N : Nat, ∀ k : Nat, N ≤ k -> s k = s N := by
  have hanti : Antitone (fun n => μ (s n)) := by
    apply antitone_nat_of_succ_le
    intro n
    rcases hstep n with heq | hlt
    · rw [heq]
    · omega
  obtain ⟨N, value, hval⟩ :=
    FiniteWidthStreett.LeveledGraph.eventually_constant_of_antitone hanti
  refine ⟨N, ?_⟩
  intro k hk
  induction k with
  | zero =>
      have hN0 : N = 0 := Nat.le_zero.mp hk
      rw [hN0]
  | succ k ih =>
      rcases Nat.lt_or_ge N (k + 1) with hlt | hge
      · have hkN : s k = s N := ih (by omega)
        rcases hstep k with heq | hdec
        · rw [heq, hkN]
        · exfalso
          have hk1 : μ (s k) = value := hval k (by omega)
          have hk2 : μ (s (k + 1)) = value := hval (k + 1) (by omega)
          omega
      · have hNeq : N = k + 1 := by omega
        rw [hNeq]

/-- Min-even parity of an eventually constant sequence is its limit parity. -/
theorem natSeqMinEvenParity_iff_of_eventually_constant
    {f : Nat -> Nat} {N : Nat}
    (hconst : ∀ k : Nat, N ≤ k -> f k = f N) :
    NatSeqMinEvenParity f ↔ DetParityAutomaton.NatEven (f N) := by
  constructor
  · rintro ⟨p, hpEven, hpSeen, _⟩
    rcases hpSeen N with ⟨k, hk, hkp⟩
    rw [hconst k hk] at hkp
    rw [hkp]
    exact hpEven
  · intro heven
    refine ⟨f N, heven, ?_, ?_⟩
    · intro n
      exact ⟨max n N, le_max_left n N, hconst _ (le_max_right n N)⟩
    · intro q hq
      rcases hq N with ⟨k, hk, hkq⟩
      rw [hconst k hk] at hkq
      omega

/--
For an eventually constant thread, recolored min-even parity coincides with
original min-even parity.
-/
theorem recolor_natSeqMinEvenParity_iff
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {s : Nat -> A.State} {N : Nat}
    (hconst : ∀ k : Nat, N ≤ k -> s k = s N) :
    NatSeqMinEvenParity (fun n => (recolor A).priority (s n)) ↔
      NatSeqMinEvenParity (fun n => A.priority (s n)) := by
  have hconstR : ∀ k : Nat, N ≤ k ->
      (recolor A).priority (s k) = (recolor A).priority (s N) := by
    intro k hk
    rw [hconst k hk]
  have hconstA : ∀ k : Nat, N ≤ k ->
      A.priority (s k) = A.priority (s N) := by
    intro k hk
    rw [hconst k hk]
  rw [natSeqMinEvenParity_iff_of_eventually_constant hconstR,
    natSeqMinEvenParity_iff_of_eventually_constant hconstA]
  by_cases h : DetParityAutomaton.NatEven (A.priority (s N))
  · rw [recolor_priority_even A h]
    exact ⟨fun _ => h, fun _ => ⟨0, rfl⟩⟩
  · rw [recolor_priority_odd A h]
    constructor
    · rintro ⟨m, hm⟩
      omega
    · intro h1
      exact absurd h1 h

/-- Cast a step support across recoloring. -/
def StepSupport.recolorCast
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {s : A.State} {letter : Alphabet}
    (ss : A.StepSupport s letter) :
    (recolor A).StepSupport s letter where
  support := ss.support
  support_satisfies := ss.support_satisfies
  support_atoms := ss.support_atoms

/-- Cast a step support from the recolored automaton back. -/
def StepSupport.recolorCastBack
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {s : A.State} {letter : Alphabet}
    (ss : (recolor A).StepSupport s letter) :
    A.StepSupport s letter where
  support := ss.support
  support_satisfies := ss.support_satisfies
  support_atoms := ss.support_atoms

/-- Cast a macro support choice across recoloring. -/
def MacroStepSupport.recolorCast
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {states : Finset A.State} {letter : Alphabet}
    (msc : A.MacroStepSupport states letter) :
    (recolor A).MacroStepSupport states letter where
  choice := fun state => (msc.choice state).recolorCast

/-- Cast a macro support choice from the recolored automaton back. -/
def MacroStepSupport.recolorCastBack
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {states : Finset A.State} {letter : Alphabet}
    (msc : (recolor A).MacroStepSupport states letter) :
    A.MacroStepSupport states letter where
  choice := fun state => (msc.choice state).recolorCastBack

@[simp]
theorem MacroStepSupport.recolorCast_support
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {states : Finset A.State} {letter : Alphabet}
    (msc : A.MacroStepSupport states letter) :
    (MacroStepSupport.recolorCast msc).support = msc.support :=
  rfl

@[simp]
theorem MacroStepSupport.recolorCastBack_support
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {states : Finset A.State} {letter : Alphabet}
    (msc : (recolor A).MacroStepSupport states letter) :
    (MacroStepSupport.recolorCastBack msc).support = msc.support :=
  rfl

section DAGTransport

variable {A : AlternatingParityAutomaton.{u, v} Alphabet}
variable {word : OmegaWord Alphabet}
variable {μ : A.State -> Nat}

/-- Transport a positional run DAG to the recolored automaton. -/
noncomputable def PositionalRunDAG.recolorTo
    (hweak : SelfOrDecreasing A μ)
    (D : A.PositionalRunDAG word) :
    (recolor A).PositionalRunDAG word where
  frontier := D.frontier
  choice := fun n => MacroStepSupport.recolorCast (D.choice n)
  initial_mem := D.initial_mem
  frontier_succ := D.frontier_succ
  threads_accept := by
    intro s hzero hstep
    have hstep' : ∀ n : Nat, ∃ h : s n ∈ D.frontier n,
        s (n + 1) ∈ ((D.choice n).choice ⟨s n, h⟩).support := by
      intro n
      exact hstep n
    have haccept := D.threads_accept s hzero hstep'
    have hmono : ∀ n : Nat, s (n + 1) = s n ∨ μ (s (n + 1)) < μ (s n) := by
      intro n
      rcases hstep' n with ⟨h, hsup⟩
      exact hweak (s n) (word n) (s (n + 1))
        (((D.choice n).choice ⟨s n, h⟩).support_atoms (s (n + 1)) hsup)
    obtain ⟨N, hconst⟩ := thread_eventually_constant hmono
    exact (recolor_natSeqMinEvenParity_iff (A := A) hconst).mpr haccept

/-- Transport a positional run DAG from the recolored automaton back. -/
noncomputable def PositionalRunDAG.recolorFrom
    (hweak : SelfOrDecreasing A μ)
    (D : (recolor A).PositionalRunDAG word) :
    A.PositionalRunDAG word where
  frontier := D.frontier
  choice := fun n => MacroStepSupport.recolorCastBack (D.choice n)
  initial_mem := D.initial_mem
  frontier_succ := D.frontier_succ
  threads_accept := by
    intro s hzero hstep
    have hstep' : ∀ n : Nat, ∃ h : s n ∈ D.frontier n,
        s (n + 1) ∈ ((D.choice n).choice ⟨s n, h⟩).support := by
      intro n
      exact hstep n
    have haccept := D.threads_accept s hzero hstep'
    have hmono : ∀ n : Nat, s (n + 1) = s n ∨ μ (s (n + 1)) < μ (s n) := by
      intro n
      rcases hstep' n with ⟨h, hsup⟩
      exact hweak (s n) (word n) (s (n + 1))
        (((D.choice n).choice ⟨s n, h⟩).support_atoms (s (n + 1)) hsup)
    obtain ⟨N, hconst⟩ := thread_eventually_constant hmono
    exact (recolor_natSeqMinEvenParity_iff (A := A) hconst).mp haccept

/-- Recoloring preserves the accepted language of a weak automaton. -/
theorem recolor_accepts_iff
    (hweak : SelfOrDecreasing A μ) :
    (recolor A).Accepts word ↔ A.Accepts word := by
  rw [← nonempty_positionalRunDAG_iff_accepts,
    ← nonempty_positionalRunDAG_iff_accepts]
  constructor
  · rintro ⟨D⟩
    exact ⟨PositionalRunDAG.recolorFrom hweak D⟩
  · rintro ⟨D⟩
    exact ⟨PositionalRunDAG.recolorTo hweak D⟩

end DAGTransport

/--
Unconditional alternation removal for weak alternating parity automata:
the Miyano-Hayashi breakpoint automaton of the recolored automaton
recognizes the same language.
-/
noncomputable def weakAPAToNBACompilation
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    (μ : A.State -> Nat)
    (hweak : SelfOrDecreasing A μ) :
    APARunToNondetBuchiCompilation.{u, v, v} A where
  buchi := MiyanoHayashi.buchiCore (recolor A)
  correct := fun _word =>
    (MiyanoHayashi.buchiCore_accepts_iff_accepts
      (recolor_buchiShaped A)).trans (recolor_accepts_iff hweak)

/--
Weak alternation removal composed with the checked Piterman construction:
an unconditional APA-to-DPA compilation for weak automata.
-/
noncomputable def weakAPAToDPACompilation
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    (μ : A.State -> Nat)
    (hweak : SelfOrDecreasing A μ) :
    APARunToDPACompilation.{u, v, v} A := by
  classical
  exact
    { dpa :=
        ((NondetBuchiAutomaton.Piterman.CompactTreeData.toDPACompiler
          Alphabet).compile (weakAPAToNBACompilation μ hweak).buchi).dpa
      correct := fun word =>
        (((NondetBuchiAutomaton.Piterman.CompactTreeData.toDPACompiler
          Alphabet).compile
            (weakAPAToNBACompilation μ hweak).buchi).correct word).trans
          ((weakAPAToNBACompilation μ hweak).correct word) }

end AlternatingParityAutomaton

end DistributedSynthesis
