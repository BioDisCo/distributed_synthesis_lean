/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Definition.DefAlternatingAutomata
import DistributedSynthesis.Formalizations.Theorem.ThmLTLAlternatingStep

/-!
# Certified finite LTL alternating automata

This module packages the finite closure/state-space step of the full
LTL-to-DPA route.  The concrete closure can be instantiated by subformula
closure; the record exposes the exact finite-state and transition-closure
obligations needed by later determinization.
-/

namespace DistributedSynthesis

universe u v w

private theorem nat_eventually_constant_of_succ_le
    (f : Nat -> Nat)
    (hf : ∀ n, f (n + 1) ≤ f n) :
    ∃ N : Nat, ∀ n : Nat, N ≤ n -> f n = f N := by
  classical
  have hfanti : Antitone f := antitone_nat_of_succ_le hf
  let values : Set Nat := Set.range f
  have hvaluesFinite : values.Finite := by
    refine (Set.finite_Iic (f 0)).subset ?_
    intro value hvalue
    rcases hvalue with ⟨n, rfl⟩
    exact hfanti (Nat.zero_le n)
  have hvaluesNonempty : values.Nonempty := ⟨f 0, ⟨0, rfl⟩⟩
  rcases Set.exists_min_image values id hvaluesFinite hvaluesNonempty with
    ⟨value, hvalue, hmin⟩
  rcases hvalue with ⟨N, hN⟩
  subst value
  refine ⟨N, fun n hn => ?_⟩
  exact le_antisymm (hfanti hn) (hmin (f n) ⟨n, rfl⟩)

namespace PositiveLTL

/--
Priority used by the canonical subformula APA.

Outer temporal obligations receive smaller priority numbers than their proper
subformulas.  This makes an unfulfilled recurring `until` obligation rejecting,
while a recurring `release` obligation is accepting, matching the standard weak
alternating automaton discipline for LTL.
-/
def alternatingPriority {AP : Type u} (root state : PositiveLTL AP) : Nat :=
  let rank := root.size - state.size
  match state with
  | PositiveLTL.until _ _ => 2 * rank + 1
  | PositiveLTL.release _ _ => 2 * rank
  | _ => 2 * rank

theorem alternatingPriority_until_not_even {AP : Type u}
    (root φ ψ : PositiveLTL AP) :
    ¬ DetParityAutomaton.NatEven
      (PositiveLTL.alternatingPriority root (PositiveLTL.until φ ψ)) := by
  intro h
  rcases h with ⟨m, hm⟩
  simp [alternatingPriority] at hm
  omega

theorem alternatingPriority_release_even {AP : Type u}
    (root φ ψ : PositiveLTL AP) :
    DetParityAutomaton.NatEven
      (PositiveLTL.alternatingPriority root (PositiveLTL.release φ ψ)) := by
  refine ⟨root.size - (PositiveLTL.release φ ψ).size, ?_⟩
  simp [alternatingPriority]

theorem alternatingPriority_verum_even {AP : Type u}
    (root : PositiveLTL AP) :
    DetParityAutomaton.NatEven
      (PositiveLTL.alternatingPriority root PositiveLTL.verum) := by
  refine ⟨root.size - (PositiveLTL.verum : PositiveLTL AP).size, ?_⟩
  simp [alternatingPriority]

theorem alternatingPriority_falsum_even {AP : Type u}
    (root : PositiveLTL AP) :
    DetParityAutomaton.NatEven
      (PositiveLTL.alternatingPriority root PositiveLTL.falsum) := by
  refine ⟨root.size - (PositiveLTL.falsum : PositiveLTL AP).size, ?_⟩
  simp [alternatingPriority]

theorem alternatingPriority_lit_even {AP : Type u}
    (root : PositiveLTL AP)
    (literal : LTLLiteral AP) :
    DetParityAutomaton.NatEven
      (PositiveLTL.alternatingPriority root (PositiveLTL.lit literal)) := by
  refine ⟨root.size - (PositiveLTL.lit literal).size, ?_⟩
  simp [alternatingPriority]

theorem alternatingPriority_conj_even {AP : Type u}
    (root φ ψ : PositiveLTL AP) :
    DetParityAutomaton.NatEven
      (PositiveLTL.alternatingPriority root (PositiveLTL.conj φ ψ)) := by
  refine ⟨root.size - (PositiveLTL.conj φ ψ).size, ?_⟩
  simp [alternatingPriority]

theorem alternatingPriority_disj_even {AP : Type u}
    (root φ ψ : PositiveLTL AP) :
    DetParityAutomaton.NatEven
      (PositiveLTL.alternatingPriority root (PositiveLTL.disj φ ψ)) := by
  refine ⟨root.size - (PositiveLTL.disj φ ψ).size, ?_⟩
  simp [alternatingPriority]

theorem alternatingPriority_next_even {AP : Type u}
    (root φ : PositiveLTL AP) :
    DetParityAutomaton.NatEven
      (PositiveLTL.alternatingPriority root (PositiveLTL.next φ)) := by
  refine ⟨root.size - (PositiveLTL.next φ).size, ?_⟩
  simp [alternatingPriority]

theorem alternatingPriority_even_of_not_until {AP : Type u}
    (root state : PositiveLTL AP)
    (hnotUntil : ∀ φ ψ : PositiveLTL AP, state ≠ PositiveLTL.until φ ψ) :
    DetParityAutomaton.NatEven
      (PositiveLTL.alternatingPriority root state) := by
  cases state with
  | verum => exact alternatingPriority_verum_even root
  | falsum => exact alternatingPriority_falsum_even root
  | lit literal => exact alternatingPriority_lit_even root literal
  | conj φ ψ => exact alternatingPriority_conj_even root φ ψ
  | disj φ ψ => exact alternatingPriority_disj_even root φ ψ
  | next φ => exact alternatingPriority_next_even root φ
  | «until» φ ψ => exact False.elim (hnotUntil φ ψ rfl)
  | «release» φ ψ => exact alternatingPriority_release_even root φ ψ

theorem alternatingPriority_even_iff_not_until {AP : Type u}
    (root state : PositiveLTL AP) :
    DetParityAutomaton.NatEven
        (PositiveLTL.alternatingPriority root state) ↔
      ∀ φ ψ : PositiveLTL AP, state ≠ PositiveLTL.until φ ψ := by
  constructor
  · intro heven φ ψ hstate
    subst state
    exact alternatingPriority_until_not_even root φ ψ heven
  · intro hnotUntil
    exact alternatingPriority_even_of_not_until root state hnotUntil

theorem alternatingPriority_not_even_iff_until {AP : Type u}
    (root state : PositiveLTL AP) :
    ¬ DetParityAutomaton.NatEven
        (PositiveLTL.alternatingPriority root state) ↔
      ∃ φ ψ : PositiveLTL AP, state = PositiveLTL.until φ ψ := by
  constructor
  · intro hnotEven
    by_contra hnotUntilExists
    exact hnotEven
      (PositiveLTL.alternatingPriority_even_of_not_until
        root state
        (fun φ ψ hstate =>
          hnotUntilExists ⟨φ, ψ, hstate⟩))
  · intro h
    rcases h with ⟨φ, ψ, hstate⟩
    subst state
    exact PositiveLTL.alternatingPriority_until_not_even root φ ψ

/--
For subformulas of a fixed root, strictly smaller formula size means strictly
larger canonical priority.  Thus an outer temporal obligation dominates all of
its proper subformula obligations in the minimum-priority acceptance order.
-/
theorem alternatingPriority_lt_of_size_lt {AP : Type u}
    (root state child : PositiveLTL AP)
    (hstateRoot : state.size ≤ root.size)
    (hchildState : child.size < state.size) :
    PositiveLTL.alternatingPriority root state <
      PositiveLTL.alternatingPriority root child := by
  cases state <;> cases child <;> simp [alternatingPriority] <;> omega

theorem alternatingPriority_lt_of_proper_subformula {AP : Type u}
    {root state child : PositiveLTL AP}
    (hstateRoot : state ∈ root.subformulas)
    (hchildState : child.size < state.size) :
    PositiveLTL.alternatingPriority root state <
      PositiveLTL.alternatingPriority root child :=
  alternatingPriority_lt_of_size_lt root state child
    (PositiveLTL.size_le_of_mem_subformulas hstateRoot)
    hchildState

private theorem eval_subformulaPmap
    {AP : Type u}
    {Letter : Type v}
    (interp : AP -> Letter -> Prop)
    (word : OmegaWord Letter)
    (root : PositiveLTL AP)
    (step : PosBool (PositiveLTL AP))
    (hclosed : ∀ ψ, ψ ∈ step.atoms -> ψ ∈ root.subformulas) :
    PosBool.Eval
        (fun nextState : root.Subformula =>
          PositiveLTL.Satisfies interp word nextState.1)
        (step.pmap (fun ψ h => ⟨ψ, hclosed ψ h⟩)) ↔
      PosBool.Eval
        (fun ψ => PositiveLTL.Satisfies interp word ψ)
        step := by
  induction step with
  | verum => simp [PosBool.pmap, PosBool.Eval]
  | falsum => simp [PosBool.pmap, PosBool.Eval]
  | atom ψ => simp [PosBool.pmap, PosBool.Eval]
  | conj φ ψ ihφ ihψ =>
      simpa [PosBool.pmap, PosBool.Eval, ihφ, ihψ]
  | disj φ ψ ihφ ihψ =>
      simpa [PosBool.pmap, PosBool.Eval, ihφ, ihψ]

/--
Extract raw-formula witnesses from a subformula-closure transition.

This is the direction needed for reverse APA soundness: a transition that is
true over subtype states gives a raw tableau transition true over formulas,
where each selected formula carries some proof that it belongs to the root
closure.
-/
private theorem eval_exists_subformula_of_eval_pmap
    {AP : Type u}
    (root : PositiveLTL AP)
    (step : PosBool (PositiveLTL AP))
    (hclosed : ∀ ψ, ψ ∈ step.atoms -> ψ ∈ root.subformulas)
    (valuation : root.Subformula -> Prop) :
    PosBool.Eval
        valuation
        (step.pmap (fun ψ h => ⟨ψ, hclosed ψ h⟩)) ->
      PosBool.Eval
        (fun ψ => ∃ hψ : ψ ∈ root.subformulas, valuation ⟨ψ, hψ⟩)
        step := by
  induction step with
  | verum =>
      intro _
      simp [PosBool.Eval]
  | falsum =>
      intro hfalse
      exact False.elim hfalse
  | atom ψ =>
      intro hψ
      refine ⟨hclosed ψ (by simp [PosBool.atoms]), ?_⟩
      simpa [PosBool.pmap, PosBool.Eval] using hψ
  | conj φ ψ ihφ ihψ =>
      intro hconj
      constructor
      · exact
          ihφ
            (fun atom hmem => hclosed atom (by simp [PosBool.atoms, hmem]))
            (by simpa [PosBool.pmap, PosBool.Eval] using hconj.1)
      · exact
          ihψ
            (fun atom hmem => hclosed atom (by simp [PosBool.atoms, hmem]))
            (by simpa [PosBool.pmap, PosBool.Eval] using hconj.2)
  | disj φ ψ ihφ ihψ =>
      intro hdisj
      rcases hdisj with hφ | hψ
      · exact
          Or.inl
            (ihφ
              (fun atom hmem => hclosed atom (by simp [PosBool.atoms, hmem]))
              (by simpa [PosBool.pmap, PosBool.Eval] using hφ))
      · exact
          Or.inr
            (ihψ
              (fun atom hmem => hclosed atom (by simp [PosBool.atoms, hmem]))
              (by simpa [PosBool.pmap, PosBool.Eval] using hψ))

/-- The concrete finite transition on the subformula closure of a root formula. -/
noncomputable def subformulaTransition
    {AP : Type u}
    {Letter : Type v}
    (root : PositiveLTL AP)
    (interp : AP -> Letter -> Prop)
    [∀ ap letter, Decidable (interp ap letter)]
    (state : root.Subformula)
    (letter : Letter) :
    PosBool root.Subformula :=
  let step := alternatingStep interp letter state.1
  step.pmap (fun ψ h =>
    ⟨ψ,
      subformulas_trans
        (alternatingStep_atoms_subformulas interp letter state.1 ψ h)
        state.2⟩)

/--
Every successor state of the restricted subformula transition either is the
source state itself or denotes a strict subformula of the source.
-/
theorem subformulaTransition_atoms_self_or_size_lt
    {AP : Type u}
    {Letter : Type v}
    (root : PositiveLTL AP)
    (interp : AP -> Letter -> Prop)
    [∀ ap letter, Decidable (interp ap letter)]
    (state next : root.Subformula)
    (letter : Letter)
    (hmem : next ∈ (subformulaTransition root interp state letter).atoms) :
    next.1 = state.1 ∨ next.1.size < state.1.size := by
  unfold subformulaTransition at hmem
  let step := alternatingStep interp letter state.1
  let embed : ∀ ψ, ψ ∈ step.atoms -> root.Subformula :=
    fun ψ h =>
      ⟨ψ,
        subformulas_trans
          (alternatingStep_atoms_subformulas interp letter state.1 ψ h)
          state.2⟩
  change next ∈ (step.pmap embed).atoms at hmem
  rcases PosBool.mem_atoms_pmap step embed hmem with ⟨ψ, hψ, hnext⟩
  have hnextDenote : next.1 = ψ := by
    rw [hnext]
  rcases alternatingStep_atoms_self_or_size_lt interp letter state.1 ψ hψ with
    hself | hlt
  · left
    rw [hnextDenote, hself]
  · right
    rw [hnextDenote]
    exact hlt

/--
Progress-guided support for an `until` transition.

If the right side already holds at the current letter, the selected support
takes the right disjunct and cannot contain the `until` self-loop.  Otherwise
the self-loop is selected together with the left-side obligations, and the
next-suffix `until` obligation is justified by the semantic unfolding law.
-/
theorem until_guided_transition_support
    {AP : Type u}
    {Letter : Type v}
    (interp : AP -> Letter -> Prop)
    [∀ ap letter, Decidable (interp ap letter)]
    (word : OmegaWord Letter)
    (φ ψ : PositiveLTL AP)
    (hsat : Satisfies interp word (PositiveLTL.until φ ψ)) :
    ∃ support : List (PositiveLTL AP),
      (∀ θ, θ ∈ support ->
        Satisfies interp (OmegaWord.drop word 1) θ) ∧
        (∀ θ, θ ∈ support ->
          θ ∈ (alternatingStep interp (word 0) (PositiveLTL.until φ ψ)).atoms) ∧
          PosBool.Eval
            (fun θ => θ ∈ support)
            (alternatingStep interp (word 0) (PositiveLTL.until φ ψ)) ∧
            (PositiveLTL.until φ ψ ∈ support ->
              ¬ Satisfies interp word ψ) := by
  classical
  by_cases hψnow : Satisfies interp word ψ
  · have hstepψ :
        PosBool.Eval
          (fun θ => Satisfies interp (OmegaWord.drop word 1) θ)
          (alternatingStep interp (word 0) ψ) :=
      (alternatingStep_correct interp word ψ).mpr hψnow
    rcases
      (PosBool.eval_iff_exists_support_subset_atoms
        (fun θ => Satisfies interp (OmegaWord.drop word 1) θ)
        (alternatingStep interp (word 0) ψ)).mp hstepψ with
      ⟨support, hsupport, hatomsψ, hevalψ⟩
    refine ⟨support, hsupport, ?_, ?_, ?_⟩
    · intro θ hθ
      simp [alternatingStep, PosBool.atoms]
      exact Or.inl (hatomsψ θ hθ)
    · simp [alternatingStep, PosBool.Eval]
      exact Or.inl hevalψ
    · intro hself
      have hselfAtom :
          PositiveLTL.until φ ψ ∈ (alternatingStep interp (word 0) ψ).atoms :=
        hatomsψ (PositiveLTL.until φ ψ) hself
      rcases
        alternatingStep_atoms_self_or_size_lt
          interp (word 0) ψ (PositiveLTL.until φ ψ) hselfAtom with
        hsame | hlt
      · have hsize : (PositiveLTL.until φ ψ).size = ψ.size := by
          simpa [hsame]
        have hψlt : ψ.size < (PositiveLTL.until φ ψ).size :=
          PositiveLTL.size_lt_until_right φ ψ
        omega
      · have hψlt : ψ.size < (PositiveLTL.until φ ψ).size :=
          PositiveLTL.size_lt_until_right φ ψ
        omega
  · have hunfold :=
      (satisfies_until_unfold interp word φ ψ).mp hsat
    rcases hunfold with hψ | hcontinue
    · exact False.elim (hψnow hψ)
    · rcases hcontinue with ⟨hφnow, hnext⟩
      have hstepφ :
          PosBool.Eval
            (fun θ => Satisfies interp (OmegaWord.drop word 1) θ)
            (alternatingStep interp (word 0) φ) :=
        (alternatingStep_correct interp word φ).mpr hφnow
      rcases
        (PosBool.eval_iff_exists_support_subset_atoms
          (fun θ => Satisfies interp (OmegaWord.drop word 1) θ)
          (alternatingStep interp (word 0) φ)).mp hstepφ with
        ⟨supportφ, hsupportφ, hatomsφ, hevalφ⟩
      refine
        ⟨supportφ ++ [PositiveLTL.until φ ψ], ?_, ?_, ?_, ?_⟩
      · intro θ hθ
        rw [List.mem_append] at hθ
        rcases hθ with hθ | hθ
        · exact hsupportφ θ hθ
        · simp at hθ
          subst θ
          exact hnext
      · intro θ hθ
        rw [List.mem_append] at hθ
        simp [alternatingStep, PosBool.atoms]
        rcases hθ with hθ | hθ
        · exact Or.inr (Or.inl (hatomsφ θ hθ))
        · simp at hθ
          subst θ
          exact Or.inr (Or.inr rfl)
      · change
          PosBool.Eval
            (fun θ => θ ∈ supportφ ++ [PositiveLTL.until φ ψ])
            (PosBool.disj
              (alternatingStep interp (word 0) ψ)
              (PosBool.conj
                (alternatingStep interp (word 0) φ)
                (PosBool.atom (PositiveLTL.until φ ψ))))
        exact
          Or.inr
            ⟨PosBool.eval_mono
                (fun θ hθ => by
                  rw [List.mem_append]
                  exact Or.inl hθ)
                (alternatingStep interp (word 0) φ)
                hevalφ,
              by simp [PosBool.Eval]⟩
      · intro _
        exact hψnow

/--
Progress-guided support for a `release` transition.

The selected support always satisfies the right-side obligation now.  If the
left side does not already close the release obligation at the current suffix,
the support contains the `release` self-loop, justified by the semantic
unfolding law.
-/
theorem release_guided_transition_support
    {AP : Type u}
    {Letter : Type v}
    (interp : AP -> Letter -> Prop)
    [∀ ap letter, Decidable (interp ap letter)]
    (word : OmegaWord Letter)
    (φ ψ : PositiveLTL AP)
    (hsat : Satisfies interp word (PositiveLTL.release φ ψ)) :
    ∃ support : List (PositiveLTL AP),
      (∀ θ, θ ∈ support ->
        Satisfies interp (OmegaWord.drop word 1) θ) ∧
        (∀ θ, θ ∈ support ->
          θ ∈ (alternatingStep interp (word 0) (PositiveLTL.release φ ψ)).atoms) ∧
          PosBool.Eval
            (fun θ => θ ∈ support)
            (alternatingStep interp (word 0) (PositiveLTL.release φ ψ)) ∧
            (¬ Satisfies interp word φ ->
              PositiveLTL.release φ ψ ∈ support) ∧
              (PositiveLTL.release φ ψ ∈ support ->
                ¬ Satisfies interp word φ) := by
  classical
  have hunfold :=
    (satisfies_release_unfold interp word φ ψ).mp hsat
  rcases hunfold with ⟨hψnow, hφnowOrNext⟩
  have hstepψ :
      PosBool.Eval
        (fun θ => Satisfies interp (OmegaWord.drop word 1) θ)
        (alternatingStep interp (word 0) ψ) :=
    (alternatingStep_correct interp word ψ).mpr hψnow
  rcases
    (PosBool.eval_iff_exists_support_subset_atoms
      (fun θ => Satisfies interp (OmegaWord.drop word 1) θ)
      (alternatingStep interp (word 0) ψ)).mp hstepψ with
    ⟨supportψ, hsupportψ, hatomsψ, hevalψ⟩
  by_cases hφnow : Satisfies interp word φ
  · have hstepφ :
        PosBool.Eval
          (fun θ => Satisfies interp (OmegaWord.drop word 1) θ)
          (alternatingStep interp (word 0) φ) :=
      (alternatingStep_correct interp word φ).mpr hφnow
    rcases
      (PosBool.eval_iff_exists_support_subset_atoms
        (fun θ => Satisfies interp (OmegaWord.drop word 1) θ)
        (alternatingStep interp (word 0) φ)).mp hstepφ with
      ⟨supportφ, hsupportφ, hatomsφ, hevalφ⟩
    refine
      ⟨supportψ ++ supportφ, ?_, ?_, ?_, ?_, ?_⟩
    · intro θ hθ
      rw [List.mem_append] at hθ
      rcases hθ with hθ | hθ
      · exact hsupportψ θ hθ
      · exact hsupportφ θ hθ
    · intro θ hθ
      rw [List.mem_append] at hθ
      simp [alternatingStep, PosBool.atoms]
      rcases hθ with hθ | hθ
      · exact Or.inl (hatomsψ θ hθ)
      · exact Or.inr (Or.inl (hatomsφ θ hθ))
    · change
        PosBool.Eval
          (fun θ => θ ∈ supportψ ++ supportφ)
          (PosBool.conj
            (alternatingStep interp (word 0) ψ)
            (PosBool.disj
              (alternatingStep interp (word 0) φ)
              (PosBool.atom (PositiveLTL.release φ ψ))))
      exact
        ⟨PosBool.eval_mono
            (fun θ hθ => by
              rw [List.mem_append]
              exact Or.inl hθ)
            (alternatingStep interp (word 0) ψ)
            hevalψ,
          Or.inl
            (PosBool.eval_mono
              (fun θ hθ => by
                rw [List.mem_append]
                exact Or.inr hθ)
              (alternatingStep interp (word 0) φ)
              hevalφ)⟩
    · intro hnotφ
      exact False.elim (hnotφ hφnow)
    · intro hself _hφ
      rw [List.mem_append] at hself
      rcases hself with hselfψ | hselfφ
      · have hatom := hatomsψ (PositiveLTL.release φ ψ) hselfψ
        rcases
          PositiveLTL.alternatingStep_atoms_self_or_size_lt
            interp (word 0) ψ (PositiveLTL.release φ ψ) hatom with
          hsame | hlt
        · have hright := PositiveLTL.size_lt_release_right φ ψ
          have hsize :
              (PositiveLTL.release φ ψ).size = ψ.size :=
            congrArg PositiveLTL.size hsame
          rw [hsize] at hright
          exact Nat.lt_irrefl _ hright
        · exact (Nat.lt_asymm hlt (PositiveLTL.size_lt_release_right φ ψ))
      · have hatom := hatomsφ (PositiveLTL.release φ ψ) hselfφ
        rcases
          PositiveLTL.alternatingStep_atoms_self_or_size_lt
            interp (word 0) φ (PositiveLTL.release φ ψ) hatom with
          hsame | hlt
        · have hleft := PositiveLTL.size_lt_release_left φ ψ
          have hsize :
              (PositiveLTL.release φ ψ).size = φ.size :=
            congrArg PositiveLTL.size hsame
          rw [hsize] at hleft
          exact Nat.lt_irrefl _ hleft
        · exact (Nat.lt_asymm hlt (PositiveLTL.size_lt_release_left φ ψ))
  · refine
      ⟨supportψ ++ [PositiveLTL.release φ ψ], ?_, ?_, ?_, ?_, ?_⟩
    have hnext :
        Satisfies interp (OmegaWord.drop word 1)
          (PositiveLTL.release φ ψ) := by
      rcases hφnowOrNext with hφ | hnext
      · exact False.elim (hφnow hφ)
      · exact hnext
    · intro θ hθ
      rw [List.mem_append] at hθ
      rcases hθ with hθ | hθ
      · exact hsupportψ θ hθ
      · simp at hθ
        subst θ
        exact hnext
    · intro θ hθ
      rw [List.mem_append] at hθ
      simp [alternatingStep, PosBool.atoms]
      rcases hθ with hθ | hθ
      · exact Or.inl (hatomsψ θ hθ)
      · simp at hθ
        subst θ
        exact Or.inr (Or.inr rfl)
    · change
        PosBool.Eval
          (fun θ => θ ∈ supportψ ++ [PositiveLTL.release φ ψ])
          (PosBool.conj
            (alternatingStep interp (word 0) ψ)
            (PosBool.disj
              (alternatingStep interp (word 0) φ)
              (PosBool.atom (PositiveLTL.release φ ψ))))
      exact
        ⟨PosBool.eval_mono
            (fun θ hθ => by
              rw [List.mem_append]
              exact Or.inl hθ)
            (alternatingStep interp (word 0) ψ)
            hevalψ,
          Or.inr (by simp [PosBool.Eval])⟩
    · intro _hnotφ
      simp
    · intro _hself
      exact hφnow

end PositiveLTL

/--
A finite closure of positive LTL formulas sufficient for the alternating
transition construction.
-/
structure FiniteLTLAlternatingClosure
    (AP : Type u)
    (Letter : Type v)
    where
  Carrier : Type w
  carrierFinite : Fintype Carrier
  formula : PositiveLTL AP
  denote : Carrier -> PositiveLTL AP
  initial : Carrier
  initial_denote : denote initial = formula
  priority : Carrier -> Nat
  transition :
    (interp : AP -> Letter -> Prop) ->
      (∀ ap letter, Decidable (interp ap letter)) ->
        Carrier -> Letter -> PosBool Carrier
  step_correct :
    ∀ (interp : AP -> Letter -> Prop)
      (dec : ∀ ap letter, Decidable (interp ap letter))
      (state : Carrier)
      (word : OmegaWord Letter),
      PosBool.Eval
          (fun nextState =>
            PositiveLTL.Satisfies interp (OmegaWord.drop word 1) (denote nextState))
          (transition interp dec state (word 0)) ↔
        PositiveLTL.Satisfies interp word (denote state)

attribute [instance] FiniteLTLAlternatingClosure.carrierFinite

/-- Turn a finite LTL closure certificate into an alternating parity automaton. -/
noncomputable def FiniteLTLAlternatingClosure.toAPA
    {AP : Type u}
    {Letter : Type v}
    (closure : FiniteLTLAlternatingClosure.{u, v, w} AP Letter)
    (interp : AP -> Letter -> Prop)
    (dec : ∀ ap letter, Decidable (interp ap letter)) :
    AlternatingParityAutomaton Letter where
  State := closure.Carrier
  stateFinite := closure.carrierFinite
  initial := closure.initial
  step := closure.transition interp dec
  priority := closure.priority

/--
The canonical local language of closure states: a state accepts exactly the
words satisfying the formula it denotes.
-/
def FiniteLTLAlternatingClosure.language
    {AP : Type u}
    {Letter : Type v}
    (closure : FiniteLTLAlternatingClosure.{u, v, w} AP Letter)
    (interp : AP -> Letter -> Prop)
    (state : closure.Carrier) :
    Set (OmegaWord Letter) :=
  { word | PositiveLTL.Satisfies interp word (closure.denote state) }

/-- The alternating automaton generated by a closure certificate has the expected step equation. -/
theorem FiniteLTLAlternatingClosure.toAPA_stepEquation
    {AP : Type u}
    {Letter : Type v}
    (closure : FiniteLTLAlternatingClosure.{u, v, w} AP Letter)
    (interp : AP -> Letter -> Prop)
    (dec : ∀ ap letter, Decidable (interp ap letter)) :
    (closure.toAPA interp dec).StepEquation (closure.language interp) := by
  intro state word
  exact closure.step_correct interp dec state word

/--
If a closure state is semantically satisfied, its symbolic transition has a
finite support of successor states that are semantically satisfied on the
suffix word.
-/
theorem FiniteLTLAlternatingClosure.exists_transition_support_of_satisfies
    {AP : Type u}
    {Letter : Type v}
    (closure : FiniteLTLAlternatingClosure.{u, v, w} AP Letter)
    (interp : AP -> Letter -> Prop)
    (dec : ∀ ap letter, Decidable (interp ap letter))
    (state : closure.Carrier)
    (word : OmegaWord Letter)
    (hsat : PositiveLTL.Satisfies interp word (closure.denote state)) :
    ∃ support : List closure.Carrier,
      (∀ nextState, nextState ∈ support ->
        PositiveLTL.Satisfies
          interp (OmegaWord.drop word 1) (closure.denote nextState)) ∧
        PosBool.Eval
          (fun nextState => nextState ∈ support)
          (closure.transition interp dec state (word 0)) := by
  have hstep :
      PosBool.Eval
        (fun nextState =>
          PositiveLTL.Satisfies
            interp (OmegaWord.drop word 1) (closure.denote nextState))
        (closure.transition interp dec state (word 0)) :=
    (closure.step_correct interp dec state word).mpr hsat
  exact
    ((closure.toAPA interp dec).step_exists_support
      (fun nextState =>
        PositiveLTL.Satisfies
          interp (OmegaWord.drop word 1) (closure.denote nextState))
      state (word 0) hstep)

/--
Numbered-child form of `exists_transition_support_of_satisfies`, matching the
successor valuation used in APA run trees.
-/
theorem FiniteLTLAlternatingClosure.exists_numbered_transition_children_of_satisfies
    {AP : Type u}
    {Letter : Type v}
    (closure : FiniteLTLAlternatingClosure.{u, v, w} AP Letter)
    (interp : AP -> Letter -> Prop)
    (dec : ∀ ap letter, Decidable (interp ap letter))
    (state : closure.Carrier)
    (word : OmegaWord Letter)
    (hsat : PositiveLTL.Satisfies interp word (closure.denote state)) :
    ∃ support : List closure.Carrier,
      (∀ nextState, nextState ∈ support ->
        PositiveLTL.Satisfies
          interp (OmegaWord.drop word 1) (closure.denote nextState)) ∧
        PosBool.Eval
          (fun nextState =>
            ∃ child : Nat,
              (∃ childState : closure.Carrier, support[child]? = some childState) ∧
                (support[child]?).getD closure.initial = nextState)
          (closure.transition interp dec state (word 0)) := by
  rcases
    closure.exists_transition_support_of_satisfies
      interp dec state word hsat with
    ⟨support, hsupport, hstep⟩
  refine ⟨support, hsupport, ?_⟩
  exact
    (closure.toAPA interp dec).step_support_as_numbered_children
      support (closure.transition interp dec state (word 0)) hstep

/--
Satisfied closure states have a local APA run-tree expansion whose active
children remain semantically satisfied on the suffix word.
-/
theorem FiniteLTLAlternatingClosure.exists_satisfying_stepExpansion
    {AP : Type u}
    {Letter : Type v}
    (closure : FiniteLTLAlternatingClosure.{u, v, w} AP Letter)
    (interp : AP -> Letter -> Prop)
    (dec : ∀ ap letter, Decidable (interp ap letter))
    (state : closure.Carrier)
    (word : OmegaWord Letter)
    (hsat : PositiveLTL.Satisfies interp word (closure.denote state)) :
    ∃ expansion :
      (closure.toAPA interp dec).StepExpansion state (word 0),
      ∀ child,
        expansion.childActive child ->
          PositiveLTL.Satisfies
            interp (OmegaWord.drop word 1) (closure.denote (expansion.childState child)) := by
  have hstep :
      PosBool.Eval
        (fun nextState =>
          PositiveLTL.Satisfies
            interp (OmegaWord.drop word 1) (closure.denote nextState))
        (closure.transition interp dec state (word 0)) := by
    exact (closure.step_correct interp dec state word).mpr hsat
  exact
    (closure.toAPA interp dec).step_exists_expansion
      (fun nextState =>
        PositiveLTL.Satisfies
          interp (OmegaWord.drop word 1) (closure.denote nextState))
      state (word 0) hstep

/--
Satisfied closure states have an exact local APA run-tree expansion: every
active child is one of the actual atoms of the symbolic transition formula.
-/
theorem FiniteLTLAlternatingClosure.exists_satisfying_exactStepExpansion
    {AP : Type u}
    {Letter : Type v}
    (closure : FiniteLTLAlternatingClosure.{u, v, w} AP Letter)
    (interp : AP -> Letter -> Prop)
    (dec : ∀ ap letter, Decidable (interp ap letter))
    (state : closure.Carrier)
    (word : OmegaWord Letter)
    (hsat : PositiveLTL.Satisfies interp word (closure.denote state)) :
    ∃ expansion :
      (closure.toAPA interp dec).ExactStepExpansion state (word 0),
      ∀ child,
        expansion.childActive child ->
          PositiveLTL.Satisfies
            interp (OmegaWord.drop word 1) (closure.denote (expansion.childState child)) := by
  have hstep :
      PosBool.Eval
        (fun nextState =>
          PositiveLTL.Satisfies
            interp (OmegaWord.drop word 1) (closure.denote nextState))
        (closure.transition interp dec state (word 0)) :=
    (closure.step_correct interp dec state word).mpr hsat
  exact
    (closure.toAPA interp dec).step_exists_exact_expansion
      (fun nextState =>
        PositiveLTL.Satisfies
          interp (OmegaWord.drop word 1) (closure.denote nextState))
      state (word 0) hstep

/--
Finite-node data for the canonical run generated from a semantically satisfied
closure state.  The Boolean component is the active-node predicate; whenever it
is true, the stored state satisfies the formula denoted by that state at the
corresponding suffix.
-/
noncomputable def FiniteLTLAlternatingClosure.satisfyingRunNodeData
    {AP : Type u}
    {Letter : Type v}
    (closure : FiniteLTLAlternatingClosure.{u, v, w} AP Letter)
    (interp : AP -> Letter -> Prop)
    (dec : ∀ ap letter, Decidable (interp ap letter))
    (word : OmegaWord Letter)
    (hsatInitial :
      PositiveLTL.Satisfies interp word (closure.denote closure.initial)) :
    (node : AlternatingParityAutomaton.Node) ->
      { data : closure.Carrier × Prop //
        data.2 ->
          PositiveLTL.Satisfies
            interp (OmegaWord.drop word node.length) (closure.denote data.1) }
  | [] =>
      ⟨(closure.initial, True), by
        intro _
        simpa using hsatInitial⟩
  | child :: node =>
      let parent :=
        closure.satisfyingRunNodeData interp dec word hsatInitial node
      haveI : Decidable parent.1.2 := Classical.propDecidable parent.1.2
      if hparent : parent.1.2 then
        let existsExpansion :=
          closure.exists_satisfying_exactStepExpansion
            interp dec parent.1.1 (OmegaWord.drop word node.length)
            (parent.2 hparent)
        let expansion :=
          Classical.choose existsExpansion
        ⟨(expansion.childState child, expansion.childActive child), by
          intro hchild
          have hspec :
              ∀ child,
                expansion.childActive child ->
                  PositiveLTL.Satisfies
                    interp
                    (OmegaWord.drop (OmegaWord.drop word node.length) 1)
                    (closure.denote (expansion.childState child)) :=
            Classical.choose_spec existsExpansion
          have hsatChild := hspec child hchild
          simpa [OmegaWord.drop_drop, Nat.add_comm, Nat.add_assoc] using hsatChild⟩
      else
        ⟨(closure.initial, False), by
          intro hfalse
          exact False.elim hfalse⟩

noncomputable def FiniteLTLAlternatingClosure.satisfyingRunActive
    {AP : Type u}
    {Letter : Type v}
    (closure : FiniteLTLAlternatingClosure.{u, v, w} AP Letter)
    (interp : AP -> Letter -> Prop)
    (dec : ∀ ap letter, Decidable (interp ap letter))
    (word : OmegaWord Letter)
    (hsatInitial :
      PositiveLTL.Satisfies interp word (closure.denote closure.initial))
    (node : AlternatingParityAutomaton.Node) :
    Prop :=
  (closure.satisfyingRunNodeData interp dec word hsatInitial node).1.2

noncomputable def FiniteLTLAlternatingClosure.satisfyingRunState
    {AP : Type u}
    {Letter : Type v}
    (closure : FiniteLTLAlternatingClosure.{u, v, w} AP Letter)
    (interp : AP -> Letter -> Prop)
    (dec : ∀ ap letter, Decidable (interp ap letter))
    (word : OmegaWord Letter)
    (hsatInitial :
      PositiveLTL.Satisfies interp word (closure.denote closure.initial))
    (node : AlternatingParityAutomaton.Node) :
    closure.Carrier :=
  (closure.satisfyingRunNodeData interp dec word hsatInitial node).1.1

theorem FiniteLTLAlternatingClosure.satisfyingRun_root_active
    {AP : Type u}
    {Letter : Type v}
    (closure : FiniteLTLAlternatingClosure.{u, v, w} AP Letter)
    (interp : AP -> Letter -> Prop)
    (dec : ∀ ap letter, Decidable (interp ap letter))
    (word : OmegaWord Letter)
    (hsatInitial :
      PositiveLTL.Satisfies interp word (closure.denote closure.initial)) :
    closure.satisfyingRunActive interp dec word hsatInitial [] := by
  simp [satisfyingRunActive, satisfyingRunNodeData]

theorem FiniteLTLAlternatingClosure.satisfyingRun_root_state
    {AP : Type u}
    {Letter : Type v}
    (closure : FiniteLTLAlternatingClosure.{u, v, w} AP Letter)
    (interp : AP -> Letter -> Prop)
    (dec : ∀ ap letter, Decidable (interp ap letter))
    (word : OmegaWord Letter)
    (hsatInitial :
      PositiveLTL.Satisfies interp word (closure.denote closure.initial)) :
    closure.satisfyingRunState interp dec word hsatInitial [] = closure.initial := by
  simp [satisfyingRunState, satisfyingRunNodeData]

theorem FiniteLTLAlternatingClosure.satisfyingRun_step_satisfied
    {AP : Type u}
    {Letter : Type v}
    (closure : FiniteLTLAlternatingClosure.{u, v, w} AP Letter)
    (interp : AP -> Letter -> Prop)
    (dec : ∀ ap letter, Decidable (interp ap letter))
    (word : OmegaWord Letter)
    (hsatInitial :
      PositiveLTL.Satisfies interp word (closure.denote closure.initial))
    (node : AlternatingParityAutomaton.Node)
    (hactive :
      closure.satisfyingRunActive interp dec word hsatInitial node) :
    PosBool.Eval
      (fun nextState =>
        ∃ child : Nat,
          closure.satisfyingRunActive interp dec word hsatInitial (child :: node) ∧
            closure.satisfyingRunState interp dec word hsatInitial (child :: node) =
              nextState)
        ((closure.toAPA interp dec).step
          (closure.satisfyingRunState interp dec word hsatInitial node)
          (word node.length)) := by
  let parent :=
    closure.satisfyingRunNodeData interp dec word hsatInitial node
  have hparent : parent.1.2 := hactive
  haveI : Decidable parent.1.2 := Classical.propDecidable parent.1.2
  let existsExpansion :=
    closure.exists_satisfying_exactStepExpansion
      interp dec parent.1.1 (OmegaWord.drop word node.length)
      (parent.2 hparent)
  let expansion := Classical.choose existsExpansion
  have htransition : expansion.step_satisfied =
      (Classical.choose existsExpansion).step_satisfied := rfl
  change
    PosBool.Eval
      (fun nextState =>
        ∃ child : Nat,
          closure.satisfyingRunActive interp dec word hsatInitial (child :: node) ∧
            closure.satisfyingRunState interp dec word hsatInitial (child :: node) =
              nextState)
      (closure.transition interp dec
        (closure.satisfyingRunState interp dec word hsatInitial node)
        (word node.length))
  change
    PosBool.Eval
      (fun nextState =>
        ∃ child : Nat,
          closure.satisfyingRunActive interp dec word hsatInitial (child :: node) ∧
            closure.satisfyingRunState interp dec word hsatInitial (child :: node) =
              nextState)
      (closure.transition interp dec parent.1.1 (word node.length))
  refine
    PosBool.eval_mono
      (fun nextState hnext => ?_)
      (closure.transition interp dec parent.1.1 (word node.length))
      expansion.step_satisfied
  rcases hnext with ⟨child, hchildActive, hchildState⟩
  refine ⟨child, ?_, ?_⟩
  · simpa [satisfyingRunActive, satisfyingRunNodeData, parent, hparent,
      existsExpansion, expansion] using hchildActive
  · simpa [satisfyingRunState, satisfyingRunNodeData, parent, hparent,
      existsExpansion, expansion] using hchildState

/--
In the canonical satisfying run, every active child is backed by an actual atom
of the symbolic transition chosen at its active parent.
-/
theorem FiniteLTLAlternatingClosure.satisfyingRun_child_atom
    {AP : Type u}
    {Letter : Type v}
    (closure : FiniteLTLAlternatingClosure.{u, v, w} AP Letter)
    (interp : AP -> Letter -> Prop)
    (dec : ∀ ap letter, Decidable (interp ap letter))
    (word : OmegaWord Letter)
    (hsatInitial :
      PositiveLTL.Satisfies interp word (closure.denote closure.initial))
    (node : AlternatingParityAutomaton.Node)
    (child : Nat)
    (hactiveParent :
      closure.satisfyingRunActive interp dec word hsatInitial node)
    (hactiveChild :
      closure.satisfyingRunActive interp dec word hsatInitial (child :: node)) :
    closure.satisfyingRunState interp dec word hsatInitial (child :: node) ∈
      (closure.transition interp dec
        (closure.satisfyingRunState interp dec word hsatInitial node)
        (word node.length)).atoms := by
  let parent :=
    closure.satisfyingRunNodeData interp dec word hsatInitial node
  have hparent : parent.1.2 := hactiveParent
  haveI : Decidable parent.1.2 := Classical.propDecidable parent.1.2
  let existsExpansion :=
    closure.exists_satisfying_exactStepExpansion
      interp dec parent.1.1 (OmegaWord.drop word node.length)
      (parent.2 hparent)
  let expansion := Classical.choose existsExpansion
  have hchildExpansion :
      expansion.childActive child := by
    simpa [satisfyingRunActive, satisfyingRunNodeData, parent, hparent,
      existsExpansion, expansion] using hactiveChild
  have hatom :
      expansion.childState child ∈
        (closure.transition interp dec parent.1.1 (word node.length)).atoms :=
    expansion.child_atom child hchildExpansion
  simpa [satisfyingRunState, satisfyingRunNodeData, parent, hparent,
    existsExpansion, expansion] using hatom

/--
Every active node in the canonical run generated from semantic satisfaction
still denotes a formula that is true at the suffix indexed by that node.
-/
theorem FiniteLTLAlternatingClosure.satisfyingRun_active_satisfies
    {AP : Type u}
    {Letter : Type v}
    (closure : FiniteLTLAlternatingClosure.{u, v, w} AP Letter)
    (interp : AP -> Letter -> Prop)
    (dec : ∀ ap letter, Decidable (interp ap letter))
    (word : OmegaWord Letter)
    (hsatInitial :
      PositiveLTL.Satisfies interp word (closure.denote closure.initial))
    (node : AlternatingParityAutomaton.Node)
    (hactive :
      closure.satisfyingRunActive interp dec word hsatInitial node) :
    PositiveLTL.Satisfies
      interp (OmegaWord.drop word node.length)
      (closure.denote
        (closure.satisfyingRunState interp dec word hsatInitial node)) :=
  (closure.satisfyingRunNodeData interp dec word hsatInitial node).2 hactive

/-- The run tree generated from semantic satisfaction of the initial closure state. -/
noncomputable def FiniteLTLAlternatingClosure.satisfyingRun
    {AP : Type u}
    {Letter : Type v}
    (closure : FiniteLTLAlternatingClosure.{u, v, w} AP Letter)
    (interp : AP -> Letter -> Prop)
    (dec : ∀ ap letter, Decidable (interp ap letter))
    (word : OmegaWord Letter)
    (hsatInitial :
      PositiveLTL.Satisfies interp word (closure.denote closure.initial)) :
    (closure.toAPA interp dec).Run word where
  active := closure.satisfyingRunActive interp dec word hsatInitial
  stateAt := closure.satisfyingRunState interp dec word hsatInitial
  root_active := closure.satisfyingRun_root_active interp dec word hsatInitial
  root_state := closure.satisfyingRun_root_state interp dec word hsatInitial
  step_satisfied :=
    closure.satisfyingRun_step_satisfied interp dec word hsatInitial

/--
On an active branch of the generated run, every branch state semantically
satisfies its denoted formula at the matching suffix.
-/
theorem FiniteLTLAlternatingClosure.satisfyingRun_branch_satisfies
    {AP : Type u}
    {Letter : Type v}
    (closure : FiniteLTLAlternatingClosure.{u, v, w} AP Letter)
    (interp : AP -> Letter -> Prop)
    (dec : ∀ ap letter, Decidable (interp ap letter))
    (word : OmegaWord Letter)
    (hsatInitial :
      PositiveLTL.Satisfies interp word (closure.denote closure.initial))
    (branch : Nat -> Nat)
    (hbranch :
      (closure.satisfyingRun interp dec word hsatInitial).ActiveBranch branch)
    (n : Nat) :
    PositiveLTL.Satisfies
      interp (OmegaWord.drop word n)
      (closure.denote
        ((closure.satisfyingRun interp dec word hsatInitial).stateAt
      (AlternatingParityAutomaton.branchPrefix branch n))) := by
  have hactive := hbranch n
  have hsat :=
    closure.satisfyingRun_active_satisfies
      interp dec word hsatInitial
      (AlternatingParityAutomaton.branchPrefix branch n)
      hactive
  simpa using hsat

/--
Forward semantic-to-APA acceptance reduced to the remaining parity argument:
each active branch of the generated run must have an even least recurring
priority.
-/
theorem FiniteLTLAlternatingClosure.accepts_of_initial_satisfies_of_branch_min_even
    {AP : Type u}
    {Letter : Type v}
    (closure : FiniteLTLAlternatingClosure.{u, v, w} AP Letter)
    (interp : AP -> Letter -> Prop)
    (dec : ∀ ap letter, Decidable (interp ap letter))
    (word : OmegaWord Letter)
    (hsatInitial :
      PositiveLTL.Satisfies interp word (closure.denote closure.initial))
    (hminEven :
      ∀ branch : Nat -> Nat,
        (closure.satisfyingRun interp dec word hsatInitial).ActiveBranch branch ->
          ∃ p : Nat,
            AlternatingParityAutomaton.Run.PrioritySeenInfinitelyOften
              (closure.satisfyingRun interp dec word hsatInitial) branch p ∧
              (∀ q : Nat,
                AlternatingParityAutomaton.Run.PrioritySeenInfinitelyOften
                  (closure.satisfyingRun interp dec word hsatInitial) branch q -> p ≤ q) ∧
                DetParityAutomaton.NatEven p) :
    (closure.toAPA interp dec).Accepts word := by
  refine ⟨closure.satisfyingRun interp dec word hsatInitial, ?_⟩
  exact
    AlternatingParityAutomaton.Run.accepting_of_all_min_priority_even
      (closure.satisfyingRun interp dec word hsatInitial) hminEven

/-- The initial closure state denotes the requested LTL formula. -/
theorem FiniteLTLAlternatingClosure.initial_language_iff
    {AP : Type u}
    {Letter : Type v}
    (closure : FiniteLTLAlternatingClosure.{u, v, w} AP Letter)
    (interp : AP -> Letter -> Prop)
    (word : OmegaWord Letter) :
    closure.language interp closure.initial word ↔
      PositiveLTL.Satisfies interp word closure.formula := by
  rw [FiniteLTLAlternatingClosure.language, closure.initial_denote]
  rfl

/--
The canonical language certificate induced by the semantic language of each
closure state.
-/
def FiniteLTLAlternatingClosure.languageCertificate
    {AP : Type u}
    {Letter : Type v}
    (closure : FiniteLTLAlternatingClosure.{u, v, w} AP Letter)
    (interp : AP -> Letter -> Prop)
    (dec : ∀ ap letter, Decidable (interp ap letter)) :
    (closure.toAPA interp dec).LanguageCertificate where
  language := closure.language interp
  stepEquation := closure.toAPA_stepEquation interp dec

/--
Package a state-wise run-tree semantic correctness theorem as a canonical
run-language certificate for the LTL alternating automaton.

This is the exact bridge needed by the run-semantics backend.  The remaining
mathematical obligation is the argument supplied as `hcorrect`: APA
run-acceptance from every closure state is equivalent to satisfaction of that
state's denoted formula.
-/
def FiniteLTLAlternatingClosure.runLanguageCertificateOfAcceptsFromIff
    {AP : Type u}
    {Letter : Type v}
    (closure : FiniteLTLAlternatingClosure.{u, v, w} AP Letter)
    (interp : AP -> Letter -> Prop)
    (dec : ∀ ap letter, Decidable (interp ap letter))
    (hcorrect :
      ∀ state : closure.Carrier,
        ∀ word : OmegaWord Letter,
          (closure.toAPA interp dec).AcceptsFrom state word ↔
            PositiveLTL.Satisfies interp word (closure.denote state)) :
    (closure.toAPA interp dec).RunLanguageCertificate where
  toLanguageCertificate := closure.languageCertificate interp dec
  acceptsFrom_iff := by
    intro state word
    exact hcorrect state word

/--
The state-wise correctness theorem for a run-language certificate immediately
identifies the initial accepted run language with the closure formula.
-/
theorem FiniteLTLAlternatingClosure.initialRunLanguage_iff_of_acceptsFromIff
    {AP : Type u}
    {Letter : Type v}
    (closure : FiniteLTLAlternatingClosure.{u, v, w} AP Letter)
    (interp : AP -> Letter -> Prop)
    (dec : ∀ ap letter, Decidable (interp ap letter))
    (hcorrect :
      ∀ state : closure.Carrier,
        ∀ word : OmegaWord Letter,
          (closure.toAPA interp dec).AcceptsFrom state word ↔
            PositiveLTL.Satisfies interp word (closure.denote state))
    (word : OmegaWord Letter) :
    word ∈
        (closure.runLanguageCertificateOfAcceptsFromIff
          interp dec hcorrect).toLanguageCertificate.initialLanguage ↔
      PositiveLTL.Satisfies interp word closure.formula := by
  change closure.language interp closure.initial word ↔
    PositiveLTL.Satisfies interp word closure.formula
  exact closure.initial_language_iff interp word

/--
One-step reverse soundness for an accepting closure state.

If every accepting successor state denotes a formula true on the one-letter
suffix, then acceptance from the current state implies semantic truth of the
current state's denotation.  The remaining hard part of APA soundness is making
this successor premise available across temporal self-loops.
-/
theorem FiniteLTLAlternatingClosure.acceptsFrom_satisfies_of_successors
    {AP : Type u}
    {Letter : Type v}
    (closure : FiniteLTLAlternatingClosure.{u, v, w} AP Letter)
    (interp : AP -> Letter -> Prop)
    (dec : ∀ ap letter, Decidable (interp ap letter))
    (state : closure.Carrier)
    (word : OmegaWord Letter)
    (haccepts :
      (closure.toAPA interp dec).AcceptsFrom state word)
    (hsuccessors :
      ∀ nextState : closure.Carrier,
        (closure.toAPA interp dec).AcceptsFrom
          nextState (OmegaWord.drop word 1) ->
        PositiveLTL.Satisfies
          interp (OmegaWord.drop word 1) (closure.denote nextState)) :
    PositiveLTL.Satisfies interp word (closure.denote state) := by
  have hstepAccepts :=
    (closure.toAPA interp dec).acceptsFrom_step state word haccepts
  have hstepSatisfies :
      PosBool.Eval
        (fun nextState =>
          PositiveLTL.Satisfies
            interp (OmegaWord.drop word 1) (closure.denote nextState))
        ((closure.toAPA interp dec).step state (word 0)) :=
    PosBool.eval_mono
      (fun nextState hnext => hsuccessors nextState hnext)
      ((closure.toAPA interp dec).step state (word 0))
      hstepAccepts
  exact (closure.step_correct interp dec state word).mp hstepSatisfies

/--
Atom-local one-step reverse soundness for an accepting closure state.

This is the form used by structural/temporal arguments: successor soundness is
needed only for states that actually occur as atoms of the current transition.
-/
theorem FiniteLTLAlternatingClosure.acceptsFrom_satisfies_of_atom_successors
    {AP : Type u}
    {Letter : Type v}
    (closure : FiniteLTLAlternatingClosure.{u, v, w} AP Letter)
    (interp : AP -> Letter -> Prop)
    (dec : ∀ ap letter, Decidable (interp ap letter))
    (state : closure.Carrier)
    (word : OmegaWord Letter)
    (haccepts :
      (closure.toAPA interp dec).AcceptsFrom state word)
    (hsuccessors :
      ∀ nextState : closure.Carrier,
        nextState ∈
          ((closure.toAPA interp dec).step state (word 0)).atoms ->
        (closure.toAPA interp dec).AcceptsFrom
          nextState (OmegaWord.drop word 1) ->
        PositiveLTL.Satisfies
          interp (OmegaWord.drop word 1) (closure.denote nextState)) :
    PositiveLTL.Satisfies interp word (closure.denote state) := by
  have hstepAccepts :=
    (closure.toAPA interp dec).acceptsFrom_step state word haccepts
  have hstepSatisfies :
      PosBool.Eval
        (fun nextState =>
          PositiveLTL.Satisfies
            interp (OmegaWord.drop word 1) (closure.denote nextState))
        ((closure.toAPA interp dec).step state (word 0)) :=
    PosBool.eval_mono_of_imp_on_atoms
      ((closure.toAPA interp dec).step state (word 0))
      (fun nextState hmem hnext => hsuccessors nextState hmem hnext)
      hstepAccepts
  exact (closure.step_correct interp dec state word).mp hstepSatisfies

/--
The standard finite closure for a positive LTL formula: states are exactly the
subformulas of the root formula, and transitions are the one-step alternating
LTL tableau restricted to that finite carrier.
-/
noncomputable def PositiveLTL.subformulaClosure
    {AP : Type u}
    {Letter : Type v}
    [DecidableEq AP]
    (φ : PositiveLTL AP) :
    FiniteLTLAlternatingClosure.{u, v, u} AP Letter where
  Carrier := φ.Subformula
  carrierFinite := PositiveLTL.subformulaFintype φ
  formula := φ
  denote := fun state => state.1
  initial := PositiveLTL.rootSubformula φ
  initial_denote := rfl
  priority := fun state => PositiveLTL.alternatingPriority φ state.1
  transition := fun interp dec state letter =>
    haveI := dec
    PositiveLTL.subformulaTransition φ interp state letter
  step_correct := by
    intro interp dec state word
    haveI := dec
    unfold PositiveLTL.subformulaTransition
    rw [PositiveLTL.eval_subformulaPmap]
    exact @PositiveLTL.alternatingStep_correct AP Letter interp dec word state.1

/--
Reverse soundness for accepting canonical subformula states whose transition
does not contain a self-loop atom.  In that case every accepting successor is a
strictly smaller formula, so a structural induction hypothesis is enough to
recover semantic satisfaction of the current state.
-/
theorem PositiveLTL.subformulaClosure_acceptsFrom_satisfies_of_no_self_atom
    {AP : Type u}
    {Letter : Type v}
    [DecidableEq AP]
    (root : PositiveLTL AP)
    (interp : AP -> Letter -> Prop)
    (dec : ∀ ap letter, Decidable (interp ap letter))
    (state : root.Subformula)
    (word : OmegaWord Letter)
    (haccepts :
      ((PositiveLTL.subformulaClosure (Letter := Letter) root).toAPA
        interp dec).AcceptsFrom state word)
    (hNoSelf :
      ∀ nextState : root.Subformula,
        nextState ∈
          (((PositiveLTL.subformulaClosure (Letter := Letter) root).toAPA
            interp dec).step state (word 0)).atoms ->
        nextState ≠ state)
    (hsuccessors :
      ∀ nextState : root.Subformula,
        nextState.1.size < state.1.size ->
        ((PositiveLTL.subformulaClosure (Letter := Letter) root).toAPA
          interp dec).AcceptsFrom nextState (OmegaWord.drop word 1) ->
        PositiveLTL.Satisfies interp (OmegaWord.drop word 1) nextState.1) :
    PositiveLTL.Satisfies interp word state.1 := by
  let closure := PositiveLTL.subformulaClosure (Letter := Letter) root
  exact
    closure.acceptsFrom_satisfies_of_atom_successors
      interp dec state word haccepts
      (fun nextState hmem hnextAccepts => by
        have hmemTransition :
            nextState ∈
              (PositiveLTL.subformulaTransition root interp state (word 0)).atoms := by
          simpa [closure, PositiveLTL.subformulaClosure,
            FiniteLTLAlternatingClosure.toAPA] using hmem
        have hmove :=
          PositiveLTL.subformulaTransition_atoms_self_or_size_lt
            root interp state nextState (word 0) hmemTransition
        rcases hmove with hself | hlt
        · exact False.elim (hNoSelf nextState hmem (Subtype.ext hself))
        · exact hsuccessors nextState hlt hnextAccepts)

/--
One-step semantic soundness for a concrete macro transition of the canonical
subformula APA.

If a source state is present in the macro-state at the current letter and all
states in the selected next macro-state satisfy their formulas on the suffix,
then the source state satisfies its formula now.
-/
theorem PositiveLTL.subformulaClosure_satisfies_of_macroTransition_next
    {AP : Type u}
    {Letter : Type v}
    [DecidableEq AP]
    (root : PositiveLTL AP)
    (interp : AP -> Letter -> Prop)
    (dec : ∀ ap letter, Decidable (interp ap letter))
    (word : OmegaWord Letter)
    {states nextStates :
      Finset
        (((PositiveLTL.subformulaClosure (Letter := Letter) root).toAPA
          interp dec).State)}
    {stateEdges :
      Finset
        ((((PositiveLTL.subformulaClosure (Letter := Letter) root).toAPA
            interp dec).State) ×
          (((PositiveLTL.subformulaClosure (Letter := Letter) root).toAPA
            interp dec).State))}
    (htransition :
      ((PositiveLTL.subformulaClosure (Letter := Letter) root).toAPA
        interp dec).MacroTransitionWithStateEdges
          states (word 0) nextStates stateEdges)
    {state :
      ((PositiveLTL.subformulaClosure (Letter := Letter) root).toAPA
        interp dec).State}
    (hstate : state ∈ states)
    (hnext :
      ∀ nextState, nextState ∈ nextStates ->
        PositiveLTL.Satisfies interp (OmegaWord.drop word 1) nextState.1) :
    PositiveLTL.Satisfies interp word state.1 := by
  let closure := PositiveLTL.subformulaClosure (Letter := Letter) root
  let A := closure.toAPA interp dec
  have hstep :
      PosBool.Eval
        (fun nextState : A.State => nextState ∈ nextStates)
        (A.step state (word 0)) := by
    exact htransition.eval_source hstate
  have hstepSatisfies :
      PosBool.Eval
        (fun nextState : A.State =>
          PositiveLTL.Satisfies interp (OmegaWord.drop word 1) nextState.1)
        (A.step state (word 0)) :=
    PosBool.eval_mono
      (fun nextState hnextState => hnext nextState hnextState)
      (A.step state (word 0))
      hstep
  exact (closure.step_correct interp dec state word).mp hstepSatisfies

/--
Bounded one-step semantic soundness for a concrete macro transition.

If the source formula is strictly below a size bound, then every transition
atom used by its one-step tableau is also below that bound.  Thus target
semantic truth is only needed for target states below the same bound, even
when the macro transition contains unrelated larger states contributed by
other sources.
-/
theorem PositiveLTL.subformulaClosure_satisfies_of_macroTransition_next_of_size_lt
    {AP : Type u}
    {Letter : Type v}
    [DecidableEq AP]
    (root : PositiveLTL AP)
    (interp : AP -> Letter -> Prop)
    (dec : ∀ ap letter, Decidable (interp ap letter))
    (word : OmegaWord Letter)
    {states nextStates :
      Finset
        (((PositiveLTL.subformulaClosure (Letter := Letter) root).toAPA
          interp dec).State)}
    {stateEdges :
      Finset
        ((((PositiveLTL.subformulaClosure (Letter := Letter) root).toAPA
            interp dec).State) ×
          (((PositiveLTL.subformulaClosure (Letter := Letter) root).toAPA
            interp dec).State))}
    (htransition :
      ((PositiveLTL.subformulaClosure (Letter := Letter) root).toAPA
        interp dec).MacroTransitionWithStateEdges
          states (word 0) nextStates stateEdges)
    {state :
      ((PositiveLTL.subformulaClosure (Letter := Letter) root).toAPA
        interp dec).State}
    (hstate : state ∈ states)
    {bound : Nat}
    (hsize : state.1.size < bound)
    (hnext :
      ∀ nextState, nextState ∈ nextStates ->
        nextState.1.size < bound ->
          PositiveLTL.Satisfies interp
            (OmegaWord.drop word 1) nextState.1) :
    PositiveLTL.Satisfies interp word state.1 := by
  let closure := PositiveLTL.subformulaClosure (Letter := Letter) root
  let A := closure.toAPA interp dec
  have hstep :
      PosBool.Eval
        (fun nextState : A.State => nextState ∈ nextStates)
        (A.step state (word 0)) :=
    htransition.eval_source hstate
  have hstepSatisfies :
      PosBool.Eval
        (fun nextState : A.State =>
          PositiveLTL.Satisfies interp (OmegaWord.drop word 1) nextState.1)
        (A.step state (word 0)) := by
    refine
      PosBool.eval_mono_of_imp_on_atoms
        (A.step state (word 0))
        ?_
        hstep
    intro nextState hmem hnextMem
    have hmemTransition :
        nextState ∈
          (PositiveLTL.subformulaTransition root interp state (word 0)).atoms := by
      simpa [A, closure, PositiveLTL.subformulaClosure,
        FiniteLTLAlternatingClosure.toAPA] using hmem
    have hmove :=
      PositiveLTL.subformulaTransition_atoms_self_or_size_lt
        root interp state nextState (word 0) hmemTransition
    have hnextSize : nextState.1.size < bound := by
      rcases hmove with hself | hlt
      · simpa [hself] using hsize
      · exact Nat.lt_trans hlt hsize
    exact hnext nextState hnextMem hnextSize
  exact (closure.step_correct interp dec state word).mp hstepSatisfies

/--
One-step semantic soundness for a concrete macro transition when the current
source state has no self atom in its tableau step.

This is the macro-transition analogue of
`subformulaClosure_acceptsFrom_satisfies_of_no_self_atom`: every selected atom
of the source step is then strictly smaller, so a structural induction
hypothesis on smaller target formulas is enough to prove the current formula.
-/
theorem PositiveLTL.subformulaClosure_satisfies_of_macroTransition_next_of_no_self_atom
    {AP : Type u}
    {Letter : Type v}
    [DecidableEq AP]
    (root : PositiveLTL AP)
    (interp : AP -> Letter -> Prop)
    (dec : ∀ ap letter, Decidable (interp ap letter))
    (word : OmegaWord Letter)
    {states nextStates :
      Finset
        (((PositiveLTL.subformulaClosure (Letter := Letter) root).toAPA
          interp dec).State)}
    {stateEdges :
      Finset
        ((((PositiveLTL.subformulaClosure (Letter := Letter) root).toAPA
            interp dec).State) ×
          (((PositiveLTL.subformulaClosure (Letter := Letter) root).toAPA
            interp dec).State))}
    (htransition :
      ((PositiveLTL.subformulaClosure (Letter := Letter) root).toAPA
        interp dec).MacroTransitionWithStateEdges
          states (word 0) nextStates stateEdges)
    {state :
      ((PositiveLTL.subformulaClosure (Letter := Letter) root).toAPA
        interp dec).State}
    (hstate : state ∈ states)
    (hNoSelf :
      ∀ nextState :
        ((PositiveLTL.subformulaClosure (Letter := Letter) root).toAPA
          interp dec).State,
        nextState ∈
          (((PositiveLTL.subformulaClosure (Letter := Letter) root).toAPA
            interp dec).step state (word 0)).atoms ->
          nextState ≠ state)
    (hnext :
      ∀ nextState, nextState ∈ nextStates ->
        nextState.1.size < state.1.size ->
          PositiveLTL.Satisfies interp
            (OmegaWord.drop word 1) nextState.1) :
    PositiveLTL.Satisfies interp word state.1 := by
  let closure := PositiveLTL.subformulaClosure (Letter := Letter) root
  let A := closure.toAPA interp dec
  have hstep :
      PosBool.Eval
        (fun nextState : A.State => nextState ∈ nextStates)
        (A.step state (word 0)) :=
    htransition.eval_source hstate
  have hstepSatisfies :
      PosBool.Eval
        (fun nextState : A.State =>
          PositiveLTL.Satisfies interp (OmegaWord.drop word 1) nextState.1)
        (A.step state (word 0)) := by
    refine
      PosBool.eval_mono_of_imp_on_atoms
        (A.step state (word 0))
        ?_
        hstep
    intro nextState hmem hnextMem
    have hmemTransition :
        nextState ∈
          (PositiveLTL.subformulaTransition root interp state (word 0)).atoms := by
      simpa [A, closure, PositiveLTL.subformulaClosure,
        FiniteLTLAlternatingClosure.toAPA] using hmem
    have hmove :=
      PositiveLTL.subformulaTransition_atoms_self_or_size_lt
        root interp state nextState (word 0) hmemTransition
    rcases hmove with hself | hlt
    · exact False.elim (hNoSelf nextState hmem (Subtype.ext hself))
    · exact hnext nextState hnextMem hlt
  exact (closure.step_correct interp dec state word).mp hstepSatisfies

/--
One-step semantic soundness for source states whose transition has no
successor atoms.

For literals, `⊤`, and impossible `⊥` macro-transition sources, a concrete
macro transition already proves the current formula.  No target-frontier
semantic hypothesis is needed, because the transition formula has no atom on
which such a hypothesis could be used.
-/
theorem PositiveLTL.subformulaClosure_satisfies_of_macroTransition_no_atoms
    {AP : Type u}
    {Letter : Type v}
    [DecidableEq AP]
    (root : PositiveLTL AP)
    (interp : AP -> Letter -> Prop)
    (dec : ∀ ap letter, Decidable (interp ap letter))
    (word : OmegaWord Letter)
    {states nextStates :
      Finset
        (((PositiveLTL.subformulaClosure (Letter := Letter) root).toAPA
          interp dec).State)}
    {stateEdges :
      Finset
        ((((PositiveLTL.subformulaClosure (Letter := Letter) root).toAPA
            interp dec).State) ×
          (((PositiveLTL.subformulaClosure (Letter := Letter) root).toAPA
            interp dec).State))}
    (htransition :
      ((PositiveLTL.subformulaClosure (Letter := Letter) root).toAPA
        interp dec).MacroTransitionWithStateEdges
          states (word 0) nextStates stateEdges)
    {state :
      ((PositiveLTL.subformulaClosure (Letter := Letter) root).toAPA
        interp dec).State}
    (hstate : state ∈ states)
    (hNoAtoms :
      ∀ nextState : ((PositiveLTL.subformulaClosure (Letter := Letter) root).toAPA
          interp dec).State,
        nextState ∈
          (((PositiveLTL.subformulaClosure (Letter := Letter) root).toAPA
            interp dec).step state (word 0)).atoms ->
          False) :
    PositiveLTL.Satisfies interp word state.1 := by
  let closure := PositiveLTL.subformulaClosure (Letter := Letter) root
  let A := closure.toAPA interp dec
  have hstep :
      PosBool.Eval
        (fun nextState : A.State => nextState ∈ nextStates)
        (A.step state (word 0)) :=
    htransition.eval_source hstate
  have hstepSatisfies :
      PosBool.Eval
        (fun nextState : A.State =>
          PositiveLTL.Satisfies interp (OmegaWord.drop word 1) nextState.1)
        (A.step state (word 0)) :=
    PosBool.eval_mono_of_imp_on_atoms
      (A.step state (word 0))
      (fun nextState hmem _hnext => False.elim (hNoAtoms nextState hmem))
      hstep
  exact (closure.step_correct interp dec state word).mp hstepSatisfies

/--
Literal source states are forced locally by any concrete macro transition.
-/
theorem PositiveLTL.subformulaClosure_macroTransition_lit_satisfies
    {AP : Type u}
    {Letter : Type v}
    [DecidableEq AP]
    (root : PositiveLTL AP)
    (interp : AP -> Letter -> Prop)
    (dec : ∀ ap letter, Decidable (interp ap letter))
    (word : OmegaWord Letter)
    {states nextStates :
      Finset
        (((PositiveLTL.subformulaClosure (Letter := Letter) root).toAPA
          interp dec).State)}
    {stateEdges :
      Finset
        ((((PositiveLTL.subformulaClosure (Letter := Letter) root).toAPA
            interp dec).State) ×
          (((PositiveLTL.subformulaClosure (Letter := Letter) root).toAPA
            interp dec).State))}
    (htransition :
      ((PositiveLTL.subformulaClosure (Letter := Letter) root).toAPA
        interp dec).MacroTransitionWithStateEdges
          states (word 0) nextStates stateEdges)
    {state :
      ((PositiveLTL.subformulaClosure (Letter := Letter) root).toAPA
        interp dec).State}
    (hstateMem : state ∈ states)
    {literal : LTLLiteral AP}
    (hstate : state.1 = PositiveLTL.lit literal) :
    PositiveLTL.Satisfies interp word state.1 := by
  letI := dec
  let A :=
    (PositiveLTL.subformulaClosure (Letter := Letter) root).toAPA interp dec
  refine
    PositiveLTL.subformulaClosure_satisfies_of_macroTransition_no_atoms
      root interp dec word htransition hstateMem ?_
  intro nextState hmem
  have hmemSub :
      nextState ∈
        (PositiveLTL.subformulaTransition root interp state (word 0)).atoms := by
    simpa [A, FiniteLTLAlternatingClosure.toAPA,
      PositiveLTL.subformulaClosure] using hmem
  have hmemFormula :
      nextState.1 ∈
        (PositiveLTL.alternatingStep interp (word 0) state.1).atoms := by
    let step := PositiveLTL.alternatingStep interp (word 0) state.1
    let embed : ∀ θ, θ ∈ step.atoms -> root.Subformula :=
      fun θ hθ =>
        ⟨θ,
          PositiveLTL.subformulas_trans
            (PositiveLTL.alternatingStep_atoms_subformulas
              interp (word 0) state.1 θ hθ)
            state.2⟩
    change nextState ∈ (step.pmap embed).atoms at hmemSub
    rcases PosBool.mem_atoms_pmap step embed hmemSub with
      ⟨θ, hθ, hnext⟩
    have hnextDenote : nextState.1 = θ := by
      rw [hnext]
    simpa [step, hnextDenote] using hθ
  by_cases hlit : PositiveLTL.literalHolds interp (word 0) literal
  · simpa [hstate, PositiveLTL.alternatingStep, PosBool.atoms, hlit]
      using hmemFormula
  · simpa [hstate, PositiveLTL.alternatingStep, PosBool.atoms, hlit]
      using hmemFormula

/--
False source states cannot participate in a concrete macro transition.

The statement is phrased semantically: from such a transition we may derive
`Satisfies ... falsum`, i.e. `False`.  This is the impossible base case needed
by support-witness soundness.
-/
theorem PositiveLTL.subformulaClosure_macroTransition_falsum_satisfies
    {AP : Type u}
    {Letter : Type v}
    [DecidableEq AP]
    (root : PositiveLTL AP)
    (interp : AP -> Letter -> Prop)
    (dec : ∀ ap letter, Decidable (interp ap letter))
    (word : OmegaWord Letter)
    {states nextStates :
      Finset
        (((PositiveLTL.subformulaClosure (Letter := Letter) root).toAPA
          interp dec).State)}
    {stateEdges :
      Finset
        ((((PositiveLTL.subformulaClosure (Letter := Letter) root).toAPA
            interp dec).State) ×
          (((PositiveLTL.subformulaClosure (Letter := Letter) root).toAPA
            interp dec).State))}
    (htransition :
      ((PositiveLTL.subformulaClosure (Letter := Letter) root).toAPA
        interp dec).MacroTransitionWithStateEdges
          states (word 0) nextStates stateEdges)
    {state :
      ((PositiveLTL.subformulaClosure (Letter := Letter) root).toAPA
        interp dec).State}
    (hstateMem : state ∈ states)
    (hstate : state.1 = PositiveLTL.falsum) :
    PositiveLTL.Satisfies interp word state.1 := by
  let A :=
    (PositiveLTL.subformulaClosure (Letter := Letter) root).toAPA interp dec
  refine
    PositiveLTL.subformulaClosure_satisfies_of_macroTransition_no_atoms
      root interp dec word htransition hstateMem ?_
  intro nextState hmem
  have hmemSub :
      nextState ∈
        (PositiveLTL.subformulaTransition root interp state (word 0)).atoms := by
    simpa [A, FiniteLTLAlternatingClosure.toAPA,
      PositiveLTL.subformulaClosure] using hmem
  have hmemFormula :
      nextState.1 ∈
        (PositiveLTL.alternatingStep interp (word 0) state.1).atoms := by
    let step := PositiveLTL.alternatingStep interp (word 0) state.1
    let embed : ∀ θ, θ ∈ step.atoms -> root.Subformula :=
      fun θ hθ =>
        ⟨θ,
          PositiveLTL.subformulas_trans
            (PositiveLTL.alternatingStep_atoms_subformulas
              interp (word 0) state.1 θ hθ)
            state.2⟩
    change nextState ∈ (step.pmap embed).atoms at hmemSub
    rcases PosBool.mem_atoms_pmap step embed hmemSub with
      ⟨θ, hθ, hnext⟩
    have hnextDenote : nextState.1 = θ := by
      rw [hnext]
    simpa [step, hnextDenote] using hθ
  simpa [hstate, PositiveLTL.alternatingStep, PosBool.atoms] using hmemFormula

/--
Backward semantic propagation along one step of a concrete macro-run prefix
for the canonical subformula APA.

This is the prefix-facing form of `subformulaClosure_satisfies_of_macroTransition_next`.
It is useful for support-witness soundness: once a later macro-frontier is
known semantically true, truth propagates one finite prefix step backwards.
-/
theorem PositiveLTL.subformulaClosure_macroRunPrefix_satisfies_step_back
    {AP : Type u}
    {Letter : Type v}
    [DecidableEq AP]
    (root : PositiveLTL AP)
    (interp : AP -> Letter -> Prop)
    (dec : ∀ ap letter, Decidable (interp ap letter))
    {initialStates :
      Finset
        (((PositiveLTL.subformulaClosure (Letter := Letter) root).toAPA
          interp dec).State)}
    {word : OmegaWord Letter}
    {n : Nat}
    (pref :
      ((PositiveLTL.subformulaClosure (Letter := Letter) root).toAPA
        interp dec).MacroRunPrefix initialStates word (n + 1))
    (hnext :
      ∀ nextState, nextState ∈ pref.states (n + 1) ->
        PositiveLTL.Satisfies interp
          (OmegaWord.drop word (n + 1)) nextState.1) :
    ∀ state, state ∈ pref.states n ->
      PositiveLTL.Satisfies interp (OmegaWord.drop word n) state.1 := by
  intro state hstate
  let A := (PositiveLTL.subformulaClosure (Letter := Letter) root).toAPA
    interp dec
  have hmacro :
      A.MacroTransition (pref.states n) (word n) (pref.states (n + 1)) :=
    pref.step_transition n (Nat.lt_succ_self n)
  rcases A.exists_stateEdges_of_macroTransition hmacro with
    ⟨stateEdges, htransition⟩
  have hnextDrop :
      ∀ nextState, nextState ∈ pref.states (n + 1) ->
        PositiveLTL.Satisfies interp
          (OmegaWord.drop (OmegaWord.drop word n) 1) nextState.1 := by
    intro nextState hnextState
    simpa [OmegaWord.drop_drop, Nat.add_comm, Nat.add_assoc] using
      hnext nextState hnextState
  simpa [OmegaWord.drop] using
    PositiveLTL.subformulaClosure_satisfies_of_macroTransition_next
      root interp dec (OmegaWord.drop word n)
      (states := pref.states n)
      (nextStates := pref.states (n + 1))
      (stateEdges := stateEdges)
      htransition
      hstate
      hnextDrop

/--
Bounded one-step semantic propagation along a concrete macro-run prefix.

This is the size-bounded version of
`subformulaClosure_macroRunPrefix_satisfies_step_back`: to prove a source
state below `bound`, it only needs target-frontier truth for target states
below the same bound.  Self-looping temporal states are handled by the
source-size premise.
-/
theorem PositiveLTL.subformulaClosure_macroRunPrefix_satisfies_step_back_of_size_lt
    {AP : Type u}
    {Letter : Type v}
    [DecidableEq AP]
    (root : PositiveLTL AP)
    (interp : AP -> Letter -> Prop)
    (dec : ∀ ap letter, Decidable (interp ap letter))
    {initialStates :
      Finset
        (((PositiveLTL.subformulaClosure (Letter := Letter) root).toAPA
          interp dec).State)}
    {word : OmegaWord Letter}
    {n bound : Nat}
    (pref :
      ((PositiveLTL.subformulaClosure (Letter := Letter) root).toAPA
        interp dec).MacroRunPrefix initialStates word (n + 1))
    (hnext :
      ∀ nextState, nextState ∈ pref.states (n + 1) ->
        nextState.1.size < bound ->
          PositiveLTL.Satisfies interp
            (OmegaWord.drop word (n + 1)) nextState.1) :
    ∀ state, state ∈ pref.states n ->
      state.1.size < bound ->
        PositiveLTL.Satisfies interp (OmegaWord.drop word n) state.1 := by
  intro state hstate hsize
  let A := (PositiveLTL.subformulaClosure (Letter := Letter) root).toAPA
    interp dec
  have hmacro :
      A.MacroTransition (pref.states n) (word n) (pref.states (n + 1)) :=
    pref.step_transition n (Nat.lt_succ_self n)
  rcases A.exists_stateEdges_of_macroTransition hmacro with
    ⟨stateEdges, htransition⟩
  have hnextDrop :
      ∀ nextState, nextState ∈ pref.states (n + 1) ->
        nextState.1.size < bound ->
          PositiveLTL.Satisfies interp
            (OmegaWord.drop (OmegaWord.drop word n) 1) nextState.1 := by
    intro nextState hnextState hlt
    simpa [OmegaWord.drop_drop, Nat.add_comm, Nat.add_assoc] using
      hnext nextState hnextState hlt
  simpa [OmegaWord.drop] using
    PositiveLTL.subformulaClosure_satisfies_of_macroTransition_next_of_size_lt
      root interp dec (OmegaWord.drop word n)
      (states := pref.states n)
      (nextStates := pref.states (n + 1))
      (stateEdges := stateEdges)
      htransition
      hstate
      hsize
      hnextDrop

/--
Backward semantic propagation along an entire concrete macro-run prefix for the
canonical subformula APA.

If the endpoint macro-state of a finite prefix is semantically true on its
suffix, then every earlier macro-state of that same prefix is semantically
true on the corresponding earlier suffix.
-/
theorem PositiveLTL.subformulaClosure_macroRunPrefix_satisfies_back
    {AP : Type u}
    {Letter : Type v}
    [DecidableEq AP]
    (root : PositiveLTL AP)
    (interp : AP -> Letter -> Prop)
    (dec : ∀ ap letter, Decidable (interp ap letter))
    {initialStates :
      Finset
        (((PositiveLTL.subformulaClosure (Letter := Letter) root).toAPA
          interp dec).State)}
    {word : OmegaWord Letter}
    {offset : Nat}
    (pref :
      ((PositiveLTL.subformulaClosure (Letter := Letter) root).toAPA
        interp dec).MacroRunPrefix initialStates word offset)
    (hfrontier :
      ∀ state, state ∈ pref.states offset ->
        PositiveLTL.Satisfies interp
          (OmegaWord.drop word offset) state.1) :
    ∀ n, n ≤ offset ->
      ∀ state, state ∈ pref.states n ->
        PositiveLTL.Satisfies interp (OmegaWord.drop word n) state.1 := by
  induction offset with
  | zero =>
      intro n hn state hstate
      have hn0 : n = 0 := by omega
      subst n
      simpa using hfrontier state hstate
  | succ offset ih =>
      intro n hn state hstate
      by_cases hnlast : n = offset + 1
      · subst n
        exact hfrontier state hstate
      · have hnle : n ≤ offset := by omega
        let A := (PositiveLTL.subformulaClosure (Letter := Letter) root).toAPA
          interp dec
        let prefShort : A.MacroRunPrefix initialStates word offset :=
          { states := pref.states
            initial_states := pref.initial_states
            step_transition := by
              intro m hm
              exact pref.step_transition m (by omega) }
        have hfrontierShort :
            ∀ state, state ∈ prefShort.states offset ->
              PositiveLTL.Satisfies interp
                (OmegaWord.drop word offset) state.1 := by
          intro frontierState hfrontierState
          have hstepBack :=
            PositiveLTL.subformulaClosure_macroRunPrefix_satisfies_step_back
              root interp dec
              (initialStates := initialStates)
              (word := word)
              (n := offset)
              pref
              hfrontier
          exact hstepBack frontierState hfrontierState
        have hresult :=
          ih prefShort hfrontierShort n hnle state hstate
        simpa [prefShort] using hresult

/--
Bounded backward semantic propagation along an entire concrete macro-run
prefix for the canonical subformula APA.

This is the prefix version needed for structural induction on formula size:
truth for endpoint states below `bound` propagates backwards to all earlier
states below `bound`.
-/
theorem PositiveLTL.subformulaClosure_macroRunPrefix_satisfies_back_of_size_lt
    {AP : Type u}
    {Letter : Type v}
    [DecidableEq AP]
    (root : PositiveLTL AP)
    (interp : AP -> Letter -> Prop)
    (dec : ∀ ap letter, Decidable (interp ap letter))
    {initialStates :
      Finset
        (((PositiveLTL.subformulaClosure (Letter := Letter) root).toAPA
          interp dec).State)}
    {word : OmegaWord Letter}
    {offset bound : Nat}
    (pref :
      ((PositiveLTL.subformulaClosure (Letter := Letter) root).toAPA
        interp dec).MacroRunPrefix initialStates word offset)
    (hfrontier :
      ∀ state, state ∈ pref.states offset ->
        state.1.size < bound ->
          PositiveLTL.Satisfies interp
            (OmegaWord.drop word offset) state.1) :
    ∀ n, n ≤ offset ->
      ∀ state, state ∈ pref.states n ->
        state.1.size < bound ->
          PositiveLTL.Satisfies interp (OmegaWord.drop word n) state.1 := by
  induction offset with
  | zero =>
      intro n hn state hstate hsize
      have hn0 : n = 0 := by omega
      subst n
      simpa using hfrontier state hstate hsize
  | succ offset ih =>
      intro n hn state hstate hsize
      by_cases hnlast : n = offset + 1
      · subst n
        exact hfrontier state hstate hsize
      · have hnle : n ≤ offset := by omega
        let A := (PositiveLTL.subformulaClosure (Letter := Letter) root).toAPA
          interp dec
        let prefShort : A.MacroRunPrefix initialStates word offset :=
          { states := pref.states
            initial_states := pref.initial_states
            step_transition := by
              intro m hm
              exact pref.step_transition m (by omega) }
        have hfrontierShort :
            ∀ state, state ∈ prefShort.states offset ->
              state.1.size < bound ->
                PositiveLTL.Satisfies interp
                  (OmegaWord.drop word offset) state.1 := by
          intro frontierState hfrontierState hfrontierSize
          have hstepBack :=
            PositiveLTL.subformulaClosure_macroRunPrefix_satisfies_step_back_of_size_lt
              root interp dec
              (initialStates := initialStates)
              (word := word)
              (n := offset)
              (bound := bound)
              pref
              hfrontier
          exact hstepBack frontierState hfrontierState hfrontierSize
        have hresult :=
          ih prefShort hfrontierShort n hnle state hstate hsize
        simpa [prefShort] using hresult

/--
If a canonical subformula transition contains the source state itself as an
atom, then the source formula is one of the two temporal fixed-point forms.
-/
theorem PositiveLTL.subformulaTransition_self_atom_is_until_or_release
    {AP : Type u}
    {Letter : Type v}
    [DecidableEq AP]
    (root : PositiveLTL AP)
    (interp : AP -> Letter -> Prop)
    (dec : ∀ ap letter, Decidable (interp ap letter))
    (state : root.Subformula)
    (letter : Letter)
    (hmem :
      state ∈
        (PositiveLTL.subformulaTransition root interp state letter).atoms) :
    (∃ φ ψ : PositiveLTL AP, state.1 = PositiveLTL.until φ ψ) ∨
      ∃ φ ψ : PositiveLTL AP, state.1 = PositiveLTL.release φ ψ := by
  unfold PositiveLTL.subformulaTransition at hmem
  let step := @PositiveLTL.alternatingStep AP Letter interp dec
    letter state.1
  let embed : ∀ θ, θ ∈ step.atoms -> root.Subformula :=
    fun θ hθ =>
      ⟨θ,
        PositiveLTL.subformulas_trans
          (PositiveLTL.alternatingStep_atoms_subformulas
            interp letter state.1 θ hθ)
          state.2⟩
  have hmem' : state ∈ (step.pmap embed).atoms := by
    simpa [step, embed] using hmem
  rcases PosBool.mem_atoms_pmap step embed hmem' with
    ⟨θ, hθ, hstateEq⟩
  have hθState : θ = state.1 := by
    have hval := congrArg Subtype.val hstateEq
    simpa [embed] using hval.symm
  exact
    PositiveLTL.alternatingStep_self_atom_is_until_or_release
      interp letter state.1 (by simpa [step, hθState] using hθ)

/--
Self atoms of the concrete APA step are exactly the temporal fixed-point
sources (`until` or `release`).
-/
theorem PositiveLTL.subformulaClosure_step_self_atom_is_until_or_release
    {AP : Type u}
    {Letter : Type v}
    [DecidableEq AP]
    (root : PositiveLTL AP)
    (interp : AP -> Letter -> Prop)
    (dec : ∀ ap letter, Decidable (interp ap letter))
    (state :
      ((PositiveLTL.subformulaClosure (Letter := Letter) root).toAPA
        interp dec).State)
    (letter : Letter)
    (hmem :
      state ∈
        (((PositiveLTL.subformulaClosure (Letter := Letter) root).toAPA
          interp dec).step state letter).atoms) :
    (∃ φ ψ : PositiveLTL AP, state.1 = PositiveLTL.until φ ψ) ∨
      ∃ φ ψ : PositiveLTL AP, state.1 = PositiveLTL.release φ ψ := by
  have hmemTransition :
      state ∈
        (PositiveLTL.subformulaTransition root interp state letter).atoms := by
    simpa [PositiveLTL.subformulaClosure, FiniteLTLAlternatingClosure.toAPA]
      using hmem
  exact
    PositiveLTL.subformulaTransition_self_atom_is_until_or_release
      root interp dec state letter hmemTransition

/--
Non-temporal source states have no self atom in their concrete APA step.
-/
theorem PositiveLTL.subformulaClosure_step_no_self_atom_of_not_until_or_release
    {AP : Type u}
    {Letter : Type v}
    [DecidableEq AP]
    (root : PositiveLTL AP)
    (interp : AP -> Letter -> Prop)
    (dec : ∀ ap letter, Decidable (interp ap letter))
    (state :
      ((PositiveLTL.subformulaClosure (Letter := Letter) root).toAPA
        interp dec).State)
    (letter : Letter)
    (hnotUntil :
      ∀ φ ψ : PositiveLTL AP, state.1 ≠ PositiveLTL.until φ ψ)
    (hnotRelease :
      ∀ φ ψ : PositiveLTL AP, state.1 ≠ PositiveLTL.release φ ψ) :
    ∀ nextState,
      nextState ∈
        (((PositiveLTL.subformulaClosure (Letter := Letter) root).toAPA
          interp dec).step state letter).atoms ->
        nextState ≠ state := by
  intro nextState hmem hnextEq
  have hself :
      state ∈
        (((PositiveLTL.subformulaClosure (Letter := Letter) root).toAPA
          interp dec).step state letter).atoms := by
    simpa [hnextEq] using hmem
  rcases
      PositiveLTL.subformulaClosure_step_self_atom_is_until_or_release
        root interp dec state letter hself with
    ⟨φ, ψ, hstate⟩ | ⟨φ, ψ, hstate⟩
  · exact hnotUntil φ ψ hstate
  · exact hnotRelease φ ψ hstate

/--
Until progress extracted from a concrete transition of the finite
subformula-closure APA.

The conclusion is stated over the underlying formulas: a transition out of
`φ U ψ` either already satisfies the `ψ` branch, or it satisfies the `φ`
branch and keeps the same until state as a continuation successor.
-/
theorem PositiveLTL.subformulaTransition_until_progress
    {AP : Type u}
    {Letter : Type v}
    [DecidableEq AP]
    (root : PositiveLTL AP)
    (interp : AP -> Letter -> Prop)
    [∀ ap letter, Decidable (interp ap letter)]
    (state : root.Subformula)
    (letter : Letter)
    {φ ψ : PositiveLTL AP}
    (hstate : state.1 = PositiveLTL.until φ ψ)
    {nextStates : Finset root.Subformula}
    (hstep :
      PosBool.Eval (fun nextState : root.Subformula => nextState ∈ nextStates)
        (PositiveLTL.subformulaTransition root interp state letter)) :
    let formulaVal : PositiveLTL AP -> Prop :=
      fun θ => ∃ hθ : θ ∈ root.subformulas,
        (⟨θ, hθ⟩ : root.Subformula) ∈ nextStates
    PosBool.Eval formulaVal (PositiveLTL.alternatingStep interp letter ψ) ∨
      (PosBool.Eval formulaVal (PositiveLTL.alternatingStep interp letter φ) ∧
        state ∈ nextStates) := by
  classical
  dsimp only
  let formulaVal : PositiveLTL AP -> Prop :=
    fun θ => ∃ hθ : θ ∈ root.subformulas,
      (⟨θ, hθ⟩ : root.Subformula) ∈ nextStates
  let step := PositiveLTL.alternatingStep interp letter state.1
  let embed : ∀ θ, θ ∈ step.atoms -> root.Subformula :=
    fun θ hθ =>
      ⟨θ,
        PositiveLTL.subformulas_trans
          (PositiveLTL.alternatingStep_atoms_subformulas
            interp letter state.1 θ hθ)
          state.2⟩
  have hstepFormula :
      PosBool.Eval formulaVal step := by
    refine
      PosBool.eval_of_pmap_imp
        step embed
        (valuation := formulaVal)
        (valuation' := fun nextState : root.Subformula =>
          nextState ∈ nextStates)
        ?_
        (by
          simpa [PositiveLTL.subformulaTransition, step, embed] using hstep)
    intro θ hθ hnext
    refine ⟨(embed θ hθ).2, ?_⟩
    simpa [embed] using hnext
  by_cases hψ :
      PosBool.Eval formulaVal (PositiveLTL.alternatingStep interp letter ψ)
  · exact Or.inl hψ
  · rcases
      PositiveLTL.alternatingStep_until_progress_of_not_right
        interp letter φ ψ formulaVal
        (by simpa [step, hstate] using hstepFormula)
        hψ with
      ⟨hφ, huntil⟩
    right
    refine ⟨hφ, ?_⟩
    rcases huntil with ⟨hmem, hnext⟩
    have hstateEq :
        (⟨PositiveLTL.until φ ψ, hmem⟩ : root.Subformula) = state :=
      Subtype.ext hstate.symm
    simpa [hstateEq] using hnext

/--
Until progress extracted from a concrete macro transition of the canonical
subformula APA.
-/
theorem PositiveLTL.subformulaClosure_macroTransition_until_progress
    {AP : Type u}
    {Letter : Type v}
    [DecidableEq AP]
    (root : PositiveLTL AP)
    (interp : AP -> Letter -> Prop)
    (dec : ∀ ap letter, Decidable (interp ap letter))
    (word : OmegaWord Letter)
    {states nextStates :
      Finset
        (((PositiveLTL.subformulaClosure (Letter := Letter) root).toAPA
          interp dec).State)}
    {stateEdges :
      Finset
        ((((PositiveLTL.subformulaClosure (Letter := Letter) root).toAPA
            interp dec).State) ×
          (((PositiveLTL.subformulaClosure (Letter := Letter) root).toAPA
            interp dec).State))}
    (htransition :
      ((PositiveLTL.subformulaClosure (Letter := Letter) root).toAPA
        interp dec).MacroTransitionWithStateEdges
          states (word 0) nextStates stateEdges)
    {state :
      ((PositiveLTL.subformulaClosure (Letter := Letter) root).toAPA
        interp dec).State}
    (hstateMem : state ∈ states)
    {φ ψ : PositiveLTL AP}
    (hstate : state.1 = PositiveLTL.until φ ψ) :
    let formulaVal : PositiveLTL AP -> Prop :=
      fun θ => ∃ hθ : θ ∈ root.subformulas,
        (⟨θ, hθ⟩ :
          ((PositiveLTL.subformulaClosure (Letter := Letter) root).toAPA
            interp dec).State) ∈ nextStates
    PosBool.Eval formulaVal (PositiveLTL.alternatingStep interp (word 0) ψ) ∨
      (PosBool.Eval formulaVal
          (PositiveLTL.alternatingStep interp (word 0) φ) ∧
        state ∈ nextStates) := by
  letI := dec
  let A :=
    (PositiveLTL.subformulaClosure (Letter := Letter) root).toAPA
      interp dec
  have hstepA :
      PosBool.Eval (fun nextState : A.State => nextState ∈ nextStates)
        (A.step state (word 0)) :=
    htransition.eval_source hstateMem
  have hstepSub :
      PosBool.Eval (fun nextState : A.State => nextState ∈ nextStates)
        (PositiveLTL.subformulaTransition root interp state (word 0)) := by
    simpa [A, FiniteLTLAlternatingClosure.toAPA,
      PositiveLTL.subformulaClosure] using hstepA
  exact
    PositiveLTL.subformulaTransition_until_progress
      root interp state (word 0) hstate hstepSub

/--
Non-circular semantic until progress for a concrete macro transition.

Only smaller target formulas are assumed semantically true.  The conclusion is
the one-step `until` body: either `ψ` holds now, or `φ` holds now and the same
until state occurs in the target frontier.
-/
theorem PositiveLTL.subformulaClosure_macroTransition_until_satisfies_progress_of_smaller
    {AP : Type u}
    {Letter : Type v}
    [DecidableEq AP]
    (root : PositiveLTL AP)
    (interp : AP -> Letter -> Prop)
    (dec : ∀ ap letter, Decidable (interp ap letter))
    (word : OmegaWord Letter)
    {states nextStates :
      Finset
        (((PositiveLTL.subformulaClosure (Letter := Letter) root).toAPA
          interp dec).State)}
    {stateEdges :
      Finset
        ((((PositiveLTL.subformulaClosure (Letter := Letter) root).toAPA
            interp dec).State) ×
          (((PositiveLTL.subformulaClosure (Letter := Letter) root).toAPA
            interp dec).State))}
    (htransition :
      ((PositiveLTL.subformulaClosure (Letter := Letter) root).toAPA
        interp dec).MacroTransitionWithStateEdges
          states (word 0) nextStates stateEdges)
    {state :
      ((PositiveLTL.subformulaClosure (Letter := Letter) root).toAPA
        interp dec).State}
    (hstateMem : state ∈ states)
    {φ ψ : PositiveLTL AP}
    (hstate : state.1 = PositiveLTL.until φ ψ)
    (htargetSmaller :
      ∀ nextState, nextState ∈ nextStates ->
        nextState.1.size < (PositiveLTL.until φ ψ).size ->
          PositiveLTL.Satisfies interp
            (OmegaWord.drop word 1) nextState.1) :
    PositiveLTL.Satisfies interp word ψ ∨
      (PositiveLTL.Satisfies interp word φ ∧ state ∈ nextStates) := by
  letI := dec
  let A :=
    (PositiveLTL.subformulaClosure (Letter := Letter) root).toAPA
      interp dec
  let formulaVal : PositiveLTL AP -> Prop :=
    fun θ => ∃ hθ : θ ∈ root.subformulas,
      (⟨θ, hθ⟩ : A.State) ∈ nextStates
  have hprogress :
      PosBool.Eval formulaVal (PositiveLTL.alternatingStep interp (word 0) ψ) ∨
        (PosBool.Eval formulaVal
            (PositiveLTL.alternatingStep interp (word 0) φ) ∧
          state ∈ nextStates) := by
    simpa [A, formulaVal] using
      (PositiveLTL.subformulaClosure_macroTransition_until_progress
        root interp dec word htransition hstateMem hstate)
  rcases hprogress with hψEval | hφEval
  · left
    have hψEvalSat :
        PosBool.Eval
          (fun θ => PositiveLTL.Satisfies interp (OmegaWord.drop word 1) θ)
          (PositiveLTL.alternatingStep interp (word 0) ψ) := by
      refine
        PosBool.eval_mono_of_imp_on_atoms
          (PositiveLTL.alternatingStep interp (word 0) ψ)
          ?_
          hψEval
      intro θ hmem hθ
      rcases hθ with ⟨hsub, hnext⟩
      have hlt : θ.size < (PositiveLTL.until φ ψ).size := by
        rcases
          PositiveLTL.alternatingStep_atoms_self_or_size_lt
            interp (word 0) ψ θ hmem with hself | hlt
        · rw [hself]
          exact PositiveLTL.size_lt_until_right φ ψ
        · exact Nat.lt_trans hlt (PositiveLTL.size_lt_until_right φ ψ)
      exact htargetSmaller (⟨θ, hsub⟩ : A.State) hnext hlt
    exact (PositiveLTL.alternatingStep_correct interp word ψ).mp hψEvalSat
  · right
    rcases hφEval with ⟨hφEval, hnext⟩
    have hφEvalSat :
        PosBool.Eval
          (fun θ => PositiveLTL.Satisfies interp (OmegaWord.drop word 1) θ)
          (PositiveLTL.alternatingStep interp (word 0) φ) := by
      refine
        PosBool.eval_mono_of_imp_on_atoms
          (PositiveLTL.alternatingStep interp (word 0) φ)
          ?_
          hφEval
      intro θ hmem hθ
      rcases hθ with ⟨hsub, hnextState⟩
      have hlt : θ.size < (PositiveLTL.until φ ψ).size := by
        rcases
          PositiveLTL.alternatingStep_atoms_self_or_size_lt
            interp (word 0) φ θ hmem with hself | hlt
        · rw [hself]
          exact PositiveLTL.size_lt_until_left φ ψ
        · exact Nat.lt_trans hlt (PositiveLTL.size_lt_until_left φ ψ)
      exact htargetSmaller (⟨θ, hsub⟩ : A.State) hnextState hlt
    exact
      ⟨(PositiveLTL.alternatingStep_correct interp word φ).mp hφEvalSat,
        hnext⟩

/--
Source-support-specific semantic until progress for a concrete macro
transition.

This strengthens
`subformulaClosure_macroTransition_until_satisfies_progress_of_smaller`: in the
continuation case, the selected support of the `until` source itself contains
the `until` self-loop, so the self-edge is present in the recorded
`stateEdges`.  This is the form needed by accepting recurring-edge arguments,
where parity rules out recurring selected `until` self-loops.
-/
theorem PositiveLTL.subformulaClosure_macroTransition_until_satisfies_progress_of_smaller_or_self_edge
    {AP : Type u}
    {Letter : Type v}
    [DecidableEq AP]
    (root : PositiveLTL AP)
    (interp : AP -> Letter -> Prop)
    (dec : ∀ ap letter, Decidable (interp ap letter))
    (word : OmegaWord Letter)
    {states nextStates :
      Finset
        (((PositiveLTL.subformulaClosure (Letter := Letter) root).toAPA
          interp dec).State)}
    {stateEdges :
      Finset
        ((((PositiveLTL.subformulaClosure (Letter := Letter) root).toAPA
            interp dec).State) ×
          (((PositiveLTL.subformulaClosure (Letter := Letter) root).toAPA
            interp dec).State))}
    (htransition :
      ((PositiveLTL.subformulaClosure (Letter := Letter) root).toAPA
        interp dec).MacroTransitionWithStateEdges
          states (word 0) nextStates stateEdges)
    {state :
      ((PositiveLTL.subformulaClosure (Letter := Letter) root).toAPA
        interp dec).State}
    (hstateMem : state ∈ states)
    {φ ψ : PositiveLTL AP}
    (hstate : state.1 = PositiveLTL.until φ ψ)
    (htargetSmaller :
      ∀ nextState, nextState ∈ nextStates ->
        nextState.1.size < (PositiveLTL.until φ ψ).size ->
          PositiveLTL.Satisfies interp
            (OmegaWord.drop word 1) nextState.1) :
    PositiveLTL.Satisfies interp word ψ ∨
      (PositiveLTL.Satisfies interp word φ ∧
        (state, state) ∈ stateEdges) := by
  letI := dec
  let A :=
    (PositiveLTL.subformulaClosure (Letter := Letter) root).toAPA
      interp dec
  rcases htransition with ⟨supportChoice, hsupport, hedges⟩
  let source : { state // state ∈ states } := ⟨state, hstateMem⟩
  let sourceSupport := supportChoice.choice source
  let formulaVal : PositiveLTL AP -> Prop :=
    fun θ => ∃ hθ : θ ∈ root.subformulas,
      (⟨θ, hθ⟩ : A.State) ∈ sourceSupport.support
  let step := PositiveLTL.alternatingStep interp (word 0) state.1
  let embed : ∀ θ, θ ∈ step.atoms -> A.State :=
    fun θ hθ =>
      ⟨θ,
        PositiveLTL.subformulas_trans
          (PositiveLTL.alternatingStep_atoms_subformulas
            interp (word 0) state.1 θ hθ)
          state.2⟩
  have hstepA :
      PosBool.Eval (fun nextState : A.State =>
          nextState ∈ sourceSupport.support)
        (A.step state (word 0)) :=
    sourceSupport.support_satisfies
  have hstepSub :
      PosBool.Eval (fun nextState : A.State =>
          nextState ∈ sourceSupport.support)
        (PositiveLTL.subformulaTransition root interp state (word 0)) := by
    simpa [A, FiniteLTLAlternatingClosure.toAPA,
      PositiveLTL.subformulaClosure] using hstepA
  have hstepFormula :
      PosBool.Eval formulaVal step := by
    refine
      PositiveLTL.eval_exists_subformula_of_eval_pmap
        root step
        (fun θ hθ =>
          PositiveLTL.subformulas_trans
            (PositiveLTL.alternatingStep_atoms_subformulas
              interp (word 0) state.1 θ hθ)
            state.2)
        (fun nextState : A.State => nextState ∈ sourceSupport.support)
        ?_
    simpa [A, PositiveLTL.subformulaTransition, step, embed] using hstepSub
  have hrawUntil :
      PosBool.Eval formulaVal
        (PositiveLTL.alternatingStep interp (word 0)
          (PositiveLTL.until φ ψ)) := by
    simpa [step, hstate] using hstepFormula
  by_cases hψEval :
      PosBool.Eval formulaVal
        (PositiveLTL.alternatingStep interp (word 0) ψ)
  · left
    have hψEvalSat :
        PosBool.Eval
          (fun θ => PositiveLTL.Satisfies interp (OmegaWord.drop word 1) θ)
          (PositiveLTL.alternatingStep interp (word 0) ψ) := by
      refine
        PosBool.eval_mono_of_imp_on_atoms
          (PositiveLTL.alternatingStep interp (word 0) ψ)
          ?_
          hψEval
      intro θ hmem hθ
      rcases hθ with ⟨hsub, hnextSupport⟩
      have hnextStates :
          (⟨θ, hsub⟩ : A.State) ∈ nextStates := by
        rw [← hsupport]
        exact
          (AlternatingParityAutomaton.MacroStepSupport.mem_support
            (supportChoice := supportChoice)
            (nextState := (⟨θ, hsub⟩ : A.State))).mpr
            ⟨source, hnextSupport⟩
      have hlt : θ.size < (PositiveLTL.until φ ψ).size := by
        rcases
          PositiveLTL.alternatingStep_atoms_self_or_size_lt
            interp (word 0) ψ θ hmem with hself | hlt
        · rw [hself]
          exact PositiveLTL.size_lt_until_right φ ψ
        · exact Nat.lt_trans hlt (PositiveLTL.size_lt_until_right φ ψ)
      exact htargetSmaller (⟨θ, hsub⟩ : A.State) hnextStates hlt
    exact (PositiveLTL.alternatingStep_correct interp word ψ).mp hψEvalSat
  · right
    rcases
      PositiveLTL.alternatingStep_until_progress_of_not_right
        interp (word 0) φ ψ formulaVal hrawUntil hψEval with
      ⟨hφEval, hselfVal⟩
    have hφEvalSat :
        PosBool.Eval
          (fun θ => PositiveLTL.Satisfies interp (OmegaWord.drop word 1) θ)
          (PositiveLTL.alternatingStep interp (word 0) φ) := by
      refine
        PosBool.eval_mono_of_imp_on_atoms
          (PositiveLTL.alternatingStep interp (word 0) φ)
          ?_
          hφEval
      intro θ hmem hθ
      rcases hθ with ⟨hsub, hnextSupport⟩
      have hnextStates :
          (⟨θ, hsub⟩ : A.State) ∈ nextStates := by
        rw [← hsupport]
        exact
          (AlternatingParityAutomaton.MacroStepSupport.mem_support
            (supportChoice := supportChoice)
            (nextState := (⟨θ, hsub⟩ : A.State))).mpr
            ⟨source, hnextSupport⟩
      have hlt : θ.size < (PositiveLTL.until φ ψ).size := by
        rcases
          PositiveLTL.alternatingStep_atoms_self_or_size_lt
            interp (word 0) φ θ hmem with hself | hlt
        · rw [hself]
          exact PositiveLTL.size_lt_until_left φ ψ
        · exact Nat.lt_trans hlt (PositiveLTL.size_lt_until_left φ ψ)
      exact htargetSmaller (⟨θ, hsub⟩ : A.State) hnextStates hlt
    refine
      ⟨(PositiveLTL.alternatingStep_correct interp word φ).mp hφEvalSat,
        ?_⟩
    rcases hselfVal with ⟨hselfSub, hselfSupport⟩
    have hselfState :
        (⟨PositiveLTL.until φ ψ, hselfSub⟩ : A.State) = state :=
      Subtype.ext hstate.symm
    rw [← hedges]
    refine
      (AlternatingParityAutomaton.MacroStepSupport.mem_stateEdges
        (supportChoice := supportChoice)
        (edge := (state, state))).mpr ?_
    refine ⟨source, rfl, ?_⟩
    simpa [hselfState] using hselfSupport

/--
Release progress extracted from a concrete transition of the finite
subformula-closure APA.

The conclusion is stated over the underlying formulas: a transition out of
`φ R ψ` provides the `ψ` obligation now and either the `φ` obligation now or
the same release state as a continuation successor.
-/
theorem PositiveLTL.subformulaTransition_release_progress
    {AP : Type u}
    {Letter : Type v}
    [DecidableEq AP]
    (root : PositiveLTL AP)
    (interp : AP -> Letter -> Prop)
    [∀ ap letter, Decidable (interp ap letter)]
    (state : root.Subformula)
    (letter : Letter)
    {φ ψ : PositiveLTL AP}
    (hstate : state.1 = PositiveLTL.release φ ψ)
    {nextStates : Finset root.Subformula}
    (hstep :
      PosBool.Eval (fun nextState : root.Subformula => nextState ∈ nextStates)
        (PositiveLTL.subformulaTransition root interp state letter)) :
    let formulaVal : PositiveLTL AP -> Prop :=
      fun θ => ∃ hθ : θ ∈ root.subformulas,
        (⟨θ, hθ⟩ : root.Subformula) ∈ nextStates
    PosBool.Eval formulaVal (PositiveLTL.alternatingStep interp letter ψ) ∧
      (PosBool.Eval formulaVal (PositiveLTL.alternatingStep interp letter φ) ∨
        state ∈ nextStates) := by
  classical
  dsimp only
  let formulaVal : PositiveLTL AP -> Prop :=
    fun θ => ∃ hθ : θ ∈ root.subformulas,
      (⟨θ, hθ⟩ : root.Subformula) ∈ nextStates
  let step := PositiveLTL.alternatingStep interp letter state.1
  let embed : ∀ θ, θ ∈ step.atoms -> root.Subformula :=
    fun θ hθ =>
      ⟨θ,
        PositiveLTL.subformulas_trans
          (PositiveLTL.alternatingStep_atoms_subformulas
            interp letter state.1 θ hθ)
          state.2⟩
  have hstepFormula :
      PosBool.Eval formulaVal step := by
    refine
      PosBool.eval_of_pmap_imp
        step embed
        (valuation := formulaVal)
        (valuation' := fun nextState : root.Subformula =>
          nextState ∈ nextStates)
        ?_
        (by
          simpa [PositiveLTL.subformulaTransition, step, embed] using hstep)
    intro θ hθ hnext
    refine ⟨(embed θ hθ).2, ?_⟩
    simpa [embed] using hnext
  have hprogress :
      PosBool.Eval formulaVal (PositiveLTL.alternatingStep interp letter ψ) ∧
        (PosBool.Eval formulaVal
            (PositiveLTL.alternatingStep interp letter φ) ∨
          formulaVal (PositiveLTL.release φ ψ)) := by
    exact
      PositiveLTL.alternatingStep_release_progress
        interp letter φ ψ formulaVal
        (by simpa [step, hstate] using hstepFormula)
  refine ⟨hprogress.1, ?_⟩
  rcases hprogress.2 with hφ | hrelease
  · exact Or.inl hφ
  · rcases hrelease with ⟨hmem, hnext⟩
    right
    have hstateEq :
        (⟨PositiveLTL.release φ ψ, hmem⟩ : root.Subformula) = state :=
      Subtype.ext hstate.symm
    simpa [hstateEq] using hnext

/--
Release progress extracted from a concrete macro transition of the canonical
subformula APA.

This is the macro-transition form of
`subformulaTransition_release_progress`: if the source frontier contains a
release state, then the chosen next frontier satisfies the positive-Boolean
`ψ` obligation and either the positive-Boolean `φ` obligation or the release
state itself as continuation.
-/
theorem PositiveLTL.subformulaClosure_macroTransition_release_progress
    {AP : Type u}
    {Letter : Type v}
    [DecidableEq AP]
    (root : PositiveLTL AP)
    (interp : AP -> Letter -> Prop)
    (dec : ∀ ap letter, Decidable (interp ap letter))
    (word : OmegaWord Letter)
    {states nextStates :
      Finset
        (((PositiveLTL.subformulaClosure (Letter := Letter) root).toAPA
          interp dec).State)}
    {stateEdges :
      Finset
        ((((PositiveLTL.subformulaClosure (Letter := Letter) root).toAPA
            interp dec).State) ×
          (((PositiveLTL.subformulaClosure (Letter := Letter) root).toAPA
            interp dec).State))}
    (htransition :
      ((PositiveLTL.subformulaClosure (Letter := Letter) root).toAPA
        interp dec).MacroTransitionWithStateEdges
          states (word 0) nextStates stateEdges)
    {state :
      ((PositiveLTL.subformulaClosure (Letter := Letter) root).toAPA
        interp dec).State}
    (hstateMem : state ∈ states)
    {φ ψ : PositiveLTL AP}
    (hstate : state.1 = PositiveLTL.release φ ψ) :
    let formulaVal : PositiveLTL AP -> Prop :=
      fun θ => ∃ hθ : θ ∈ root.subformulas,
        (⟨θ, hθ⟩ :
          ((PositiveLTL.subformulaClosure (Letter := Letter) root).toAPA
            interp dec).State) ∈ nextStates
    PosBool.Eval formulaVal (PositiveLTL.alternatingStep interp (word 0) ψ) ∧
      (PosBool.Eval formulaVal
          (PositiveLTL.alternatingStep interp (word 0) φ) ∨
        state ∈ nextStates) := by
  letI := dec
  let A :=
    (PositiveLTL.subformulaClosure (Letter := Letter) root).toAPA
      interp dec
  have hstepA :
      PosBool.Eval (fun nextState : A.State => nextState ∈ nextStates)
        (A.step state (word 0)) :=
    htransition.eval_source hstateMem
  have hstepSub :
      PosBool.Eval (fun nextState : A.State => nextState ∈ nextStates)
        (PositiveLTL.subformulaTransition root interp state (word 0)) := by
    simpa [A, FiniteLTLAlternatingClosure.toAPA,
      PositiveLTL.subformulaClosure] using hstepA
  exact
    PositiveLTL.subformulaTransition_release_progress
      root interp state (word 0) hstate hstepSub

/--
Semantic release progress extracted from a concrete macro transition.

If the target frontier of the transition is already semantically true at the
next suffix, a source state representing `φ R ψ` yields the coinduction
obligation: `ψ` is true now, and either `φ` is true now or the same release
state continues into the target frontier.
-/
theorem PositiveLTL.subformulaClosure_macroTransition_release_satisfies_progress
    {AP : Type u}
    {Letter : Type v}
    [DecidableEq AP]
    (root : PositiveLTL AP)
    (interp : AP -> Letter -> Prop)
    (dec : ∀ ap letter, Decidable (interp ap letter))
    (word : OmegaWord Letter)
    {states nextStates :
      Finset
        (((PositiveLTL.subformulaClosure (Letter := Letter) root).toAPA
          interp dec).State)}
    {stateEdges :
      Finset
        ((((PositiveLTL.subformulaClosure (Letter := Letter) root).toAPA
            interp dec).State) ×
          (((PositiveLTL.subformulaClosure (Letter := Letter) root).toAPA
            interp dec).State))}
    (htransition :
      ((PositiveLTL.subformulaClosure (Letter := Letter) root).toAPA
        interp dec).MacroTransitionWithStateEdges
          states (word 0) nextStates stateEdges)
    {state :
      ((PositiveLTL.subformulaClosure (Letter := Letter) root).toAPA
        interp dec).State}
    (hstateMem : state ∈ states)
    {φ ψ : PositiveLTL AP}
    (hstate : state.1 = PositiveLTL.release φ ψ)
    (htarget :
      ∀ nextState, nextState ∈ nextStates ->
        PositiveLTL.Satisfies interp (OmegaWord.drop word 1) nextState.1) :
    PositiveLTL.Satisfies interp word ψ ∧
      (PositiveLTL.Satisfies interp word φ ∨ state ∈ nextStates) := by
  letI := dec
  let A :=
    (PositiveLTL.subformulaClosure (Letter := Letter) root).toAPA
      interp dec
  let formulaVal : PositiveLTL AP -> Prop :=
    fun θ => ∃ hθ : θ ∈ root.subformulas,
      (⟨θ, hθ⟩ : A.State) ∈ nextStates
  have hprogress :
      PosBool.Eval formulaVal (PositiveLTL.alternatingStep interp (word 0) ψ) ∧
        (PosBool.Eval formulaVal
            (PositiveLTL.alternatingStep interp (word 0) φ) ∨
          state ∈ nextStates) := by
    simpa [A, formulaVal] using
      (PositiveLTL.subformulaClosure_macroTransition_release_progress
        root interp dec word htransition hstateMem hstate)
  have hψEval :
      PosBool.Eval
        (fun θ => PositiveLTL.Satisfies interp (OmegaWord.drop word 1) θ)
        (PositiveLTL.alternatingStep interp (word 0) ψ) :=
    PosBool.eval_mono
      (fun θ hθ => by
        rcases hθ with ⟨hsub, hnext⟩
        exact htarget (⟨θ, hsub⟩ : A.State) hnext)
      (PositiveLTL.alternatingStep interp (word 0) ψ)
      hprogress.1
  refine
    ⟨(PositiveLTL.alternatingStep_correct interp word ψ).mp hψEval, ?_⟩
  rcases hprogress.2 with hφEval | hnext
  · left
    have hφEvalSat :
        PosBool.Eval
          (fun θ => PositiveLTL.Satisfies interp (OmegaWord.drop word 1) θ)
          (PositiveLTL.alternatingStep interp (word 0) φ) :=
      PosBool.eval_mono
        (fun θ hθ => by
          rcases hθ with ⟨hsub, hnext⟩
          exact htarget (⟨θ, hsub⟩ : A.State) hnext)
        (PositiveLTL.alternatingStep interp (word 0) φ)
        hφEval
    exact (PositiveLTL.alternatingStep_correct interp word φ).mp hφEvalSat
  · exact Or.inr hnext

/--
Non-circular semantic release progress for a concrete macro transition.

Unlike `subformulaClosure_macroTransition_release_satisfies_progress`, this
theorem does not assume that the whole target frontier is already true.  It
only needs target truth for formulas strictly smaller than the source release
formula.  If the transition keeps the same release state, the conclusion
returns that state-membership as the coinductive continuation.
-/
theorem PositiveLTL.subformulaClosure_macroTransition_release_satisfies_progress_of_smaller
    {AP : Type u}
    {Letter : Type v}
    [DecidableEq AP]
    (root : PositiveLTL AP)
    (interp : AP -> Letter -> Prop)
    (dec : ∀ ap letter, Decidable (interp ap letter))
    (word : OmegaWord Letter)
    {states nextStates :
      Finset
        (((PositiveLTL.subformulaClosure (Letter := Letter) root).toAPA
          interp dec).State)}
    {stateEdges :
      Finset
        ((((PositiveLTL.subformulaClosure (Letter := Letter) root).toAPA
            interp dec).State) ×
          (((PositiveLTL.subformulaClosure (Letter := Letter) root).toAPA
            interp dec).State))}
    (htransition :
      ((PositiveLTL.subformulaClosure (Letter := Letter) root).toAPA
        interp dec).MacroTransitionWithStateEdges
          states (word 0) nextStates stateEdges)
    {state :
      ((PositiveLTL.subformulaClosure (Letter := Letter) root).toAPA
        interp dec).State}
    (hstateMem : state ∈ states)
    {φ ψ : PositiveLTL AP}
    (hstate : state.1 = PositiveLTL.release φ ψ)
    (htargetSmaller :
      ∀ nextState, nextState ∈ nextStates ->
        nextState.1.size < (PositiveLTL.release φ ψ).size ->
          PositiveLTL.Satisfies interp
            (OmegaWord.drop word 1) nextState.1) :
    PositiveLTL.Satisfies interp word ψ ∧
      (PositiveLTL.Satisfies interp word φ ∨ state ∈ nextStates) := by
  letI := dec
  let A :=
    (PositiveLTL.subformulaClosure (Letter := Letter) root).toAPA
      interp dec
  let formulaVal : PositiveLTL AP -> Prop :=
    fun θ => ∃ hθ : θ ∈ root.subformulas,
      (⟨θ, hθ⟩ : A.State) ∈ nextStates
  have hprogress :
      PosBool.Eval formulaVal (PositiveLTL.alternatingStep interp (word 0) ψ) ∧
        (PosBool.Eval formulaVal
            (PositiveLTL.alternatingStep interp (word 0) φ) ∨
          state ∈ nextStates) := by
    simpa [A, formulaVal] using
      (PositiveLTL.subformulaClosure_macroTransition_release_progress
        root interp dec word htransition hstateMem hstate)
  have hψEval :
      PosBool.Eval
        (fun θ => PositiveLTL.Satisfies interp (OmegaWord.drop word 1) θ)
        (PositiveLTL.alternatingStep interp (word 0) ψ) := by
    refine
      PosBool.eval_mono_of_imp_on_atoms
        (PositiveLTL.alternatingStep interp (word 0) ψ)
        ?_
        hprogress.1
    intro θ hmem hθ
    rcases hθ with ⟨hθRoot, hθNext⟩
    have hθlt :
        θ.size < (PositiveLTL.release φ ψ).size := by
      rcases
        PositiveLTL.alternatingStep_atoms_self_or_size_lt
          interp (word 0) ψ θ hmem with hself | hlt
      · rw [hself]
        exact PositiveLTL.size_lt_release_right φ ψ
      · exact Nat.lt_trans hlt (PositiveLTL.size_lt_release_right φ ψ)
    exact htargetSmaller (⟨θ, hθRoot⟩ : A.State) hθNext hθlt
  refine
    ⟨(PositiveLTL.alternatingStep_correct interp word ψ).mp hψEval, ?_⟩
  rcases hprogress.2 with hφEval | hnext
  · left
    have hφEvalSat :
        PosBool.Eval
          (fun θ => PositiveLTL.Satisfies interp (OmegaWord.drop word 1) θ)
          (PositiveLTL.alternatingStep interp (word 0) φ) := by
      refine
        PosBool.eval_mono_of_imp_on_atoms
          (PositiveLTL.alternatingStep interp (word 0) φ)
          ?_
          hφEval
      intro θ hmem hθ
      rcases hθ with ⟨hθRoot, hθNext⟩
      have hθlt :
          θ.size < (PositiveLTL.release φ ψ).size := by
        rcases
          PositiveLTL.alternatingStep_atoms_self_or_size_lt
            interp (word 0) φ θ hmem with hself | hlt
        · rw [hself]
          exact PositiveLTL.size_lt_release_left φ ψ
        · exact Nat.lt_trans hlt (PositiveLTL.size_lt_release_left φ ψ)
      exact htargetSmaller (⟨θ, hθRoot⟩ : A.State) hθNext hθlt
    exact
      (PositiveLTL.alternatingStep_correct interp word φ).mp hφEvalSat
  · exact Or.inr hnext

/--
Run-based fixed-point progress for accepting `until` states.

Unlike the `AcceptsFrom` version below, this theorem keeps the successor inside
the same accepting run tree.  If the `ψ` branch of the tableau is impossible
among the actual active root children, then the run has an active self-loop
child for `φ U ψ`; the subtree below that child is accepting.
-/
theorem PositiveLTL.subformulaClosure_until_acceptingRun_progress_of_not_right
    {AP : Type u}
    {Letter : Type v}
    [DecidableEq AP]
    (root : PositiveLTL AP)
    (interp : AP -> Letter -> Prop)
    (dec : ∀ ap letter, Decidable (interp ap letter))
    (state : root.Subformula)
    (word : OmegaWord Letter)
    (φ ψ : PositiveLTL AP)
    (hstate : state.1 = PositiveLTL.until φ ψ)
    (run :
      (((PositiveLTL.subformulaClosure (Letter := Letter) root).toAPA
        interp dec).withInitial state).Run word)
    (hacc : run.Accepting)
    (hnotRight :
      ¬ PosBool.Eval
        (fun θ =>
          ∃ hθ : θ ∈ root.subformulas,
            ∃ child : Nat,
              run.active [child] ∧
                run.stateAt [child] = (⟨θ, hθ⟩ : root.Subformula))
        (PositiveLTL.alternatingStep interp (word 0) ψ)) :
    PosBool.Eval
        (fun θ =>
          ∃ hθ : θ ∈ root.subformulas,
            ∃ child : Nat,
              run.active [child] ∧
                run.stateAt [child] = (⟨θ, hθ⟩ : root.Subformula))
        (PositiveLTL.alternatingStep interp (word 0) φ) ∧
      ∃ child : Nat,
        ∃ hchild : run.active [child],
          run.stateAt [child] = state ∧
            (run.childRun child hchild).Accepting := by
  let closure := PositiveLTL.subformulaClosure (Letter := Letter) root
  let A := closure.toAPA interp dec
  let step : PosBool (PositiveLTL AP) :=
    PositiveLTL.alternatingStep interp (word 0) state.1
  let valuation : root.Subformula -> Prop :=
    fun nextState =>
      ∃ child : Nat,
        run.active [child] ∧ run.stateAt [child] = nextState
  let formulaVal : PositiveLTL AP -> Prop :=
    fun θ =>
      ∃ hθ : θ ∈ root.subformulas,
        ∃ child : Nat,
          run.active [child] ∧
            run.stateAt [child] = (⟨θ, hθ⟩ : root.Subformula)
  have hrootState : run.stateAt [] = state := by
    simpa [A, closure, AlternatingParityAutomaton.withInitial] using run.root_state
  have hstepRun := run.step_satisfied [] run.root_active
  have hstepActive :
      PosBool.Eval valuation
        (step.pmap
          (fun θ hθ =>
            (⟨θ,
              PositiveLTL.subformulas_trans
                (PositiveLTL.alternatingStep_atoms_subformulas
                  interp (word 0) state.1 θ hθ)
                state.2⟩ : root.Subformula))) := by
    change
      PosBool.Eval
        (fun nextState : root.Subformula =>
          ∃ child : Nat,
            run.active [child] ∧ run.stateAt [child] = nextState)
        (((A.withInitial state).step (run.stateAt []) (word 0))) at hstepRun
    rw [hrootState] at hstepRun
    simpa [A, closure, PositiveLTL.subformulaClosure,
      AlternatingParityAutomaton.withInitial,
      FiniteLTLAlternatingClosure.toAPA, PositiveLTL.subformulaTransition,
      step, valuation] using hstepRun
  have hraw :
      PosBool.Eval formulaVal step :=
    PositiveLTL.eval_exists_subformula_of_eval_pmap
      root step
      (fun θ hθ =>
        PositiveLTL.subformulas_trans
          (PositiveLTL.alternatingStep_atoms_subformulas
            interp (word 0) state.1 θ hθ)
          state.2)
      valuation hstepActive
  have hrawUntil :
      PosBool.Eval formulaVal
        (PositiveLTL.alternatingStep interp (word 0)
          (PositiveLTL.until φ ψ)) := by
    simpa [step, hstate] using hraw
  rcases
    PositiveLTL.alternatingStep_until_progress_of_not_right
      interp (word 0) φ ψ formulaVal hrawUntil
      (by simpa [formulaVal] using hnotRight) with
    ⟨hleft, hself⟩
  constructor
  · simpa [formulaVal] using hleft
  · rcases hself with ⟨hselfMem, child, hchildActive, hchildState⟩
    have hselfState :
        (⟨PositiveLTL.until φ ψ, hselfMem⟩ : root.Subformula) = state :=
      Subtype.ext hstate.symm
    refine ⟨child, hchildActive, ?_, ?_⟩
    · simpa [hselfState] using hchildState
    · exact run.childRun_accepting child hchildActive hacc

/--
Semantic run-based fixed-point progress for accepting `until` states.

This is the run-coherent counterpart of
`subformulaClosure_until_acceptsFrom_semantic_progress`: the self-loop successor
is an actual active child of the given accepting run tree, not a newly chosen
accepting witness.
-/
theorem PositiveLTL.subformulaClosure_until_acceptingRun_semantic_progress
    {AP : Type u}
    {Letter : Type v}
    [DecidableEq AP]
    (root : PositiveLTL AP)
    (interp : AP -> Letter -> Prop)
    (dec : ∀ ap letter, Decidable (interp ap letter))
    (state : root.Subformula)
    (word : OmegaWord Letter)
    (φ ψ : PositiveLTL AP)
    (hstate : state.1 = PositiveLTL.until φ ψ)
    (run :
      (((PositiveLTL.subformulaClosure (Letter := Letter) root).toAPA
        interp dec).withInitial state).Run word)
    (hacc : run.Accepting)
    (hnotψ : ¬ PositiveLTL.Satisfies interp word ψ)
    (hsuccessors :
      ∀ child : Nat,
        ∀ hchild : run.active [child],
          (run.stateAt [child]).1.size < (PositiveLTL.until φ ψ).size ->
            PositiveLTL.Satisfies interp (OmegaWord.drop word 1)
              (run.stateAt [child]).1) :
    PositiveLTL.Satisfies interp word φ ∧
      ∃ child : Nat,
        ∃ hchild : run.active [child],
          run.stateAt [child] = state ∧
            (run.childRun child hchild).Accepting := by
  let formulaVal : PositiveLTL AP -> Prop :=
    fun θ =>
      ∃ hθ : θ ∈ root.subformulas,
        ∃ child : Nat,
          run.active [child] ∧
            run.stateAt [child] = (⟨θ, hθ⟩ : root.Subformula)
  have hnotRight :
      ¬ PosBool.Eval formulaVal
        (PositiveLTL.alternatingStep interp (word 0) ψ) := by
    intro hright
    have hrightSatisfies :
        PosBool.Eval
          (fun θ =>
            PositiveLTL.Satisfies interp (OmegaWord.drop word 1) θ)
          (PositiveLTL.alternatingStep interp (word 0) ψ) := by
      refine
        PosBool.eval_mono_of_imp_on_atoms
          (PositiveLTL.alternatingStep interp (word 0) ψ)
          ?_ hright
      intro θ hmem hθActive
      rcases hθActive with ⟨hθRoot, child, hchildActive, hchildState⟩
      have hθltUntil :
          θ.size < (PositiveLTL.until φ ψ).size := by
        rcases
          PositiveLTL.alternatingStep_atoms_self_or_size_lt
            interp (word 0) ψ θ hmem with hself | hlt
        · rw [hself]
          exact PositiveLTL.size_lt_until_right φ ψ
        · exact Nat.lt_trans hlt (PositiveLTL.size_lt_until_right φ ψ)
      have hchildSize :
          (run.stateAt [child]).1.size < (PositiveLTL.until φ ψ).size := by
        simpa [hchildState] using hθltUntil
      have hchildSat :=
        hsuccessors child hchildActive hchildSize
      simpa [hchildState] using hchildSat
    exact hnotψ
      ((PositiveLTL.alternatingStep_correct interp word ψ).mp
        hrightSatisfies)
  rcases
    PositiveLTL.subformulaClosure_until_acceptingRun_progress_of_not_right
      root interp dec state word φ ψ hstate run hacc
      (by simpa [formulaVal] using hnotRight) with
    ⟨hleftActive, hself⟩
  have hleftSatisfies :
      PosBool.Eval
        (fun θ =>
          PositiveLTL.Satisfies interp (OmegaWord.drop word 1) θ)
        (PositiveLTL.alternatingStep interp (word 0) φ) := by
    refine
      PosBool.eval_mono_of_imp_on_atoms
        (PositiveLTL.alternatingStep interp (word 0) φ)
        ?_ hleftActive
    intro θ hmem hθActive
    rcases hθActive with ⟨hθRoot, child, hchildActive, hchildState⟩
    have hθltUntil :
        θ.size < (PositiveLTL.until φ ψ).size := by
      rcases
        PositiveLTL.alternatingStep_atoms_self_or_size_lt
          interp (word 0) φ θ hmem with hselfFormula | hlt
      · rw [hselfFormula]
        exact PositiveLTL.size_lt_until_left φ ψ
      · exact Nat.lt_trans hlt (PositiveLTL.size_lt_until_left φ ψ)
    have hchildSize :
        (run.stateAt [child]).1.size < (PositiveLTL.until φ ψ).size := by
      simpa [hchildState] using hθltUntil
    have hchildSat :=
      hsuccessors child hchildActive hchildSize
    simpa [hchildState] using hchildSat
  exact
    ⟨(PositiveLTL.alternatingStep_correct interp word φ).mp
        hleftSatisfies,
      hself⟩

/--
Node-local run-based fixed-point progress for accepting `until` states.

This is the continuation form needed by the game view: after any finite active
history, the subtree below the current node is still accepting, and the usual
`until` progress argument applies to that continuation.
-/
theorem PositiveLTL.subformulaClosure_until_acceptingRun_semantic_progress_at_node
    {AP : Type u}
    {Letter : Type v}
    [DecidableEq AP]
    (root : PositiveLTL AP)
    (interp : AP -> Letter -> Prop)
    (dec : ∀ ap letter, Decidable (interp ap letter))
    (initial : root.Subformula)
    (word : OmegaWord Letter)
    (run :
      (((PositiveLTL.subformulaClosure (Letter := Letter) root).toAPA
        interp dec).withInitial initial).Run word)
    (hacc : run.Accepting)
    (node : AlternatingParityAutomaton.Node)
    (hpath : run.PathActive node)
    (φ ψ : PositiveLTL AP)
    (hstate :
      (run.stateAt node).1 = PositiveLTL.until φ ψ)
    (hnotψ :
      ¬ PositiveLTL.Satisfies interp (OmegaWord.drop word node.length) ψ)
    (hsuccessors :
      ∀ child : Nat,
        ∀ hchild : (run.subRun node (run.pathActive_self node hpath)).active [child],
          (((run.subRun node (run.pathActive_self node hpath)).stateAt [child]).1).size <
              (PositiveLTL.until φ ψ).size ->
            PositiveLTL.Satisfies interp
              (OmegaWord.drop (OmegaWord.drop word node.length) 1)
              ((run.subRun node
                (run.pathActive_self node hpath)).stateAt [child]).1) :
    PositiveLTL.Satisfies interp (OmegaWord.drop word node.length) φ ∧
      ∃ child : Nat,
        ∃ hchild : (run.subRun node (run.pathActive_self node hpath)).active [child],
          (run.subRun node
            (run.pathActive_self node hpath)).stateAt [child] = run.stateAt node ∧
            ((run.subRun node
              (run.pathActive_self node hpath)).childRun child hchild).Accepting := by
  let closure := PositiveLTL.subformulaClosure (Letter := Letter) root
  let A := closure.toAPA interp dec
  let hnode : run.active node := run.pathActive_self node hpath
  let sub :
      (A.withInitial (run.stateAt node)).Run
        (OmegaWord.drop word node.length) := by
    simpa [A, closure, AlternatingParityAutomaton.withInitial] using
      (run.subRun node hnode)
  have hsubAcc : sub.Accepting := by
    simpa [sub] using
      (run.subRun_accepting node hpath hnode hacc)
  have hsucc :
      ∀ child : Nat,
        ∀ hchild : sub.active [child],
          (sub.stateAt [child]).1.size < (PositiveLTL.until φ ψ).size ->
            PositiveLTL.Satisfies interp
              (OmegaWord.drop (OmegaWord.drop word node.length) 1)
              (sub.stateAt [child]).1 := by
    intro child hchild hlt
    exact hsuccessors child (by simpa [sub, hnode] using hchild)
      (by simpa [sub] using hlt)
  rcases
    PositiveLTL.subformulaClosure_until_acceptingRun_semantic_progress
      root interp dec (run.stateAt node) (OmegaWord.drop word node.length)
      φ ψ hstate sub hsubAcc hnotψ hsucc with
    ⟨hφ, child, hchild, hchildState, hchildAcc⟩
  refine ⟨hφ, child, ?_, ?_, ?_⟩
  · simpa [sub, hnode] using hchild
  · simpa [sub] using hchildState
  · simpa [sub] using hchildAcc

/--
An accepting run from an `until` state cannot avoid the right-hand side
forever.  Otherwise node-local progress repeatedly produces an active
self-loop branch whose priority is eventually the odd `until` priority,
contradicting parity acceptance.
-/
theorem PositiveLTL.subformulaClosure_until_acceptingRun_not_never_right
    {AP : Type u}
    {Letter : Type v}
    [DecidableEq AP]
    (root : PositiveLTL AP)
    (interp : AP -> Letter -> Prop)
    (dec : ∀ ap letter, Decidable (interp ap letter))
    (state : root.Subformula)
    (word : OmegaWord Letter)
    (φ ψ : PositiveLTL AP)
    (hstate : state.1 = PositiveLTL.until φ ψ)
    (run :
      (((PositiveLTL.subformulaClosure (Letter := Letter) root).toAPA
        interp dec).withInitial state).Run word)
    (hacc : run.Accepting)
    (hsuccessors :
      ∀ n : Nat,
      ∀ nextState : root.Subformula,
        nextState.1.size < (PositiveLTL.until φ ψ).size ->
        ((PositiveLTL.subformulaClosure (Letter := Letter) root).toAPA
          interp dec).AcceptsFrom nextState (OmegaWord.drop word (n + 1)) ->
        PositiveLTL.Satisfies interp (OmegaWord.drop word (n + 1))
          nextState.1)
    (hneverψ :
      ∀ n : Nat,
        ¬ PositiveLTL.Satisfies interp (OmegaWord.drop word n) ψ) :
    False := by
  let closure := PositiveLTL.subformulaClosure (Letter := Letter) root
  let A := closure.toAPA interp dec
  let P : AlternatingParityAutomaton.Node -> Prop :=
    fun node => run.stateAt node = state
  have hrootP : P [] := by
    simpa [P, A, closure, AlternatingParityAutomaton.withInitial]
      using run.root_state
  have hstep :
      ∀ node : AlternatingParityAutomaton.Node,
        run.PathActive node ->
          P node ->
            ∃ child : Nat, run.active (child :: node) ∧ P (child :: node) := by
    intro node hpath hnodeState
    have hnodeUntil :
        (run.stateAt node).1 = PositiveLTL.until φ ψ := by
      exact (congrArg Subtype.val hnodeState).trans hstate
    have hnotψ :
        ¬ PositiveLTL.Satisfies interp (OmegaWord.drop word node.length) ψ := by
      exact hneverψ node.length
    have hsucc :
        ∀ child : Nat,
          ∀ hchild :
            (run.subRun node (run.pathActive_self node hpath)).active [child],
            (((run.subRun node
              (run.pathActive_self node hpath)).stateAt [child]).1).size <
                (PositiveLTL.until φ ψ).size ->
              PositiveLTL.Satisfies interp
                (OmegaWord.drop (OmegaWord.drop word node.length) 1)
                ((run.subRun node
                  (run.pathActive_self node hpath)).stateAt [child]).1 := by
      intro child hchild hlt
      have hsubAcc :
          (run.subRun node (run.pathActive_self node hpath)).Accepting :=
        run.subRun_accepting node hpath (run.pathActive_self node hpath) hacc
      have hchildAccepts :
          A.AcceptsFrom
            ((run.subRun node
              (run.pathActive_self node hpath)).stateAt [child])
            (OmegaWord.drop word (node.length + 1)) := by
        have hraw :=
          (run.subRun node
            (run.pathActive_self node hpath)).childRun_acceptsFrom
              child hchild hsubAcc
        simpa [A, closure, AlternatingParityAutomaton.withInitial,
          OmegaWord.drop_drop, Nat.add_comm, Nat.add_assoc] using hraw
      have hsat :=
        hsuccessors node.length
          ((run.subRun node
            (run.pathActive_self node hpath)).stateAt [child])
          hlt hchildAccepts
      simpa [OmegaWord.drop_drop, Nat.add_comm, Nat.add_assoc] using hsat
    rcases
      PositiveLTL.subformulaClosure_until_acceptingRun_semantic_progress_at_node
        root interp dec state word run hacc node hpath φ ψ
        hnodeUntil hnotψ hsucc with
      ⟨_hφ, child, hchild, hchildState, _hchildAcc⟩
    refine ⟨child, ?_, ?_⟩
    · simpa using hchild
    · have hchildState' :
          run.stateAt (child :: node) = run.stateAt node := by
        simpa using hchildState
      simpa [P, hnodeState] using hchildState'
  let branch := run.choicePathBranch P hrootP hstep
  have hbranchActive : run.ActiveBranch branch :=
    run.choicePathBranch_active P hrootP hstep
  let p := PositiveLTL.alternatingPriority root (PositiveLTL.until φ ψ)
  have hpOdd : ¬ DetParityAutomaton.NatEven p := by
    simpa [p] using
      PositiveLTL.alternatingPriority_until_not_even root φ ψ
  have heventual :
      ∃ N : Nat,
        ∀ n : Nat, N ≤ n ->
          ((PositiveLTL.subformulaClosure (Letter := Letter) root).toAPA
            interp dec).priority
            (run.stateAt (AlternatingParityAutomaton.branchPrefix branch n)) = p := by
    refine ⟨0, ?_⟩
    intro n _hn
    have hP := run.choicePathBranch_property P hrootP hstep n
    change PositiveLTL.alternatingPriority root
      (run.stateAt (AlternatingParityAutomaton.branchPrefix branch n)).1 = p
    exact congrArg (PositiveLTL.alternatingPriority root)
      ((congrArg Subtype.val hP).trans hstate)
  exact
    (run.not_accepting_of_eventually_odd_priority branch hbranchActive p
      hpOdd heventual) hacc

/--
Closure-level fixed-point progress for accepting `until` states.

If an accepting run from `φ U ψ` cannot proceed through the right-side tableau
branch, then it must provide accepting successors for the left branch and for
the `until` self-loop on the suffix.
-/
theorem PositiveLTL.subformulaClosure_until_acceptsFrom_progress_of_not_right
    {AP : Type u}
    {Letter : Type v}
    [DecidableEq AP]
    (root : PositiveLTL AP)
    (interp : AP -> Letter -> Prop)
    (dec : ∀ ap letter, Decidable (interp ap letter))
    (state : root.Subformula)
    (word : OmegaWord Letter)
    (φ ψ : PositiveLTL AP)
    (hstate : state.1 = PositiveLTL.until φ ψ)
    (haccepts :
      ((PositiveLTL.subformulaClosure (Letter := Letter) root).toAPA
        interp dec).AcceptsFrom state word)
    (hnotRight :
      ¬ PosBool.Eval
        (fun θ =>
          ∃ hθ : θ ∈ root.subformulas,
            ((PositiveLTL.subformulaClosure (Letter := Letter) root).toAPA
              interp dec).AcceptsFrom
                (⟨θ, hθ⟩ : root.Subformula) (OmegaWord.drop word 1))
        (PositiveLTL.alternatingStep interp (word 0) ψ)) :
    PosBool.Eval
        (fun θ =>
          ∃ hθ : θ ∈ root.subformulas,
            ((PositiveLTL.subformulaClosure (Letter := Letter) root).toAPA
              interp dec).AcceptsFrom
                (⟨θ, hθ⟩ : root.Subformula) (OmegaWord.drop word 1))
        (PositiveLTL.alternatingStep interp (word 0) φ) ∧
      ((PositiveLTL.subformulaClosure (Letter := Letter) root).toAPA
        interp dec).AcceptsFrom state (OmegaWord.drop word 1) := by
  let closure := PositiveLTL.subformulaClosure (Letter := Letter) root
  let A := closure.toAPA interp dec
  let step : PosBool (PositiveLTL AP) :=
    PositiveLTL.alternatingStep interp (word 0) state.1
  let valuation : root.Subformula -> Prop :=
    fun nextState => A.AcceptsFrom nextState (OmegaWord.drop word 1)
  let formulaVal : PositiveLTL AP -> Prop :=
    fun θ =>
      ∃ hθ : θ ∈ root.subformulas,
        A.AcceptsFrom (⟨θ, hθ⟩ : root.Subformula) (OmegaWord.drop word 1)
  have hstepAccepts :
      PosBool.Eval valuation
        (step.pmap
          (fun θ hθ =>
            (⟨θ,
              PositiveLTL.subformulas_trans
                (PositiveLTL.alternatingStep_atoms_subformulas
                  interp (word 0) state.1 θ hθ)
                state.2⟩ : root.Subformula))) := by
    have hstep := A.acceptsFrom_step state word haccepts
    simpa [A, closure, PositiveLTL.subformulaClosure,
      FiniteLTLAlternatingClosure.toAPA, PositiveLTL.subformulaTransition,
      step, valuation] using hstep
  have hraw :
      PosBool.Eval formulaVal step :=
    PositiveLTL.eval_exists_subformula_of_eval_pmap
      root step
      (fun θ hθ =>
        PositiveLTL.subformulas_trans
          (PositiveLTL.alternatingStep_atoms_subformulas
            interp (word 0) state.1 θ hθ)
          state.2)
      valuation hstepAccepts
  have hrawUntil :
      PosBool.Eval formulaVal
        (PositiveLTL.alternatingStep interp (word 0)
          (PositiveLTL.until φ ψ)) := by
    simpa [step, hstate] using hraw
  rcases
    PositiveLTL.alternatingStep_until_progress_of_not_right
      interp (word 0) φ ψ formulaVal hrawUntil
      (by simpa [formulaVal, A, closure] using hnotRight) with
    ⟨hleft, hself⟩
  refine ⟨by simpa [formulaVal, A, closure] using hleft, ?_⟩
  rcases hself with ⟨hselfMem, hselfAccepts⟩
  have hselfState :
      (⟨PositiveLTL.until φ ψ, hselfMem⟩ : root.Subformula) = state :=
    Subtype.ext hstate.symm
  simpa [A, closure, hselfState] using hselfAccepts

/--
Semantic fixed-point progress for accepting `until` states.

Under the structural induction hypothesis for strict subformulas, an accepting
run from `φ U ψ` with `ψ` false must satisfy `φ` now and keep accepting the same
`until` obligation on the suffix.
-/
theorem PositiveLTL.subformulaClosure_until_acceptsFrom_semantic_progress
    {AP : Type u}
    {Letter : Type v}
    [DecidableEq AP]
    (root : PositiveLTL AP)
    (interp : AP -> Letter -> Prop)
    (dec : ∀ ap letter, Decidable (interp ap letter))
    (state : root.Subformula)
    (word : OmegaWord Letter)
    (φ ψ : PositiveLTL AP)
    (hstate : state.1 = PositiveLTL.until φ ψ)
    (haccepts :
      ((PositiveLTL.subformulaClosure (Letter := Letter) root).toAPA
        interp dec).AcceptsFrom state word)
    (hnotψ : ¬ PositiveLTL.Satisfies interp word ψ)
    (hsuccessors :
      ∀ nextState : root.Subformula,
        nextState.1.size < (PositiveLTL.until φ ψ).size ->
        ((PositiveLTL.subformulaClosure (Letter := Letter) root).toAPA
          interp dec).AcceptsFrom nextState (OmegaWord.drop word 1) ->
        PositiveLTL.Satisfies interp (OmegaWord.drop word 1) nextState.1) :
    PositiveLTL.Satisfies interp word φ ∧
      ((PositiveLTL.subformulaClosure (Letter := Letter) root).toAPA
        interp dec).AcceptsFrom state (OmegaWord.drop word 1) := by
  let A :=
    (PositiveLTL.subformulaClosure (Letter := Letter) root).toAPA interp dec
  let formulaVal : PositiveLTL AP -> Prop :=
    fun θ =>
      ∃ hθ : θ ∈ root.subformulas,
        A.AcceptsFrom (⟨θ, hθ⟩ : root.Subformula) (OmegaWord.drop word 1)
  have hnotRight :
      ¬ PosBool.Eval formulaVal
        (PositiveLTL.alternatingStep interp (word 0) ψ) := by
    intro hright
    have hrightSatisfies :
        PosBool.Eval
          (fun θ =>
            PositiveLTL.Satisfies interp (OmegaWord.drop word 1) θ)
          (PositiveLTL.alternatingStep interp (word 0) ψ) := by
      refine
        PosBool.eval_mono_of_imp_on_atoms
          (PositiveLTL.alternatingStep interp (word 0) ψ)
          ?_ hright
      intro θ hmem hθAccepts
      rcases hθAccepts with ⟨hθRoot, hθAccepts⟩
      have hθltUntil :
          θ.size < (PositiveLTL.until φ ψ).size := by
        rcases
          PositiveLTL.alternatingStep_atoms_self_or_size_lt
            interp (word 0) ψ θ hmem with hself | hlt
        · rw [hself]
          exact PositiveLTL.size_lt_until_right φ ψ
        · exact Nat.lt_trans hlt (PositiveLTL.size_lt_until_right φ ψ)
      exact hsuccessors
        (⟨θ, hθRoot⟩ : root.Subformula) hθltUntil hθAccepts
    exact hnotψ
      ((PositiveLTL.alternatingStep_correct interp word ψ).mp
        hrightSatisfies)
  rcases
    PositiveLTL.subformulaClosure_until_acceptsFrom_progress_of_not_right
      root interp dec state word φ ψ hstate haccepts
      (by simpa [formulaVal, A] using hnotRight) with
    ⟨hleftAccepts, hselfAccepts⟩
  have hleftSatisfies :
      PosBool.Eval
        (fun θ =>
          PositiveLTL.Satisfies interp (OmegaWord.drop word 1) θ)
        (PositiveLTL.alternatingStep interp (word 0) φ) := by
    refine
      PosBool.eval_mono_of_imp_on_atoms
        (PositiveLTL.alternatingStep interp (word 0) φ)
        ?_ hleftAccepts
    intro θ hmem hθAccepts
    rcases hθAccepts with ⟨hθRoot, hθAccepts⟩
    have hθltUntil :
        θ.size < (PositiveLTL.until φ ψ).size := by
      rcases
        PositiveLTL.alternatingStep_atoms_self_or_size_lt
          interp (word 0) φ θ hmem with hself | hlt
      · rw [hself]
        exact PositiveLTL.size_lt_until_left φ ψ
      · exact Nat.lt_trans hlt (PositiveLTL.size_lt_until_left φ ψ)
    exact hsuccessors
      (⟨θ, hθRoot⟩ : root.Subformula) hθltUntil hθAccepts
  exact
    ⟨(PositiveLTL.alternatingStep_correct interp word φ).mp
        hleftSatisfies,
      hselfAccepts⟩

/--
Iterated fixed-point progress for accepting `until` states.

If the right side never holds along the first `n` suffixes, then accepting the
same `φ U ψ` state forces `φ` on each of those suffixes and preserves the
accepting `until` obligation at suffix `n`.
-/
theorem PositiveLTL.subformulaClosure_until_acceptsFrom_semantic_progress_iterate
    {AP : Type u}
    {Letter : Type v}
    [DecidableEq AP]
    (root : PositiveLTL AP)
    (interp : AP -> Letter -> Prop)
    (dec : ∀ ap letter, Decidable (interp ap letter))
    (state : root.Subformula)
    (word : OmegaWord Letter)
    (φ ψ : PositiveLTL AP)
    (hstate : state.1 = PositiveLTL.until φ ψ)
    (hsuccessors :
      ∀ n : Nat,
      ∀ nextState : root.Subformula,
        nextState.1.size < (PositiveLTL.until φ ψ).size ->
        ((PositiveLTL.subformulaClosure (Letter := Letter) root).toAPA
          interp dec).AcceptsFrom nextState (OmegaWord.drop word (n + 1)) ->
        PositiveLTL.Satisfies interp (OmegaWord.drop word (n + 1))
          nextState.1)
    (hnotψ : ∀ n : Nat,
      ¬ PositiveLTL.Satisfies interp (OmegaWord.drop word n) ψ)
    (n : Nat)
    (haccepts :
      ((PositiveLTL.subformulaClosure (Letter := Letter) root).toAPA
        interp dec).AcceptsFrom state word) :
    (∀ k : Nat, k < n ->
      PositiveLTL.Satisfies interp (OmegaWord.drop word k) φ) ∧
    ((PositiveLTL.subformulaClosure (Letter := Letter) root).toAPA
      interp dec).AcceptsFrom state (OmegaWord.drop word n) := by
  induction n with
  | zero =>
      constructor
      · intro k hk
        exact False.elim (Nat.not_lt_zero k hk)
      · simpa using haccepts
  | succ n ih =>
      rcases ih with ⟨hφBefore, hacceptsAtN⟩
      have hstep :
          PositiveLTL.Satisfies interp (OmegaWord.drop word n) φ ∧
          ((PositiveLTL.subformulaClosure (Letter := Letter) root).toAPA
            interp dec).AcceptsFrom state
              (OmegaWord.drop (OmegaWord.drop word n) 1) := by
        refine
          PositiveLTL.subformulaClosure_until_acceptsFrom_semantic_progress
            root interp dec state (OmegaWord.drop word n) φ ψ hstate
            hacceptsAtN (hnotψ n) ?_
        intro nextState hlt hnextAccepts
        have hnextAccepts' :
            ((PositiveLTL.subformulaClosure (Letter := Letter) root).toAPA
              interp dec).AcceptsFrom nextState
                (OmegaWord.drop word (n + 1)) := by
          simpa [OmegaWord.drop_drop, Nat.add_comm, Nat.add_assoc]
            using hnextAccepts
        have hsatisfies' :
            PositiveLTL.Satisfies interp (OmegaWord.drop word (n + 1))
              nextState.1 :=
          hsuccessors n nextState hlt hnextAccepts'
        simpa [OmegaWord.drop_drop, Nat.add_comm, Nat.add_assoc]
          using hsatisfies'
      constructor
      · intro k hk
        have hkLe : k ≤ n := Nat.le_of_lt_succ hk
        by_cases hkLt : k < n
        · exact hφBefore k hkLt
        · have hnLe : n ≤ k := Nat.le_of_not_gt hkLt
          have hkEq : k = n := Nat.le_antisymm hkLe hnLe
          subst k
          exact hstep.1
      · simpa [OmegaWord.drop_drop, Nat.add_comm, Nat.add_assoc]
          using hstep.2

/--
Bounded fixed-point progress for accepting `until` states.

Only the first `n` suffixes have to exclude the right side.  This is the form
used with the least future occurrence of the right side when proving reverse
semantic soundness.
-/
theorem PositiveLTL.subformulaClosure_until_acceptsFrom_semantic_progress_until
    {AP : Type u}
    {Letter : Type v}
    [DecidableEq AP]
    (root : PositiveLTL AP)
    (interp : AP -> Letter -> Prop)
    (dec : ∀ ap letter, Decidable (interp ap letter))
    (state : root.Subformula)
    (word : OmegaWord Letter)
    (φ ψ : PositiveLTL AP)
    (hstate : state.1 = PositiveLTL.until φ ψ)
    (hsuccessors :
      ∀ n : Nat,
      ∀ nextState : root.Subformula,
        nextState.1.size < (PositiveLTL.until φ ψ).size ->
        ((PositiveLTL.subformulaClosure (Letter := Letter) root).toAPA
          interp dec).AcceptsFrom nextState (OmegaWord.drop word (n + 1)) ->
        PositiveLTL.Satisfies interp (OmegaWord.drop word (n + 1))
          nextState.1)
    (n : Nat)
    (hnotψ : ∀ k : Nat, k < n ->
      ¬ PositiveLTL.Satisfies interp (OmegaWord.drop word k) ψ)
    (haccepts :
      ((PositiveLTL.subformulaClosure (Letter := Letter) root).toAPA
        interp dec).AcceptsFrom state word) :
    (∀ k : Nat, k < n ->
      PositiveLTL.Satisfies interp (OmegaWord.drop word k) φ) ∧
    ((PositiveLTL.subformulaClosure (Letter := Letter) root).toAPA
      interp dec).AcceptsFrom state (OmegaWord.drop word n) := by
  induction n with
  | zero =>
      constructor
      · intro k hk
        exact False.elim (Nat.not_lt_zero k hk)
      · simpa using haccepts
  | succ n ih =>
      have hnotBefore : ∀ k : Nat, k < n ->
          ¬ PositiveLTL.Satisfies interp (OmegaWord.drop word k) ψ := by
        intro k hk
        exact hnotψ k (Nat.lt_trans hk (Nat.lt_succ_self n))
      rcases ih hnotBefore with ⟨hφBefore, hacceptsAtN⟩
      have hstep :
          PositiveLTL.Satisfies interp (OmegaWord.drop word n) φ ∧
          ((PositiveLTL.subformulaClosure (Letter := Letter) root).toAPA
            interp dec).AcceptsFrom state
              (OmegaWord.drop (OmegaWord.drop word n) 1) := by
        refine
          PositiveLTL.subformulaClosure_until_acceptsFrom_semantic_progress
            root interp dec state (OmegaWord.drop word n) φ ψ hstate
            hacceptsAtN (hnotψ n (Nat.lt_succ_self n)) ?_
        intro nextState hlt hnextAccepts
        have hnextAccepts' :
            ((PositiveLTL.subformulaClosure (Letter := Letter) root).toAPA
              interp dec).AcceptsFrom nextState
                (OmegaWord.drop word (n + 1)) := by
          simpa [OmegaWord.drop_drop, Nat.add_comm, Nat.add_assoc]
            using hnextAccepts
        have hsatisfies' :
            PositiveLTL.Satisfies interp (OmegaWord.drop word (n + 1))
              nextState.1 :=
          hsuccessors n nextState hlt hnextAccepts'
        simpa [OmegaWord.drop_drop, Nat.add_comm, Nat.add_assoc]
          using hsatisfies'
      constructor
      · intro k hk
        have hkLe : k ≤ n := Nat.le_of_lt_succ hk
        by_cases hkLt : k < n
        · exact hφBefore k hkLt
        · have hnLe : n ≤ k := Nat.le_of_not_gt hkLt
          have hkEq : k = n := Nat.le_antisymm hkLe hnLe
          subst k
          exact hstep.1
      · simpa [OmegaWord.drop_drop, Nat.add_comm, Nat.add_assoc]
          using hstep.2

/--
Reverse semantic soundness for accepting canonical `until` states.

The proof is the fixed-point argument: if the right side never appears, the
run-level self-loop extraction above yields an odd recurring branch; otherwise
take the first right-side occurrence and use bounded progress for all earlier
positions.
-/
theorem PositiveLTL.subformulaClosure_until_acceptsFrom_satisfies
    {AP : Type u}
    {Letter : Type v}
    [DecidableEq AP]
    (root : PositiveLTL AP)
    (interp : AP -> Letter -> Prop)
    (dec : ∀ ap letter, Decidable (interp ap letter))
    (state : root.Subformula)
    (word : OmegaWord Letter)
    (φ ψ : PositiveLTL AP)
    (hstate : state.1 = PositiveLTL.until φ ψ)
    (haccepts :
      ((PositiveLTL.subformulaClosure (Letter := Letter) root).toAPA
        interp dec).AcceptsFrom state word)
    (hsuccessors :
      ∀ n : Nat,
      ∀ nextState : root.Subformula,
        nextState.1.size < (PositiveLTL.until φ ψ).size ->
        ((PositiveLTL.subformulaClosure (Letter := Letter) root).toAPA
          interp dec).AcceptsFrom nextState (OmegaWord.drop word (n + 1)) ->
        PositiveLTL.Satisfies interp (OmegaWord.drop word (n + 1))
          nextState.1) :
    PositiveLTL.Satisfies interp word state.1 := by
  classical
  rw [hstate]
  by_cases hexists :
      ∃ n : Nat,
        PositiveLTL.Satisfies interp (OmegaWord.drop word n) ψ
  · let n := Nat.find hexists
    have hψn :
        PositiveLTL.Satisfies interp (OmegaWord.drop word n) ψ := by
      simpa [n] using Nat.find_spec hexists
    have hnotBefore :
        ∀ k : Nat, k < n ->
          ¬ PositiveLTL.Satisfies interp (OmegaWord.drop word k) ψ := by
      intro k hk
      simpa [n] using (Nat.find_min (p :=
        fun m => PositiveLTL.Satisfies interp (OmegaWord.drop word m) ψ)
        hexists hk)
    rcases
      PositiveLTL.subformulaClosure_until_acceptsFrom_semantic_progress_until
        root interp dec state word φ ψ hstate hsuccessors n hnotBefore
        haccepts with
      ⟨hφBefore, _hacceptsAtN⟩
    exact ⟨n, hψn, hφBefore⟩
  · rcases haccepts with ⟨run, hacc⟩
    have hneverψ :
        ∀ n : Nat,
          ¬ PositiveLTL.Satisfies interp (OmegaWord.drop word n) ψ := by
      intro n hψn
      exact hexists ⟨n, hψn⟩
    exact False.elim
      (PositiveLTL.subformulaClosure_until_acceptingRun_not_never_right
        root interp dec state word φ ψ hstate run hacc hsuccessors hneverψ)

/--
Semantic fixed-point progress for accepting `release` states.

The release tableau always requires the right side now.  The left side may
close the obligation now; otherwise the self-loop keeps the same release state
accepted on the suffix.
-/
theorem PositiveLTL.subformulaClosure_release_acceptsFrom_semantic_progress
    {AP : Type u}
    {Letter : Type v}
    [DecidableEq AP]
    (root : PositiveLTL AP)
    (interp : AP -> Letter -> Prop)
    (dec : ∀ ap letter, Decidable (interp ap letter))
    (state : root.Subformula)
    (word : OmegaWord Letter)
    (φ ψ : PositiveLTL AP)
    (hstate : state.1 = PositiveLTL.release φ ψ)
    (haccepts :
      ((PositiveLTL.subformulaClosure (Letter := Letter) root).toAPA
        interp dec).AcceptsFrom state word)
    (hsuccessors :
      ∀ nextState : root.Subformula,
        nextState.1.size < (PositiveLTL.release φ ψ).size ->
        ((PositiveLTL.subformulaClosure (Letter := Letter) root).toAPA
          interp dec).AcceptsFrom nextState (OmegaWord.drop word 1) ->
        PositiveLTL.Satisfies interp (OmegaWord.drop word 1) nextState.1) :
    PositiveLTL.Satisfies interp word ψ ∧
      (PositiveLTL.Satisfies interp word φ ∨
        ((PositiveLTL.subformulaClosure (Letter := Letter) root).toAPA
          interp dec).AcceptsFrom state (OmegaWord.drop word 1)) := by
  let closure := PositiveLTL.subformulaClosure (Letter := Letter) root
  let A := closure.toAPA interp dec
  let step : PosBool (PositiveLTL AP) :=
    PositiveLTL.alternatingStep interp (word 0) state.1
  let valuation : root.Subformula -> Prop :=
    fun nextState => A.AcceptsFrom nextState (OmegaWord.drop word 1)
  let formulaVal : PositiveLTL AP -> Prop :=
    fun θ =>
      ∃ hθ : θ ∈ root.subformulas,
        A.AcceptsFrom (⟨θ, hθ⟩ : root.Subformula) (OmegaWord.drop word 1)
  have hstepAccepts :
      PosBool.Eval valuation
        (step.pmap
          (fun θ hθ =>
            (⟨θ,
              PositiveLTL.subformulas_trans
                (PositiveLTL.alternatingStep_atoms_subformulas
                  interp (word 0) state.1 θ hθ)
                state.2⟩ : root.Subformula))) := by
    have hstep := A.acceptsFrom_step state word haccepts
    simpa [A, closure, PositiveLTL.subformulaClosure,
      FiniteLTLAlternatingClosure.toAPA, PositiveLTL.subformulaTransition,
      step, valuation] using hstep
  have hraw :
      PosBool.Eval formulaVal step :=
    PositiveLTL.eval_exists_subformula_of_eval_pmap
      root step
      (fun θ hθ =>
        PositiveLTL.subformulas_trans
          (PositiveLTL.alternatingStep_atoms_subformulas
            interp (word 0) state.1 θ hθ)
          state.2)
      valuation hstepAccepts
  have hrawRelease :
      PosBool.Eval formulaVal
        (PositiveLTL.alternatingStep interp (word 0)
          (PositiveLTL.release φ ψ)) := by
    simpa [step, hstate] using hraw
  rcases
    PositiveLTL.alternatingStep_release_progress
      interp (word 0) φ ψ formulaVal hrawRelease with
    ⟨hψAccepts, hleftOrSelf⟩
  have hψSatisfiesStep :
      PosBool.Eval
        (fun θ =>
          PositiveLTL.Satisfies interp (OmegaWord.drop word 1) θ)
        (PositiveLTL.alternatingStep interp (word 0) ψ) := by
    refine
      PosBool.eval_mono_of_imp_on_atoms
        (PositiveLTL.alternatingStep interp (word 0) ψ)
        ?_ hψAccepts
    intro θ hmem hθAccepts
    rcases hθAccepts with ⟨hθRoot, hθAccepts⟩
    have hθltRelease :
        θ.size < (PositiveLTL.release φ ψ).size := by
      rcases
        PositiveLTL.alternatingStep_atoms_self_or_size_lt
          interp (word 0) ψ θ hmem with hself | hlt
      · rw [hself]
        exact PositiveLTL.size_lt_release_right φ ψ
      · exact Nat.lt_trans hlt (PositiveLTL.size_lt_release_right φ ψ)
    exact hsuccessors
      (⟨θ, hθRoot⟩ : root.Subformula) hθltRelease hθAccepts
  refine
    ⟨(PositiveLTL.alternatingStep_correct interp word ψ).mp
        hψSatisfiesStep,
      ?_⟩
  rcases hleftOrSelf with hφAccepts | hselfAccepts
  · left
    have hφSatisfiesStep :
        PosBool.Eval
          (fun θ =>
            PositiveLTL.Satisfies interp (OmegaWord.drop word 1) θ)
          (PositiveLTL.alternatingStep interp (word 0) φ) := by
      refine
        PosBool.eval_mono_of_imp_on_atoms
          (PositiveLTL.alternatingStep interp (word 0) φ)
          ?_ hφAccepts
      intro θ hmem hθAccepts
      rcases hθAccepts with ⟨hθRoot, hθAccepts⟩
      have hθltRelease :
          θ.size < (PositiveLTL.release φ ψ).size := by
        rcases
          PositiveLTL.alternatingStep_atoms_self_or_size_lt
            interp (word 0) φ θ hmem with hself | hlt
        · rw [hself]
          exact PositiveLTL.size_lt_release_left φ ψ
        · exact Nat.lt_trans hlt (PositiveLTL.size_lt_release_left φ ψ)
      exact hsuccessors
        (⟨θ, hθRoot⟩ : root.Subformula) hθltRelease hθAccepts
    exact (PositiveLTL.alternatingStep_correct interp word φ).mp
      hφSatisfiesStep
  · right
    rcases hselfAccepts with ⟨hselfMem, hselfAccepts⟩
    have hselfState :
        (⟨PositiveLTL.release φ ψ, hselfMem⟩ : root.Subformula) = state :=
      Subtype.ext hstate.symm
    simpa [A, closure, hselfState] using hselfAccepts

/--
Bounded reverse progress for accepting `release` states.

If the left side has not appeared before position `n`, acceptance propagates to
suffix `n` and the right side holds at every earlier suffix.
-/
theorem PositiveLTL.subformulaClosure_release_acceptsFrom_semantic_progress_until
    {AP : Type u}
    {Letter : Type v}
    [DecidableEq AP]
    (root : PositiveLTL AP)
    (interp : AP -> Letter -> Prop)
    (dec : ∀ ap letter, Decidable (interp ap letter))
    (state : root.Subformula)
    (word : OmegaWord Letter)
    (φ ψ : PositiveLTL AP)
    (hstate : state.1 = PositiveLTL.release φ ψ)
    (hsuccessors :
      ∀ n : Nat,
      ∀ nextState : root.Subformula,
        nextState.1.size < (PositiveLTL.release φ ψ).size ->
        ((PositiveLTL.subformulaClosure (Letter := Letter) root).toAPA
          interp dec).AcceptsFrom nextState (OmegaWord.drop word (n + 1)) ->
        PositiveLTL.Satisfies interp (OmegaWord.drop word (n + 1))
          nextState.1)
    (n : Nat)
    (hnotφ : ∀ k : Nat, k < n ->
      ¬ PositiveLTL.Satisfies interp (OmegaWord.drop word k) φ)
    (haccepts :
      ((PositiveLTL.subformulaClosure (Letter := Letter) root).toAPA
        interp dec).AcceptsFrom state word) :
    (∀ k : Nat, k < n ->
      PositiveLTL.Satisfies interp (OmegaWord.drop word k) ψ) ∧
    ((PositiveLTL.subformulaClosure (Letter := Letter) root).toAPA
      interp dec).AcceptsFrom state (OmegaWord.drop word n) := by
  induction n with
  | zero =>
      constructor
      · intro k hk
        exact False.elim (Nat.not_lt_zero k hk)
      · simpa using haccepts
  | succ n ih =>
      have hnotBefore : ∀ k : Nat, k < n ->
          ¬ PositiveLTL.Satisfies interp (OmegaWord.drop word k) φ := by
        intro k hk
        exact hnotφ k (Nat.lt_trans hk (Nat.lt_succ_self n))
      rcases ih hnotBefore with ⟨hψBefore, hacceptsAtN⟩
      have hstep :
          PositiveLTL.Satisfies interp (OmegaWord.drop word n) ψ ∧
          ((PositiveLTL.subformulaClosure (Letter := Letter) root).toAPA
            interp dec).AcceptsFrom state
              (OmegaWord.drop (OmegaWord.drop word n) 1) := by
        have hsuccAtN :
            ∀ nextState : root.Subformula,
              nextState.1.size < (PositiveLTL.release φ ψ).size ->
              ((PositiveLTL.subformulaClosure (Letter := Letter) root).toAPA
                interp dec).AcceptsFrom nextState
                  (OmegaWord.drop (OmegaWord.drop word n) 1) ->
              PositiveLTL.Satisfies interp
                (OmegaWord.drop (OmegaWord.drop word n) 1) nextState.1 := by
          intro nextState hlt hnextAccepts
          have hnextAccepts' :
              ((PositiveLTL.subformulaClosure (Letter := Letter) root).toAPA
                interp dec).AcceptsFrom nextState
                  (OmegaWord.drop word (n + 1)) := by
            simpa [OmegaWord.drop_drop, Nat.add_comm, Nat.add_assoc]
              using hnextAccepts
          have hsatisfies' :
              PositiveLTL.Satisfies interp (OmegaWord.drop word (n + 1))
                nextState.1 :=
            hsuccessors n nextState hlt hnextAccepts'
          simpa [OmegaWord.drop_drop, Nat.add_comm, Nat.add_assoc]
            using hsatisfies'
        rcases
          PositiveLTL.subformulaClosure_release_acceptsFrom_semantic_progress
            root interp dec state (OmegaWord.drop word n) φ ψ hstate
            hacceptsAtN hsuccAtN with
          ⟨hψn, hφOrSelf⟩
        rcases hφOrSelf with hφn | hself
        · exact False.elim (hnotφ n (Nat.lt_succ_self n) hφn)
        · exact ⟨hψn, hself⟩
      constructor
      · intro k hk
        have hkLe : k ≤ n := Nat.le_of_lt_succ hk
        by_cases hkLt : k < n
        · exact hψBefore k hkLt
        · have hnLe : n ≤ k := Nat.le_of_not_gt hkLt
          have hkEq : k = n := Nat.le_antisymm hkLe hnLe
          subst k
          exact hstep.1
      · simpa [OmegaWord.drop_drop, Nat.add_comm, Nat.add_assoc]
          using hstep.2

/-- Reverse semantic soundness for accepting canonical `release` states. -/
theorem PositiveLTL.subformulaClosure_release_acceptsFrom_satisfies
    {AP : Type u}
    {Letter : Type v}
    [DecidableEq AP]
    (root : PositiveLTL AP)
    (interp : AP -> Letter -> Prop)
    (dec : ∀ ap letter, Decidable (interp ap letter))
    (state : root.Subformula)
    (word : OmegaWord Letter)
    (φ ψ : PositiveLTL AP)
    (hstate : state.1 = PositiveLTL.release φ ψ)
    (haccepts :
      ((PositiveLTL.subformulaClosure (Letter := Letter) root).toAPA
        interp dec).AcceptsFrom state word)
    (hsuccessors :
      ∀ n : Nat,
      ∀ nextState : root.Subformula,
        nextState.1.size < (PositiveLTL.release φ ψ).size ->
        ((PositiveLTL.subformulaClosure (Letter := Letter) root).toAPA
          interp dec).AcceptsFrom nextState (OmegaWord.drop word (n + 1)) ->
        PositiveLTL.Satisfies interp (OmegaWord.drop word (n + 1))
          nextState.1) :
    PositiveLTL.Satisfies interp word state.1 := by
  rw [hstate]
  intro n
  by_cases hφBefore :
      ∃ k : Nat, k < n ∧
        PositiveLTL.Satisfies interp (OmegaWord.drop word k) φ
  · exact Or.inr hφBefore
  · left
    have hnotφBefore :
        ∀ k : Nat, k < n ->
          ¬ PositiveLTL.Satisfies interp (OmegaWord.drop word k) φ := by
      intro k hk hφk
      exact hφBefore ⟨k, hk, hφk⟩
    rcases
      PositiveLTL.subformulaClosure_release_acceptsFrom_semantic_progress_until
        root interp dec state word φ ψ hstate hsuccessors n hnotφBefore
        haccepts with
      ⟨_hψBefore, hacceptsAtN⟩
    have hsuccAtN :
        ∀ nextState : root.Subformula,
          nextState.1.size < (PositiveLTL.release φ ψ).size ->
          ((PositiveLTL.subformulaClosure (Letter := Letter) root).toAPA
            interp dec).AcceptsFrom nextState
              (OmegaWord.drop (OmegaWord.drop word n) 1) ->
          PositiveLTL.Satisfies interp
            (OmegaWord.drop (OmegaWord.drop word n) 1) nextState.1 := by
      intro nextState hlt hnextAccepts
      have hnextAccepts' :
          ((PositiveLTL.subformulaClosure (Letter := Letter) root).toAPA
            interp dec).AcceptsFrom nextState
              (OmegaWord.drop word (n + 1)) := by
        simpa [OmegaWord.drop_drop, Nat.add_comm, Nat.add_assoc]
          using hnextAccepts
      have hsatisfies' :
          PositiveLTL.Satisfies interp (OmegaWord.drop word (n + 1))
            nextState.1 :=
        hsuccessors n nextState hlt hnextAccepts'
      simpa [OmegaWord.drop_drop, Nat.add_comm, Nat.add_assoc]
        using hsatisfies'
    rcases
      PositiveLTL.subformulaClosure_release_acceptsFrom_semantic_progress
        root interp dec state (OmegaWord.drop word n) φ ψ hstate
        hacceptsAtN hsuccAtN with
      ⟨hψn, _hφOrSelf⟩
    simpa [OmegaWord.drop_drop, Nat.add_comm, Nat.add_assoc] using hψn

/--
State-wise reverse semantic soundness for the canonical subformula APA.

Acceptance from any closure state implies satisfaction of the formula denoted by
that state.  The proof is by strong induction on formula size; non-fixed-point
states use one-step reverse soundness, while `until` and `release` use the
fixed-point progress theorems above.
-/
theorem PositiveLTL.subformulaClosure_acceptsFrom_satisfies
    {AP : Type u}
    {Letter : Type v}
    [DecidableEq AP]
    (root : PositiveLTL AP)
    (interp : AP -> Letter -> Prop)
    (dec : ∀ ap letter, Decidable (interp ap letter))
    (state : root.Subformula)
    (word : OmegaWord Letter)
    (haccepts :
      ((PositiveLTL.subformulaClosure (Letter := Letter) root).toAPA
        interp dec).AcceptsFrom state word) :
    PositiveLTL.Satisfies interp word state.1 := by
  let A := (PositiveLTL.subformulaClosure (Letter := Letter) root).toAPA
    interp dec
  let P : Nat -> Prop :=
    fun m =>
      ∀ state : root.Subformula,
        state.1.size = m ->
          ∀ word : OmegaWord Letter,
            A.AcceptsFrom state word ->
              PositiveLTL.Satisfies interp word state.1
  have hP : ∀ m : Nat, P m := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
        intro state hsize word haccepts
        by_cases huntil :
            ∃ φ ψ : PositiveLTL AP, state.1 = PositiveLTL.until φ ψ
        · rcases huntil with ⟨φ, ψ, hstate⟩
          refine
            PositiveLTL.subformulaClosure_until_acceptsFrom_satisfies
              root interp dec state word φ ψ hstate
              (by simpa [A] using haccepts) ?_
          intro n nextState hlt hnextAccepts
          have hltm : nextState.1.size < m := by
            have hstateSize : (PositiveLTL.until φ ψ).size = m := by
              rw [← hstate, hsize]
            rw [← hstateSize]
            exact hlt
          exact ih nextState.1.size hltm nextState rfl
            (OmegaWord.drop word (n + 1)) (by simpa [A] using hnextAccepts)
        · by_cases hrelease :
            ∃ φ ψ : PositiveLTL AP, state.1 = PositiveLTL.release φ ψ
          · rcases hrelease with ⟨φ, ψ, hstate⟩
            refine
              PositiveLTL.subformulaClosure_release_acceptsFrom_satisfies
                root interp dec state word φ ψ hstate
                (by simpa [A] using haccepts) ?_
            intro n nextState hlt hnextAccepts
            have hltm : nextState.1.size < m := by
              have hstateSize : (PositiveLTL.release φ ψ).size = m := by
                rw [← hstate, hsize]
              rw [← hstateSize]
              exact hlt
            exact ih nextState.1.size hltm nextState rfl
              (OmegaWord.drop word (n + 1)) (by simpa [A] using hnextAccepts)
          · refine
              PositiveLTL.subformulaClosure_acceptsFrom_satisfies_of_no_self_atom
                root interp dec state word (by simpa [A] using haccepts)
                ?_ ?_
            · intro nextState hmem hnextEq
              have hmemTransition :
                  state ∈
                    (PositiveLTL.subformulaTransition root interp state
                      (word 0)).atoms := by
                have hmem' :
                    nextState ∈
                      (PositiveLTL.subformulaTransition root interp state
                        (word 0)).atoms := by
                  simpa [A, PositiveLTL.subformulaClosure,
                    FiniteLTLAlternatingClosure.toAPA] using hmem
                simpa [hnextEq] using hmem'
              rcases
                PositiveLTL.subformulaTransition_self_atom_is_until_or_release
                  root interp dec state (word 0) hmemTransition with
                hbadUntil | hbadRelease
              · exact huntil hbadUntil
              · exact hrelease hbadRelease
            · intro nextState hlt hnextAccepts
              have hltm : nextState.1.size < m := by
                simpa [hsize] using hlt
              exact ih nextState.1.size hltm nextState rfl
                (OmegaWord.drop word 1) (by simpa [A] using hnextAccepts)
  exact hP state.1.size state rfl word (by simpa [A] using haccepts)

/--
Closure-level guided expansion for an `until` state.

The support selected by `until_guided_transition_support` is embedded into the
subformula carrier.  Active children are exact transition atoms, remain
semantically true on the next suffix, and an active child that stays at the same
`until` state certifies that the right side was not true at the current suffix.
-/
theorem PositiveLTL.subformulaClosure_until_guided_exactStepExpansion
    {AP : Type u}
    {Letter : Type v}
    [DecidableEq AP]
    (root : PositiveLTL AP)
    (interp : AP -> Letter -> Prop)
    (dec : ∀ ap letter, Decidable (interp ap letter))
    (word : OmegaWord Letter)
    (φ ψ : PositiveLTL AP)
    (state : root.Subformula)
    (hstate : state.1 = PositiveLTL.until φ ψ)
    (hsat :
      PositiveLTL.Satisfies interp word state.1) :
    ∃ expansion :
      ((PositiveLTL.subformulaClosure (Letter := Letter) root).toAPA
        interp dec).ExactStepExpansion state (word 0),
      (∀ child,
        expansion.childActive child ->
          PositiveLTL.Satisfies interp (OmegaWord.drop word 1)
            (expansion.childState child).1) ∧
        (∀ child,
          expansion.childActive child ->
            expansion.childState child = state ->
              ¬ PositiveLTL.Satisfies interp word ψ) := by
  classical
  rcases state with ⟨stateFormula, hstateMem⟩
  dsimp at hstate hsat
  subst stateFormula
  rcases
    @PositiveLTL.until_guided_transition_support AP Letter interp dec
      word φ ψ hsat with
    ⟨support, hsupport, hatoms, heval, hselfProgress⟩
  let step : PosBool (PositiveLTL AP) :=
    @PositiveLTL.alternatingStep AP Letter interp dec
      (word 0) (PositiveLTL.until φ ψ)
  let embed : ∀ θ, θ ∈ step.atoms -> root.Subformula :=
    fun θ hθ =>
      ⟨θ,
        PositiveLTL.subformulas_trans
          (PositiveLTL.alternatingStep_atoms_subformulas
            interp (word 0) (PositiveLTL.until φ ψ) θ hθ)
          hstateMem⟩
  let supportCarrier : List root.Subformula :=
    support.attach.map
      (fun θ =>
        ⟨θ.1,
          PositiveLTL.subformulas_trans
            (PositiveLTL.alternatingStep_atoms_subformulas
              interp (word 0) (PositiveLTL.until φ ψ) θ.1
              (hatoms θ.1 θ.2))
            hstateMem⟩)
  have hmemCarrier :
      ∀ θ, ∀ hθ : θ ∈ support,
        (⟨θ,
          PositiveLTL.subformulas_trans
            (PositiveLTL.alternatingStep_atoms_subformulas
              interp (word 0) (PositiveLTL.until φ ψ) θ
              (hatoms θ hθ))
            hstateMem⟩ : root.Subformula) ∈ supportCarrier := by
    intro θ hθ
    dsimp [supportCarrier]
    refine List.mem_map.mpr ?_
    refine ⟨⟨θ, hθ⟩, by simp, ?_⟩
    rfl
  have hevalCarrier :
      PosBool.Eval
        (fun nextState : root.Subformula => nextState ∈ supportCarrier)
        (step.pmap embed) := by
    exact
      PosBool.eval_pmap_of_imp
        step embed
        (valuation := fun θ => θ ∈ support)
        (valuation' := fun nextState : root.Subformula =>
          nextState ∈ supportCarrier)
        (fun θ hθ hθSupport => by
          have htarget :=
            hmemCarrier θ hθSupport
          have hsame :
              embed θ hθ =
                (⟨θ,
                  PositiveLTL.subformulas_trans
                    (PositiveLTL.alternatingStep_atoms_subformulas
                      interp (word 0) (PositiveLTL.until φ ψ) θ
                      (hatoms θ hθSupport))
                    hstateMem⟩ : root.Subformula) := by
            ext
            rfl
          simpa [hsame] using htarget)
        heval
  have hatomsCarrier :
      ∀ nextState : root.Subformula,
        nextState ∈ supportCarrier ->
          nextState ∈ (step.pmap embed).atoms := by
    intro nextState hnext
    dsimp [supportCarrier] at hnext
    rcases List.mem_map.mp hnext with ⟨θ, _hθmem, hnextEq⟩
    rcases θ with ⟨θ, hθSupport⟩
    subst nextState
    have himage :
        embed θ (hatoms θ hθSupport) ∈ (step.pmap embed).atoms :=
      PosBool.mem_atoms_pmap_of_mem_atoms step embed (hatoms θ hθSupport)
    simpa [embed] using himage
  refine
    ⟨AlternatingParityAutomaton.ExactStepExpansion.ofSupport
      ((PositiveLTL.subformulaClosure (Letter := Letter) root).toAPA
        interp dec)
      (⟨PositiveLTL.until φ ψ, hstateMem⟩ : root.Subformula)
      (word 0)
      supportCarrier
      ?_
      ?_,
      ?_, ?_⟩
  · intro nextState hnext
    simpa [FiniteLTLAlternatingClosure.toAPA, PositiveLTL.subformulaClosure,
      PositiveLTL.subformulaTransition, step, embed] using
      hatomsCarrier nextState hnext
  · simpa [FiniteLTLAlternatingClosure.toAPA, PositiveLTL.subformulaClosure,
      PositiveLTL.subformulaTransition, step, embed] using hevalCarrier
  · intro child hchild
    rcases hchild with ⟨childState, hchildState⟩
    have hmem : childState ∈ supportCarrier :=
      (PosBool.mem_iff_exists_getElem? supportCarrier childState).mpr
        ⟨child, hchildState⟩
    dsimp [supportCarrier] at hmem
    rcases List.mem_map.mp hmem with ⟨θ, _hθmem, hchildEq⟩
    rcases θ with ⟨θ, hθSupport⟩
    have hstateEq :
        (supportCarrier[child]?).getD
            (PositiveLTL.rootSubformula root) =
          (⟨θ,
            PositiveLTL.subformulas_trans
              (PositiveLTL.alternatingStep_atoms_subformulas
                interp (word 0) (PositiveLTL.until φ ψ) θ
                (hatoms θ hθSupport))
              hstateMem⟩ : root.Subformula) := by
      have hget :
          (supportCarrier[child]?).getD
              (PositiveLTL.rootSubformula root) = childState := by
        simpa [Option.getD] using
          congrArg
            (fun opt : Option root.Subformula =>
              opt.getD (PositiveLTL.rootSubformula root))
            hchildState
      exact Eq.trans hget hchildEq.symm
    change
      PositiveLTL.Satisfies interp (OmegaWord.drop word 1)
        ((supportCarrier[child]?).getD
          (PositiveLTL.rootSubformula root)).1
    rw [hstateEq]
    exact hsupport θ hθSupport
  · intro child hchild hchildSelf
    rcases hchild with ⟨childState, hchildState⟩
    have hmem : childState ∈ supportCarrier :=
      (PosBool.mem_iff_exists_getElem? supportCarrier childState).mpr
        ⟨child, hchildState⟩
    dsimp [supportCarrier] at hmem
    rcases List.mem_map.mp hmem with ⟨θ, _hθmem, hchildEq⟩
    rcases θ with ⟨θ, hθSupport⟩
    have hstateEq :
        (supportCarrier[child]?).getD
            (PositiveLTL.rootSubformula root) =
          (⟨θ,
            PositiveLTL.subformulas_trans
              (PositiveLTL.alternatingStep_atoms_subformulas
                interp (word 0) (PositiveLTL.until φ ψ) θ
                (hatoms θ hθSupport))
              hstateMem⟩ : root.Subformula) := by
      have hget :
          (supportCarrier[child]?).getD
              (PositiveLTL.rootSubformula root) = childState := by
        simpa [Option.getD] using
          congrArg
            (fun opt : Option root.Subformula =>
              opt.getD (PositiveLTL.rootSubformula root))
            hchildState
      exact Eq.trans hget hchildEq.symm
    have hθSelf : θ = PositiveLTL.until φ ψ := by
      have hdenote :=
        congrArg Subtype.val hchildSelf
      change
        ((supportCarrier[child]?).getD
          (PositiveLTL.rootSubformula root)).1 =
          PositiveLTL.until φ ψ at hdenote
      rw [hstateEq] at hdenote
      exact hdenote
    exact hselfProgress (by simpa [hθSelf] using hθSupport)

/--
Closure-level guided expansion for a `release` state.

When the current left side does not close a satisfied `release`, the selected
support contains the release self-loop, hence the exact expansion has an active
child that stays at the same closure state.
-/
theorem PositiveLTL.subformulaClosure_release_guided_exactStepExpansion
    {AP : Type u}
    {Letter : Type v}
    [DecidableEq AP]
    (root : PositiveLTL AP)
    (interp : AP -> Letter -> Prop)
    (dec : ∀ ap letter, Decidable (interp ap letter))
    (word : OmegaWord Letter)
    (φ ψ : PositiveLTL AP)
    (state : root.Subformula)
    (hstate : state.1 = PositiveLTL.release φ ψ)
    (hsat :
      PositiveLTL.Satisfies interp word state.1) :
    ∃ expansion :
      ((PositiveLTL.subformulaClosure (Letter := Letter) root).toAPA
        interp dec).ExactStepExpansion state (word 0),
      (∀ child,
        expansion.childActive child ->
          PositiveLTL.Satisfies interp (OmegaWord.drop word 1)
            (expansion.childState child).1) ∧
        (¬ PositiveLTL.Satisfies interp word φ ->
          ∃ child,
            expansion.childActive child ∧
              expansion.childState child = state) ∧
        (∀ child,
          expansion.childActive child ->
          expansion.childState child = state ->
            ¬ PositiveLTL.Satisfies interp word φ) := by
  classical
  rcases state with ⟨stateFormula, hstateMem⟩
  dsimp at hstate hsat
  subst stateFormula
  rcases
    @PositiveLTL.release_guided_transition_support AP Letter interp dec
      word φ ψ hsat with
    ⟨support, hsupport, hatoms, heval, hselfProgress⟩
  let step : PosBool (PositiveLTL AP) :=
    @PositiveLTL.alternatingStep AP Letter interp dec
      (word 0) (PositiveLTL.release φ ψ)
  let embed : ∀ θ, θ ∈ step.atoms -> root.Subformula :=
    fun θ hθ =>
      ⟨θ,
        PositiveLTL.subformulas_trans
          (PositiveLTL.alternatingStep_atoms_subformulas
            interp (word 0) (PositiveLTL.release φ ψ) θ hθ)
          hstateMem⟩
  let supportCarrier : List root.Subformula :=
    support.attach.map
      (fun θ =>
        ⟨θ.1,
          PositiveLTL.subformulas_trans
            (PositiveLTL.alternatingStep_atoms_subformulas
              interp (word 0) (PositiveLTL.release φ ψ) θ.1
              (hatoms θ.1 θ.2))
            hstateMem⟩)
  have hmemCarrier :
      ∀ θ, ∀ hθ : θ ∈ support,
        (⟨θ,
          PositiveLTL.subformulas_trans
            (PositiveLTL.alternatingStep_atoms_subformulas
              interp (word 0) (PositiveLTL.release φ ψ) θ
              (hatoms θ hθ))
            hstateMem⟩ : root.Subformula) ∈ supportCarrier := by
    intro θ hθ
    dsimp [supportCarrier]
    refine List.mem_map.mpr ?_
    refine ⟨⟨θ, hθ⟩, by simp, ?_⟩
    rfl
  have hevalCarrier :
      PosBool.Eval
        (fun nextState : root.Subformula => nextState ∈ supportCarrier)
        (step.pmap embed) := by
    exact
      PosBool.eval_pmap_of_imp
        step embed
        (valuation := fun θ => θ ∈ support)
        (valuation' := fun nextState : root.Subformula =>
          nextState ∈ supportCarrier)
        (fun θ hθ hθSupport => by
          have htarget :=
            hmemCarrier θ hθSupport
          have hsame :
              embed θ hθ =
                (⟨θ,
                  PositiveLTL.subformulas_trans
                    (PositiveLTL.alternatingStep_atoms_subformulas
                      interp (word 0) (PositiveLTL.release φ ψ) θ
                      (hatoms θ hθSupport))
                    hstateMem⟩ : root.Subformula) := by
            ext
            rfl
          simpa [hsame] using htarget)
        heval
  have hatomsCarrier :
      ∀ nextState : root.Subformula,
        nextState ∈ supportCarrier ->
          nextState ∈ (step.pmap embed).atoms := by
    intro nextState hnext
    dsimp [supportCarrier] at hnext
    rcases List.mem_map.mp hnext with ⟨θ, _hθmem, hnextEq⟩
    rcases θ with ⟨θ, hθSupport⟩
    subst nextState
    have himage :
        embed θ (hatoms θ hθSupport) ∈ (step.pmap embed).atoms :=
      PosBool.mem_atoms_pmap_of_mem_atoms step embed (hatoms θ hθSupport)
    simpa [embed] using himage
  let expansion :=
    AlternatingParityAutomaton.ExactStepExpansion.ofSupport
      ((PositiveLTL.subformulaClosure (Letter := Letter) root).toAPA
        interp dec)
      (⟨PositiveLTL.release φ ψ, hstateMem⟩ : root.Subformula)
      (word 0)
      supportCarrier
      (by
        intro nextState hnext
        simpa [FiniteLTLAlternatingClosure.toAPA,
          PositiveLTL.subformulaClosure,
          PositiveLTL.subformulaTransition, step, embed] using
          hatomsCarrier nextState hnext)
      (by
        simpa [FiniteLTLAlternatingClosure.toAPA,
          PositiveLTL.subformulaClosure,
          PositiveLTL.subformulaTransition, step, embed] using hevalCarrier)
  refine ⟨expansion, ?_, ?_, ?_⟩
  · intro child hchild
    rcases hchild with ⟨childState, hchildState⟩
    have hmem : childState ∈ supportCarrier :=
      (PosBool.mem_iff_exists_getElem? supportCarrier childState).mpr
        ⟨child, hchildState⟩
    dsimp [supportCarrier] at hmem
    rcases List.mem_map.mp hmem with ⟨θ, _hθmem, hchildEq⟩
    rcases θ with ⟨θ, hθSupport⟩
    have hstateEq :
        (supportCarrier[child]?).getD
            (PositiveLTL.rootSubformula root) =
          (⟨θ,
            PositiveLTL.subformulas_trans
              (PositiveLTL.alternatingStep_atoms_subformulas
                interp (word 0) (PositiveLTL.release φ ψ) θ
                (hatoms θ hθSupport))
              hstateMem⟩ : root.Subformula) := by
      have hget :
          (supportCarrier[child]?).getD
              (PositiveLTL.rootSubformula root) = childState := by
        simpa [Option.getD] using
          congrArg
            (fun opt : Option root.Subformula =>
              opt.getD (PositiveLTL.rootSubformula root))
            hchildState
      exact Eq.trans hget hchildEq.symm
    change
      PositiveLTL.Satisfies interp (OmegaWord.drop word 1)
        ((supportCarrier[child]?).getD
          (PositiveLTL.rootSubformula root)).1
    rw [hstateEq]
    exact hsupport θ hθSupport
  · intro hnotφ
    have hselfSupport :
        PositiveLTL.release φ ψ ∈ support :=
      hselfProgress.1 hnotφ
    have hselfCarrier :
        (⟨PositiveLTL.release φ ψ, hstateMem⟩ : root.Subformula) ∈
          supportCarrier := by
      simpa using hmemCarrier (PositiveLTL.release φ ψ) hselfSupport
    rcases
      (PosBool.mem_iff_exists_getElem? supportCarrier
        (⟨PositiveLTL.release φ ψ, hstateMem⟩ : root.Subformula)).mp
        hselfCarrier with
      ⟨child, hchild⟩
    refine ⟨child, ?_, ?_⟩
    · exact ⟨(⟨PositiveLTL.release φ ψ, hstateMem⟩ : root.Subformula), hchild⟩
    · change
        (supportCarrier[child]?).getD
            (PositiveLTL.rootSubformula root) =
          (⟨PositiveLTL.release φ ψ, hstateMem⟩ : root.Subformula)
      simp [hchild]
  · intro child hchildActive hchildSelf
    rcases hchildActive with ⟨childState, hchildState⟩
    have hmem : childState ∈ supportCarrier :=
      (PosBool.mem_iff_exists_getElem? supportCarrier childState).mpr
        ⟨child, hchildState⟩
    dsimp [supportCarrier] at hmem
    rcases List.mem_map.mp hmem with ⟨θ, _hθmem, hchildEq⟩
    rcases θ with ⟨θ, hθSupport⟩
    have hget :
        (supportCarrier[child]?).getD
            (PositiveLTL.rootSubformula root) = childState := by
      simpa [Option.getD] using
        congrArg
          (fun opt : Option root.Subformula =>
            opt.getD (PositiveLTL.rootSubformula root))
          hchildState
    have hchildStateSelf :
        childState =
          (⟨PositiveLTL.release φ ψ, hstateMem⟩ : root.Subformula) :=
      hget.symm.trans hchildSelf
    have hθRelease : θ = PositiveLTL.release φ ψ := by
      have hchildEqState :
          (⟨θ,
            PositiveLTL.subformulas_trans
              (PositiveLTL.alternatingStep_atoms_subformulas
                interp (word 0) (PositiveLTL.release φ ψ) θ
                (hatoms θ hθSupport))
              hstateMem⟩ : root.Subformula) =
            (⟨PositiveLTL.release φ ψ, hstateMem⟩ : root.Subformula) := by
        exact hchildEq.trans hchildStateSelf
      exact congrArg Subtype.val hchildEqState
    have hselfSupport :
        PositiveLTL.release φ ψ ∈ support := by
      simpa [hθRelease] using hθSupport
    exact hselfProgress.2 hselfSupport

/--
Every satisfied state of the canonical closure has an exact expansion that is
progress-guided for temporal self-loops.
-/
theorem PositiveLTL.subformulaClosure_exists_progress_exactStepExpansion
    {AP : Type u}
    {Letter : Type v}
    [DecidableEq AP]
    (root : PositiveLTL AP)
    (interp : AP -> Letter -> Prop)
    (dec : ∀ ap letter, Decidable (interp ap letter))
    (state : root.Subformula)
    (word : OmegaWord Letter)
    (hsat :
      PositiveLTL.Satisfies interp word state.1) :
    ∃ expansion :
      ((PositiveLTL.subformulaClosure (Letter := Letter) root).toAPA
        interp dec).ExactStepExpansion state (word 0),
      (∀ child,
        expansion.childActive child ->
          PositiveLTL.Satisfies interp (OmegaWord.drop word 1)
            (expansion.childState child).1) ∧
        (∀ child φ ψ,
          expansion.childActive child ->
          state.1 = PositiveLTL.until φ ψ ->
          expansion.childState child = state ->
              ¬ PositiveLTL.Satisfies interp word ψ) ∧
        (∀ φ ψ,
          state.1 = PositiveLTL.release φ ψ ->
          ¬ PositiveLTL.Satisfies interp word φ ->
            ∃ child,
              expansion.childActive child ∧
                expansion.childState child = state) ∧
        (∀ child φ ψ,
          expansion.childActive child ->
          state.1 = PositiveLTL.release φ ψ ->
          expansion.childState child = state ->
            ¬ PositiveLTL.Satisfies interp word φ) := by
  classical
  let closure := PositiveLTL.subformulaClosure (Letter := Letter) root
  by_cases huntilExists :
      ∃ φ ψ : PositiveLTL AP, state.1 = PositiveLTL.until φ ψ
  · rcases huntilExists with ⟨φ, ψ, hstate⟩
    rcases
      PositiveLTL.subformulaClosure_until_guided_exactStepExpansion
        root interp dec word φ ψ state hstate hsat with
      ⟨expansion, hsatChildren, hprogress⟩
    refine ⟨expansion, hsatChildren, ?_, ?_, ?_⟩
    · intro child φ' ψ' hactive huntil hself
      have hsame : PositiveLTL.until φ ψ = PositiveLTL.until φ' ψ' := by
        rw [← hstate]
        exact huntil
      cases hsame
      exact hprogress child hactive hself
    · intro φ' ψ' hrelease _hnotφ
      have hbad : PositiveLTL.until φ ψ = PositiveLTL.release φ' ψ' := by
        rw [← hstate]
        exact hrelease
      cases hbad
    · intro child φ' ψ' _ hrelease _
      have hbad : PositiveLTL.until φ ψ = PositiveLTL.release φ' ψ' := by
        rw [← hstate]
        exact hrelease
      cases hbad
  · by_cases hreleaseExists :
        ∃ φ ψ : PositiveLTL AP, state.1 = PositiveLTL.release φ ψ
    · rcases hreleaseExists with ⟨φ, ψ, hstate⟩
      rcases
        PositiveLTL.subformulaClosure_release_guided_exactStepExpansion
          root interp dec word φ ψ state hstate hsat with
        ⟨expansion, hsatChildren, hprogress, hselfOnly⟩
      refine ⟨expansion, hsatChildren, ?_, ?_, ?_⟩
      · intro child φ' ψ' _ huntil _
        exact False.elim (huntilExists ⟨φ', ψ', huntil⟩)
      · intro φ' ψ' hrelease hnotφ
        have hsame : PositiveLTL.release φ ψ = PositiveLTL.release φ' ψ' := by
          rw [← hstate]
          exact hrelease
        cases hsame
        exact hprogress hnotφ
      · intro child φ' ψ' hactive hrelease hself
        have hsame : PositiveLTL.release φ ψ = PositiveLTL.release φ' ψ' := by
          rw [← hstate]
          exact hrelease
        cases hsame
        exact hselfOnly child hactive hself
    · rcases
        closure.exists_satisfying_exactStepExpansion
          interp dec state word hsat with
        ⟨expansion, hsatChildren⟩
      refine ⟨expansion, hsatChildren, ?_, ?_, ?_⟩
      · intro child φ ψ _ huntil _
        exact False.elim (huntilExists ⟨φ, ψ, huntil⟩)
      · intro φ ψ hrelease _
        exact False.elim (hreleaseExists ⟨φ, ψ, hrelease⟩)
      · intro child φ ψ _ hrelease _
        exact False.elim (hreleaseExists ⟨φ, ψ, hrelease⟩)

/--
Node data for the guided satisfying run of the canonical subformula closure.
It is the semantic run construction specialized so that `until` transitions use
the progress-guided exact expansion.
-/
noncomputable def PositiveLTL.subformulaClosure_guidedRunNodeData
    {AP : Type u}
    {Letter : Type v}
    [DecidableEq AP]
    (root : PositiveLTL AP)
    (interp : AP -> Letter -> Prop)
    (dec : ∀ ap letter, Decidable (interp ap letter))
    (word : OmegaWord Letter)
    (hsatInitial : PositiveLTL.Satisfies interp word root) :
    (node : AlternatingParityAutomaton.Node) ->
      { data : root.Subformula × Prop //
        data.2 ->
          PositiveLTL.Satisfies
            interp (OmegaWord.drop word node.length) data.1.1 }
  | [] =>
      ⟨(PositiveLTL.rootSubformula root, True), by
        intro _
        simpa using hsatInitial⟩
  | child :: node =>
      let parent :=
        PositiveLTL.subformulaClosure_guidedRunNodeData
          root interp dec word hsatInitial node
      haveI : Decidable parent.1.2 := Classical.propDecidable parent.1.2
      if hparent : parent.1.2 then
        let existsExpansion :=
          PositiveLTL.subformulaClosure_exists_progress_exactStepExpansion
            root interp dec parent.1.1
            (OmegaWord.drop word node.length)
            (parent.2 hparent)
        let expansion :=
          Classical.choose existsExpansion
        ⟨(expansion.childState child, expansion.childActive child), by
          intro hchild
          have hspec :
              (∀ child,
                expansion.childActive child ->
                  PositiveLTL.Satisfies interp
                    (OmegaWord.drop (OmegaWord.drop word node.length) 1)
                    (expansion.childState child).1) ∧
                (∀ child φ ψ,
                  expansion.childActive child ->
                    parent.1.1.1 = PositiveLTL.until φ ψ ->
                    expansion.childState child = parent.1.1 ->
                      ¬ PositiveLTL.Satisfies
                        interp (OmegaWord.drop word node.length) ψ) ∧
                (∀ φ ψ,
                  parent.1.1.1 = PositiveLTL.release φ ψ ->
                    ¬ PositiveLTL.Satisfies
                      interp (OmegaWord.drop word node.length) φ ->
                      ∃ child,
                        expansion.childActive child ∧
                          expansion.childState child = parent.1.1) ∧
                  (∀ child φ ψ,
                    expansion.childActive child ->
                      parent.1.1.1 = PositiveLTL.release φ ψ ->
                      expansion.childState child = parent.1.1 ->
                        ¬ PositiveLTL.Satisfies
                          interp (OmegaWord.drop word node.length) φ) :=
            Classical.choose_spec existsExpansion
          have hsatChild := hspec.1 child hchild
          simpa [OmegaWord.drop_drop, Nat.add_comm, Nat.add_assoc] using hsatChild⟩
      else
        ⟨(PositiveLTL.rootSubformula root, False), by
          intro hfalse
          exact False.elim hfalse⟩

noncomputable def PositiveLTL.subformulaClosure_guidedRunActive
    {AP : Type u}
    {Letter : Type v}
    [DecidableEq AP]
    (root : PositiveLTL AP)
    (interp : AP -> Letter -> Prop)
    (dec : ∀ ap letter, Decidable (interp ap letter))
    (word : OmegaWord Letter)
    (hsatInitial : PositiveLTL.Satisfies interp word root)
    (node : AlternatingParityAutomaton.Node) :
    Prop :=
  (PositiveLTL.subformulaClosure_guidedRunNodeData
    root interp dec word hsatInitial node).1.2

noncomputable def PositiveLTL.subformulaClosure_guidedRunState
    {AP : Type u}
    {Letter : Type v}
    [DecidableEq AP]
    (root : PositiveLTL AP)
    (interp : AP -> Letter -> Prop)
    (dec : ∀ ap letter, Decidable (interp ap letter))
    (word : OmegaWord Letter)
    (hsatInitial : PositiveLTL.Satisfies interp word root)
    (node : AlternatingParityAutomaton.Node) :
    root.Subformula :=
  (PositiveLTL.subformulaClosure_guidedRunNodeData
    root interp dec word hsatInitial node).1.1

theorem PositiveLTL.subformulaClosure_guidedRun_root_active
    {AP : Type u}
    {Letter : Type v}
    [DecidableEq AP]
    (root : PositiveLTL AP)
    (interp : AP -> Letter -> Prop)
    (dec : ∀ ap letter, Decidable (interp ap letter))
    (word : OmegaWord Letter)
    (hsatInitial : PositiveLTL.Satisfies interp word root) :
    PositiveLTL.subformulaClosure_guidedRunActive
      root interp dec word hsatInitial [] := by
  simp [PositiveLTL.subformulaClosure_guidedRunActive,
    PositiveLTL.subformulaClosure_guidedRunNodeData]

theorem PositiveLTL.subformulaClosure_guidedRun_root_state
    {AP : Type u}
    {Letter : Type v}
    [DecidableEq AP]
    (root : PositiveLTL AP)
    (interp : AP -> Letter -> Prop)
    (dec : ∀ ap letter, Decidable (interp ap letter))
    (word : OmegaWord Letter)
    (hsatInitial : PositiveLTL.Satisfies interp word root) :
    PositiveLTL.subformulaClosure_guidedRunState
      root interp dec word hsatInitial [] =
        (PositiveLTL.subformulaClosure (Letter := Letter) root).initial := by
  simp [PositiveLTL.subformulaClosure_guidedRunState,
    PositiveLTL.subformulaClosure_guidedRunNodeData,
    PositiveLTL.subformulaClosure]

theorem PositiveLTL.subformulaClosure_guidedRun_step_satisfied
    {AP : Type u}
    {Letter : Type v}
    [DecidableEq AP]
    (root : PositiveLTL AP)
    (interp : AP -> Letter -> Prop)
    (dec : ∀ ap letter, Decidable (interp ap letter))
    (word : OmegaWord Letter)
    (hsatInitial : PositiveLTL.Satisfies interp word root)
    (node : AlternatingParityAutomaton.Node)
    (hactive :
      PositiveLTL.subformulaClosure_guidedRunActive
        root interp dec word hsatInitial node) :
    PosBool.Eval
      (fun nextState =>
        ∃ child : Nat,
          PositiveLTL.subformulaClosure_guidedRunActive
            root interp dec word hsatInitial (child :: node) ∧
            PositiveLTL.subformulaClosure_guidedRunState
              root interp dec word hsatInitial (child :: node) = nextState)
        (((PositiveLTL.subformulaClosure (Letter := Letter) root).toAPA
          interp dec).step
          (PositiveLTL.subformulaClosure_guidedRunState
            root interp dec word hsatInitial node)
          (word node.length)) := by
  let parent :=
    PositiveLTL.subformulaClosure_guidedRunNodeData
      root interp dec word hsatInitial node
  have hparent : parent.1.2 := hactive
  haveI : Decidable parent.1.2 := Classical.propDecidable parent.1.2
  let existsExpansion :=
    PositiveLTL.subformulaClosure_exists_progress_exactStepExpansion
      root interp dec parent.1.1 (OmegaWord.drop word node.length)
      (parent.2 hparent)
  let expansion := Classical.choose existsExpansion
  change
    PosBool.Eval
      (fun nextState =>
        ∃ child : Nat,
          PositiveLTL.subformulaClosure_guidedRunActive
            root interp dec word hsatInitial (child :: node) ∧
            PositiveLTL.subformulaClosure_guidedRunState
              root interp dec word hsatInitial (child :: node) = nextState)
      (PositiveLTL.subformulaTransition root interp
        parent.1.1 (word node.length))
  refine
    PosBool.eval_mono
      (fun nextState hnext => ?_)
      (PositiveLTL.subformulaTransition root interp parent.1.1
        (word node.length))
      expansion.step_satisfied
  rcases hnext with ⟨child, hchildActive, hchildState⟩
  refine ⟨child, ?_, ?_⟩
  · simpa [PositiveLTL.subformulaClosure_guidedRunActive,
      PositiveLTL.subformulaClosure_guidedRunNodeData, parent, hparent,
      existsExpansion, expansion] using hchildActive
  · simpa [PositiveLTL.subformulaClosure_guidedRunState,
      PositiveLTL.subformulaClosure_guidedRunNodeData, parent, hparent,
      existsExpansion, expansion] using hchildState

/--
In the progress-guided satisfying run, every active child is backed by an
actual atom of the parent transition.
-/
theorem PositiveLTL.subformulaClosure_guidedRun_child_atom
    {AP : Type u}
    {Letter : Type v}
    [DecidableEq AP]
    (root : PositiveLTL AP)
    (interp : AP -> Letter -> Prop)
    (dec : ∀ ap letter, Decidable (interp ap letter))
    (word : OmegaWord Letter)
    (hsatInitial : PositiveLTL.Satisfies interp word root)
    (node : AlternatingParityAutomaton.Node)
    (child : Nat)
    (hactiveParent :
      PositiveLTL.subformulaClosure_guidedRunActive
        root interp dec word hsatInitial node)
    (hactiveChild :
      PositiveLTL.subformulaClosure_guidedRunActive
        root interp dec word hsatInitial (child :: node)) :
    PositiveLTL.subformulaClosure_guidedRunState
      root interp dec word hsatInitial (child :: node) ∈
      (PositiveLTL.subformulaTransition root interp
        (PositiveLTL.subformulaClosure_guidedRunState
          root interp dec word hsatInitial node)
        (word node.length)).atoms := by
  let parent :=
    PositiveLTL.subformulaClosure_guidedRunNodeData
      root interp dec word hsatInitial node
  have hparent : parent.1.2 := hactiveParent
  haveI : Decidable parent.1.2 := Classical.propDecidable parent.1.2
  let existsExpansion :=
    PositiveLTL.subformulaClosure_exists_progress_exactStepExpansion
      root interp dec parent.1.1 (OmegaWord.drop word node.length)
      (parent.2 hparent)
  let expansion := Classical.choose existsExpansion
  have hchildExpansion :
      expansion.childActive child := by
    simpa [PositiveLTL.subformulaClosure_guidedRunActive,
      PositiveLTL.subformulaClosure_guidedRunNodeData, parent, hparent,
      existsExpansion, expansion] using hactiveChild
  have hatom :
      expansion.childState child ∈
        (PositiveLTL.subformulaTransition root interp
          parent.1.1 (word node.length)).atoms :=
    expansion.child_atom child hchildExpansion
  simpa [PositiveLTL.subformulaClosure_guidedRunState,
    PositiveLTL.subformulaClosure_guidedRunNodeData, parent, hparent,
    existsExpansion, expansion] using hatom

theorem PositiveLTL.subformulaClosure_guidedRun_active_satisfies
    {AP : Type u}
    {Letter : Type v}
    [DecidableEq AP]
    (root : PositiveLTL AP)
    (interp : AP -> Letter -> Prop)
    (dec : ∀ ap letter, Decidable (interp ap letter))
    (word : OmegaWord Letter)
    (hsatInitial : PositiveLTL.Satisfies interp word root)
    (node : AlternatingParityAutomaton.Node)
    (hactive :
      PositiveLTL.subformulaClosure_guidedRunActive
        root interp dec word hsatInitial node) :
    PositiveLTL.Satisfies interp (OmegaWord.drop word node.length)
      (PositiveLTL.subformulaClosure_guidedRunState
        root interp dec word hsatInitial node).1 :=
  (PositiveLTL.subformulaClosure_guidedRunNodeData
    root interp dec word hsatInitial node).2 hactive

theorem PositiveLTL.subformulaClosure_guidedRun_child_until_self_progress
    {AP : Type u}
    {Letter : Type v}
    [DecidableEq AP]
    (root : PositiveLTL AP)
    (interp : AP -> Letter -> Prop)
    (dec : ∀ ap letter, Decidable (interp ap letter))
    (word : OmegaWord Letter)
    (hsatInitial : PositiveLTL.Satisfies interp word root)
    (node : AlternatingParityAutomaton.Node)
    (child : Nat)
    (φ ψ : PositiveLTL AP)
    (hactiveParent :
      PositiveLTL.subformulaClosure_guidedRunActive
        root interp dec word hsatInitial node)
    (hactiveChild :
      PositiveLTL.subformulaClosure_guidedRunActive
        root interp dec word hsatInitial (child :: node))
    (hparentUntil :
      (PositiveLTL.subformulaClosure_guidedRunState
        root interp dec word hsatInitial node).1 =
        PositiveLTL.until φ ψ)
    (hself :
      PositiveLTL.subformulaClosure_guidedRunState
        root interp dec word hsatInitial (child :: node) =
      PositiveLTL.subformulaClosure_guidedRunState
        root interp dec word hsatInitial node) :
    ¬ PositiveLTL.Satisfies interp
        (OmegaWord.drop word node.length) ψ := by
  let parent :=
    PositiveLTL.subformulaClosure_guidedRunNodeData
      root interp dec word hsatInitial node
  have hparent : parent.1.2 := hactiveParent
  haveI : Decidable parent.1.2 := Classical.propDecidable parent.1.2
  let existsExpansion :=
    PositiveLTL.subformulaClosure_exists_progress_exactStepExpansion
      root interp dec parent.1.1 (OmegaWord.drop word node.length)
      (parent.2 hparent)
  let expansion := Classical.choose existsExpansion
  have hspec := Classical.choose_spec existsExpansion
  have hchildExpansion :
      expansion.childActive child := by
    simpa [PositiveLTL.subformulaClosure_guidedRunActive,
      PositiveLTL.subformulaClosure_guidedRunNodeData, parent, hparent,
      existsExpansion, expansion] using hactiveChild
  have hparentUntil' : parent.1.1.1 = PositiveLTL.until φ ψ := by
    simpa [PositiveLTL.subformulaClosure_guidedRunState, parent] using
      hparentUntil
  have hself' : expansion.childState child = parent.1.1 := by
    simpa [PositiveLTL.subformulaClosure_guidedRunState,
      PositiveLTL.subformulaClosure_guidedRunNodeData, parent, hparent,
      existsExpansion, expansion] using hself
  exact hspec.2.1 child φ ψ hchildExpansion hparentUntil' hself'

theorem PositiveLTL.subformulaClosure_guidedRun_child_release_self_of_not_left
    {AP : Type u}
    {Letter : Type v}
    [DecidableEq AP]
    (root : PositiveLTL AP)
    (interp : AP -> Letter -> Prop)
    (dec : ∀ ap letter, Decidable (interp ap letter))
    (word : OmegaWord Letter)
    (hsatInitial : PositiveLTL.Satisfies interp word root)
    (node : AlternatingParityAutomaton.Node)
    (φ ψ : PositiveLTL AP)
    (hactiveParent :
      PositiveLTL.subformulaClosure_guidedRunActive
        root interp dec word hsatInitial node)
    (hparentRelease :
      (PositiveLTL.subformulaClosure_guidedRunState
        root interp dec word hsatInitial node).1 =
        PositiveLTL.release φ ψ)
    (hnotLeft :
      ¬ PositiveLTL.Satisfies interp
          (OmegaWord.drop word node.length) φ) :
    ∃ child,
      PositiveLTL.subformulaClosure_guidedRunActive
        root interp dec word hsatInitial (child :: node) ∧
      PositiveLTL.subformulaClosure_guidedRunState
        root interp dec word hsatInitial (child :: node) =
      PositiveLTL.subformulaClosure_guidedRunState
        root interp dec word hsatInitial node := by
  let parent :=
    PositiveLTL.subformulaClosure_guidedRunNodeData
      root interp dec word hsatInitial node
  have hparent : parent.1.2 := hactiveParent
  haveI : Decidable parent.1.2 := Classical.propDecidable parent.1.2
  let existsExpansion :=
    PositiveLTL.subformulaClosure_exists_progress_exactStepExpansion
      root interp dec parent.1.1 (OmegaWord.drop word node.length)
      (parent.2 hparent)
  let expansion := Classical.choose existsExpansion
  have hspec := Classical.choose_spec existsExpansion
  have hparentRelease' : parent.1.1.1 = PositiveLTL.release φ ψ := by
    simpa [PositiveLTL.subformulaClosure_guidedRunState, parent] using
      hparentRelease
  rcases hspec.2.2.1 φ ψ hparentRelease' hnotLeft with
    ⟨child, hchildActive, hchildState⟩
  refine ⟨child, ?_, ?_⟩
  · simpa [PositiveLTL.subformulaClosure_guidedRunActive,
      PositiveLTL.subformulaClosure_guidedRunNodeData, parent, hparent,
      existsExpansion, expansion] using hchildActive
  · simpa [PositiveLTL.subformulaClosure_guidedRunState,
      PositiveLTL.subformulaClosure_guidedRunNodeData, parent, hparent,
      existsExpansion, expansion] using hchildState

theorem PositiveLTL.subformulaClosure_guidedRun_child_release_self_not_left
    {AP : Type u}
    {Letter : Type v}
    [DecidableEq AP]
    (root : PositiveLTL AP)
    (interp : AP -> Letter -> Prop)
    (dec : ∀ ap letter, Decidable (interp ap letter))
    (word : OmegaWord Letter)
    (hsatInitial : PositiveLTL.Satisfies interp word root)
    (node : AlternatingParityAutomaton.Node)
    (child : Nat)
    (φ ψ : PositiveLTL AP)
    (hactiveParent :
      PositiveLTL.subformulaClosure_guidedRunActive
        root interp dec word hsatInitial node)
    (hactiveChild :
      PositiveLTL.subformulaClosure_guidedRunActive
        root interp dec word hsatInitial (child :: node))
    (hparentRelease :
      (PositiveLTL.subformulaClosure_guidedRunState
        root interp dec word hsatInitial node).1 =
        PositiveLTL.release φ ψ)
    (hself :
      PositiveLTL.subformulaClosure_guidedRunState
        root interp dec word hsatInitial (child :: node) =
      PositiveLTL.subformulaClosure_guidedRunState
        root interp dec word hsatInitial node) :
    ¬ PositiveLTL.Satisfies interp
        (OmegaWord.drop word node.length) φ := by
  let parent :=
    PositiveLTL.subformulaClosure_guidedRunNodeData
      root interp dec word hsatInitial node
  have hparent : parent.1.2 := hactiveParent
  haveI : Decidable parent.1.2 := Classical.propDecidable parent.1.2
  let existsExpansion :=
    PositiveLTL.subformulaClosure_exists_progress_exactStepExpansion
      root interp dec parent.1.1 (OmegaWord.drop word node.length)
      (parent.2 hparent)
  let expansion := Classical.choose existsExpansion
  have hspec := Classical.choose_spec existsExpansion
  have hchildExpansion :
      expansion.childActive child := by
    simpa [PositiveLTL.subformulaClosure_guidedRunActive,
      PositiveLTL.subformulaClosure_guidedRunNodeData, parent, hparent,
      existsExpansion, expansion] using hactiveChild
  have hparentRelease' : parent.1.1.1 = PositiveLTL.release φ ψ := by
    simpa [PositiveLTL.subformulaClosure_guidedRunState, parent] using
      hparentRelease
  have hself' : expansion.childState child = parent.1.1 := by
    simpa [PositiveLTL.subformulaClosure_guidedRunState,
      PositiveLTL.subformulaClosure_guidedRunNodeData, parent, hparent,
      existsExpansion, expansion] using hself
  exact hspec.2.2.2 child φ ψ hchildExpansion hparentRelease' hself'

/-- The progress-guided run tree generated from semantic satisfaction. -/
noncomputable def PositiveLTL.subformulaClosure_guidedRun
    {AP : Type u}
    {Letter : Type v}
    [DecidableEq AP]
    (root : PositiveLTL AP)
    (interp : AP -> Letter -> Prop)
    (dec : ∀ ap letter, Decidable (interp ap letter))
    (word : OmegaWord Letter)
    (hsatInitial : PositiveLTL.Satisfies interp word root) :
    ((PositiveLTL.subformulaClosure (Letter := Letter) root).toAPA
      interp dec).Run word where
  active := PositiveLTL.subformulaClosure_guidedRunActive
    root interp dec word hsatInitial
  stateAt := PositiveLTL.subformulaClosure_guidedRunState
    root interp dec word hsatInitial
  root_active :=
    PositiveLTL.subformulaClosure_guidedRun_root_active
      root interp dec word hsatInitial
  root_state :=
    PositiveLTL.subformulaClosure_guidedRun_root_state
      root interp dec word hsatInitial
  step_satisfied :=
    PositiveLTL.subformulaClosure_guidedRun_step_satisfied
      root interp dec word hsatInitial

/--
Along the progress-guided run for the canonical subformula closure, every
active child either keeps the same formula state or moves to a strict
subformula.
-/
theorem PositiveLTL.subformulaClosure_guidedRun_child_self_or_size_lt
    {AP : Type u}
    {Letter : Type v}
    [DecidableEq AP]
    (root : PositiveLTL AP)
    (interp : AP -> Letter -> Prop)
    (dec : ∀ ap letter, Decidable (interp ap letter))
    (word : OmegaWord Letter)
    (hsatInitial : PositiveLTL.Satisfies interp word root)
    (node : AlternatingParityAutomaton.Node)
    (child : Nat)
    (hactiveParent :
      PositiveLTL.subformulaClosure_guidedRunActive
        root interp dec word hsatInitial node)
    (hactiveChild :
      PositiveLTL.subformulaClosure_guidedRunActive
        root interp dec word hsatInitial (child :: node)) :
    (PositiveLTL.subformulaClosure_guidedRunState
        root interp dec word hsatInitial (child :: node)).1 =
      (PositiveLTL.subformulaClosure_guidedRunState
        root interp dec word hsatInitial node).1 ∨
      (PositiveLTL.subformulaClosure_guidedRunState
        root interp dec word hsatInitial (child :: node)).1.size <
        (PositiveLTL.subformulaClosure_guidedRunState
          root interp dec word hsatInitial node).1.size := by
  have hatom :=
    PositiveLTL.subformulaClosure_guidedRun_child_atom
      root interp dec word hsatInitial node child hactiveParent hactiveChild
  exact
    PositiveLTL.subformulaTransition_atoms_self_or_size_lt
      root interp
      (PositiveLTL.subformulaClosure_guidedRunState
        root interp dec word hsatInitial node)
      (PositiveLTL.subformulaClosure_guidedRunState
        root interp dec word hsatInitial (child :: node))
      (word node.length)
      hatom

/--
Self-loop children in the progress-guided run can only occur at temporal
fixed-point states.  Non-temporal formulas always move to a strict subformula.
-/
theorem PositiveLTL.subformulaClosure_guidedRun_child_self_is_until_or_release
    {AP : Type u}
    {Letter : Type v}
    [DecidableEq AP]
    (root : PositiveLTL AP)
    (interp : AP -> Letter -> Prop)
    (dec : ∀ ap letter, Decidable (interp ap letter))
    (word : OmegaWord Letter)
    (hsatInitial : PositiveLTL.Satisfies interp word root)
    (node : AlternatingParityAutomaton.Node)
    (child : Nat)
    (hactiveParent :
      PositiveLTL.subformulaClosure_guidedRunActive
        root interp dec word hsatInitial node)
    (hactiveChild :
      PositiveLTL.subformulaClosure_guidedRunActive
        root interp dec word hsatInitial (child :: node))
    (hself :
      PositiveLTL.subformulaClosure_guidedRunState
        root interp dec word hsatInitial (child :: node) =
      PositiveLTL.subformulaClosure_guidedRunState
        root interp dec word hsatInitial node) :
    (∃ φ ψ : PositiveLTL AP,
      (PositiveLTL.subformulaClosure_guidedRunState
        root interp dec word hsatInitial node).1 = PositiveLTL.until φ ψ) ∨
      ∃ φ ψ : PositiveLTL AP,
        (PositiveLTL.subformulaClosure_guidedRunState
          root interp dec word hsatInitial node).1 = PositiveLTL.release φ ψ := by
  have hchildAtom :=
    PositiveLTL.subformulaClosure_guidedRun_child_atom
      root interp dec word hsatInitial node child hactiveParent hactiveChild
  have hselfAtom :
      PositiveLTL.subformulaClosure_guidedRunState
        root interp dec word hsatInitial node ∈
        (PositiveLTL.subformulaTransition root interp
          (PositiveLTL.subformulaClosure_guidedRunState
            root interp dec word hsatInitial node)
          (word node.length)).atoms := by
    simpa [hself] using hchildAtom
  exact
    PositiveLTL.subformulaTransition_self_atom_is_until_or_release
      root interp dec
      (PositiveLTL.subformulaClosure_guidedRunState
        root interp dec word hsatInitial node)
      (word node.length)
      hselfAtom

/--
On an active branch of the progress-guided run, every branch state
semantically satisfies its formula at the matching suffix.
-/
theorem PositiveLTL.subformulaClosure_guidedRun_branch_satisfies
    {AP : Type u}
    {Letter : Type v}
    [DecidableEq AP]
    (root : PositiveLTL AP)
    (interp : AP -> Letter -> Prop)
    (dec : ∀ ap letter, Decidable (interp ap letter))
    (word : OmegaWord Letter)
    (hsatInitial : PositiveLTL.Satisfies interp word root)
    (branch : Nat -> Nat)
    (hbranch :
      (PositiveLTL.subformulaClosure_guidedRun
        root interp dec word hsatInitial).ActiveBranch branch)
    (n : Nat) :
    PositiveLTL.Satisfies interp (OmegaWord.drop word n)
      ((PositiveLTL.subformulaClosure_guidedRun
        root interp dec word hsatInitial).stateAt
          (AlternatingParityAutomaton.branchPrefix branch n)).1 := by
  have hactive := hbranch n
  simpa using
    PositiveLTL.subformulaClosure_guidedRun_active_satisfies
      root interp dec word hsatInitial
      (AlternatingParityAutomaton.branchPrefix branch n)
      hactive

/--
Along any active guided branch, the formula component eventually becomes
constant.  Formula sizes form an antitone natural sequence, hence eventually
stabilize; once the size is stable, the local self-or-strict-subformula
invariant forces equality of formulas at every later step.
-/
theorem PositiveLTL.subformulaClosure_guidedRun_branch_eventually_formula_eq
    {AP : Type u}
    {Letter : Type v}
    [DecidableEq AP]
    (root : PositiveLTL AP)
    (interp : AP -> Letter -> Prop)
    (dec : ∀ ap letter, Decidable (interp ap letter))
    (word : OmegaWord Letter)
    (hsatInitial : PositiveLTL.Satisfies interp word root)
    (branch : Nat -> Nat)
    (hbranch :
      (PositiveLTL.subformulaClosure_guidedRun
        root interp dec word hsatInitial).ActiveBranch branch) :
    ∃ N : Nat,
      ∀ n : Nat, N ≤ n ->
        ((PositiveLTL.subformulaClosure_guidedRun
          root interp dec word hsatInitial).stateAt
            (AlternatingParityAutomaton.branchPrefix branch n)).1 =
        ((PositiveLTL.subformulaClosure_guidedRun
          root interp dec word hsatInitial).stateAt
            (AlternatingParityAutomaton.branchPrefix branch N)).1 := by
  let stateFormula : Nat -> PositiveLTL AP :=
    fun n =>
      ((PositiveLTL.subformulaClosure_guidedRun
        root interp dec word hsatInitial).stateAt
          (AlternatingParityAutomaton.branchPrefix branch n)).1
  let sizeSeq : Nat -> Nat := fun n => (stateFormula n).size
  have hsucc_le : ∀ n, sizeSeq (n + 1) ≤ sizeSeq n := by
    intro n
    have hmove :=
      PositiveLTL.subformulaClosure_guidedRun_child_self_or_size_lt
        root interp dec word hsatInitial
        (AlternatingParityAutomaton.branchPrefix branch n)
        (branch n)
        (hbranch n)
        (by simpa using hbranch (n + 1))
    rcases hmove with hsame | hlt
    · change (stateFormula (n + 1)).size ≤ (stateFormula n).size
      rw [show stateFormula (n + 1) = stateFormula n by
        simpa [stateFormula, PositiveLTL.subformulaClosure_guidedRun] using hsame]
    · exact Nat.le_of_lt hlt
  rcases nat_eventually_constant_of_succ_le sizeSeq hsucc_le with
    ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n hn
  change stateFormula n = stateFormula N
  refine Nat.le_induction ?base ?step n hn
  · rfl
  · intro m hm ih
    have hmove :=
      PositiveLTL.subformulaClosure_guidedRun_child_self_or_size_lt
        root interp dec word hsatInitial
        (AlternatingParityAutomaton.branchPrefix branch m)
        (branch m)
        (hbranch m)
        (by simpa using hbranch (m + 1))
    rcases hmove with hsame | hlt
    · change stateFormula (m + 1) = stateFormula N
      rw [show stateFormula (m + 1) = stateFormula m by
        simpa [stateFormula, PositiveLTL.subformulaClosure_guidedRun] using hsame]
      exact ih
    · have hmSize : sizeSeq m = sizeSeq N := hN m hm
      have hsuccSize : sizeSeq (m + 1) = sizeSeq N :=
        hN (m + 1) (Nat.le_trans hm (Nat.le_succ m))
      have hbad : sizeSeq (m + 1) < sizeSeq m := by
        simpa [sizeSeq, stateFormula] using hlt
      rw [hmSize, hsuccSize] at hbad
      exact False.elim (Nat.lt_irrefl _ hbad)

/--
Every active guided branch has even least recurring priority.  If the eventual
branch formula had odd priority, it would be an `until` formula; semantic
satisfaction supplies a future right-side witness, while the guided self-loop
progress lemma forbids the right side at every stable self-loop position.
-/
theorem PositiveLTL.subformulaClosure_guidedRun_branch_min_even
    {AP : Type u}
    {Letter : Type v}
    [DecidableEq AP]
    (root : PositiveLTL AP)
    (interp : AP -> Letter -> Prop)
    (dec : ∀ ap letter, Decidable (interp ap letter))
    (word : OmegaWord Letter)
    (hsatInitial : PositiveLTL.Satisfies interp word root)
    (branch : Nat -> Nat)
    (hbranch :
      (PositiveLTL.subformulaClosure_guidedRun
        root interp dec word hsatInitial).ActiveBranch branch) :
    ∃ p : Nat,
      AlternatingParityAutomaton.Run.PrioritySeenInfinitelyOften
        (PositiveLTL.subformulaClosure_guidedRun
          root interp dec word hsatInitial) branch p ∧
        (∀ q : Nat,
          AlternatingParityAutomaton.Run.PrioritySeenInfinitelyOften
            (PositiveLTL.subformulaClosure_guidedRun
              root interp dec word hsatInitial) branch q -> p ≤ q) ∧
          DetParityAutomaton.NatEven p := by
  classical
  let run :=
    PositiveLTL.subformulaClosure_guidedRun
      root interp dec word hsatInitial
  rcases
    PositiveLTL.subformulaClosure_guidedRun_branch_eventually_formula_eq
      root interp dec word hsatInitial branch hbranch with
    ⟨N, hformula⟩
  let stableFormula : PositiveLTL AP :=
    (run.stateAt (AlternatingParityAutomaton.branchPrefix branch N)).1
  let p := PositiveLTL.alternatingPriority root stableFormula
  have hpriority_eventual :
      ∀ n : Nat, N ≤ n ->
        ((PositiveLTL.subformulaClosure (Letter := Letter) root).toAPA
          interp dec).priority
          (run.stateAt (AlternatingParityAutomaton.branchPrefix branch n)) = p := by
    intro n hn
    change
      PositiveLTL.alternatingPriority root
        (run.stateAt (AlternatingParityAutomaton.branchPrefix branch n)).1 = p
    rw [hformula n hn]
  have hpEven : DetParityAutomaton.NatEven p := by
    by_contra hpNotEven
    rcases
      (PositiveLTL.alternatingPriority_not_even_iff_until
        root stableFormula).mp hpNotEven with
      ⟨φ, ψ, hstableUntil⟩
    have hsatStable :
        PositiveLTL.Satisfies interp (OmegaWord.drop word N)
          (PositiveLTL.until φ ψ) := by
      have hsatN :=
        PositiveLTL.subformulaClosure_guidedRun_branch_satisfies
          root interp dec word hsatInitial branch hbranch N
      simpa [run, stableFormula, hstableUntil] using hsatN
    rcases hsatStable with ⟨t, hψt, _hbefore⟩
    let m := N + t
    have hm_ge : N ≤ m := by
      dsimp [m]
      exact Nat.le_add_right N t
    have hparentUntil :
        (PositiveLTL.subformulaClosure_guidedRunState
          root interp dec word hsatInitial
          (AlternatingParityAutomaton.branchPrefix branch m)).1 =
          PositiveLTL.until φ ψ := by
      have hfm := hformula m hm_ge
      simpa [run, stableFormula, hstableUntil] using hfm
    have hself :
        PositiveLTL.subformulaClosure_guidedRunState
          root interp dec word hsatInitial
          (AlternatingParityAutomaton.branchPrefix branch (m + 1)) =
        PositiveLTL.subformulaClosure_guidedRunState
          root interp dec word hsatInitial
          (AlternatingParityAutomaton.branchPrefix branch m) := by
      apply Subtype.ext
      have hfm := hformula m hm_ge
      have hfm_succ := hformula (m + 1) (Nat.le_trans hm_ge (Nat.le_succ m))
      simpa [run] using hfm_succ.trans hfm.symm
    have hnotψ_len :=
      PositiveLTL.subformulaClosure_guidedRun_child_until_self_progress
        root interp dec word hsatInitial
        (AlternatingParityAutomaton.branchPrefix branch m)
        (branch m) φ ψ
        (hbranch m)
        (by simpa using hbranch (m + 1))
        hparentUntil
        (by simpa using hself)
    have hnotψ :
        ¬ PositiveLTL.Satisfies interp (OmegaWord.drop word m) ψ := by
      simpa using hnotψ_len
    exact hnotψ (by
      simpa [m, OmegaWord.drop_drop, Nat.add_assoc] using hψt)
  exact
    (run.branchAccepts_iff_min_priority_even branch).mp
      (run.branchAccepts_of_eventually_priority branch p hpEven
        ⟨N, hpriority_eventual⟩)

/--
Forward semantic-to-APA acceptance for the canonical closure, reduced to the
remaining parity argument on the progress-guided run.
-/
theorem PositiveLTL.subformulaClosure_accepts_of_initial_satisfies_of_guided_branch_min_even
    {AP : Type u}
    {Letter : Type v}
    [DecidableEq AP]
    (root : PositiveLTL AP)
    (interp : AP -> Letter -> Prop)
    (dec : ∀ ap letter, Decidable (interp ap letter))
    (word : OmegaWord Letter)
    (hsatInitial : PositiveLTL.Satisfies interp word root)
    (hminEven :
      ∀ branch : Nat -> Nat,
        (PositiveLTL.subformulaClosure_guidedRun
          root interp dec word hsatInitial).ActiveBranch branch ->
          ∃ p : Nat,
            AlternatingParityAutomaton.Run.PrioritySeenInfinitelyOften
              (PositiveLTL.subformulaClosure_guidedRun
                root interp dec word hsatInitial) branch p ∧
              (∀ q : Nat,
                AlternatingParityAutomaton.Run.PrioritySeenInfinitelyOften
                  (PositiveLTL.subformulaClosure_guidedRun
                    root interp dec word hsatInitial) branch q -> p ≤ q) ∧
                DetParityAutomaton.NatEven p) :
    ((PositiveLTL.subformulaClosure (Letter := Letter) root).toAPA
      interp dec).Accepts word := by
  refine
    ⟨PositiveLTL.subformulaClosure_guidedRun
      root interp dec word hsatInitial, ?_⟩
  exact
    AlternatingParityAutomaton.Run.accepting_of_all_min_priority_even
      (PositiveLTL.subformulaClosure_guidedRun
        root interp dec word hsatInitial)
      hminEven

/-- Semantic satisfaction of the root formula yields APA run-tree acceptance. -/
theorem PositiveLTL.subformulaClosure_accepts_of_initial_satisfies
    {AP : Type u}
    {Letter : Type v}
    [DecidableEq AP]
    (root : PositiveLTL AP)
    (interp : AP -> Letter -> Prop)
    (dec : ∀ ap letter, Decidable (interp ap letter))
    (word : OmegaWord Letter)
    (hsatInitial : PositiveLTL.Satisfies interp word root) :
    ((PositiveLTL.subformulaClosure (Letter := Letter) root).toAPA
      interp dec).Accepts word :=
  PositiveLTL.subformulaClosure_accepts_of_initial_satisfies_of_guided_branch_min_even
    root interp dec word hsatInitial
    (fun branch hbranch =>
      PositiveLTL.subformulaClosure_guidedRun_branch_min_even
        root interp dec word hsatInitial branch hbranch)

noncomputable def PositiveLTL.subformulaClosure_guidedRunFromNodeData
    {AP : Type u}
    {Letter : Type v}
    [DecidableEq AP]
    (root : PositiveLTL AP)
    (interp : AP -> Letter -> Prop)
    (dec : ∀ ap letter, Decidable (interp ap letter))
    (word : OmegaWord Letter)
    (initial : root.Subformula)
    (hsatInitial : PositiveLTL.Satisfies interp word initial.1) :
    (node : AlternatingParityAutomaton.Node) ->
      { data : root.Subformula × Prop //
        data.2 ->
          PositiveLTL.Satisfies
            interp (OmegaWord.drop word node.length) data.1.1 }
  | [] =>
      ⟨(initial, True), by
        intro _
        simpa using hsatInitial⟩
  | child :: node =>
      let parent :=
        PositiveLTL.subformulaClosure_guidedRunFromNodeData
          root interp dec word initial hsatInitial node
      haveI : Decidable parent.1.2 := Classical.propDecidable parent.1.2
      if hparent : parent.1.2 then
        let existsExpansion :=
          PositiveLTL.subformulaClosure_exists_progress_exactStepExpansion
            root interp dec parent.1.1
            (OmegaWord.drop word node.length)
            (parent.2 hparent)
        let expansion :=
          Classical.choose existsExpansion
        ⟨(expansion.childState child, expansion.childActive child), by
          intro hchild
          have hspec :
              (∀ child,
                expansion.childActive child ->
                  PositiveLTL.Satisfies interp
                    (OmegaWord.drop (OmegaWord.drop word node.length) 1)
                    (expansion.childState child).1) ∧
                (∀ child φ ψ,
                  expansion.childActive child ->
                    parent.1.1.1 = PositiveLTL.until φ ψ ->
                    expansion.childState child = parent.1.1 ->
                      ¬ PositiveLTL.Satisfies
                        interp (OmegaWord.drop word node.length) ψ) ∧
                (∀ φ ψ,
                  parent.1.1.1 = PositiveLTL.release φ ψ ->
                    ¬ PositiveLTL.Satisfies
                      interp (OmegaWord.drop word node.length) φ ->
                      ∃ child,
                        expansion.childActive child ∧
                          expansion.childState child = parent.1.1) ∧
                  (∀ child φ ψ,
                    expansion.childActive child ->
                      parent.1.1.1 = PositiveLTL.release φ ψ ->
                      expansion.childState child = parent.1.1 ->
                        ¬ PositiveLTL.Satisfies
                          interp (OmegaWord.drop word node.length) φ) :=
            Classical.choose_spec existsExpansion
          have hsatChild := hspec.1 child hchild
          simpa [OmegaWord.drop_drop, Nat.add_comm, Nat.add_assoc] using hsatChild⟩
      else
        ⟨(initial, False), by
          intro hfalse
          exact False.elim hfalse⟩

noncomputable def PositiveLTL.subformulaClosure_guidedRunFromActive
    {AP : Type u}
    {Letter : Type v}
    [DecidableEq AP]
    (root : PositiveLTL AP)
    (interp : AP -> Letter -> Prop)
    (dec : ∀ ap letter, Decidable (interp ap letter))
    (word : OmegaWord Letter)
    (initial : root.Subformula)
    (hsatInitial : PositiveLTL.Satisfies interp word initial.1)
    (node : AlternatingParityAutomaton.Node) :
    Prop :=
  (PositiveLTL.subformulaClosure_guidedRunFromNodeData
    root interp dec word initial hsatInitial node).1.2

noncomputable def PositiveLTL.subformulaClosure_guidedRunFromState
    {AP : Type u}
    {Letter : Type v}
    [DecidableEq AP]
    (root : PositiveLTL AP)
    (interp : AP -> Letter -> Prop)
    (dec : ∀ ap letter, Decidable (interp ap letter))
    (word : OmegaWord Letter)
    (initial : root.Subformula)
    (hsatInitial : PositiveLTL.Satisfies interp word initial.1)
    (node : AlternatingParityAutomaton.Node) :
    root.Subformula :=
  (PositiveLTL.subformulaClosure_guidedRunFromNodeData
    root interp dec word initial hsatInitial node).1.1

/--
In the progress-guided run, active children can only occur below active
parents.  This is specific to the guided construction: inactive parents force
all descendants chosen at the next step to be inactive.
-/
theorem PositiveLTL.subformulaClosure_guidedRunFrom_active_parent
    {AP : Type u}
    {Letter : Type v}
    [DecidableEq AP]
    (root : PositiveLTL AP)
    (interp : AP -> Letter -> Prop)
    (dec : ∀ ap letter, Decidable (interp ap letter))
    (word : OmegaWord Letter)
    (initial : root.Subformula)
    (hsatInitial : PositiveLTL.Satisfies interp word initial.1)
    (node : AlternatingParityAutomaton.Node)
    (child : Nat)
    (hchild :
      PositiveLTL.subformulaClosure_guidedRunFromActive
        root interp dec word initial hsatInitial (child :: node)) :
    PositiveLTL.subformulaClosure_guidedRunFromActive
      root interp dec word initial hsatInitial node := by
  let parent :=
    PositiveLTL.subformulaClosure_guidedRunFromNodeData
      root interp dec word initial hsatInitial node
  haveI : Decidable parent.1.2 := Classical.propDecidable parent.1.2
  by_cases hparent : parent.1.2
  · simpa [PositiveLTL.subformulaClosure_guidedRunFromActive, parent] using hparent
  · have hfalse : False := by
      simpa [PositiveLTL.subformulaClosure_guidedRunFromActive,
        PositiveLTL.subformulaClosure_guidedRunFromNodeData, parent, hparent] using hchild
    exact False.elim hfalse

theorem PositiveLTL.subformulaClosure_guidedRunFrom_root_active
    {AP : Type u}
    {Letter : Type v}
    [DecidableEq AP]
    (root : PositiveLTL AP)
    (interp : AP -> Letter -> Prop)
    (dec : ∀ ap letter, Decidable (interp ap letter))
    (word : OmegaWord Letter)
    (initial : root.Subformula)
    (hsatInitial : PositiveLTL.Satisfies interp word initial.1) :
    PositiveLTL.subformulaClosure_guidedRunFromActive
      root interp dec word initial hsatInitial [] := by
  simp [PositiveLTL.subformulaClosure_guidedRunFromActive,
    PositiveLTL.subformulaClosure_guidedRunFromNodeData]

theorem PositiveLTL.subformulaClosure_guidedRunFrom_root_state
    {AP : Type u}
    {Letter : Type v}
    [DecidableEq AP]
    (root : PositiveLTL AP)
    (interp : AP -> Letter -> Prop)
    (dec : ∀ ap letter, Decidable (interp ap letter))
    (word : OmegaWord Letter)
    (initial : root.Subformula)
    (hsatInitial : PositiveLTL.Satisfies interp word initial.1) :
    PositiveLTL.subformulaClosure_guidedRunFromState
      root interp dec word initial hsatInitial [] = initial := by
  simp [PositiveLTL.subformulaClosure_guidedRunFromState,
    PositiveLTL.subformulaClosure_guidedRunFromNodeData,
    PositiveLTL.subformulaClosure]

theorem PositiveLTL.subformulaClosure_guidedRunFrom_step_satisfied
    {AP : Type u}
    {Letter : Type v}
    [DecidableEq AP]
    (root : PositiveLTL AP)
    (interp : AP -> Letter -> Prop)
    (dec : ∀ ap letter, Decidable (interp ap letter))
    (word : OmegaWord Letter)
    (initial : root.Subformula)
    (hsatInitial : PositiveLTL.Satisfies interp word initial.1)
    (node : AlternatingParityAutomaton.Node)
    (hactive :
      PositiveLTL.subformulaClosure_guidedRunFromActive
        root interp dec word initial hsatInitial node) :
    PosBool.Eval
      (fun nextState =>
        ∃ child : Nat,
          PositiveLTL.subformulaClosure_guidedRunFromActive
            root interp dec word initial hsatInitial (child :: node) ∧
            PositiveLTL.subformulaClosure_guidedRunFromState
              root interp dec word initial hsatInitial (child :: node) = nextState)
        (((PositiveLTL.subformulaClosure (Letter := Letter) root).toAPA
          interp dec).step
          (PositiveLTL.subformulaClosure_guidedRunFromState
            root interp dec word initial hsatInitial node)
          (word node.length)) := by
  let parent :=
    PositiveLTL.subformulaClosure_guidedRunFromNodeData
      root interp dec word initial hsatInitial node
  have hparent : parent.1.2 := hactive
  haveI : Decidable parent.1.2 := Classical.propDecidable parent.1.2
  let existsExpansion :=
    PositiveLTL.subformulaClosure_exists_progress_exactStepExpansion
      root interp dec parent.1.1 (OmegaWord.drop word node.length)
      (parent.2 hparent)
  let expansion := Classical.choose existsExpansion
  change
    PosBool.Eval
      (fun nextState =>
        ∃ child : Nat,
          PositiveLTL.subformulaClosure_guidedRunFromActive
            root interp dec word initial hsatInitial (child :: node) ∧
            PositiveLTL.subformulaClosure_guidedRunFromState
              root interp dec word initial hsatInitial (child :: node) = nextState)
      (PositiveLTL.subformulaTransition root interp
        parent.1.1 (word node.length))
  refine
    PosBool.eval_mono
      (fun nextState hnext => ?_)
      (PositiveLTL.subformulaTransition root interp parent.1.1
        (word node.length))
      expansion.step_satisfied
  rcases hnext with ⟨child, hchildActive, hchildState⟩
  refine ⟨child, ?_, ?_⟩
  · simpa [PositiveLTL.subformulaClosure_guidedRunFromActive,
      PositiveLTL.subformulaClosure_guidedRunFromNodeData, parent, hparent,
      existsExpansion, expansion] using hchildActive
  · simpa [PositiveLTL.subformulaClosure_guidedRunFromState,
      PositiveLTL.subformulaClosure_guidedRunFromNodeData, parent, hparent,
      existsExpansion, expansion] using hchildState

/--
In the progress-guided satisfying run, every active child is backed by an
actual atom of the parent transition.
-/
theorem PositiveLTL.subformulaClosure_guidedRunFrom_child_atom
    {AP : Type u}
    {Letter : Type v}
    [DecidableEq AP]
    (root : PositiveLTL AP)
    (interp : AP -> Letter -> Prop)
    (dec : ∀ ap letter, Decidable (interp ap letter))
    (word : OmegaWord Letter)
    (initial : root.Subformula)
    (hsatInitial : PositiveLTL.Satisfies interp word initial.1)
    (node : AlternatingParityAutomaton.Node)
    (child : Nat)
    (hactiveParent :
      PositiveLTL.subformulaClosure_guidedRunFromActive
        root interp dec word initial hsatInitial node)
    (hactiveChild :
      PositiveLTL.subformulaClosure_guidedRunFromActive
        root interp dec word initial hsatInitial (child :: node)) :
    PositiveLTL.subformulaClosure_guidedRunFromState
      root interp dec word initial hsatInitial (child :: node) ∈
      (PositiveLTL.subformulaTransition root interp
        (PositiveLTL.subformulaClosure_guidedRunFromState
          root interp dec word initial hsatInitial node)
        (word node.length)).atoms := by
  let parent :=
    PositiveLTL.subformulaClosure_guidedRunFromNodeData
      root interp dec word initial hsatInitial node
  have hparent : parent.1.2 := hactiveParent
  haveI : Decidable parent.1.2 := Classical.propDecidable parent.1.2
  let existsExpansion :=
    PositiveLTL.subformulaClosure_exists_progress_exactStepExpansion
      root interp dec parent.1.1 (OmegaWord.drop word node.length)
      (parent.2 hparent)
  let expansion := Classical.choose existsExpansion
  have hchildExpansion :
      expansion.childActive child := by
    simpa [PositiveLTL.subformulaClosure_guidedRunFromActive,
      PositiveLTL.subformulaClosure_guidedRunFromNodeData, parent, hparent,
      existsExpansion, expansion] using hactiveChild
  have hatom :
      expansion.childState child ∈
        (PositiveLTL.subformulaTransition root interp
          parent.1.1 (word node.length)).atoms :=
    expansion.child_atom child hchildExpansion
  simpa [PositiveLTL.subformulaClosure_guidedRunFromState,
    PositiveLTL.subformulaClosure_guidedRunFromNodeData, parent, hparent,
    existsExpansion, expansion] using hatom

theorem PositiveLTL.subformulaClosure_guidedRunFrom_active_satisfies
    {AP : Type u}
    {Letter : Type v}
    [DecidableEq AP]
    (root : PositiveLTL AP)
    (interp : AP -> Letter -> Prop)
    (dec : ∀ ap letter, Decidable (interp ap letter))
    (word : OmegaWord Letter)
    (initial : root.Subformula)
    (hsatInitial : PositiveLTL.Satisfies interp word initial.1)
    (node : AlternatingParityAutomaton.Node)
    (hactive :
      PositiveLTL.subformulaClosure_guidedRunFromActive
        root interp dec word initial hsatInitial node) :
    PositiveLTL.Satisfies interp (OmegaWord.drop word node.length)
      (PositiveLTL.subformulaClosure_guidedRunFromState
        root interp dec word initial hsatInitial node).1 :=
  (PositiveLTL.subformulaClosure_guidedRunFromNodeData
    root interp dec word initial hsatInitial node).2 hactive

theorem PositiveLTL.subformulaClosure_guidedRunFrom_child_until_self_progress
    {AP : Type u}
    {Letter : Type v}
    [DecidableEq AP]
    (root : PositiveLTL AP)
    (interp : AP -> Letter -> Prop)
    (dec : ∀ ap letter, Decidable (interp ap letter))
    (word : OmegaWord Letter)
    (initial : root.Subformula)
    (hsatInitial : PositiveLTL.Satisfies interp word initial.1)
    (node : AlternatingParityAutomaton.Node)
    (child : Nat)
    (φ ψ : PositiveLTL AP)
    (hactiveParent :
      PositiveLTL.subformulaClosure_guidedRunFromActive
        root interp dec word initial hsatInitial node)
    (hactiveChild :
      PositiveLTL.subformulaClosure_guidedRunFromActive
        root interp dec word initial hsatInitial (child :: node))
    (hparentUntil :
      (PositiveLTL.subformulaClosure_guidedRunFromState
        root interp dec word initial hsatInitial node).1 =
        PositiveLTL.until φ ψ)
    (hself :
      PositiveLTL.subformulaClosure_guidedRunFromState
        root interp dec word initial hsatInitial (child :: node) =
      PositiveLTL.subformulaClosure_guidedRunFromState
        root interp dec word initial hsatInitial node) :
    ¬ PositiveLTL.Satisfies interp
        (OmegaWord.drop word node.length) ψ := by
  let parent :=
    PositiveLTL.subformulaClosure_guidedRunFromNodeData
      root interp dec word initial hsatInitial node
  have hparent : parent.1.2 := hactiveParent
  haveI : Decidable parent.1.2 := Classical.propDecidable parent.1.2
  let existsExpansion :=
    PositiveLTL.subformulaClosure_exists_progress_exactStepExpansion
      root interp dec parent.1.1 (OmegaWord.drop word node.length)
      (parent.2 hparent)
  let expansion := Classical.choose existsExpansion
  have hspec := Classical.choose_spec existsExpansion
  have hchildExpansion :
      expansion.childActive child := by
    simpa [PositiveLTL.subformulaClosure_guidedRunFromActive,
      PositiveLTL.subformulaClosure_guidedRunFromNodeData, parent, hparent,
      existsExpansion, expansion] using hactiveChild
  have hparentUntil' : parent.1.1.1 = PositiveLTL.until φ ψ := by
    simpa [PositiveLTL.subformulaClosure_guidedRunFromState, parent] using
      hparentUntil
  have hself' : expansion.childState child = parent.1.1 := by
    simpa [PositiveLTL.subformulaClosure_guidedRunFromState,
      PositiveLTL.subformulaClosure_guidedRunFromNodeData, parent, hparent,
      existsExpansion, expansion] using hself
  exact hspec.2.1 child φ ψ hchildExpansion hparentUntil' hself'

theorem PositiveLTL.subformulaClosure_guidedRunFrom_child_release_self_of_not_left
    {AP : Type u}
    {Letter : Type v}
    [DecidableEq AP]
    (root : PositiveLTL AP)
    (interp : AP -> Letter -> Prop)
    (dec : ∀ ap letter, Decidable (interp ap letter))
    (word : OmegaWord Letter)
    (initial : root.Subformula)
    (hsatInitial : PositiveLTL.Satisfies interp word initial.1)
    (node : AlternatingParityAutomaton.Node)
    (φ ψ : PositiveLTL AP)
    (hactiveParent :
      PositiveLTL.subformulaClosure_guidedRunFromActive
        root interp dec word initial hsatInitial node)
    (hparentRelease :
      (PositiveLTL.subformulaClosure_guidedRunFromState
        root interp dec word initial hsatInitial node).1 =
        PositiveLTL.release φ ψ)
    (hnotLeft :
      ¬ PositiveLTL.Satisfies interp
          (OmegaWord.drop word node.length) φ) :
    ∃ child,
      PositiveLTL.subformulaClosure_guidedRunFromActive
        root interp dec word initial hsatInitial (child :: node) ∧
      PositiveLTL.subformulaClosure_guidedRunFromState
        root interp dec word initial hsatInitial (child :: node) =
      PositiveLTL.subformulaClosure_guidedRunFromState
        root interp dec word initial hsatInitial node := by
  let parent :=
    PositiveLTL.subformulaClosure_guidedRunFromNodeData
      root interp dec word initial hsatInitial node
  have hparent : parent.1.2 := hactiveParent
  haveI : Decidable parent.1.2 := Classical.propDecidable parent.1.2
  let existsExpansion :=
    PositiveLTL.subformulaClosure_exists_progress_exactStepExpansion
      root interp dec parent.1.1 (OmegaWord.drop word node.length)
      (parent.2 hparent)
  let expansion := Classical.choose existsExpansion
  have hspec := Classical.choose_spec existsExpansion
  have hparentRelease' : parent.1.1.1 = PositiveLTL.release φ ψ := by
    simpa [PositiveLTL.subformulaClosure_guidedRunFromState, parent] using
      hparentRelease
  rcases hspec.2.2.1 φ ψ hparentRelease' hnotLeft with
    ⟨child, hchildActive, hchildState⟩
  refine ⟨child, ?_, ?_⟩
  · simpa [PositiveLTL.subformulaClosure_guidedRunFromActive,
      PositiveLTL.subformulaClosure_guidedRunFromNodeData, parent, hparent,
      existsExpansion, expansion] using hchildActive
  · simpa [PositiveLTL.subformulaClosure_guidedRunFromState,
      PositiveLTL.subformulaClosure_guidedRunFromNodeData, parent, hparent,
      existsExpansion, expansion] using hchildState

theorem PositiveLTL.subformulaClosure_guidedRunFrom_child_release_self_not_left
    {AP : Type u}
    {Letter : Type v}
    [DecidableEq AP]
    (root : PositiveLTL AP)
    (interp : AP -> Letter -> Prop)
    (dec : ∀ ap letter, Decidable (interp ap letter))
    (word : OmegaWord Letter)
    (initial : root.Subformula)
    (hsatInitial : PositiveLTL.Satisfies interp word initial.1)
    (node : AlternatingParityAutomaton.Node)
    (child : Nat)
    (φ ψ : PositiveLTL AP)
    (hactiveParent :
      PositiveLTL.subformulaClosure_guidedRunFromActive
        root interp dec word initial hsatInitial node)
    (hactiveChild :
      PositiveLTL.subformulaClosure_guidedRunFromActive
        root interp dec word initial hsatInitial (child :: node))
    (hparentRelease :
      (PositiveLTL.subformulaClosure_guidedRunFromState
        root interp dec word initial hsatInitial node).1 =
        PositiveLTL.release φ ψ)
    (hself :
      PositiveLTL.subformulaClosure_guidedRunFromState
        root interp dec word initial hsatInitial (child :: node) =
      PositiveLTL.subformulaClosure_guidedRunFromState
        root interp dec word initial hsatInitial node) :
    ¬ PositiveLTL.Satisfies interp
        (OmegaWord.drop word node.length) φ := by
  let parent :=
    PositiveLTL.subformulaClosure_guidedRunFromNodeData
      root interp dec word initial hsatInitial node
  have hparent : parent.1.2 := hactiveParent
  haveI : Decidable parent.1.2 := Classical.propDecidable parent.1.2
  let existsExpansion :=
    PositiveLTL.subformulaClosure_exists_progress_exactStepExpansion
      root interp dec parent.1.1 (OmegaWord.drop word node.length)
      (parent.2 hparent)
  let expansion := Classical.choose existsExpansion
  have hspec := Classical.choose_spec existsExpansion
  have hchildExpansion :
      expansion.childActive child := by
    simpa [PositiveLTL.subformulaClosure_guidedRunFromActive,
      PositiveLTL.subformulaClosure_guidedRunFromNodeData, parent, hparent,
      existsExpansion, expansion] using hactiveChild
  have hparentRelease' : parent.1.1.1 = PositiveLTL.release φ ψ := by
    simpa [PositiveLTL.subformulaClosure_guidedRunFromState, parent] using
      hparentRelease
  have hself' : expansion.childState child = parent.1.1 := by
    simpa [PositiveLTL.subformulaClosure_guidedRunFromState,
      PositiveLTL.subformulaClosure_guidedRunFromNodeData, parent, hparent,
      existsExpansion, expansion] using hself
  exact hspec.2.2.2 child φ ψ hchildExpansion hparentRelease' hself'

/-- The progress-guided run tree generated from semantic satisfaction. -/
noncomputable def PositiveLTL.subformulaClosure_guidedRunFrom
    {AP : Type u}
    {Letter : Type v}
    [DecidableEq AP]
    (root : PositiveLTL AP)
    (interp : AP -> Letter -> Prop)
    (dec : ∀ ap letter, Decidable (interp ap letter))
    (word : OmegaWord Letter)
    (initial : root.Subformula)
    (hsatInitial : PositiveLTL.Satisfies interp word initial.1) :
    (((PositiveLTL.subformulaClosure (Letter := Letter) root).toAPA
      interp dec).withInitial initial).Run word where
  active := PositiveLTL.subformulaClosure_guidedRunFromActive
    root interp dec word initial hsatInitial
  stateAt := PositiveLTL.subformulaClosure_guidedRunFromState
    root interp dec word initial hsatInitial
  root_active :=
    PositiveLTL.subformulaClosure_guidedRunFrom_root_active
      root interp dec word initial hsatInitial
  root_state :=
    PositiveLTL.subformulaClosure_guidedRunFrom_root_state
      root interp dec word initial hsatInitial
  step_satisfied :=
    PositiveLTL.subformulaClosure_guidedRunFrom_step_satisfied
      root interp dec word initial hsatInitial

/--
Every active node of the progress-guided run lies on an active root-to-node
path.  Generic APA run trees do not enforce this from `active` alone, so this
construction-specific invariant is useful for branch-local recurrence proofs.
-/
theorem PositiveLTL.subformulaClosure_guidedRunFrom_pathActive_of_active
    {AP : Type u}
    {Letter : Type v}
    [DecidableEq AP]
    (root : PositiveLTL AP)
    (interp : AP -> Letter -> Prop)
    (dec : ∀ ap letter, Decidable (interp ap letter))
    (word : OmegaWord Letter)
    (initial : root.Subformula)
    (hsatInitial : PositiveLTL.Satisfies interp word initial.1)
    (node : AlternatingParityAutomaton.Node)
    (hactive :
      PositiveLTL.subformulaClosure_guidedRunFromActive
        root interp dec word initial hsatInitial node) :
    (PositiveLTL.subformulaClosure_guidedRunFrom
      root interp dec word initial hsatInitial).PathActive node := by
  induction node with
  | nil =>
      exact
        (PositiveLTL.subformulaClosure_guidedRunFrom
          root interp dec word initial hsatInitial).pathActive_nil
  | cons child node ih =>
      have hparent :
          PositiveLTL.subformulaClosure_guidedRunFromActive
            root interp dec word initial hsatInitial node :=
        PositiveLTL.subformulaClosure_guidedRunFrom_active_parent
          root interp dec word initial hsatInitial node child hactive
      have hpathParent :=
        ih hparent
      exact
        hpathParent.extend
          (PositiveLTL.subformulaClosure_guidedRunFrom
            root interp dec word initial hsatInitial)
          node child
          (by
            simpa [PositiveLTL.subformulaClosure_guidedRunFrom] using hactive)

/--
Along the progress-guided run for the canonical subformula closure, every
active child either keeps the same formula state or moves to a strict
subformula.
-/
theorem PositiveLTL.subformulaClosure_guidedRunFrom_child_self_or_size_lt
    {AP : Type u}
    {Letter : Type v}
    [DecidableEq AP]
    (root : PositiveLTL AP)
    (interp : AP -> Letter -> Prop)
    (dec : ∀ ap letter, Decidable (interp ap letter))
    (word : OmegaWord Letter)
    (initial : root.Subformula)
    (hsatInitial : PositiveLTL.Satisfies interp word initial.1)
    (node : AlternatingParityAutomaton.Node)
    (child : Nat)
    (hactiveParent :
      PositiveLTL.subformulaClosure_guidedRunFromActive
        root interp dec word initial hsatInitial node)
    (hactiveChild :
      PositiveLTL.subformulaClosure_guidedRunFromActive
        root interp dec word initial hsatInitial (child :: node)) :
    (PositiveLTL.subformulaClosure_guidedRunFromState
        root interp dec word initial hsatInitial (child :: node)).1 =
      (PositiveLTL.subformulaClosure_guidedRunFromState
        root interp dec word initial hsatInitial node).1 ∨
      (PositiveLTL.subformulaClosure_guidedRunFromState
        root interp dec word initial hsatInitial (child :: node)).1.size <
        (PositiveLTL.subformulaClosure_guidedRunFromState
          root interp dec word initial hsatInitial node).1.size := by
  have hatom :=
    PositiveLTL.subformulaClosure_guidedRunFrom_child_atom
      root interp dec word initial hsatInitial node child hactiveParent hactiveChild
  exact
    PositiveLTL.subformulaTransition_atoms_self_or_size_lt
      root interp
      (PositiveLTL.subformulaClosure_guidedRunFromState
        root interp dec word initial hsatInitial node)
      (PositiveLTL.subformulaClosure_guidedRunFromState
        root interp dec word initial hsatInitial (child :: node))
      (word node.length)
      hatom

/--
State-wise version of
`subformulaClosure_guidedRun_child_self_is_until_or_release`.
-/
theorem PositiveLTL.subformulaClosure_guidedRunFrom_child_self_is_until_or_release
    {AP : Type u}
    {Letter : Type v}
    [DecidableEq AP]
    (root : PositiveLTL AP)
    (interp : AP -> Letter -> Prop)
    (dec : ∀ ap letter, Decidable (interp ap letter))
    (word : OmegaWord Letter)
    (initial : root.Subformula)
    (hsatInitial : PositiveLTL.Satisfies interp word initial.1)
    (node : AlternatingParityAutomaton.Node)
    (child : Nat)
    (hactiveParent :
      PositiveLTL.subformulaClosure_guidedRunFromActive
        root interp dec word initial hsatInitial node)
    (hactiveChild :
      PositiveLTL.subformulaClosure_guidedRunFromActive
        root interp dec word initial hsatInitial (child :: node))
    (hself :
      PositiveLTL.subformulaClosure_guidedRunFromState
        root interp dec word initial hsatInitial (child :: node) =
      PositiveLTL.subformulaClosure_guidedRunFromState
        root interp dec word initial hsatInitial node) :
    (∃ φ ψ : PositiveLTL AP,
      (PositiveLTL.subformulaClosure_guidedRunFromState
        root interp dec word initial hsatInitial node).1 =
          PositiveLTL.until φ ψ) ∨
      ∃ φ ψ : PositiveLTL AP,
        (PositiveLTL.subformulaClosure_guidedRunFromState
          root interp dec word initial hsatInitial node).1 =
            PositiveLTL.release φ ψ := by
  have hchildAtom :=
    PositiveLTL.subformulaClosure_guidedRunFrom_child_atom
      root interp dec word initial hsatInitial node child
      hactiveParent hactiveChild
  have hselfAtom :
      PositiveLTL.subformulaClosure_guidedRunFromState
        root interp dec word initial hsatInitial node ∈
        (PositiveLTL.subformulaTransition root interp
          (PositiveLTL.subformulaClosure_guidedRunFromState
            root interp dec word initial hsatInitial node)
          (word node.length)).atoms := by
    simpa [hself] using hchildAtom
  exact
    PositiveLTL.subformulaTransition_self_atom_is_until_or_release
      root interp dec
      (PositiveLTL.subformulaClosure_guidedRunFromState
        root interp dec word initial hsatInitial node)
      (word node.length)
      hselfAtom

/--
On an active branch of the progress-guided run, every branch state
semantically satisfies its formula at the matching suffix.
-/
theorem PositiveLTL.subformulaClosure_guidedRunFrom_branch_satisfies
    {AP : Type u}
    {Letter : Type v}
    [DecidableEq AP]
    (root : PositiveLTL AP)
    (interp : AP -> Letter -> Prop)
    (dec : ∀ ap letter, Decidable (interp ap letter))
    (word : OmegaWord Letter)
    (initial : root.Subformula)
    (hsatInitial : PositiveLTL.Satisfies interp word initial.1)
    (branch : Nat -> Nat)
    (hbranch :
      (PositiveLTL.subformulaClosure_guidedRunFrom
        root interp dec word initial hsatInitial).ActiveBranch branch)
    (n : Nat) :
    PositiveLTL.Satisfies interp (OmegaWord.drop word n)
      ((PositiveLTL.subformulaClosure_guidedRunFrom
        root interp dec word initial hsatInitial).stateAt
          (AlternatingParityAutomaton.branchPrefix branch n)).1 := by
  have hactive := hbranch n
  simpa using
    PositiveLTL.subformulaClosure_guidedRunFrom_active_satisfies
      root interp dec word initial hsatInitial
      (AlternatingParityAutomaton.branchPrefix branch n)
      hactive

/--
If a progress-guided branch keeps the same formula across one step, then that
formula is necessarily an `until` or a `release` fixed point.
-/
theorem PositiveLTL.subformulaClosure_guidedRunFrom_branch_self_step_is_until_or_release
    {AP : Type u}
    {Letter : Type v}
    [DecidableEq AP]
    (root : PositiveLTL AP)
    (interp : AP -> Letter -> Prop)
    (dec : ∀ ap letter, Decidable (interp ap letter))
    (word : OmegaWord Letter)
    (initial : root.Subformula)
    (hsatInitial : PositiveLTL.Satisfies interp word initial.1)
    (branch : Nat -> Nat)
    (hbranch :
      (PositiveLTL.subformulaClosure_guidedRunFrom
        root interp dec word initial hsatInitial).ActiveBranch branch)
    (n : Nat)
    (hselfFormula :
      ((PositiveLTL.subformulaClosure_guidedRunFrom
        root interp dec word initial hsatInitial).stateAt
          (AlternatingParityAutomaton.branchPrefix branch (n + 1))).1 =
      ((PositiveLTL.subformulaClosure_guidedRunFrom
        root interp dec word initial hsatInitial).stateAt
          (AlternatingParityAutomaton.branchPrefix branch n)).1) :
    (∃ φ ψ : PositiveLTL AP,
      ((PositiveLTL.subformulaClosure_guidedRunFrom
        root interp dec word initial hsatInitial).stateAt
          (AlternatingParityAutomaton.branchPrefix branch n)).1 =
          PositiveLTL.until φ ψ) ∨
      ∃ φ ψ : PositiveLTL AP,
        ((PositiveLTL.subformulaClosure_guidedRunFrom
          root interp dec word initial hsatInitial).stateAt
            (AlternatingParityAutomaton.branchPrefix branch n)).1 =
            PositiveLTL.release φ ψ := by
  have hselfState :
      PositiveLTL.subformulaClosure_guidedRunFromState
        root interp dec word initial hsatInitial
        (AlternatingParityAutomaton.branchPrefix branch (n + 1)) =
      PositiveLTL.subformulaClosure_guidedRunFromState
        root interp dec word initial hsatInitial
        (AlternatingParityAutomaton.branchPrefix branch n) := by
    apply Subtype.ext
    simpa [PositiveLTL.subformulaClosure_guidedRunFrom] using hselfFormula
  simpa [PositiveLTL.subformulaClosure_guidedRunFrom] using
    PositiveLTL.subformulaClosure_guidedRunFrom_child_self_is_until_or_release
      root interp dec word initial hsatInitial
      (AlternatingParityAutomaton.branchPrefix branch n)
      (branch n)
      (hbranch n)
      (by simpa using hbranch (n + 1))
      (by simpa using hselfState)

/--
Along any active guided branch, the formula component eventually becomes
constant.  Formula sizes form an antitone natural sequence, hence eventually
stabilize; once the size is stable, the local self-or-strict-subformula
invariant forces equality of formulas at every later step.
-/
theorem PositiveLTL.subformulaClosure_guidedRunFrom_branch_eventually_formula_eq
    {AP : Type u}
    {Letter : Type v}
    [DecidableEq AP]
    (root : PositiveLTL AP)
    (interp : AP -> Letter -> Prop)
    (dec : ∀ ap letter, Decidable (interp ap letter))
    (word : OmegaWord Letter)
    (initial : root.Subformula)
    (hsatInitial : PositiveLTL.Satisfies interp word initial.1)
    (branch : Nat -> Nat)
    (hbranch :
      (PositiveLTL.subformulaClosure_guidedRunFrom
        root interp dec word initial hsatInitial).ActiveBranch branch) :
    ∃ N : Nat,
      ∀ n : Nat, N ≤ n ->
        ((PositiveLTL.subformulaClosure_guidedRunFrom
          root interp dec word initial hsatInitial).stateAt
            (AlternatingParityAutomaton.branchPrefix branch n)).1 =
        ((PositiveLTL.subformulaClosure_guidedRunFrom
          root interp dec word initial hsatInitial).stateAt
            (AlternatingParityAutomaton.branchPrefix branch N)).1 := by
  let stateFormula : Nat -> PositiveLTL AP :=
    fun n =>
      ((PositiveLTL.subformulaClosure_guidedRunFrom
        root interp dec word initial hsatInitial).stateAt
          (AlternatingParityAutomaton.branchPrefix branch n)).1
  let sizeSeq : Nat -> Nat := fun n => (stateFormula n).size
  have hsucc_le : ∀ n, sizeSeq (n + 1) ≤ sizeSeq n := by
    intro n
    have hmove :=
      PositiveLTL.subformulaClosure_guidedRunFrom_child_self_or_size_lt
        root interp dec word initial hsatInitial
        (AlternatingParityAutomaton.branchPrefix branch n)
        (branch n)
        (hbranch n)
        (by simpa using hbranch (n + 1))
    rcases hmove with hsame | hlt
    · change (stateFormula (n + 1)).size ≤ (stateFormula n).size
      rw [show stateFormula (n + 1) = stateFormula n by
        simpa [stateFormula, PositiveLTL.subformulaClosure_guidedRunFrom] using hsame]
    · exact Nat.le_of_lt hlt
  rcases nat_eventually_constant_of_succ_le sizeSeq hsucc_le with
    ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n hn
  change stateFormula n = stateFormula N
  refine Nat.le_induction ?base ?step n hn
  · rfl
  · intro m hm ih
    have hmove :=
      PositiveLTL.subformulaClosure_guidedRunFrom_child_self_or_size_lt
        root interp dec word initial hsatInitial
        (AlternatingParityAutomaton.branchPrefix branch m)
        (branch m)
        (hbranch m)
        (by simpa using hbranch (m + 1))
    rcases hmove with hsame | hlt
    · change stateFormula (m + 1) = stateFormula N
      rw [show stateFormula (m + 1) = stateFormula m by
        simpa [stateFormula, PositiveLTL.subformulaClosure_guidedRunFrom] using hsame]
      exact ih
    · have hmSize : sizeSeq m = sizeSeq N := hN m hm
      have hsuccSize : sizeSeq (m + 1) = sizeSeq N :=
        hN (m + 1) (Nat.le_trans hm (Nat.le_succ m))
      have hbad : sizeSeq (m + 1) < sizeSeq m := by
        simpa [sizeSeq, stateFormula] using hlt
      rw [hmSize, hsuccSize] at hbad
      exact False.elim (Nat.lt_irrefl _ hbad)

/--
Every active guided branch has even least recurring priority.  If the eventual
branch formula had odd priority, it would be an `until` formula; semantic
satisfaction supplies a future right-side witness, while the guided self-loop
progress lemma forbids the right side at every stable self-loop position.
-/
theorem PositiveLTL.subformulaClosure_guidedRunFrom_branch_min_even
    {AP : Type u}
    {Letter : Type v}
    [DecidableEq AP]
    (root : PositiveLTL AP)
    (interp : AP -> Letter -> Prop)
    (dec : ∀ ap letter, Decidable (interp ap letter))
    (word : OmegaWord Letter)
    (initial : root.Subformula)
    (hsatInitial : PositiveLTL.Satisfies interp word initial.1)
    (branch : Nat -> Nat)
    (hbranch :
      (PositiveLTL.subformulaClosure_guidedRunFrom
        root interp dec word initial hsatInitial).ActiveBranch branch) :
    ∃ p : Nat,
      AlternatingParityAutomaton.Run.PrioritySeenInfinitelyOften
        (PositiveLTL.subformulaClosure_guidedRunFrom
          root interp dec word initial hsatInitial) branch p ∧
        (∀ q : Nat,
          AlternatingParityAutomaton.Run.PrioritySeenInfinitelyOften
            (PositiveLTL.subformulaClosure_guidedRunFrom
              root interp dec word initial hsatInitial) branch q -> p ≤ q) ∧
          DetParityAutomaton.NatEven p := by
  classical
  let run :=
    PositiveLTL.subformulaClosure_guidedRunFrom
      root interp dec word initial hsatInitial
  rcases
    PositiveLTL.subformulaClosure_guidedRunFrom_branch_eventually_formula_eq
      root interp dec word initial hsatInitial branch hbranch with
    ⟨N, hformula⟩
  let stableFormula : PositiveLTL AP :=
    (run.stateAt (AlternatingParityAutomaton.branchPrefix branch N)).1
  let p := PositiveLTL.alternatingPriority root stableFormula
  have hpriority_eventual :
      ∀ n : Nat, N ≤ n ->
        ((PositiveLTL.subformulaClosure (Letter := Letter) root).toAPA
          interp dec).priority
          (run.stateAt (AlternatingParityAutomaton.branchPrefix branch n)) = p := by
    intro n hn
    change
      PositiveLTL.alternatingPriority root
        (run.stateAt (AlternatingParityAutomaton.branchPrefix branch n)).1 = p
    rw [hformula n hn]
  have hpEven : DetParityAutomaton.NatEven p := by
    by_contra hpNotEven
    rcases
      (PositiveLTL.alternatingPriority_not_even_iff_until
        root stableFormula).mp hpNotEven with
      ⟨φ, ψ, hstableUntil⟩
    have hsatStable :
        PositiveLTL.Satisfies interp (OmegaWord.drop word N)
          (PositiveLTL.until φ ψ) := by
      have hsatN :=
        PositiveLTL.subformulaClosure_guidedRunFrom_branch_satisfies
          root interp dec word initial hsatInitial branch hbranch N
      simpa [run, stableFormula, hstableUntil] using hsatN
    rcases hsatStable with ⟨t, hψt, _hbefore⟩
    let m := N + t
    have hm_ge : N ≤ m := by
      dsimp [m]
      exact Nat.le_add_right N t
    have hparentUntil :
        (PositiveLTL.subformulaClosure_guidedRunFromState
          root interp dec word initial hsatInitial
          (AlternatingParityAutomaton.branchPrefix branch m)).1 =
          PositiveLTL.until φ ψ := by
      have hfm := hformula m hm_ge
      simpa [run, stableFormula, hstableUntil] using hfm
    have hself :
        PositiveLTL.subformulaClosure_guidedRunFromState
          root interp dec word initial hsatInitial
          (AlternatingParityAutomaton.branchPrefix branch (m + 1)) =
        PositiveLTL.subformulaClosure_guidedRunFromState
          root interp dec word initial hsatInitial
          (AlternatingParityAutomaton.branchPrefix branch m) := by
      apply Subtype.ext
      have hfm := hformula m hm_ge
      have hfm_succ := hformula (m + 1) (Nat.le_trans hm_ge (Nat.le_succ m))
      simpa [run] using hfm_succ.trans hfm.symm
    have hnotψ_len :=
      PositiveLTL.subformulaClosure_guidedRunFrom_child_until_self_progress
        root interp dec word initial hsatInitial
        (AlternatingParityAutomaton.branchPrefix branch m)
        (branch m) φ ψ
        (hbranch m)
        (by simpa using hbranch (m + 1))
        hparentUntil
        (by simpa using hself)
    have hnotψ :
        ¬ PositiveLTL.Satisfies interp (OmegaWord.drop word m) ψ := by
      simpa using hnotψ_len
    exact hnotψ (by
      simpa [m, OmegaWord.drop_drop, Nat.add_assoc] using hψt)
  exact
    (run.branchAccepts_iff_min_priority_even branch).mp
      (run.branchAccepts_of_eventually_priority branch p hpEven
        ⟨N, hpriority_eventual⟩)

/--
Forward semantic-to-APA acceptance for the canonical closure, reduced to the
remaining parity argument on the progress-guided run.
-/
theorem PositiveLTL.subformulaClosure_acceptsFrom_of_satisfies_of_guided_branch_min_even
    {AP : Type u}
    {Letter : Type v}
    [DecidableEq AP]
    (root : PositiveLTL AP)
    (interp : AP -> Letter -> Prop)
    (dec : ∀ ap letter, Decidable (interp ap letter))
    (word : OmegaWord Letter)
    (initial : root.Subformula)
    (hsatInitial : PositiveLTL.Satisfies interp word initial.1)
    (hminEven :
      ∀ branch : Nat -> Nat,
        (PositiveLTL.subformulaClosure_guidedRunFrom
          root interp dec word initial hsatInitial).ActiveBranch branch ->
          ∃ p : Nat,
            AlternatingParityAutomaton.Run.PrioritySeenInfinitelyOften
              (PositiveLTL.subformulaClosure_guidedRunFrom
                root interp dec word initial hsatInitial) branch p ∧
              (∀ q : Nat,
                AlternatingParityAutomaton.Run.PrioritySeenInfinitelyOften
                  (PositiveLTL.subformulaClosure_guidedRunFrom
                    root interp dec word initial hsatInitial) branch q -> p ≤ q) ∧
                DetParityAutomaton.NatEven p) :
    ((PositiveLTL.subformulaClosure (Letter := Letter) root).toAPA
      interp dec).AcceptsFrom initial word := by
  refine
    ⟨PositiveLTL.subformulaClosure_guidedRunFrom
      root interp dec word initial hsatInitial, ?_⟩
  exact
    AlternatingParityAutomaton.Run.accepting_of_all_min_priority_even
      (PositiveLTL.subformulaClosure_guidedRunFrom
        root interp dec word initial hsatInitial)
      hminEven

/-- Semantic satisfaction of the root formula yields APA run-tree acceptance. -/
theorem PositiveLTL.subformulaClosure_acceptsFrom_of_satisfies
    {AP : Type u}
    {Letter : Type v}
    [DecidableEq AP]
    (root : PositiveLTL AP)
    (interp : AP -> Letter -> Prop)
    (dec : ∀ ap letter, Decidable (interp ap letter))
    (word : OmegaWord Letter)
    (initial : root.Subformula)
    (hsatInitial : PositiveLTL.Satisfies interp word initial.1) :
    ((PositiveLTL.subformulaClosure (Letter := Letter) root).toAPA
      interp dec).AcceptsFrom initial word :=
  PositiveLTL.subformulaClosure_acceptsFrom_of_satisfies_of_guided_branch_min_even
    root interp dec word initial hsatInitial
    (fun branch hbranch =>
      PositiveLTL.subformulaClosure_guidedRunFrom_branch_min_even
        root interp dec word initial hsatInitial branch hbranch)

/--
The concrete progress-guided run generated from semantic satisfaction is
accepting.

This exposes the canonical accepting run tree, so later automata-backend
proofs can establish support-witness recurrence properties for this specific
run instead of choosing an arbitrary accepting run.
-/
theorem PositiveLTL.subformulaClosure_guidedRunFrom_accepting
    {AP : Type u}
    {Letter : Type v}
    [DecidableEq AP]
    (root : PositiveLTL AP)
    (interp : AP -> Letter -> Prop)
    (dec : ∀ ap letter, Decidable (interp ap letter))
    (word : OmegaWord Letter)
    (initial : root.Subformula)
    (hsatInitial : PositiveLTL.Satisfies interp word initial.1) :
    (PositiveLTL.subformulaClosure_guidedRunFrom
      root interp dec word initial hsatInitial).Accepting := by
  exact
    AlternatingParityAutomaton.Run.accepting_of_all_min_priority_even
      (PositiveLTL.subformulaClosure_guidedRunFrom
        root interp dec word initial hsatInitial)
      (fun branch hbranch =>
        PositiveLTL.subformulaClosure_guidedRunFrom_branch_min_even
          root interp dec word initial hsatInitial branch hbranch)

/-- State-wise run-language correctness for the canonical subformula APA. -/
theorem PositiveLTL.subformulaClosure_acceptsFrom_iff_satisfies
    {AP : Type u}
    {Letter : Type v}
    [DecidableEq AP]
    (root : PositiveLTL AP)
    (interp : AP -> Letter -> Prop)
    (dec : ∀ ap letter, Decidable (interp ap letter))
    (state : root.Subformula)
    (word : OmegaWord Letter) :
    ((PositiveLTL.subformulaClosure (Letter := Letter) root).toAPA
      interp dec).AcceptsFrom state word ↔
      PositiveLTL.Satisfies interp word state.1 := by
  constructor
  · intro haccepts
    exact
      PositiveLTL.subformulaClosure_acceptsFrom_satisfies
        root interp dec state word haccepts
  · intro hsat
    exact
      PositiveLTL.subformulaClosure_acceptsFrom_of_satisfies
        root interp dec word state hsat

/--
Every accepting state of the canonical subformula APA has the canonical
progress-guided accepting run associated with the equivalent LTL satisfaction
proof.
-/
theorem PositiveLTL.subformulaClosure_exists_accepting_guidedRunFrom_of_acceptsFrom
    {AP : Type u}
    {Letter : Type v}
    [DecidableEq AP]
    (root : PositiveLTL AP)
    (interp : AP -> Letter -> Prop)
    (dec : ∀ ap letter, Decidable (interp ap letter))
    (state : root.Subformula)
    (word : OmegaWord Letter)
    (haccepts :
      ((PositiveLTL.subformulaClosure (Letter := Letter) root).toAPA
        interp dec).AcceptsFrom state word) :
    ∃ hsat : PositiveLTL.Satisfies interp word state.1,
      (PositiveLTL.subformulaClosure_guidedRunFrom
        root interp dec word state hsat).Accepting := by
  let hsat :=
    (PositiveLTL.subformulaClosure_acceptsFrom_iff_satisfies
      root interp dec state word).mp haccepts
  exact
    ⟨hsat,
      PositiveLTL.subformulaClosure_guidedRunFrom_accepting
        root interp dec word state hsat⟩

/--
Canonical run-language certificate for the subformula APA of a positive LTL
formula.
-/
noncomputable def PositiveLTL.subformulaClosure_runLanguageCertificate
    {AP : Type u}
    {Letter : Type v}
    [DecidableEq AP]
    (root : PositiveLTL AP)
    (interp : AP -> Letter -> Prop)
    (dec : ∀ ap letter, Decidable (interp ap letter)) :
    ((PositiveLTL.subformulaClosure (Letter := Letter) root).toAPA
      interp dec).RunLanguageCertificate :=
  (PositiveLTL.subformulaClosure (Letter := Letter) root)
    |>.runLanguageCertificateOfAcceptsFromIff interp dec
      (fun state word =>
        PositiveLTL.subformulaClosure_acceptsFrom_iff_satisfies
          root interp dec state word)

/--
The canonical run-language certificate for a positive formula has the formula
itself as its initial language.
-/
theorem PositiveLTL.subformulaClosure_runLanguageCertificate_initialLanguage_iff
    {AP : Type u}
    {Letter : Type v}
    [DecidableEq AP]
    (root : PositiveLTL AP)
    (interp : AP -> Letter -> Prop)
    (dec : ∀ ap letter, Decidable (interp ap letter))
    (word : OmegaWord Letter) :
    word ∈
        ((PositiveLTL.subformulaClosure_runLanguageCertificate
          root interp dec).toLanguageCertificate.initialLanguage) ↔
      PositiveLTL.Satisfies interp word root := by
  change
    word ∈
        (PositiveLTL.subformulaClosure (Letter := Letter) root).language interp
          ((PositiveLTL.subformulaClosure (Letter := Letter) root).initial) ↔
      PositiveLTL.Satisfies interp word root
  exact
    (PositiveLTL.subformulaClosure (Letter := Letter) root)
      |>.initial_language_iff interp word


/--
Along the generated satisfying run for the canonical subformula closure, every
active child either keeps the same formula state or moves to a strict
subformula.  This is the local structural invariant used by the branch parity
argument.
-/
theorem PositiveLTL.subformulaClosure_satisfyingRun_child_self_or_size_lt
    {AP : Type u}
    {Letter : Type v}
    [DecidableEq AP]
    (φ : PositiveLTL AP)
    (interp : AP -> Letter -> Prop)
    (dec : ∀ ap letter, Decidable (interp ap letter))
    (word : OmegaWord Letter)
    (hsatInitial :
      PositiveLTL.Satisfies interp word
        ((PositiveLTL.subformulaClosure (Letter := Letter) φ).denote
          (PositiveLTL.subformulaClosure (Letter := Letter) φ).initial))
    (node : AlternatingParityAutomaton.Node)
    (child : Nat)
    (hactiveParent :
      (PositiveLTL.subformulaClosure (Letter := Letter) φ).satisfyingRunActive
        interp dec word hsatInitial node)
    (hactiveChild :
      (PositiveLTL.subformulaClosure (Letter := Letter) φ).satisfyingRunActive
        interp dec word hsatInitial (child :: node)) :
    ((PositiveLTL.subformulaClosure (Letter := Letter) φ).satisfyingRunState
        interp dec word hsatInitial (child :: node)).1 =
      ((PositiveLTL.subformulaClosure (Letter := Letter) φ).satisfyingRunState
        interp dec word hsatInitial node).1 ∨
      ((PositiveLTL.subformulaClosure (Letter := Letter) φ).satisfyingRunState
        interp dec word hsatInitial (child :: node)).1.size <
        ((PositiveLTL.subformulaClosure (Letter := Letter) φ).satisfyingRunState
          interp dec word hsatInitial node).1.size := by
  let closure := PositiveLTL.subformulaClosure (Letter := Letter) φ
  have hatom :=
    closure.satisfyingRun_child_atom
      interp dec word hsatInitial node child hactiveParent hactiveChild
  exact
    PositiveLTL.subformulaTransition_atoms_self_or_size_lt
      φ interp
      (closure.satisfyingRunState interp dec word hsatInitial node)
      (closure.satisfyingRunState interp dec word hsatInitial (child :: node))
      (word node.length)
      (by
        simpa [closure, PositiveLTL.subformulaClosure] using hatom)

end DistributedSynthesis
