/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmWeakAlternationRemoval
import DistributedSynthesis.Formalizations.Theorem.ThmLTLAlternatingAutomaton
import DistributedSynthesis.Formalizations.Theorem.ThmLTLtoDPA

/-!
# The LTL/APA semantic bridge

This file proves that the canonical subformula-closure alternating parity
automaton of a positive LTL formula recognizes exactly the satisfying
words:

* `subformulaClosure_accepts_iff_satisfies` — run-tree acceptance of
  `(subformulaClosure root).toAPA interp dec` is equivalent to
  `PositiveLTL.Satisfies interp word root`.

Both directions work at the level of `PositionalRunDAG`:

* Satisfies → Accepts builds a guided DAG: frontiers are the reached
  satisfied states, and the support at an `until` state whose right side
  holds now is taken from the right disjunct, so it cannot contain the
  self-loop.  Threads are eventually constant by weakness; a thread
  stabilizing at an `until` would have to keep the self-loop past the
  time its right side holds, a contradiction; all other limits have even
  priority.
* Accepts → Satisfies proves that every reachable state of an accepting
  DAG is satisfied at its level, by strong induction on subformula size.
  Non-temporal states step through the checked one-step equation.  For
  `until`, the self-loop must break (an eternal self-thread would have
  odd minimal priority), and satisfaction propagates down from the break
  point; for `release`, the right side holds at every self-loop level and
  the possible break supplies the left side.

The weakness witness is `subformulaClosure_selfOrDecreasing` (subformula
size), so `weakAPAToNBACompilation`/`weakAPAToDPACompilation` apply, and
the file ends with the unconditional LTL-to-DPA compilation
`PositiveLTL.subformulaClosureDPACompilation`.
-/

namespace DistributedSynthesis

universe u v

namespace PositiveLTL

variable {AP : Type u} {Letter : Type v}
variable [DecidableEq AP]

omit [DecidableEq AP] in
/-- Membership of the left `until`/`release` child in the root closure. -/
theorem left_child_mem_subformulas
    {root φ' ψ' : PositiveLTL AP}
    {s : root.Subformula}
    (hs : s.1 = PositiveLTL.until φ' ψ' ∨ s.1 = PositiveLTL.release φ' ψ') :
    φ' ∈ root.subformulas := by
  refine subformulas_trans ?_ s.2
  rcases hs with hs | hs <;> rw [hs]
  · exact List.mem_cons_of_mem _
      (List.mem_append_left _ (mem_subformulas_self φ'))
  · exact List.mem_cons_of_mem _
      (List.mem_append_left _ (mem_subformulas_self φ'))

omit [DecidableEq AP] in
/-- Membership of the right `until`/`release` child in the root closure. -/
theorem right_child_mem_subformulas
    {root φ' ψ' : PositiveLTL AP}
    {s : root.Subformula}
    (hs : s.1 = PositiveLTL.until φ' ψ' ∨ s.1 = PositiveLTL.release φ' ψ') :
    ψ' ∈ root.subformulas := by
  refine subformulas_trans ?_ s.2
  rcases hs with hs | hs <;> rw [hs]
  · exact List.mem_cons_of_mem _
      (List.mem_append_right _ (mem_subformulas_self ψ'))
  · exact List.mem_cons_of_mem _
      (List.mem_append_right _ (mem_subformulas_self ψ'))

section Bridge

variable (root : PositiveLTL AP)
variable (interp : AP -> Letter -> Prop)
variable (dec : ∀ ap letter, Decidable (interp ap letter))

/-- The canonical closure automaton, fixed for this file. -/
@[reducible] noncomputable def closureAPA :
    AlternatingParityAutomaton.{v, u} Letter :=
  (PositiveLTL.subformulaClosure (Letter := Letter) root).toAPA interp dec

/-- The weakness witness: subformula size is self-or-decreasing. -/
theorem subformulaClosure_selfOrDecreasing :
    AlternatingParityAutomaton.SelfOrDecreasing (closureAPA root interp dec)
      (fun state => state.1.size) := by
  intro s letter s' hmem
  letI := dec
  rcases subformulaTransition_atoms_self_or_size_lt
      root interp s s' letter hmem with hself | hlt
  · exact Or.inl (Subtype.ext hself)
  · exact Or.inr hlt

/-- The step equation of the closure automaton, in satisfaction form. -/
theorem closure_satisfies_iff_eval
    (s : root.Subformula) (w : OmegaWord Letter) :
    PositiveLTL.Satisfies interp w s.1 ↔
      PosBool.Eval
        (fun s' : root.Subformula =>
          PositiveLTL.Satisfies interp (OmegaWord.drop w 1) s'.1)
        ((closureAPA root interp dec).step s (w 0)) :=
  ((PositiveLTL.subformulaClosure (Letter := Letter) root).toAPA_stepEquation
    interp dec s w).symm

/-- Eval decomposition of the step at an `until` state. -/
theorem eval_step_until_iff
    {φ' ψ' : PositiveLTL AP}
    (s : root.Subformula) (hs : s.1 = PositiveLTL.until φ' ψ')
    (hφmem : φ' ∈ root.subformulas) (hψmem : ψ' ∈ root.subformulas)
    (v : root.Subformula -> Prop) (letter : Letter) :
    PosBool.Eval v ((closureAPA root interp dec).step s letter) ↔
      (PosBool.Eval v ((closureAPA root interp dec).step ⟨ψ', hψmem⟩ letter) ∨
        (PosBool.Eval v ((closureAPA root interp dec).step ⟨φ', hφmem⟩ letter) ∧ v s)) := by
  obtain ⟨sval, hval⟩ := s
  cases hs
  exact Iff.rfl

/-- Eval decomposition of the step at a `release` state. -/
theorem eval_step_release_iff
    {φ' ψ' : PositiveLTL AP}
    (s : root.Subformula) (hs : s.1 = PositiveLTL.release φ' ψ')
    (hφmem : φ' ∈ root.subformulas) (hψmem : ψ' ∈ root.subformulas)
    (v : root.Subformula -> Prop) (letter : Letter) :
    PosBool.Eval v ((closureAPA root interp dec).step s letter) ↔
      (PosBool.Eval v ((closureAPA root interp dec).step ⟨ψ', hψmem⟩ letter) ∧
        (PosBool.Eval v ((closureAPA root interp dec).step ⟨φ', hφmem⟩ letter) ∨ v s)) := by
  obtain ⟨sval, hval⟩ := s
  cases hs
  exact Iff.rfl

/-- Atoms of a child step embed into the atoms of the `until` step. -/
theorem mem_step_atoms_until_left
    {φ' ψ' : PositiveLTL AP}
    (s : root.Subformula) (hs : s.1 = PositiveLTL.until φ' ψ')
    (hψmem : ψ' ∈ root.subformulas) (letter : Letter)
    {x : root.Subformula}
    (hx : x ∈ ((closureAPA root interp dec).step ⟨ψ', hψmem⟩ letter).atoms) :
    x ∈ ((closureAPA root interp dec).step s letter).atoms := by
  obtain ⟨sval, hval⟩ := s
  cases hs
  exact List.mem_append_left _ hx

/-- Step atoms of a state are bounded by the state's size. -/
theorem step_atoms_size_le
    (t : root.Subformula) (letter : Letter)
    {x : root.Subformula}
    (hx : x ∈ ((closureAPA root interp dec).step t letter).atoms) :
    x.1.size ≤ t.1.size := by
  letI := dec
  rcases subformulaTransition_atoms_self_or_size_lt
      root interp t x letter hx with hself | hlt
  · rw [hself]
  · omega

/-- Nontemporal states have strictly smaller step atoms. -/
theorem step_atoms_size_lt_of_nontemporal
    (t : root.Subformula) (letter : Letter)
    (hnotU : ∀ φ' ψ' : PositiveLTL AP, t.1 ≠ PositiveLTL.until φ' ψ')
    (hnotR : ∀ φ' ψ' : PositiveLTL AP, t.1 ≠ PositiveLTL.release φ' ψ')
    {x : root.Subformula}
    (hx : x ∈ ((closureAPA root interp dec).step t letter).atoms) :
    x.1.size < t.1.size := by
  letI := dec
  have hraw := PosBool.mem_atoms_pmap _ _ hx
  rcases hraw with ⟨ψ, hψatoms, hxeq⟩
  have hxval : x.1 = ψ := by rw [hxeq]
  rw [hxval]
  clear hxeq hxval hx
  match ht : t.1, hψatoms with
  | PositiveLTL.verum, hψatoms => simp [alternatingStep, PosBool.atoms] at hψatoms
  | PositiveLTL.falsum, hψatoms => simp [alternatingStep, PosBool.atoms] at hψatoms
  | PositiveLTL.lit l, hψatoms =>
      by_cases hl : literalHolds interp letter l
      · simp [alternatingStep, hl, PosBool.atoms] at hψatoms
      · simp [alternatingStep, hl, PosBool.atoms] at hψatoms
  | PositiveLTL.conj a b, hψatoms =>
      rcases List.mem_append.mp hψatoms with h | h
      · have := size_le_of_mem_subformulas
          (alternatingStep_atoms_subformulas interp letter a ψ h)
        simp [PositiveLTL.size]
        omega
      · have := size_le_of_mem_subformulas
          (alternatingStep_atoms_subformulas interp letter b ψ h)
        simp [PositiveLTL.size]
        omega
  | PositiveLTL.disj a b, hψatoms =>
      rcases List.mem_append.mp hψatoms with h | h
      · have := size_le_of_mem_subformulas
          (alternatingStep_atoms_subformulas interp letter a ψ h)
        simp [PositiveLTL.size]
        omega
      · have := size_le_of_mem_subformulas
          (alternatingStep_atoms_subformulas interp letter b ψ h)
        simp [PositiveLTL.size]
        omega
  | PositiveLTL.next a, hψatoms =>
      have hψa : ψ = a := by
        simpa [alternatingStep, PosBool.atoms] using hψatoms
      rw [hψa]
      simp [PositiveLTL.size]
  | PositiveLTL.until a b, hψatoms => exact absurd rfl (ht ▸ hnotU a b)
  | PositiveLTL.release a b, hψatoms => exact absurd rfl (ht ▸ hnotR a b)

section SatisfiedSupport

variable (word : OmegaWord Letter)

/--
A satisfied support at level `n`: contained in the step atoms, all members
satisfied at level `n + 1`, and evaluating the step formula.
-/
noncomputable def satSupport (n : Nat) (s : root.Subformula) :
    Finset root.Subformula := by
  classical
  exact
    if hsat : PositiveLTL.Satisfies interp (OmegaWord.drop word n) s.1 then
      (Classical.choose
        ((PosBool.eval_iff_exists_support_subset_atoms
          (fun s' : root.Subformula =>
            PositiveLTL.Satisfies interp (OmegaWord.drop word (n + 1)) s'.1)
          ((closureAPA root interp dec).step s (word n))).mp
          (by
            have heval :=
              (closure_satisfies_iff_eval root interp dec s
                (OmegaWord.drop word n)).mp hsat
            rw [OmegaWord.drop_drop] at heval
            have hw0 : OmegaWord.drop word n 0 = word n := by
              simp [OmegaWord.drop]
            rw [hw0] at heval
            exact heval))).toFinset
    else ∅

theorem satSupport_spec {n : Nat} {s : root.Subformula}
    (hsat : PositiveLTL.Satisfies interp (OmegaWord.drop word n) s.1) :
    (∀ x ∈ satSupport root interp dec word n s,
        PositiveLTL.Satisfies interp (OmegaWord.drop word (n + 1)) x.1) ∧
      (∀ x ∈ satSupport root interp dec word n s,
        x ∈ ((closureAPA root interp dec).step s (word n)).atoms) ∧
        PosBool.Eval (· ∈ satSupport root interp dec word n s)
          ((closureAPA root interp dec).step s (word n)) := by
  classical
  rw [satSupport, dif_pos hsat]
  set hEval :=
    (PosBool.eval_iff_exists_support_subset_atoms
      (fun s' : root.Subformula =>
        PositiveLTL.Satisfies interp (OmegaWord.drop word (n + 1)) s'.1)
      ((closureAPA root interp dec).step s (word n))).mp
      (by
        have heval :=
          (closure_satisfies_iff_eval root interp dec s
            (OmegaWord.drop word n)).mp hsat
        rw [OmegaWord.drop_drop] at heval
        have hw0 : OmegaWord.drop word n 0 = word n := by
          simp [OmegaWord.drop]
        rw [hw0] at heval
        exact heval)
  have hspec := Classical.choose_spec hEval
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    exact hspec.1 x (List.mem_toFinset.mp hx)
  · intro x hx
    exact hspec.2.1 x (List.mem_toFinset.mp hx)
  · refine PosBool.eval_mono ?_ _ hspec.2.2
    intro x hx
    exact List.mem_toFinset.mpr hx

/--
The guided support: at an `until` state whose right side holds now, take
the satisfied support of the right child, so the self-loop is excluded;
otherwise take the generic satisfied support.
-/
noncomputable def guidedSupport (n : Nat) (s : root.Subformula) :
    Finset root.Subformula := by
  classical
  exact
    if h : ∃ φ' ψ' : PositiveLTL AP,
        s.1 = PositiveLTL.until φ' ψ' ∧
          PositiveLTL.Satisfies interp (OmegaWord.drop word n) ψ' then
      satSupport root interp dec word n
        ⟨Classical.choose (Classical.choose_spec h),
          right_child_mem_subformulas
            (Or.inl (Classical.choose_spec (Classical.choose_spec h)).1)⟩
    else satSupport root interp dec word n s

/-- Bundled properties of the guided support at satisfied states. -/
theorem guidedSupport_spec {n : Nat} {s : root.Subformula}
    (hsat : PositiveLTL.Satisfies interp (OmegaWord.drop word n) s.1) :
    (∀ x ∈ guidedSupport root interp dec word n s,
        PositiveLTL.Satisfies interp (OmegaWord.drop word (n + 1)) x.1) ∧
      (∀ x ∈ guidedSupport root interp dec word n s,
        x ∈ ((closureAPA root interp dec).step s (word n)).atoms) ∧
        PosBool.Eval (· ∈ guidedSupport root interp dec word n s)
          ((closureAPA root interp dec).step s (word n)) := by
  classical
  by_cases h : ∃ φ' ψ' : PositiveLTL AP,
      s.1 = PositiveLTL.until φ' ψ' ∧
        PositiveLTL.Satisfies interp (OmegaWord.drop word n) ψ'
  · have hgs :
        guidedSupport root interp dec word n s =
          satSupport root interp dec word n
            ⟨Classical.choose (Classical.choose_spec h),
              right_child_mem_subformulas
                (Or.inl (Classical.choose_spec (Classical.choose_spec h)).1)⟩ := by
      rw [guidedSupport, dif_pos h]
    set φ' := Classical.choose h with hφ'
    set ψ' := Classical.choose (Classical.choose_spec h) with hψ'
    have hspec₀ := Classical.choose_spec (Classical.choose_spec h)
    have hsuntil : s.1 = PositiveLTL.until φ' ψ' := hspec₀.1
    have hψsat : PositiveLTL.Satisfies interp (OmegaWord.drop word n) ψ' :=
      hspec₀.2
    have hψmem : ψ' ∈ root.subformulas :=
      right_child_mem_subformulas (Or.inl hsuntil)
    have hφmem : φ' ∈ root.subformulas :=
      left_child_mem_subformulas (Or.inl hsuntil)
    have hsub := satSupport_spec root interp dec word
      (n := n) (s := ⟨ψ', hψmem⟩) hψsat
    refine ⟨?_, ?_, ?_⟩
    · intro x hx
      rw [hgs] at hx
      exact hsub.1 x hx
    · intro x hx
      rw [hgs] at hx
      exact mem_step_atoms_until_left root interp dec s hsuntil hψmem
        (word n) (hsub.2.1 x hx)
    · rw [hgs]
      rw [eval_step_until_iff root interp dec s hsuntil hφmem hψmem]
      exact Or.inl hsub.2.2
  · have hgs :
        guidedSupport root interp dec word n s =
          satSupport root interp dec word n s := by
      rw [guidedSupport, dif_neg h]
    rw [hgs]
    exact satSupport_spec root interp dec word hsat

/--
Until progress: if the right side of an `until` state holds now, the
guided support excludes the state itself.
-/
theorem guidedSupport_until_progress {n : Nat} {s : root.Subformula}
    {φ' ψ' : PositiveLTL AP}
    (hsuntil : s.1 = PositiveLTL.until φ' ψ')
    (hψsat : PositiveLTL.Satisfies interp (OmegaWord.drop word n) ψ') :
    s ∉ guidedSupport root interp dec word n s := by
  classical
  intro hmem
  have h : ∃ φ'' ψ'' : PositiveLTL AP,
      s.1 = PositiveLTL.until φ'' ψ'' ∧
        PositiveLTL.Satisfies interp (OmegaWord.drop word n) ψ'' :=
    ⟨φ', ψ', hsuntil, hψsat⟩
  rw [guidedSupport, dif_pos h] at hmem
  set ψ'' := Classical.choose (Classical.choose_spec h)
  have hspec₀ := Classical.choose_spec (Classical.choose_spec h)
  have hψmem : ψ'' ∈ root.subformulas :=
    right_child_mem_subformulas (Or.inl hspec₀.1)
  by_cases hψsat'' :
      PositiveLTL.Satisfies interp (OmegaWord.drop word n)
        (⟨ψ'', hψmem⟩ : root.Subformula).1
  · have hle := step_atoms_size_le root interp dec ⟨ψ'', hψmem⟩ (word n)
      ((satSupport_spec root interp dec word hψsat'').2.1 s hmem)
    have hlt : ψ''.size < s.1.size := by
      rw [hspec₀.1]
      show ψ''.size < PositiveLTL.size (PositiveLTL.until
        (Classical.choose h) ψ'')
      simp [PositiveLTL.size]
    simp only at hle
    omega
  · rw [satSupport, dif_neg hψsat''] at hmem
    exact absurd hmem (Finset.notMem_empty s)

/-- States reached by the guided supports. -/
inductive SatReached (word : OmegaWord Letter) : Nat -> root.Subformula -> Prop
  | zero : SatReached word 0 (PositiveLTL.rootSubformula root)
  | succ {n : Nat} {s s' : root.Subformula} :
      SatReached word n s ->
      s' ∈ guidedSupport root interp dec word n s ->
      SatReached word (n + 1) s'

/-- Reached states are satisfied at their level. -/
theorem satReached_satisfies {word : OmegaWord Letter}
    (hsat : PositiveLTL.Satisfies interp word root) :
    ∀ {n : Nat} {s : root.Subformula},
      SatReached root interp dec word n s ->
        PositiveLTL.Satisfies interp (OmegaWord.drop word n) s.1 := by
  intro n s h
  induction h with
  | zero =>
      rw [OmegaWord.drop_zero]
      exact hsat
  | @succ n s s' hreach hmem ih =>
      exact (guidedSupport_spec root interp dec word ih).1 s' hmem

/-- The satisfied frontier at a level. -/
noncomputable def satFrontier (word : OmegaWord Letter) (n : Nat) :
    Finset root.Subformula := by
  classical
  exact Finset.univ.filter (SatReached root interp dec word n)

theorem mem_satFrontier {word : OmegaWord Letter} {n : Nat}
    {s : root.Subformula} :
    s ∈ satFrontier root interp dec word n ↔
      SatReached root interp dec word n s := by
  classical
  rw [satFrontier]
  simp

/-- The guided macro support choice on the satisfied frontier. -/
noncomputable def satChoice {word : OmegaWord Letter}
    (hsat : PositiveLTL.Satisfies interp word root) (n : Nat) :
    (closureAPA root interp dec).MacroStepSupport
      (satFrontier root interp dec word n) (word n) where
  choice := fun state =>
    { support := guidedSupport root interp dec word n state.1
      support_satisfies :=
        (guidedSupport_spec root interp dec word
          (satReached_satisfies root interp dec hsat
            ((mem_satFrontier root interp dec).mp state.2))).2.2
      support_atoms := fun x hx =>
        (guidedSupport_spec root interp dec word
          (satReached_satisfies root interp dec hsat
            ((mem_satFrontier root interp dec).mp state.2))).2.1 x hx }

/-- The guided positional run DAG of a satisfied word. -/
noncomputable def satisfiedDAG {word : OmegaWord Letter}
    (hsat : PositiveLTL.Satisfies interp word root) :
    (closureAPA root interp dec).PositionalRunDAG word where
  frontier := satFrontier root interp dec word
  choice := satChoice root interp dec hsat
  initial_mem := by
    ext s
    rw [mem_satFrontier]
    constructor
    · intro hreach
      cases hreach
      exact Finset.mem_singleton_self _
    · intro hmem
      have heq : s = (closureAPA root interp dec).initial :=
        Finset.mem_singleton.mp hmem
      rw [heq]
      exact SatReached.zero
  frontier_succ := by
    intro n
    ext s'
    rw [mem_satFrontier]
    constructor
    · intro hreach
      cases hreach with
      | succ hreach' hmem =>
          exact AlternatingParityAutomaton.MacroStepSupport.mem_support.mpr
            ⟨⟨_, (mem_satFrontier root interp dec).mpr hreach'⟩, hmem⟩
    · intro hmem
      rcases AlternatingParityAutomaton.MacroStepSupport.mem_support.mp hmem with
        ⟨⟨s, hs⟩, hmem'⟩
      exact SatReached.succ ((mem_satFrontier root interp dec).mp hs) hmem'
  threads_accept := by
    intro s hzero hstep
    have hreach : ∀ n : Nat, SatReached root interp dec word n (s n) := by
      intro n
      induction n with
      | zero =>
          have hz : s 0 = PositiveLTL.rootSubformula root := hzero
          rw [hz]
          exact SatReached.zero
      | succ n ih =>
          rcases hstep n with ⟨hmemF, hsupp⟩
          exact SatReached.succ ((mem_satFrontier root interp dec).mp hmemF) hsupp
    have hsatn : ∀ n : Nat,
        PositiveLTL.Satisfies interp (OmegaWord.drop word n) (s n).1 :=
      fun n => satReached_satisfies root interp dec hsat (hreach n)
    have hmono : ∀ n : Nat,
        s (n + 1) = s n ∨ (s (n + 1)).1.size < (s n).1.size := by
      intro n
      rcases hstep n with ⟨hmemF, hsupp⟩
      exact subformulaClosure_selfOrDecreasing root interp dec
        (s n) (word n) (s (n + 1))
        ((guidedSupport_spec root interp dec word (hsatn n)).2.1
          (s (n + 1)) hsupp)
    obtain ⟨N, hconst⟩ :=
      AlternatingParityAutomaton.thread_eventually_constant
        (A := closureAPA root interp dec) (μ := fun st => st.1.size) hmono
    have hconstPrio : ∀ k : Nat, N ≤ k ->
        (closureAPA root interp dec).priority (s k) =
          (closureAPA root interp dec).priority (s N) := by
      intro k hk
      rw [hconst k hk]
    rw [AlternatingParityAutomaton.natSeqMinEvenParity_iff_of_eventually_constant
      hconstPrio]
    show DetParityAutomaton.NatEven
      (PositiveLTL.alternatingPriority root (s N).1)
    match hshape : (s N).1 with
    | PositiveLTL.verum =>
        exact alternatingPriority_verum_even root
    | PositiveLTL.falsum =>
        exact alternatingPriority_falsum_even root
    | PositiveLTL.lit l =>
        exact alternatingPriority_lit_even root l
    | PositiveLTL.conj a b =>
        exact alternatingPriority_conj_even root a b
    | PositiveLTL.disj a b =>
        exact alternatingPriority_disj_even root a b
    | PositiveLTL.next a =>
        exact alternatingPriority_next_even root a
    | PositiveLTL.release a b =>
        exact alternatingPriority_release_even root a b
    | PositiveLTL.until a b =>
        exfalso
        have hsatN := hsatn N
        rw [hshape] at hsatN
        rcases hsatN with ⟨m, hψm, _⟩
        rw [OmegaWord.drop_drop] at hψm
        have hsm : s (N + m) = s N := hconst (N + m) (by omega)
        have hsm1 : s (N + m + 1) = s N := hconst (N + m + 1) (by omega)
        have hprog :=
          guidedSupport_until_progress root interp dec word
            (n := N + m) (s := s N) hshape hψm
        rcases hstep (N + m) with ⟨hmemF, hsupp⟩
        have hsupp' : s (N + m + 1) ∈
            guidedSupport root interp dec word (N + m) (s (N + m)) := hsupp
        rw [hsm, hsm1] at hsupp'
        exact hprog hsupp'

/-- Satisfaction implies run-tree acceptance of the closure automaton. -/
theorem subformulaClosure_accepts_of_satisfies
    {word : OmegaWord Letter}
    (hsat : PositiveLTL.Satisfies interp word root) :
    (closureAPA root interp dec).Accepts word :=
  AlternatingParityAutomaton.nonempty_positionalRunDAG_iff_accepts.mp
    ⟨satisfiedDAG root interp dec hsat⟩

end SatisfiedSupport

section AcceptsToSatisfies

variable {word : OmegaWord Letter}

/-- Zero-index application of a dropped word. -/
theorem drop_apply_zero (w : OmegaWord Letter) (n : Nat) :
    OmegaWord.drop w n 0 = w n := by
  simp [OmegaWord.drop]

/-- One-step satisfaction from a satisfied next-level evaluation. -/
theorem satisfies_of_eval_next
    {m : Nat} (t : root.Subformula)
    (heval : PosBool.Eval
      (fun x : root.Subformula =>
        PositiveLTL.Satisfies interp (OmegaWord.drop word (m + 1)) x.1)
      ((closureAPA root interp dec).step t (word m))) :
    PositiveLTL.Satisfies interp (OmegaWord.drop word m) t.1 := by
  rw [closure_satisfies_iff_eval root interp dec t (OmegaWord.drop word m),
    OmegaWord.drop_drop, drop_apply_zero]
  exact heval

/-- Next-level evaluation from one-step satisfaction. -/
theorem eval_next_of_satisfies
    {m : Nat} (t : root.Subformula)
    (hsat : PositiveLTL.Satisfies interp (OmegaWord.drop word m) t.1) :
    PosBool.Eval
      (fun x : root.Subformula =>
        PositiveLTL.Satisfies interp (OmegaWord.drop word (m + 1)) x.1)
      ((closureAPA root interp dec).step t (word m)) := by
  rw [closure_satisfies_iff_eval root interp dec t (OmegaWord.drop word m),
    OmegaWord.drop_drop, drop_apply_zero] at hsat
  exact hsat

variable {D : (closureAPA root interp dec).PositionalRunDAG word}

/-- Support members of a frontier state sit in the next frontier. -/
theorem support_mem_frontier
    {n : Nat} {t : root.Subformula} (h : t ∈ D.frontier n)
    {x : root.Subformula}
    (hx : x ∈ ((D.choice n).choice ⟨t, h⟩).support) :
    x ∈ D.frontier (n + 1) := by
  rw [D.frontier_succ n]
  exact AlternatingParityAutomaton.MacroStepSupport.mem_support.mpr
    ⟨⟨t, h⟩, hx⟩

/-- Rooted chains reach every frontier state. -/
theorem exists_rooted_chain :
    ∀ (k : Nat) (x : root.Subformula), x ∈ D.frontier k ->
      ∃ c : Fin (k + 1) -> root.Subformula,
        c ⟨0, by omega⟩ = (closureAPA root interp dec).initial ∧
          (∀ i : Nat, (hi : i < k) ->
            ∃ h : c ⟨i, by omega⟩ ∈ D.frontier i,
              c ⟨i + 1, by omega⟩ ∈
                ((D.choice i).choice ⟨c ⟨i, by omega⟩, h⟩).support) ∧
          c ⟨k, by omega⟩ = x := by
  intro k
  induction k with
  | zero =>
      intro x hx
      have hinit : x = (closureAPA root interp dec).initial := by
        rw [D.initial_mem] at hx
        exact Finset.mem_singleton.mp hx
      exact ⟨fun _ => x, by rw [hinit], fun i hi => absurd hi (by omega),
        rfl⟩
  | succ k ih =>
      intro x hx
      rcases AlternatingParityAutomaton.MiyanoHayashi.frontier_pred D hx with
        ⟨y, hy, hsup⟩
      rcases ih y hy with ⟨c', hc0, hedges, hlast⟩
      have hsnoc_lt : ∀ (i : Nat) (hi : i < k + 1),
          (Fin.snoc c' x : Fin (k + 2) -> root.Subformula) ⟨i, by omega⟩ =
            c' ⟨i, hi⟩ := by
        intro i hi
        have hcast : (⟨i, by omega⟩ : Fin (k + 2)) =
            Fin.castSucc ⟨i, hi⟩ := by
          ext
          rfl
        rw [hcast, Fin.snoc_castSucc]
      have hsnoc_last :
          (Fin.snoc c' x : Fin (k + 2) -> root.Subformula)
            ⟨k + 1, by omega⟩ = x := by
        have hcast : (⟨k + 1, by omega⟩ : Fin (k + 2)) = Fin.last (k + 1) := by
          ext
          rfl
        rw [hcast, Fin.snoc_last]
      refine ⟨Fin.snoc c' x, ?_, ?_, hsnoc_last⟩
      · rw [hsnoc_lt 0 (by omega)]
        exact hc0
      · intro i hi
        rcases Nat.lt_or_ge i k with hik | hik
        · rw [hsnoc_lt i (by omega), hsnoc_lt (i + 1) (by omega)]
          exact hedges i hik
        · have hieq : i = k := by omega
          subst hieq
          rw [hsnoc_lt i (by omega), hsnoc_last, hlast]
          exact ⟨hy, hsup⟩

/-- A state whose self-loop persists forever has even priority. -/
theorem even_priority_of_self_forever
    {n : Nat} {s : root.Subformula}
    (hself : ∀ k : Nat, n ≤ k -> ∃ h : s ∈ D.frontier k,
      s ∈ ((D.choice k).choice ⟨s, h⟩).support) :
    DetParityAutomaton.NatEven
      ((closureAPA root interp dec).priority s) := by
  classical
  have hmem : s ∈ D.frontier n := (hself n (le_refl n)).1
  rcases exists_rooted_chain root interp dec n s hmem with ⟨c, hc0, hedges, hlast⟩
  set t : Nat -> root.Subformula :=
    fun k => if h : k ≤ n then c ⟨k, by omega⟩ else s with ht
  have htn : ∀ k : Nat, n ≤ k -> t k = s := by
    intro k hk
    by_cases hkn : k ≤ n
    · have hkeq : k = n := by omega
      subst hkeq
      simp only [ht, dif_pos hkn]
      exact hlast
    · simp only [ht, dif_neg hkn]
  have ht0 : t 0 = (closureAPA root interp dec).initial := by
    simp only [ht, dif_pos (Nat.zero_le n)]
    exact hc0
  have htedge : ∀ k : Nat,
      ∃ h : t k ∈ D.frontier k,
        t (k + 1) ∈ ((D.choice k).choice ⟨t k, h⟩).support := by
    intro k
    rcases Nat.lt_or_ge k n with hkn | hkn
    · have hk : k ≤ n := by omega
      have hk1 : k + 1 ≤ n := by omega
      have htk : t k = c ⟨k, by omega⟩ := by
        simp only [ht, dif_pos hk]
      have htk1 : t (k + 1) = c ⟨k + 1, by omega⟩ := by
        simp only [ht, dif_pos hk1]
      rw [htk, htk1]
      exact hedges k hkn
    · have hk : t k = s := htn k hkn
      have hk1 : t (k + 1) = s := htn (k + 1) (by omega)
      rw [hk, hk1]
      exact hself k hkn
  have haccept := D.threads_accept t ht0 htedge
  rcases haccept with ⟨p, hpEven, hpSeen, _⟩
  rcases hpSeen n with ⟨k, hk, hkp⟩
  have hkp' : (closureAPA root interp dec).priority (t k) = p := hkp
  rw [htn k hk] at hkp'
  rw [hkp']
  exact hpEven

/-- Every reachable state of an accepting DAG is satisfied at its level. -/
theorem dag_frontier_satisfies :
    ∀ (sz n : Nat) (s : root.Subformula),
      s.1.size ≤ sz -> s ∈ D.frontier n ->
        PositiveLTL.Satisfies interp (OmegaWord.drop word n) s.1 := by
  classical
  intro sz
  induction sz with
  | zero =>
      intro n s hsize _
      have := PositiveLTL.size_pos s.1
      omega
  | succ sz ih =>
      intro n s hsize hmem
      have hstepSat : ∀ (j : Nat) (hj : s ∈ D.frontier j)
          (t : root.Subformula), t.1.size < s.1.size ->
          PosBool.Eval (· ∈ ((D.choice j).choice ⟨s, hj⟩).support)
            ((closureAPA root interp dec).step t (word j)) ->
          PosBool.Eval
            (fun x : root.Subformula =>
              PositiveLTL.Satisfies interp (OmegaWord.drop word (j + 1)) x.1)
            ((closureAPA root interp dec).step t (word j)) := by
        intro j hj t htlt hT
        refine PosBool.eval_mono_of_imp_on_atoms _ ?_ hT
        intro x hxatoms hxS
        have hxsz := step_atoms_size_le root interp dec t (word j) hxatoms
        exact ih (j + 1) x (by omega)
          (support_mem_frontier root interp dec hj hxS)
      have hsupportEval : ∀ (j : Nat) (hj : s ∈ D.frontier j),
          PosBool.Eval
            (fun x : root.Subformula =>
              x ∈ ((D.choice j).choice ⟨s, hj⟩).support)
            ((closureAPA root interp dec).step s (word j)) :=
        fun j hj => ((D.choice j).choice ⟨s, hj⟩).support_satisfies
      have hnontemporal :
          (∀ φ' ψ' : PositiveLTL AP, s.1 ≠ PositiveLTL.until φ' ψ') ->
          (∀ φ' ψ' : PositiveLTL AP, s.1 ≠ PositiveLTL.release φ' ψ') ->
          PositiveLTL.Satisfies interp (OmegaWord.drop word n) s.1 := by
        intro hnotU hnotR
        have hevalS := ((D.choice n).choice ⟨s, hmem⟩).support_satisfies
        have hall : ∀ x, x ∈ ((D.choice n).choice ⟨s, hmem⟩).support ->
            PositiveLTL.Satisfies interp (OmegaWord.drop word (n + 1)) x.1 := by
          intro x hx
          have hlt := step_atoms_size_lt_of_nontemporal root interp dec
            s (word n) hnotU hnotR
            (((D.choice n).choice ⟨s, hmem⟩).support_atoms x hx)
          exact ih (n + 1) x (by omega)
            (support_mem_frontier root interp dec hmem hx)
        exact satisfies_of_eval_next root interp dec s
          (PosBool.eval_mono hall _ hevalS)
      match hshape : s.1 with
      | PositiveLTL.verum =>
          have hres := hnontemporal
            (fun _ _ h => by rw [hshape] at h; simp at h)
            (fun _ _ h => by rw [hshape] at h; simp at h)
          rwa [hshape] at hres
      | PositiveLTL.falsum =>
          have hres := hnontemporal
            (fun _ _ h => by rw [hshape] at h; simp at h)
            (fun _ _ h => by rw [hshape] at h; simp at h)
          rwa [hshape] at hres
      | PositiveLTL.lit l =>
          have hres := hnontemporal
            (fun _ _ h => by rw [hshape] at h; simp at h)
            (fun _ _ h => by rw [hshape] at h; simp at h)
          rwa [hshape] at hres
      | PositiveLTL.conj a b =>
          have hres := hnontemporal
            (fun _ _ h => by rw [hshape] at h; simp at h)
            (fun _ _ h => by rw [hshape] at h; simp at h)
          rwa [hshape] at hres
      | PositiveLTL.disj a b =>
          have hres := hnontemporal
            (fun _ _ h => by rw [hshape] at h; simp at h)
            (fun _ _ h => by rw [hshape] at h; simp at h)
          rwa [hshape] at hres
      | PositiveLTL.next a =>
          have hres := hnontemporal
            (fun _ _ h => by rw [hshape] at h; simp at h)
            (fun _ _ h => by rw [hshape] at h; simp at h)
          rwa [hshape] at hres
      | PositiveLTL.until φ' ψ' =>
          have hφmem : φ' ∈ root.subformulas :=
            left_child_mem_subformulas (Or.inl hshape)
          have hψmem : ψ' ∈ root.subformulas :=
            right_child_mem_subformulas (Or.inl hshape)
          have hφlt : (⟨φ', hφmem⟩ : root.Subformula).1.size < s.1.size := by
            rw [hshape]
            simp [PositiveLTL.size]
          have hψlt : (⟨ψ', hψmem⟩ : root.Subformula).1.size < s.1.size := by
            rw [hshape]
            simp [PositiveLTL.size]
          have hnotforever :
              ¬ ∀ k : Nat, n ≤ k -> ∃ h : s ∈ D.frontier k,
                s ∈ ((D.choice k).choice ⟨s, h⟩).support := by
            intro hforever
            have heven :=
              even_priority_of_self_forever root interp dec hforever
            have heven' :
                DetParityAutomaton.NatEven
                  (PositiveLTL.alternatingPriority root s.1) := heven
            rw [hshape] at heven'
            exact alternatingPriority_until_not_even root φ' ψ' heven'
          push Not at hnotforever
          rcases hnotforever with ⟨k₀, hk₀n, hk₀⟩
          have hPex : ∃ j : Nat, n ≤ j ∧
              ¬ ∃ h : s ∈ D.frontier j,
                s ∈ ((D.choice j).choice ⟨s, h⟩).support :=
            ⟨k₀, hk₀n, not_exists.mpr hk₀⟩
          have hPm := Nat.find_spec hPex
          have hchain : ∀ j : Nat, n ≤ j -> j < Nat.find hPex ->
              ∃ h : s ∈ D.frontier j,
                s ∈ ((D.choice j).choice ⟨s, h⟩).support := by
            intro j hnj hjm
            by_contra hno
            exact Nat.find_min hPex hjm ⟨hnj, hno⟩
          have hnm : n ≤ Nat.find hPex := hPm.1
          have hmemChainAux : ∀ i : Nat, n + i ≤ Nat.find hPex ->
              s ∈ D.frontier (n + i) := by
            intro i
            induction i with
            | zero =>
                intro _
                simpa using hmem
            | succ i ihm =>
                intro hle
                rcases hchain (n + i) (by omega) (by omega) with ⟨h, hsup⟩
                have hnext := support_mem_frontier root interp dec h hsup
                have harith : n + i + 1 = n + (i + 1) := by omega
                rw [harith] at hnext
                exact hnext
          have hmemM : s ∈ D.frontier (Nat.find hPex) := by
            have := hmemChainAux (Nat.find hPex - n) (by omega)
            rwa [show n + (Nat.find hPex - n) = Nat.find hPex by omega] at this
          have hnoselfM :
              s ∉ ((D.choice (Nat.find hPex)).choice ⟨s, hmemM⟩).support := by
            intro hin
            exact hPm.2 ⟨hmemM, hin⟩
          have hdown : ∀ i : Nat, n ≤ Nat.find hPex - i ->
              PositiveLTL.Satisfies interp
                (OmegaWord.drop word (Nat.find hPex - i)) s.1 := by
            intro i
            induction i with
            | zero =>
                intro _
                simp only [Nat.sub_zero]
                have hevalS := hsupportEval (Nat.find hPex) hmemM
                rw [eval_step_until_iff root interp dec s hshape hφmem hψmem]
                  at hevalS
                rcases hevalS with hT1 | ⟨_, hselfS⟩
                · have hT1sat := hstepSat (Nat.find hPex) hmemM
                    ⟨ψ', hψmem⟩ hψlt hT1
                  refine satisfies_of_eval_next root interp dec s ?_
                  rw [eval_step_until_iff root interp dec s hshape hφmem hψmem]
                  exact Or.inl hT1sat
                · exact absurd hselfS hnoselfM
            | succ i ihdown =>
                intro hle
                by_cases hcase : Nat.find hPex - (i + 1) = Nat.find hPex - i
                · rw [hcase]
                  exact ihdown (by omega)
                · have hji : Nat.find hPex - (i + 1) + 1 = Nat.find hPex - i := by
                    omega
                  rcases hchain (Nat.find hPex - (i + 1)) hle (by omega) with
                    ⟨hmemJ, _⟩
                  have hnext : PositiveLTL.Satisfies interp
                      (OmegaWord.drop word (Nat.find hPex - (i + 1) + 1)) s.1 := by
                    rw [hji]
                    exact ihdown (by omega)
                  have hevalS := hsupportEval (Nat.find hPex - (i + 1)) hmemJ
                  rw [eval_step_until_iff root interp dec s hshape hφmem hψmem]
                    at hevalS
                  rcases hevalS with hT1 | ⟨hT2, _⟩
                  · have hT1sat := hstepSat (Nat.find hPex - (i + 1)) hmemJ
                      ⟨ψ', hψmem⟩ hψlt hT1
                    refine satisfies_of_eval_next root interp dec s ?_
                    rw [eval_step_until_iff root interp dec s hshape hφmem hψmem]
                    exact Or.inl hT1sat
                  · have hT2sat := hstepSat (Nat.find hPex - (i + 1)) hmemJ
                      ⟨φ', hφmem⟩ hφlt hT2
                    refine satisfies_of_eval_next root interp dec s ?_
                    rw [eval_step_until_iff root interp dec s hshape hφmem hψmem]
                    exact Or.inr ⟨hT2sat, hnext⟩
          have hfin := hdown (Nat.find hPex - n) (by omega)
          rw [show Nat.find hPex - (Nat.find hPex - n) = n by omega, hshape]
            at hfin
          exact hfin
      | PositiveLTL.release φ' ψ' =>
          have hφmem : φ' ∈ root.subformulas :=
            left_child_mem_subformulas (Or.inr hshape)
          have hψmem : ψ' ∈ root.subformulas :=
            right_child_mem_subformulas (Or.inr hshape)
          have hφlt : (⟨φ', hφmem⟩ : root.Subformula).1.size < s.1.size := by
            rw [hshape]
            simp [PositiveLTL.size]
          have hψlt : (⟨ψ', hψmem⟩ : root.Subformula).1.size < s.1.size := by
            rw [hshape]
            simp [PositiveLTL.size]
          by_cases hforever : ∀ k : Nat, n ≤ k ->
              ∃ h : s ∈ D.frontier k,
                s ∈ ((D.choice k).choice ⟨s, h⟩).support
          · have hψall : ∀ k : Nat, n ≤ k ->
                PositiveLTL.Satisfies interp (OmegaWord.drop word k) ψ' := by
              intro k hk
              rcases hforever k hk with ⟨hmemK, _⟩
              have hevalS := hsupportEval k hmemK
              rw [eval_step_release_iff root interp dec s hshape hφmem hψmem]
                at hevalS
              have hT1sat := hstepSat k hmemK ⟨ψ', hψmem⟩ hψlt hevalS.1
              exact satisfies_of_eval_next root interp dec ⟨ψ', hψmem⟩ hT1sat
            intro n'
            left
            rw [OmegaWord.drop_drop]
            exact hψall (n + n') (by omega)
          · push Not at hforever
            rcases hforever with ⟨k₀, hk₀n, hk₀⟩
            have hPex : ∃ j : Nat, n ≤ j ∧
                ¬ ∃ h : s ∈ D.frontier j,
                  s ∈ ((D.choice j).choice ⟨s, h⟩).support :=
              ⟨k₀, hk₀n, not_exists.mpr hk₀⟩
            have hPm := Nat.find_spec hPex
            have hchain : ∀ j : Nat, n ≤ j -> j < Nat.find hPex ->
                ∃ h : s ∈ D.frontier j,
                  s ∈ ((D.choice j).choice ⟨s, h⟩).support := by
              intro j hnj hjm
              by_contra hno
              exact Nat.find_min hPex hjm ⟨hnj, hno⟩
            have hnm : n ≤ Nat.find hPex := hPm.1
            have hmemChainAux : ∀ i : Nat, n + i ≤ Nat.find hPex ->
                s ∈ D.frontier (n + i) := by
              intro i
              induction i with
              | zero =>
                  intro _
                  simpa using hmem
              | succ i ihm =>
                  intro hle
                  rcases hchain (n + i) (by omega) (by omega) with ⟨h, hsup⟩
                  have hnext := support_mem_frontier root interp dec h hsup
                  have harith : n + i + 1 = n + (i + 1) := by omega
                  rw [harith] at hnext
                  exact hnext
            have hmemM : s ∈ D.frontier (Nat.find hPex) := by
              have := hmemChainAux (Nat.find hPex - n) (by omega)
              rwa [show n + (Nat.find hPex - n) = Nat.find hPex by omega] at this
            have hnoselfM :
                s ∉ ((D.choice (Nat.find hPex)).choice ⟨s, hmemM⟩).support := by
              intro hin
              exact hPm.2 ⟨hmemM, hin⟩
            have hdown : ∀ i : Nat, n ≤ Nat.find hPex - i ->
                PositiveLTL.Satisfies interp
                  (OmegaWord.drop word (Nat.find hPex - i)) s.1 := by
              intro i
              induction i with
              | zero =>
                  intro _
                  simp only [Nat.sub_zero]
                  have hevalS := hsupportEval (Nat.find hPex) hmemM
                  rw [eval_step_release_iff root interp dec s hshape hφmem hψmem]
                    at hevalS
                  rcases hevalS with ⟨hT1, hT2 | hselfS⟩
                  · have hT1sat := hstepSat (Nat.find hPex) hmemM
                      ⟨ψ', hψmem⟩ hψlt hT1
                    have hT2sat := hstepSat (Nat.find hPex) hmemM
                      ⟨φ', hφmem⟩ hφlt hT2
                    refine satisfies_of_eval_next root interp dec s ?_
                    rw [eval_step_release_iff root interp dec s hshape hφmem hψmem]
                    exact ⟨hT1sat, Or.inl hT2sat⟩
                  · exact absurd hselfS hnoselfM
              | succ i ihdown =>
                  intro hle
                  by_cases hcase : Nat.find hPex - (i + 1) = Nat.find hPex - i
                  · rw [hcase]
                    exact ihdown (by omega)
                  · have hji : Nat.find hPex - (i + 1) + 1 = Nat.find hPex - i := by
                      omega
                    rcases hchain (Nat.find hPex - (i + 1)) hle (by omega) with
                      ⟨hmemJ, _⟩
                    have hnext : PositiveLTL.Satisfies interp
                        (OmegaWord.drop word (Nat.find hPex - (i + 1) + 1)) s.1 := by
                      rw [hji]
                      exact ihdown (by omega)
                    have hevalS := hsupportEval (Nat.find hPex - (i + 1)) hmemJ
                    rw [eval_step_release_iff root interp dec s hshape hφmem hψmem]
                      at hevalS
                    have hT1sat := hstepSat (Nat.find hPex - (i + 1)) hmemJ
                      ⟨ψ', hψmem⟩ hψlt hevalS.1
                    refine satisfies_of_eval_next root interp dec s ?_
                    rw [eval_step_release_iff root interp dec s hshape hφmem hψmem]
                    exact ⟨hT1sat, Or.inr hnext⟩
            have hfin := hdown (Nat.find hPex - n) (by omega)
            rw [show Nat.find hPex - (Nat.find hPex - n) = n by omega, hshape]
              at hfin
            exact hfin

/-- Acceptance of the closure automaton implies satisfaction. -/
theorem subformulaClosure_satisfies_of_accepts
    (haccepts : (closureAPA root interp dec).Accepts word) :
    PositiveLTL.Satisfies interp word root := by
  rcases AlternatingParityAutomaton.exists_positionalRunDAG_of_accepts
      haccepts with ⟨D⟩
  have hmem : PositiveLTL.rootSubformula root ∈ D.frontier 0 := by
    rw [D.initial_mem]
    exact Finset.mem_singleton_self _
  have hsat := dag_frontier_satisfies root interp dec (D := D)
    root.size 0 (PositiveLTL.rootSubformula root) (le_refl _) hmem
  rw [OmegaWord.drop_zero] at hsat
  exact hsat

end AcceptsToSatisfies

/-- The LTL/APA semantic bridge. -/
theorem subformulaClosure_accepts_iff_satisfies
    (word : OmegaWord Letter) :
    (closureAPA root interp dec).Accepts word ↔
      PositiveLTL.Satisfies interp word root := by
  constructor
  · exact subformulaClosure_satisfies_of_accepts root interp dec
  · exact subformulaClosure_accepts_of_satisfies root interp dec

/--
The unconditional LTL-to-DPA compilation: weak alternation removal of the
subformula-closure automaton, corrected through the semantic bridge.
-/
noncomputable def subformulaClosureDPACompilation :
    { dpa : DetParityAutomaton.{v, u} Letter //
      ∀ word : OmegaWord Letter,
        dpa.Accepts word ↔ PositiveLTL.Satisfies interp word root } := by
  classical
  refine ⟨(AlternatingParityAutomaton.weakAPAToDPACompilation
    (A := closureAPA root interp dec)
    (fun state => state.1.size)
    (subformulaClosure_selfOrDecreasing root interp dec)).dpa, ?_⟩
  intro word
  exact ((AlternatingParityAutomaton.weakAPAToDPACompilation
    (A := closureAPA root interp dec)
    (fun state => state.1.size)
    (subformulaClosure_selfOrDecreasing root interp dec)).correct word).trans
    (subformulaClosure_accepts_iff_satisfies root interp dec word)

end Bridge

/--
The canonical unconditional LTL-to-DPA compiler: subformula-closure APA,
weak alternation removal, Miyano-Hayashi, Piterman, and the semantic
bridge.  This discharges the compiler hypothesis of
`main_result_for_ltl_dpa_finite_game_compiler` with no remaining automata
obligations.
-/
noncomputable def canonicalLTLToDPACompiler
    (interp : AP -> Letter -> Prop)
    (dec : ∀ ap letter, Decidable (interp ap letter)) :
    LTLToDPACompiler.{u, v, u} AP Letter where
  interp := interp
  compile := fun φ =>
    (subformulaClosureDPACompilation (PositiveLTL.ofLTL φ) interp dec).1
  correct := fun φ word =>
    ((subformulaClosureDPACompilation
      (PositiveLTL.ofLTL φ) interp dec).2 word).trans
      (PositiveLTL.satisfies_ofLTL interp word φ)

end PositiveLTL

end DistributedSynthesis
