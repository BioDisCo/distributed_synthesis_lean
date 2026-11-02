/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Basic

/-!
# Positive Boolean formulas

Positive Boolean formulas are used as alternating-automaton transition
conditions: atoms name successor states, conjunction means universal branching,
and disjunction means existential branching.
-/

namespace DistributedSynthesis

universe u v

/-- Positive Boolean formulas over atoms of type `Atom`. -/
inductive PosBool (Atom : Type u) : Type u where
  | verum : PosBool Atom
  | falsum : PosBool Atom
  | atom : Atom -> PosBool Atom
  | conj : PosBool Atom -> PosBool Atom -> PosBool Atom
  | disj : PosBool Atom -> PosBool Atom -> PosBool Atom
deriving Repr, DecidableEq

namespace PosBool

/-- Evaluation of a positive Boolean formula under an atom valuation. -/
def Eval {Atom : Type u} (valuation : Atom -> Prop) : PosBool Atom -> Prop
  | verum => True
  | falsum => False
  | atom a => valuation a
  | conj φ ψ => Eval valuation φ ∧ Eval valuation ψ
  | disj φ ψ => Eval valuation φ ∨ Eval valuation ψ

/-- Atoms occurring in a positive Boolean formula, with duplicates permitted. -/
def atoms {Atom : Type u} : PosBool Atom -> List Atom
  | verum => []
  | falsum => []
  | atom a => [a]
  | conj φ ψ => atoms φ ++ atoms ψ
  | disj φ ψ => atoms φ ++ atoms ψ

/-- Rename atoms in a positive Boolean formula. -/
def map {Atom : Type u} {Atom' : Type v} (f : Atom -> Atom') :
    PosBool Atom -> PosBool Atom'
  | verum => verum
  | falsum => falsum
  | atom a => atom (f a)
  | conj φ ψ => conj (map f φ) (map f ψ)
  | disj φ ψ => disj (map f φ) (map f ψ)

/-- Evaluation commutes with renaming atoms. -/
theorem eval_map {Atom : Type u} {Atom' : Type v}
    (valuation : Atom' -> Prop)
    (f : Atom -> Atom')
    (φ : PosBool Atom) :
    Eval valuation (map f φ) ↔ Eval (fun atom => valuation (f atom)) φ := by
  induction φ with
  | verum => simp [map, Eval]
  | falsum => simp [map, Eval]
  | atom atom => simp [map, Eval]
  | conj φ ψ ihφ ihψ => simp [map, Eval, ihφ, ihψ]
  | disj φ ψ ihφ ihψ => simp [map, Eval, ihφ, ihψ]

/--
Dependent atom renaming, where the target atom may use a proof that the source
atom actually occurs in the formula being renamed.
-/
def pmap {Atom : Type u} {Atom' : Type v}
    (φ : PosBool Atom)
    (f : ∀ atom, atom ∈ φ.atoms -> Atom') :
    PosBool Atom' :=
  match φ with
  | verum => verum
  | falsum => falsum
  | .atom a => .atom (f a (by simp [atoms]))
  | conj φ ψ =>
      conj
        (pmap φ (fun atom h => f atom (by simp [atoms, h])))
        (pmap ψ (fun atom h => f atom (by simp [atoms, h])))
  | disj φ ψ =>
      disj
        (pmap φ (fun atom h => f atom (by simp [atoms, h])))
        (pmap ψ (fun atom h => f atom (by simp [atoms, h])))

/-- Every source atom of a dependent renaming occurs as its image. -/
theorem mem_atoms_pmap_of_mem_atoms {Atom : Type u} {Atom' : Type v}
    (φ : PosBool Atom)
    (f : ∀ atom, atom ∈ φ.atoms -> Atom')
    {atom : Atom}
    (hmem : atom ∈ φ.atoms) :
    f atom hmem ∈ (φ.pmap f).atoms := by
  induction φ with
  | verum =>
      simp [atoms] at hmem
  | falsum =>
      simp [atoms] at hmem
  | atom source =>
      simp [pmap, atoms] at hmem ⊢
      subst atom
      rfl
  | conj φ ψ ihφ ihψ =>
      simp [atoms] at hmem
      rcases hmem with hmem | hmem
      · simp [pmap, atoms]
        left
        exact ihφ (fun atom h => f atom (by simp [atoms, h])) hmem
      · simp [pmap, atoms]
        right
        exact ihψ (fun atom h => f atom (by simp [atoms, h])) hmem
  | disj φ ψ ihφ ihψ =>
      simp [atoms] at hmem
      rcases hmem with hmem | hmem
      · simp [pmap, atoms]
        left
        exact ihφ (fun atom h => f atom (by simp [atoms, h])) hmem
      · simp [pmap, atoms]
        right
        exact ihψ (fun atom h => f atom (by simp [atoms, h])) hmem

/-- Every atom of a dependent renaming is the image of a source atom. -/
theorem mem_atoms_pmap {Atom : Type u} {Atom' : Type v}
    (φ : PosBool Atom)
    (f : ∀ atom, atom ∈ φ.atoms -> Atom')
    {atom' : Atom'}
    (hmem : atom' ∈ (φ.pmap f).atoms) :
    ∃ atom, ∃ h : atom ∈ φ.atoms, atom' = f atom h := by
  induction φ with
  | verum =>
      simp [pmap, atoms] at hmem
  | falsum =>
      simp [pmap, atoms] at hmem
  | atom atom =>
      simp [pmap, atoms] at hmem
      subst atom'
      exact ⟨atom, by simp [atoms], rfl⟩
  | conj φ ψ ihφ ihψ =>
      simp [pmap, atoms] at hmem
      rcases hmem with hmem | hmem
      · rcases ihφ (fun atom h => f atom (by simp [atoms, h])) hmem with
          ⟨atom, hatom, rfl⟩
        exact ⟨atom, by simp [atoms, hatom], rfl⟩
      · rcases ihψ (fun atom h => f atom (by simp [atoms, h])) hmem with
          ⟨atom, hatom, rfl⟩
        exact ⟨atom, by simp [atoms, hatom], rfl⟩
  | disj φ ψ ihφ ihψ =>
      simp [pmap, atoms] at hmem
      rcases hmem with hmem | hmem
      · rcases ihφ (fun atom h => f atom (by simp [atoms, h])) hmem with
          ⟨atom, hatom, rfl⟩
        exact ⟨atom, by simp [atoms, hatom], rfl⟩
      · rcases ihψ (fun atom h => f atom (by simp [atoms, h])) hmem with
          ⟨atom, hatom, rfl⟩
        exact ⟨atom, by simp [atoms, hatom], rfl⟩

/--
Dependent atom renaming preserves evaluation under a one-way implication from
the source valuation to the target valuation.
-/
theorem eval_pmap_of_imp {Atom : Type u} {Atom' : Type v}
    (φ : PosBool Atom)
    (f : ∀ atom, atom ∈ φ.atoms -> Atom')
    {valuation : Atom -> Prop}
    {valuation' : Atom' -> Prop}
    (himp :
      ∀ atom, ∀ hmem : atom ∈ φ.atoms,
        valuation atom -> valuation' (f atom hmem)) :
    Eval valuation φ -> Eval valuation' (φ.pmap f) := by
  induction φ with
  | verum =>
      intro _
      simp [pmap, Eval]
  | falsum =>
      intro hfalse
      exact False.elim hfalse
  | atom atom =>
      intro hatom
      simp [pmap, Eval]
      exact himp atom (by simp [atoms]) hatom
  | conj φ ψ ihφ ihψ =>
      intro hconj
      simp [pmap, Eval]
      constructor
      · exact
          ihφ
            (fun atom hmem => f atom (by simp [atoms, hmem]))
            (fun atom hmem hval =>
              himp atom (by simp [atoms, hmem]) hval)
            hconj.1
      · exact
          ihψ
            (fun atom hmem => f atom (by simp [atoms, hmem]))
            (fun atom hmem hval =>
              himp atom (by simp [atoms, hmem]) hval)
            hconj.2
  | disj φ ψ ihφ ihψ =>
      intro hdisj
      simp [pmap, Eval]
      rcases hdisj with hφ | hψ
      · exact
          Or.inl
            (ihφ
              (fun atom hmem => f atom (by simp [atoms, hmem]))
              (fun atom hmem hval =>
                himp atom (by simp [atoms, hmem]) hval)
              hφ)
      · exact
          Or.inr
            (ihψ
              (fun atom hmem => f atom (by simp [atoms, hmem]))
              (fun atom hmem hval =>
                himp atom (by simp [atoms, hmem]) hval)
              hψ)

/--
Dependent atom renaming reflects evaluation under a one-way implication from
the target valuation back to the source valuation.
-/
theorem eval_of_pmap_imp {Atom : Type u} {Atom' : Type v}
    (φ : PosBool Atom)
    (f : ∀ atom, atom ∈ φ.atoms -> Atom')
    {valuation : Atom -> Prop}
    {valuation' : Atom' -> Prop}
    (himp :
      ∀ atom, ∀ hmem : atom ∈ φ.atoms,
        valuation' (f atom hmem) -> valuation atom) :
    Eval valuation' (φ.pmap f) -> Eval valuation φ := by
  induction φ with
  | verum =>
      intro _
      trivial
  | falsum =>
      intro hfalse
      exact False.elim hfalse
  | atom atom =>
      intro hatom
      exact himp atom (by simp [atoms]) (by simpa [pmap, Eval] using hatom)
  | conj φ ψ ihφ ihψ =>
      intro hconj
      constructor
      · exact
          ihφ
            (fun atom hmem => f atom (by simp [atoms, hmem]))
            (fun atom hmem hval =>
              himp atom (by simp [atoms, hmem]) hval)
            (by simpa [pmap, Eval] using hconj.1)
      · exact
          ihψ
            (fun atom hmem => f atom (by simp [atoms, hmem]))
            (fun atom hmem hval =>
              himp atom (by simp [atoms, hmem]) hval)
            (by simpa [pmap, Eval] using hconj.2)
  | disj φ ψ ihφ ihψ =>
      intro hdisj
      rcases (by simpa [pmap, Eval] using hdisj) with hφ | hψ
      · exact
          Or.inl
            (ihφ
              (fun atom hmem => f atom (by simp [atoms, hmem]))
              (fun atom hmem hval =>
                himp atom (by simp [atoms, hmem]) hval)
              hφ)
      · exact
          Or.inr
            (ihψ
              (fun atom hmem => f atom (by simp [atoms, hmem]))
              (fun atom hmem hval =>
                himp atom (by simp [atoms, hmem]) hval)
              hψ)

/-- Monotonicity of positive Boolean formulas. -/
theorem eval_mono {Atom : Type u}
    {valuation₁ valuation₂ : Atom -> Prop}
    (h : ∀ atom, valuation₁ atom -> valuation₂ atom)
    (φ : PosBool Atom) :
    Eval valuation₁ φ -> Eval valuation₂ φ := by
  induction φ with
  | verum => intro _; trivial
  | falsum => intro hfalse; exact False.elim hfalse
  | atom atom => exact h atom
  | conj φ ψ ihφ ihψ =>
      intro hconj
      exact ⟨ihφ hconj.1, ihψ hconj.2⟩
  | disj φ ψ ihφ ihψ =>
      intro hdisj
      rcases hdisj with hφ | hψ
      · exact Or.inl (ihφ hφ)
      · exact Or.inr (ihψ hψ)

/--
Monotonicity of positive Boolean formulas, with the implication required only
for atoms that syntactically occur in the formula.
-/
theorem eval_mono_of_imp_on_atoms {Atom : Type u}
    {valuation₁ valuation₂ : Atom -> Prop}
    (φ : PosBool Atom)
    (h : ∀ atom, atom ∈ φ.atoms -> valuation₁ atom -> valuation₂ atom) :
    Eval valuation₁ φ -> Eval valuation₂ φ := by
  induction φ with
  | verum =>
      intro _
      trivial
  | falsum =>
      intro hfalse
      exact False.elim hfalse
  | atom atom =>
      intro hatom
      exact h atom (by simp [atoms]) hatom
  | conj φ ψ ihφ ihψ =>
      intro hconj
      constructor
      · exact
          ihφ
            (fun atom hmem hval =>
              h atom (by simp [atoms, hmem]) hval)
            hconj.1
      · exact
          ihψ
            (fun atom hmem hval =>
              h atom (by simp [atoms, hmem]) hval)
            hconj.2
  | disj φ ψ ihφ ihψ =>
      intro hdisj
      rcases hdisj with hφ | hψ
      · exact
          Or.inl
            (ihφ
              (fun atom hmem hval =>
                h atom (by simp [atoms, hmem]) hval)
              hφ)
      · exact
          Or.inr
            (ihψ
              (fun atom hmem hval =>
                h atom (by simp [atoms, hmem]) hval)
              hψ)

/-- Positive-Boolean evaluation respects pointwise equivalent valuations. -/
theorem eval_congr {Atom : Type u}
    {valuation₁ valuation₂ : Atom -> Prop}
    (h : ∀ atom, valuation₁ atom ↔ valuation₂ atom)
    (φ : PosBool Atom) :
    Eval valuation₁ φ ↔ Eval valuation₂ φ := by
  induction φ with
  | verum => simp [Eval]
  | falsum => simp [Eval]
  | atom atom => exact h atom
  | conj φ ψ ihφ ihψ => simp [Eval, ihφ, ihψ]
  | disj φ ψ ihφ ihψ => simp [Eval, ihφ, ihψ]

theorem mem_iff_exists_getElem? {Atom : Type u}
    (support : List Atom)
    (atom : Atom) :
    atom ∈ support ↔ ∃ child : Nat, support[child]? = some atom := by
  induction support generalizing atom with
  | nil =>
      simp
  | cons head tail ih =>
      constructor
      · intro hmem
        rw [List.mem_cons] at hmem
        rcases hmem with hmem | hmem
        · subst atom
          exact ⟨0, rfl⟩
        · rcases (ih atom).mp hmem with ⟨child, hchild⟩
          exact ⟨child + 1, by simpa using hchild⟩
      · intro h
        rcases h with ⟨child, hchild⟩
        cases child with
        | zero =>
            simp at hchild
            subst atom
            simp
        | succ child =>
            rw [List.mem_cons]
            right
            exact (ih atom).mpr ⟨child, by simpa using hchild⟩

/-- A list-support valuation can be read as the existence of a numbered child. -/
theorem eval_support_iff_exists_getElem? {Atom : Type u}
    (support : List Atom)
    (φ : PosBool Atom) :
    Eval (fun atom => atom ∈ support) φ ↔
      Eval (fun atom => ∃ child : Nat, support[child]? = some atom) φ :=
  eval_congr (fun atom => mem_iff_exists_getElem? support atom) φ

/--
Finite support form of positive-Boolean evaluation.

If a positive Boolean transition is true under an arbitrary valuation, then it
is already true using only finitely many atoms, all of which satisfy that
valuation.  This is the constructive witness needed when turning symbolic APA
transitions into finitely many run-tree children.
-/
theorem eval_iff_exists_support {Atom : Type u}
    (valuation : Atom -> Prop)
    (φ : PosBool Atom) :
    Eval valuation φ ↔
      ∃ support : List Atom,
        (∀ atom, atom ∈ support -> valuation atom) ∧
          Eval (fun atom => atom ∈ support) φ := by
  induction φ with
  | verum =>
      constructor
      · intro _
        exact ⟨[], by simp [Eval]⟩
      · intro _
        trivial
  | falsum =>
      constructor
      · intro h
        exact False.elim h
      · intro h
        rcases h with ⟨support, _, hfalse⟩
        exact False.elim hfalse
  | atom atom =>
      constructor
      · intro h
        refine ⟨[atom], ?_, ?_⟩
        · intro atom' hmem
          simp at hmem
          subst atom'
          exact h
        · simp [Eval]
      · intro h
        rcases h with ⟨support, hsupport, hmem⟩
        exact hsupport atom hmem
  | conj φ ψ ihφ ihψ =>
      constructor
      · intro h
        rcases h with ⟨hφ, hψ⟩
        rcases ihφ.mp hφ with ⟨supportφ, hsupportφ, hevalφ⟩
        rcases ihψ.mp hψ with ⟨supportψ, hsupportψ, hevalψ⟩
        refine ⟨supportφ ++ supportψ, ?_, ?_⟩
        · intro atom hmem
          rw [List.mem_append] at hmem
          rcases hmem with hmem | hmem
          · exact hsupportφ atom hmem
          · exact hsupportψ atom hmem
        · exact
            ⟨eval_mono
                (fun atom hmem => by
                  rw [List.mem_append]
                  exact Or.inl hmem)
                φ hevalφ,
              eval_mono
                (fun atom hmem => by
                  rw [List.mem_append]
                  exact Or.inr hmem)
                ψ hevalψ⟩
      · intro h
        rcases h with ⟨support, hsupport, heval⟩
        exact
          ⟨eval_mono hsupport φ heval.1,
            eval_mono hsupport ψ heval.2⟩
  | disj φ ψ ihφ ihψ =>
      constructor
      · intro h
        rcases h with hφ | hψ
        · rcases ihφ.mp hφ with ⟨support, hsupport, heval⟩
          exact ⟨support, hsupport, Or.inl heval⟩
        · rcases ihψ.mp hψ with ⟨support, hsupport, heval⟩
          exact ⟨support, hsupport, Or.inr heval⟩
      · intro h
        rcases h with ⟨support, hsupport, heval⟩
        rcases heval with heval | heval
        · exact Or.inl (eval_mono hsupport φ heval)
        · exact Or.inr (eval_mono hsupport ψ heval)

/--
Finite support form with no irrelevant atoms.

The witness list contains only atoms occurring in the positive Boolean formula.
For disjunctions this preserves the proof branch that made the formula true,
which is essential when extracting controlled alternating-run children.
-/
theorem eval_iff_exists_support_subset_atoms {Atom : Type u}
    (valuation : Atom -> Prop)
    (φ : PosBool Atom) :
    Eval valuation φ ↔
      ∃ support : List Atom,
        (∀ atom, atom ∈ support -> valuation atom) ∧
          (∀ atom, atom ∈ support -> atom ∈ φ.atoms) ∧
            Eval (fun atom => atom ∈ support) φ := by
  induction φ with
  | verum =>
      constructor
      · intro _
        exact ⟨[], by simp [Eval, atoms]⟩
      · intro _
        trivial
  | falsum =>
      constructor
      · intro h
        exact False.elim h
      · intro h
        rcases h with ⟨support, _, _, hfalse⟩
        exact False.elim hfalse
  | atom atom =>
      constructor
      · intro h
        refine ⟨[atom], ?_, ?_, ?_⟩
        · intro atom' hmem
          simp at hmem
          subst atom'
          exact h
        · intro atom' hmem
          simpa [atoms] using hmem
        · simp [Eval]
      · intro h
        rcases h with ⟨support, hsupport, _, hmem⟩
        exact hsupport atom hmem
  | conj φ ψ ihφ ihψ =>
      constructor
      · intro h
        rcases h with ⟨hφ, hψ⟩
        rcases ihφ.mp hφ with ⟨supportφ, hsupportφ, hatomsφ, hevalφ⟩
        rcases ihψ.mp hψ with ⟨supportψ, hsupportψ, hatomsψ, hevalψ⟩
        refine ⟨supportφ ++ supportψ, ?_, ?_, ?_⟩
        · intro atom hmem
          rw [List.mem_append] at hmem
          rcases hmem with hmem | hmem
          · exact hsupportφ atom hmem
          · exact hsupportψ atom hmem
        · intro atom hmem
          rw [List.mem_append] at hmem
          rw [atoms, List.mem_append]
          rcases hmem with hmem | hmem
          · exact Or.inl (hatomsφ atom hmem)
          · exact Or.inr (hatomsψ atom hmem)
        · exact
            ⟨eval_mono
                (fun atom hmem => by
                  rw [List.mem_append]
                  exact Or.inl hmem)
                φ hevalφ,
              eval_mono
                (fun atom hmem => by
                  rw [List.mem_append]
                  exact Or.inr hmem)
                ψ hevalψ⟩
      · intro h
        rcases h with ⟨support, hsupport, _, heval⟩
        exact
          ⟨eval_mono hsupport φ heval.1,
            eval_mono hsupport ψ heval.2⟩
  | disj φ ψ ihφ ihψ =>
      constructor
      · intro h
        rcases h with hφ | hψ
        · rcases ihφ.mp hφ with ⟨support, hsupport, hatoms, heval⟩
          refine ⟨support, hsupport, ?_, Or.inl heval⟩
          intro atom hmem
          rw [atoms, List.mem_append]
          exact Or.inl (hatoms atom hmem)
        · rcases ihψ.mp hψ with ⟨support, hsupport, hatoms, heval⟩
          refine ⟨support, hsupport, ?_, Or.inr heval⟩
          intro atom hmem
          rw [atoms, List.mem_append]
          exact Or.inr (hatoms atom hmem)
      · intro h
        rcases h with ⟨support, hsupport, _, heval⟩
        rcases heval with heval | heval
        · exact Or.inl (eval_mono hsupport φ heval)
        · exact Or.inr (eval_mono hsupport ψ heval)

end PosBool

end DistributedSynthesis
