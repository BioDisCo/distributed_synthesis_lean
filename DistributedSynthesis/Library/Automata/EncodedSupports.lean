/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Logic.EncodedPositiveBoolean
import DistributedSynthesis.Library.Computability.FiniteSearch

/-! # Primitive-recursive exact support enumeration

Supports satisfy a positive Boolean transition and contain only its syntactic
atoms. Candidate lists are sublists of the decoded atom list. Duplicates in
the syntax or in a candidate do not change the represented finite support.
Both directions of the finite-set correspondence are proved.
-/

namespace DistributedSynthesis.EncodedSupports
open EncodedFiniteLTL
variable {A : Type*} [DecidableEq A]

def evalAlgebra (selected : List A) : PostfixFold.Algebra A Bool where
  truth := true
  falsity := false
  atom := fun a => decide (a ∈ selected)
  conj := Bool.and
  disj := Bool.or
  neg := fun _ => false
  next := fun _ => false
  «until» := fun _ _ => false
  «release» := fun _ _ => false

def eval (code : Code A) (selected : List A) : Bool :=
  PostfixFold.run (evalAlgebra selected) code

def atomsAlgebra : PostfixFold.Algebra A (List A) where
  truth := []
  falsity := []
  atom := fun a => [a]
  conj := List.append
  disj := List.append
  neg := fun _ => []
  next := fun _ => []
  «until» := fun _ _ => []
  «release» := fun _ _ => []

def atoms (code : Code A) : List A := PostfixFold.run atomsAlgebra code

theorem eval_correct (code : Code A) (selected : List A) :
    eval code selected = true ↔
      PosBool.Eval (fun a => a ∈ selected) (EncodedPositiveBoolean.decode code) := by
  unfold eval EncodedPositiveBoolean.decode
  rw [PostfixFold.run_correct, PostfixFold.run_correct]
  induction EncodedFiniteLTL.decode code <;>
    simp_all [PostfixFold.formula, evalAlgebra, EncodedPositiveBoolean.algebra, PosBool.Eval]

omit [DecidableEq A] in
theorem atoms_correct (code : Code A) :
    atoms code = (EncodedPositiveBoolean.decode code).atoms := by
  unfold atoms EncodedPositiveBoolean.decode
  rw [PostfixFold.run_correct, PostfixFold.run_correct]
  induction EncodedFiniteLTL.decode code <;>
    simp_all [PostfixFold.formula, atomsAlgebra, EncodedPositiveBoolean.algebra, PosBool.atoms]

def enumerate (code : Code A) : List (List A) :=
  (atoms code).sublists'.filter (eval code)

def Valid (p : PosBool A) (selected : Finset A) : Prop :=
  PosBool.Eval (fun a => a ∈ selected) p ∧ ∀ a ∈ selected, a ∈ p.atoms

theorem enumerate_valid (code : Code A) (xs : List A) (h : xs ∈ enumerate code) :
    Valid (EncodedPositiveBoolean.decode code) xs.toFinset := by
  simp only [enumerate, List.mem_filter, List.mem_sublists', eval_correct] at h
  refine ⟨(PosBool.eval_congr (fun _ => List.mem_toFinset) _).mpr h.2, ?_⟩
  intro a ha
  rw [← atoms_correct]
  exact h.1.subset (List.mem_toFinset.mp ha)

theorem enumerate_complete (code : Code A) (selected : Finset A)
    (h : Valid (EncodedPositiveBoolean.decode code) selected) :
    ∃ xs ∈ enumerate code, xs.toFinset = selected := by
  let xs := (atoms code).filter (fun a => decide (a ∈ selected))
  have he : xs.toFinset = selected := by
    ext a
    simp only [xs, List.mem_toFinset, List.mem_filter, decide_eq_true_eq]
    exact ⟨And.right, fun ha => ⟨by rw [atoms_correct]; exact h.2 a ha, ha⟩⟩
  refine ⟨xs, ?_, he⟩
  simp only [enumerate, List.mem_filter, List.mem_sublists', eval_correct]
  refine ⟨List.filter_sublist, ?_⟩
  have hev := (PosBool.eval_congr (fun a => List.mem_toFinset) _).mp (he.symm ▸ h.1)
  exact hev

theorem enumerate_iff (code : Code A) (selected : Finset A) :
    (∃ xs ∈ enumerate code, xs.toFinset = selected) ↔
      Valid (EncodedPositiveBoolean.decode code) selected := by
  constructor
  · rintro ⟨xs, hxs, rfl⟩
    exact enumerate_valid code xs hxs
  · exact enumerate_complete code selected

section FiniteIndices

/-- Interpret a list of numeric names as a finite set of bounded states. -/
def decodeSet (n : Nat) (xs : List Nat) : Finset (Fin n) :=
  Finset.univ.filter (fun q => q.val ∈ xs)

@[simp] theorem mem_decodeSet (n : Nat) (xs : List Nat) (q : Fin n) :
    q ∈ decodeSet n xs ↔ q.val ∈ xs := by simp [decodeSet]

theorem valid_decodeSet {n : Nat} (p : PosBool (Fin n)) (xs : List Nat)
    (h : Valid (p.map Fin.val) xs.toFinset) : Valid p (decodeSet n xs) := by
  refine ⟨?_, ?_⟩
  · have he := (PosBool.eval_map (fun a => a ∈ xs.toFinset) Fin.val p).mp h.1
    exact (PosBool.eval_congr (fun q => by simp) p).mp he
  · intro q hq
    have hm (p : PosBool (Fin n)) : (p.map Fin.val).atoms = p.atoms.map Fin.val := by
      induction p <;> simp_all [PosBool.map, PosBool.atoms]
    have ha := h.2 q.val (by simpa using hq)
    rw [hm, List.mem_map] at ha
    obtain ⟨q', hq', he⟩ := ha
    exact Fin.ext he ▸ hq'

theorem valid_image {n : Nat} (p : PosBool (Fin n)) (selected : Finset (Fin n))
    (h : Valid p selected) : Valid (p.map Fin.val) (selected.image Fin.val) := by
  refine ⟨?_, ?_⟩
  · rw [PosBool.eval_map]
    apply (PosBool.eval_congr (fun q => ?_) p).mp h.1
    simp only [Finset.mem_image]
    exact ⟨fun hq => ⟨q, hq, rfl⟩,
      fun ⟨q', hq', he⟩ => Fin.ext he ▸ hq'⟩
  · intro a ha
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp ha
    have hm (p : PosBool (Fin n)) : (p.map Fin.val).atoms = p.atoms.map Fin.val := by
      induction p <;> simp_all [PosBool.map, PosBool.atoms]
    rw [hm]
    exact List.mem_map.mpr ⟨q, h.2 q hq, rfl⟩

/-- Exact correspondence with supports over a finite numeric state carrier. -/
theorem enumerate_decodeSet_iff {n : Nat} (code : Code Nat) (p : PosBool (Fin n))
    (hc : EncodedPositiveBoolean.decode code = p.map Fin.val) (selected : Finset (Fin n)) :
    (∃ xs ∈ enumerate code, decodeSet n xs = selected) ↔ Valid p selected := by
  constructor
  · rintro ⟨xs, hxs, rfl⟩
    exact valid_decodeSet p xs (hc ▸ enumerate_valid code xs hxs)
  · intro h
    obtain ⟨xs, hxs, he⟩ := enumerate_complete code (selected.image Fin.val)
      (hc.symm ▸ valid_image p selected h)
    refine ⟨xs, hxs, ?_⟩
    ext q
    rw [mem_decodeSet, ← List.mem_toFinset, he, Finset.mem_image]
    exact ⟨fun ⟨q', hq', he⟩ => Fin.ext he ▸ hq', fun hq => ⟨q, hq, rfl⟩⟩

end FiniteIndices

section Computability
variable [Primcodable A]

theorem evalAlgebra_effective : PostfixFold.EffectiveFamily (evalAlgebra (A := A)) := by
  constructor
  · exact Primrec.const _
  · exact Primrec.const _
  · have hm : PrimrecRel (fun (xs : List A) a => a ∈ xs) :=
      Primrec.eq.exists_mem_list.of_eq (fun _ _ => by simp)
    exact hm.decide
  · exact Primrec.const _
  · exact (Primrec.dom_finite (fun p : Bool × Bool => p.1 && p.2)).comp Primrec.snd
  · exact (Primrec.dom_finite (fun p : Bool × Bool => p.1 || p.2)).comp Primrec.snd
  · exact Primrec.const _
  · exact Primrec.const _
  · exact Primrec.const _

theorem eval_primrec : Primrec₂ (eval (A := A)) :=
  (PostfixFold.run_family_primrec evalAlgebra evalAlgebra_effective).comp Primrec.snd Primrec.fst

omit [DecidableEq A] in
theorem atoms_primrec : Primrec (atoms (A := A)) := by
  apply PostfixFold.run_primrec atomsAlgebra
  constructor
  · exact Primrec.list_cons.comp Primrec.id (Primrec.const [])
  · exact Primrec.const _
  · exact Primrec.list_append
  · exact Primrec.list_append
  · exact Primrec.const _
  · exact Primrec.const _
  · exact Primrec.const _

theorem enumerate_primrec : Primrec (enumerate (A := A)) := by
  have hp : PrimrecRel (fun (xs : List A) (c : Code A) => eval c xs = true) :=
    Primrec.eq.comp (eval_primrec.comp Primrec.snd Primrec.fst) (Primrec.const true)
  exact (hp.listFilter.comp (FiniteSearch.sublists_primrec.comp atoms_primrec) Primrec.id).of_eq
    (fun _ => by simp only [enumerate, Bool.decide_eq_true, id_eq])

end Computability
end DistributedSynthesis.EncodedSupports
