/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Logic.EncodedBlockTranslation
import DistributedSynthesis.Library.Logic.BinaryClock
import DistributedSynthesis.Library.Logic.BinaryWords

/-! # Ordinary postfix syntax for the complete binary protocol

All parameter-dependent loops range over explicitly supplied natural numbers
or finite lists. There are no fresh clock atoms or semantic oracle tokens.
-/
namespace DistributedSynthesis.EncodedBinarySyntax
open EncodedFiniteLTL
variable {B : Type*}

def conjunction (xs : List (Code B)) : Code B := xs.foldr (binary 3) truth
theorem conjunction_rep (xs : List (Code B)) (ps : List (LTL B))
    (h : List.Forall₂ Represents xs ps) :
    Represents (conjunction xs) (ps.foldr LTL.conj .verum) := by
  induction h with
  | nil => exact truth_rep
  | cons h _ ih => exact conj_rep h ih

def marker (one : B) : Code B := binary 3 (atom one) (unary 5 (atom one))
def zeros (one two : B) (K : Nat) : Code B :=
  conjunction ((List.range (K+1)).map fun j ↦ EncodedBlockTranslation.nextN (2*j+2)
    (binary 3 (unary 2 (atom one)) (unary 2 (atom two))))
def frame (one two : B) (K : Nat) : Code B :=
  binary 3 (marker one) (always (binary 4 (unary 2 (marker one))
    (binary 3 (atom two) (binary 3 (unary 5 (atom two))
      (binary 3 (zeros one two K) (EncodedBlockTranslation.nextN (2*K+3) (marker one)))))))
def agreement (one two : B) : Code B :=
  binary 3 (binary 4 (unary 2 (atom one)) (atom two))
    (binary 4 (unary 2 (atom two)) (atom one))
def protocol (one two both : B) (K : Nat) : Code B :=
  binary 3 (frame one two K)
    (always (binary 4 (marker one) (binary 4 (atom both) (always (agreement one two)))))
def core (one both : B) : Code B := always (binary 4 (marker one) (atom both))

def word (K : Nat) (p : B) (i : Nat) : Code B :=
  conjunction ((List.range K).map fun j ↦ EncodedBlockTranslation.nextN (2*j+3)
    (if i = j then atom p else unary 2 (atom p)))
def valid (K : Nat) (p : B) (ids : List Nat) : Code B :=
  disjunction (ids.map (word K p))
def guard (one two both : B) (K : Nat) (ids₁ ids₂ : List Nat) (objective : Code B) : Code B :=
  let vc := binary 3 (valid K two ids₁) (valid K one ids₂)
  binary 3 (protocol one two both K)
    (binary 3 (binary 4 (unary 2 (core one both))
      (always (binary 4 (unary 2 (marker one)) vc)))
      (binary 4 (unary 2 (core one both)) objective))

theorem neg_rep {p : Code B} {φ : LTL B} (h : Represents p φ) :
    Represents (unary 2 p) (.neg φ) := unary_rep 2 .neg (fun _ _ ↦ rfl) h
theorem marker_rep (one : B) : Represents (marker one) (LTL.BinaryClock.marker one) :=
  conj_rep (atom_rep one) (next_rep (atom_rep one))

theorem map_rep {A : Type*} (xs : List A) (f : A → Code B) (g : A → LTL B)
    (h : ∀ a, Represents (f a) (g a)) : List.Forall₂ Represents (xs.map f) (xs.map g) := by
  induction xs with
  | nil => exact .nil
  | cons a xs ih => exact .cons (h a) ih

theorem ofFn_range_map {C : Type*} (K : Nat) (f : Nat → C) :
    List.ofFn (fun j : Fin K ↦ f j.val) = (List.range K).map f := by
  simpa using List.ofFn_getElem_eq_map (List.range K) f

theorem zeros_rep (one two : B) (K : Nat) :
    Represents (zeros one two K) (LTL.BinaryClock.zeros one two K) := by
  apply conjunction_rep
  apply map_rep
  intro j
  exact EncodedBlockTranslation.nextN_rep _ (conj_rep (neg_rep (atom_rep one)) (neg_rep (atom_rep two)))

theorem frame_rep (one two : B) (K : Nat) :
    Represents (frame one two K) (LTL.BinaryClock.frame one two K) :=
  conj_rep (marker_rep one) (always_rep (disj_rep (neg_rep (marker_rep one))
    (conj_rep (atom_rep two) (conj_rep (next_rep (atom_rep two))
      (conj_rep (zeros_rep one two K) (EncodedBlockTranslation.nextN_rep _ (marker_rep one)))))))

theorem word_rep (K : Nat) (p : B) (i : Nat) : Represents (word K p i)
    (BinaryWords.wordTest p (fun j : Fin K ↦ decide (i = j.val))) := by
  have he : (List.ofFn fun j : Fin K ↦ LTL.BlockTranslation.nextN (2*j.val+3)
      (BinaryWords.bitTest p (decide (i = j.val)))) =
      (List.range K).map (fun j ↦ LTL.BlockTranslation.nextN (2*j+3)
        (BinaryWords.bitTest p (decide (i = j)))) := by
    simpa using List.ofFn_getElem_eq_map (List.range K)
      (fun j ↦ LTL.BlockTranslation.nextN (2*j+3) (BinaryWords.bitTest p (decide (i = j))))
  rw [BinaryWords.wordTest, he]
  apply conjunction_rep
  apply map_rep
  intro j
  apply EncodedBlockTranslation.nextN_rep
  by_cases h : i = j
  · simpa [h, BinaryWords.bitTest] using atom_rep p
  · simpa [h, BinaryWords.bitTest] using neg_rep (atom_rep p)

theorem valid_rep (K : Nat) (p : B) (ids : List Nat) : Represents (valid K p ids)
    ((ids.map fun i ↦ BinaryWords.wordTest p (fun j : Fin K ↦ decide (i = j.val))).foldr LTL.disj .falsum) :=
  disjunction_rep _ _ (map_rep ids _ _ (word_rep K p))

def protocolFormula (one two both : B) (K : Nat) : LTL B :=
  .conj (LTL.BinaryClock.frame one two K) (.always (.disj (LTL.BinaryClock.marker one)
    (.disj (.atom both) (.always (.conj (.disj (.neg (.atom one)) (.atom two))
      (.disj (.neg (.atom two)) (.atom one)))))))
def coreFormula (one both : B) : LTL B :=
  .always (.disj (LTL.BinaryClock.marker one) (.atom both))
def guardFormula (one two both : B) (K : Nat) (v₁ v₂ φ : LTL B) : LTL B :=
  .conj (protocolFormula one two both K)
    (.conj (.disj (.neg (coreFormula one both))
      (.always (.disj (.neg (LTL.BinaryClock.marker one)) (.conj v₁ v₂))))
      (.disj (.neg (coreFormula one both)) φ))

theorem protocol_rep (one two both : B) (K : Nat) :
    Represents (protocol one two both K) (protocolFormula one two both K) :=
  conj_rep (frame_rep one two K) (always_rep (disj_rep (marker_rep one)
    (disj_rep (atom_rep both) (always_rep (conj_rep
      (disj_rep (neg_rep (atom_rep one)) (atom_rep two))
      (disj_rep (neg_rep (atom_rep two)) (atom_rep one)))))))
theorem core_rep (one both : B) : Represents (core one both) (coreFormula one both) :=
  always_rep (disj_rep (marker_rep one) (atom_rep both))
theorem guard_rep (one two both : B) (K : Nat) (ids₁ ids₂ : List Nat)
    (v₁ v₂ φ : LTL B) (objective : Code B)
    (h₁ : Represents (valid K two ids₁) v₁) (h₂ : Represents (valid K one ids₂) v₂)
    (hφ : Represents objective φ) :
    Represents (guard one two both K ids₁ ids₂ objective) (guardFormula one two both K v₁ v₂ φ) :=
  conj_rep (protocol_rep one two both K) (conj_rep
    (disj_rep (neg_rep (core_rep one both)) (always_rep
      (disj_rep (neg_rep (marker_rep one)) (conj_rep h₁ h₂))))
    (disj_rep (neg_rep (core_rep one both)) hφ))

section Computability
variable [Primcodable B]
theorem conjunction_primrec : Primrec (conjunction : List (Code B) → Code B) :=
  Primrec.list_foldr Primrec.id (Primrec.const truth)
    ((binary_primrec 3).comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)).to₂

theorem zeros_primrec (one two : B) : Primrec (zeros one two) := by
  apply conjunction_primrec.comp
  apply Primrec.list_map (Primrec.list_range.comp Primrec.succ)
  exact (EncodedBlockTranslation.nextN_primrec.comp
    (Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 2) Primrec.snd) (Primrec.const 2))
    (Primrec.const _)).to₂

theorem frame_primrec (one two : B) : Primrec (frame one two) := by
  unfold frame
  repeat' first
    | exact Primrec.const _
    | exact zeros_primrec one two
    | exact EncodedBlockTranslation.nextN_primrec.comp
        (Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 2) Primrec.id) (Primrec.const 3)) (Primrec.const _)
    | apply always_primrec.comp
    | apply (binary_primrec _).comp

theorem protocol_primrec (one two both : B) : Primrec (protocol one two both) :=
  (binary_primrec 3).comp (frame_primrec one two) (Primrec.const _)

theorem word_primrec (p : B) : Primrec₂ (fun K i ↦ word K p i) := by
  apply conjunction_primrec.comp
  apply Primrec.list_map (Primrec.list_range.comp Primrec.fst)
  unfold Primrec₂
  apply EncodedBlockTranslation.nextN_primrec.comp
    (Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 2) Primrec.snd) (Primrec.const 3))
  exact Primrec.ite (Primrec.eq.comp (Primrec.snd.comp Primrec.fst) Primrec.snd)
    (Primrec.const _) (Primrec.const _)

theorem valid_primrec (p : B) : Primrec₂ (fun K ids ↦ valid K p ids) := by
  apply disjunction_primrec.comp
  apply Primrec.list_map Primrec.snd
  exact ((word_primrec p).comp (Primrec.fst.comp Primrec.fst) Primrec.snd).to₂

theorem guard_primrec {X : Type*} [Primcodable X] (one two both : B)
    {k : X → Nat} {i₁ i₂ : X → List Nat} {φ : X → Code B}
    (hk : Primrec k) (h₁ : Primrec i₁) (h₂ : Primrec i₂) (hφ : Primrec φ) :
    Primrec (fun x ↦ guard one two both (k x) (i₁ x) (i₂ x) (φ x)) := by
  exact (binary_primrec 3).comp ((protocol_primrec one two both).comp hk)
    ((binary_primrec 3).comp
      ((binary_primrec 4).comp (Primrec.const _)
        (always_primrec.comp ((binary_primrec 4).comp (Primrec.const _)
          ((binary_primrec 3).comp ((valid_primrec two).comp hk h₁) ((valid_primrec one).comp hk h₂)))))
      ((binary_primrec 4).comp (Primrec.const _) hφ))
end Computability

end DistributedSynthesis.EncodedBinarySyntax
