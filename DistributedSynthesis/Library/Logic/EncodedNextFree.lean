/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/
import DistributedSynthesis.Library.Logic.NextFree
import DistributedSynthesis.Library.Logic.PostfixFold

/-! # Primitive-recursive elimination of next in postfix LTL

The compiler uses the library's verified postfix fold. Its correctness includes
malformed source codes, with precisely the existing total decoder's semantics.
-/
namespace DistributedSynthesis.EncodedNextFree
open EncodedFiniteLTL
variable {A B : Type*}

def encode : LTL A → Code A
  | .verum => truth
  | .falsum => falsity
  | .atom a => atom a
  | .neg p => unary 2 (encode p)
  | .conj p q => binary 3 (encode p) (encode q)
  | .disj p q => binary 4 (encode p) (encode q)
  | .next p => unary 5 (encode p)
  | .until p q => binary 6 (encode p) (encode q)
  | .release p q => binary 7 (encode p) (encode q)

theorem neg_rep {c : Code A} {p : LTL A} (h : Represents c p) :
    Represents (unary 2 c) (.neg p) := unary_rep 2 .neg (fun _ _ ↦ rfl) h

theorem until_rep {c d : Code A} {p q : LTL A} (hp : Represents c p) (hq : Represents d q) :
    Represents (binary 6 c d) (.until p q) := binary_rep 6 .until (fun _ _ _ ↦ rfl) hp hq

theorem encode_rep (p : LTL A) : Represents (encode p) p := by
  induction p with
  | verum => exact truth_rep
  | falsum => exact falsity_rep
  | atom a => exact atom_rep a
  | neg p ih => exact neg_rep ih
  | conj p q ihp ihq => exact conj_rep ihp ihq
  | disj p q ihp ihq => exact disj_rep ihp ihq
  | next p ih => exact next_rep ih
  | «until» p q ihp ihq => exact until_rep ihp ihq
  | «release» p q ihp ihq => exact release_rep ihp ihq

def step (c p : Code B) : Code B :=
  binary 4 (binary 3 c (binary 6 c (binary 3 (unary 2 c) p)))
    (binary 3 (unary 2 c) (binary 6 (unary 2 c) (binary 3 c p)))

theorem step_rep {c p : Code B} {C P : LTL B} (hc : Represents c C) (hp : Represents p P) :
    Represents (step c p) (LTL.NextFreeTranslation.step C P) :=
  disj_rep (conj_rep hc (until_rep hc (conj_rep (neg_rep hc) hp)))
    (conj_rep (neg_rep hc) (until_rep (neg_rep hc) (conj_rep hc hp)))

def algebra (clock : B) (f : A → B) : PostfixFold.Algebra A (Code B) where
  truth := truth
  falsity := falsity
  atom := fun a ↦ atom (f a)
  neg := unary 2
  conj := binary 3
  disj := binary 4
  next := step (atom clock)
  «until» := binary 6
  «release» := binary 7

def translate (clock : B) (f : A → B) : Code A → Code B := PostfixFold.run (algebra clock f)

theorem formula_rep (clock : B) (f : A → B) (p : LTL A) :
    Represents (PostfixFold.formula (algebra clock f) p)
      (LTL.NextFreeTranslation.translate clock f p) := by
  induction p with
  | verum => exact truth_rep
  | falsum => exact falsity_rep
  | atom a => exact atom_rep _
  | neg p ih => exact neg_rep ih
  | conj p q ihp ihq => exact conj_rep ihp ihq
  | disj p q ihp ihq => exact disj_rep ihp ihq
  | next p ih => exact step_rep (atom_rep clock) ih
  | «until» p q ihp ihq => exact until_rep ihp ihq
  | «release» p q ihp ihq => exact release_rep ihp ihq

theorem translate_rep (clock : B) (f : A → B) (c : Code A) :
    Represents (translate clock f c) (LTL.NextFreeTranslation.translate clock f (decode c)) := by
  rw [translate, PostfixFold.run_correct]
  exact formula_rep clock f (decode c)

theorem translate_nextFree (clock : B) (f : A → B) (c : Code A) :
    LTL.NextFree (decode (translate clock f c)) := by
  rw [(translate_rep clock f c).decode]
  exact LTL.NextFreeTranslation.nextFree _ _ _

section Computability
variable [Primcodable A] [Primcodable B]

theorem step_primrec : Primrec₂ (step : Code B → Code B → Code B) := by
  unfold Primrec₂ step
  repeat' first
    | apply (binary_primrec _).comp
    | apply (unary_primrec _).comp
    | exact Primrec.fst
    | exact Primrec.snd

theorem algebra_effective (clock : B) (f : A → B) (hf : Primrec f) :
    PostfixFold.Effective (algebra clock f) where
  atom := atom_primrec.comp hf
  neg := unary_primrec 2
  conj := binary_primrec 3
  disj := binary_primrec 4
  next := step_primrec.comp (Primrec.const _) Primrec.id
  «until» := binary_primrec 6
  «release» := binary_primrec 7

theorem translate_primrec (clock : B) (f : A → B) (hf : Primrec f) :
    Primrec (translate clock f) := PostfixFold.run_primrec _ (algebra_effective clock f hf)

end Computability
end DistributedSynthesis.EncodedNextFree
