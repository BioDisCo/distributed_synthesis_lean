/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Logic.MSO.NumericFirstOrder

/-! # Primitive-recursive compilation and decision procedures for full MSO

The input is a postfix code with explicit finite contexts. The structural
encoder covers the existing MSO syntax, including embedded first-order
formulas and terms. Numeric evaluation and decision use Mathlib's `Primrec`;
no solver or complexity assumption is supplied by the caller.
-/
namespace DistributedSynthesis.MSO.Tree.Numeric
open NumericValuations EncodedProjectedTree

variable {b a n m : Nat}

def recognition {n m : Nat} (φ : Formula (language (Fin (b+1)) (Fin (a+1))) n m) :
    NumericRecognition (fun tree nodes sets => Realize tree φ nodes sets) :=
  match φ with
  | .firstOrder φ => firstOrder_recognition φ
  | .mem x X => NumericRecognition.membership x X
  | .falsum => NumericRecognition.falsum
  | .imp φ ψ => (recognition φ).impl (recognition ψ)
  | .allNode φ => (recognition φ).forallNode
  | .allSet φ => (recognition φ).forallSet

/-- Branch maximum, alphabet maximum, individual/set context sizes, formula code. -/
abbrev Input := Nat × Nat × Nat × Nat × NumericProgram.Code

def compile (x : Input) : Data :=
  EncodedTreeShape.resize (x.1+1) (count (x.2.1,x.2.2.1,x.2.2.2.1)-1)
    (NumericProgram.compile (x.1+1) x.2.2.2.2)

def formulaInput (φ : Formula (language (Fin (b+1)) (Fin (a+1))) n m) : Input :=
  (b,a,n,m,(recognition φ).program.code)

@[fun_prop] theorem compile_primrec : Primrec compile := by
  have hc : Primrec (fun x : Input => NumericProgram.compile (x.1+1) x.2.2.2.2) :=
    NumericProgram.compile_primrec.comp (by fun_prop) (by fun_prop)
  exact EncodedTreeShape.resize_primrec.comp
    (g := fun x : Input => (x.1+1,count (x.2.1,x.2.2.1,x.2.2.2.1)-1,
      NumericProgram.compile (x.1+1) x.2.2.2.2))
    (Primrec.pair (by fun_prop) (Primrec.pair (by fun_prop) hc))

theorem compile_correct (φ : Formula (language (Fin (b+1)) (Fin (a+1))) n m)
    (tree : LabeledTree (Fin (b+1)) (Fin (a+1))) (nodes : Fin n → TreeNode (Fin (b+1)))
    (sets : Fin m → Set (TreeNode (Fin (b+1)))) :
    (automaton (compile (formulaInput φ))).acceptsTree
      (number (a,n,m) ∘ encode tree nodes sets) ↔ Realize tree φ nodes sets := by
  change NumericOperations.Accepts (b+1) (a,n,m)
    (NumericProgram.compile (b+1) (recognition φ).program.code) (encode tree nodes sets) ↔ _
  rw [(recognition φ).program.compile_eq]
  exact (recognition φ).correct tree nodes sets

/-- At sentence context every numeric label represents an ordinary input letter. -/
theorem sentence_labels (tree : LabeledTree (Fin (b+1)) (Fin (count (a,0,0)-1+1))) :
    number (a,0,0) ∘ encode (fun p => ((number (a,0,0)).symm (tree p)).1) Fin.elim0 Fin.elim0 = tree := by
  funext p
  apply (number (a,0,0)).symm.injective
  simp only [Function.comp_apply, Equiv.symm_apply_apply]
  refine Prod.ext ?_ (Prod.ext (Subsingleton.elim _ _) (Subsingleton.elim _ _))
  rfl

theorem nonempty_correct (φ : Sentence (language (Fin (b+1)) (Fin (a+1)))) :
    (∃ tree, (automaton (compile (formulaInput φ))).acceptsTree tree) ↔ ∃ tree, Satisfies tree φ := by
  constructor
  · rintro ⟨tree,ht⟩
    refine ⟨fun p => ((number (a,0,0)).symm (tree p)).1, ?_⟩
    apply (compile_correct φ _ Fin.elim0 Fin.elim0).mp
    have h := sentence_labels tree
    exact (Iff.of_eq (congrArg (fun t : LabeledTree (Fin (b+1)) (Fin (count (a,0,0)-1+1)) =>
      (automaton (compile (formulaInput φ))).acceptsTree t) h)).mpr ht
  · rintro ⟨tree,ht⟩
    exact ⟨number (a,0,0) ∘ encode tree Fin.elim0 Fin.elim0,
      (compile_correct φ tree Fin.elim0 Fin.elim0).mpr ht⟩

/-- Branch maximum, alphabet cardinality (possibly zero), and sentence code. -/
abbrev SentenceInput := Nat × Nat × NumericProgram.Code

def satisfiable (x : SentenceInput) : Bool :=
  if x.2.1 = 0 then false else solve (compile (x.1,x.2.1-1,0,0,x.2.2))
def valid (x : SentenceInput) : Bool :=
  if x.2.1 = 0 then true else !(solve (EncodedTreeComplement.compile (compile (x.1,x.2.1-1,0,0,x.2.2))))

attribute [local fun_prop] solve_primrec EncodedTreeComplement.compile_primrec

@[fun_prop] theorem satisfiable_primrec : Primrec satisfiable := by
  unfold satisfiable
  apply Primrec.ite <;> fun_prop
@[fun_prop] theorem valid_primrec : Primrec valid := by
  unfold valid
  apply Primrec.ite (by fun_prop) (by fun_prop)
  exact (Primrec.dom_finite Bool.not).comp (by fun_prop)

/-- The zero-letter case has no full labelled tree and needs no automaton. -/
def sentenceInput {a : Nat} (φ : Sentence (language (Fin (b+1)) (Fin a))) : SentenceInput :=
  match a, φ with
  | 0, _ => (b,0,[])
  | a+1, φ => (b,a+1,(recognition φ).program.code)

theorem satisfiable_correct {a : Nat} (φ : Sentence (language (Fin (b+1)) (Fin a))) :
    satisfiable (sentenceInput φ) = true ↔ ∃ tree, Satisfies tree φ := by
  cases a with
  | zero =>
    change false = true ↔ _
    simp only [Bool.false_eq_true, false_iff]
    rintro ⟨tree,_⟩
    exact Fin.elim0 (tree [])
  | succ a =>
    change solve (compile (formulaInput φ)) = true ↔ _
    exact (solve_correct _).trans (nonempty_correct φ)

theorem valid_correct {a : Nat} (φ : Sentence (language (Fin (b+1)) (Fin a))) :
    valid (sentenceInput φ) = true ↔ ∀ tree, Satisfies tree φ := by
  cases a with
  | zero =>
    change true = true ↔ _
    simp only [true_iff]
    intro tree
    exact Fin.elim0 (tree [])
  | succ a =>
    change (!(solve (EncodedTreeComplement.compile (compile (formulaInput φ))))) = true ↔ _
    simp only [Bool.not_eq_true', Bool.eq_false_iff, ne_eq]
    rw [solve_correct]
    letI : Nonempty (EncodedTreeComplement.Direction (compile (formulaInput φ))) :=
      inferInstanceAs (Nonempty (Fin (b+1)))
    simp only [EncodedTreeComplement.compile_correct, not_exists, not_not]
    constructor
    · intro h tree
      exact (compile_correct φ tree Fin.elim0 Fin.elim0).mp (h _)
    · intro h tree
      have ht := (compile_correct φ _ Fin.elim0 Fin.elim0).mpr
        (h (fun p => ((number (a,0,0)).symm (tree p)).1))
      exact (Iff.of_eq (congrArg (fun t : LabeledTree (Fin (b+1)) (Fin (count (a,0,0)-1+1)) =>
        (automaton (compile (formulaInput φ))).acceptsTree t) (sentence_labels tree))).mp ht

/-- A literal natural-number input/output interface, using Mathlib's existing encoding. -/
def compileNat (c : Nat) : Nat :=
  Encodable.encode (compile ((Encodable.decode (α := Input) c).getD default))
def satisfiableNat (c : Nat) : Nat :=
  Encodable.encode (satisfiable ((Encodable.decode (α := SentenceInput) c).getD default))
def validNat (c : Nat) : Nat :=
  Encodable.encode (valid ((Encodable.decode (α := SentenceInput) c).getD default))

theorem compileNat_primrec : Nat.Primrec compileNat := Primrec.nat_iff.mp
  (Primrec.encode.comp (compile_primrec.comp (Primrec.option_getD.comp Primrec.decode (Primrec.const (default : Input)))))
theorem satisfiableNat_primrec : Nat.Primrec satisfiableNat := Primrec.nat_iff.mp
  (Primrec.encode.comp (satisfiable_primrec.comp (Primrec.option_getD.comp Primrec.decode (Primrec.const (default : SentenceInput)))))
theorem validNat_primrec : Nat.Primrec validNat := Primrec.nat_iff.mp
  (Primrec.encode.comp (valid_primrec.comp (Primrec.option_getD.comp Primrec.decode (Primrec.const (default : SentenceInput)))))

theorem compileNat_encode (x : Input) : compileNat (Encodable.encode x) = Encodable.encode (compile x) := by
  simp only [compileNat, Encodable.encodek, Option.getD_some]
theorem satisfiableNat_encode (x : SentenceInput) :
    satisfiableNat (Encodable.encode x) = Encodable.encode (satisfiable x) := by simp only [satisfiableNat, Encodable.encodek, Option.getD_some]
theorem validNat_encode (x : SentenceInput) :
    validNat (Encodable.encode x) = Encodable.encode (valid x) := by simp only [validNat, Encodable.encodek, Option.getD_some]

/-- The natural-number decision interface has exactly the full MSO semantics. -/
theorem satisfiableNat_correct {a : Nat} (φ : Sentence (language (Fin (b+1)) (Fin a))) :
    satisfiableNat (Encodable.encode (sentenceInput φ)) = Encodable.encode true ↔
      ∃ tree, Satisfies tree φ := by
  rw [satisfiableNat_encode, Encodable.encode_injective.eq_iff]
  exact satisfiable_correct φ

theorem validNat_correct {a : Nat} (φ : Sentence (language (Fin (b+1)) (Fin a))) :
    validNat (Encodable.encode (sentenceInput φ)) = Encodable.encode true ↔
      ∀ tree, Satisfies tree φ := by
  rw [validNat_encode, Encodable.encode_injective.eq_iff]
  exact valid_correct φ

end DistributedSynthesis.MSO.Tree.Numeric
