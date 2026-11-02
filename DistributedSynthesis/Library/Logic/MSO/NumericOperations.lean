/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Logic.MSO.NumericAtomLanguages
import DistributedSynthesis.Library.Logic.MSO.NumericRenaming
import DistributedSynthesis.Library.Automata.EncodedTreeIntersectionCorrect
import DistributedSynthesis.Library.Automata.EncodedTreeComap

/-! # Numeric operations on MSO valuation automata -/
namespace DistributedSynthesis.MSO.Tree.NumericOperations
open NumericValuations EncodedProjectedTree

abbrev Accepts (b : Nat) (s : Shape) (d : Data)
    (tree : LabeledTree (Fin b) (ValuationLabel (Fin (s.1+1)) s.2.1 s.2.2)) : Prop :=
  EncodedTreeShape.Accepts b (count s - 1) d (number s ∘ tree)

def atom (b : Nat) (s : Shape) (k i j d : Nat) : Data := NumericAtoms.compile (b,s,k,i,j,d)
def neg (b : Nat) (s : Shape) (d : Data) : Data :=
  EncodedTreeComplement.compile (EncodedTreeShape.resize b (count s - 1) d)
def conj (b : Nat) (s : Shape) (d e : Data) : Data :=
  EncodedTreeIntersection.compile (b,count s - 1,d,e)
def rename (b : Nat) (s t : Shape) (f g : List Nat) (d : Data) : Data :=
  EncodedTreeComap.compile (EncodedTreeShape.resize b (count s - 1) d,
    count t - 1, NumericRenaming.table (s,t,f,g))
def project (b : Nat) (s t : Shape) (f g : List Nat) (d : Data) : Data :=
  EncodedTreeProjection.compile (EncodedTreeShape.resize b (count s - 1) d,
    count t - 1, NumericRenaming.table (t,s,f,g))

attribute [local fun_prop] NumericAtoms.compile_primrec EncodedTreeComplement.compile_primrec
  EncodedTreeIntersection.compile_primrec EncodedTreeComap.compile_primrec EncodedTreeProjection.compile_primrec

@[fun_prop] theorem atom_primrec : Primrec (fun x : Nat × Shape × Nat × Nat × Nat × Nat =>
    atom x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2.1 x.2.2.2.2.2) := by unfold atom; fun_prop
@[fun_prop] theorem neg_primrec : Primrec (fun x : Nat × Shape × Data => neg x.1 x.2.1 x.2.2) := by
  unfold neg; fun_prop
@[fun_prop] theorem conj_primrec : Primrec (fun x : Nat × Shape × Data × Data => conj x.1 x.2.1 x.2.2.1 x.2.2.2) := by
  unfold conj; fun_prop
@[fun_prop] theorem rename_primrec : Primrec (fun x : Nat × Shape × Shape × List Nat × List Nat × Data =>
    rename x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2.1 x.2.2.2.2.2) := by unfold rename; fun_prop
@[fun_prop] theorem project_primrec : Primrec (fun x : Nat × Shape × Shape × List Nat × List Nat × Data =>
    project x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2.1 x.2.2.2.2.2) := by unfold project; fun_prop

variable {b a n m k l : Nat} [Inhabited (Fin b)]

theorem atom_correct (s : Shape) (k i j d : Nat)
    (tree : LabeledTree (Fin b) (ValuationLabel (Fin (s.1+1)) s.2.1 s.2.2)) :
    Accepts b s (atom b s k i j d) tree ↔ (NumericAtoms.view (b,s,k,i,j,d)).acceptsTree tree := by
  letI : Inhabited (NumericAtoms.Direction (b,s,k,i,j,d)) := inferInstanceAs (Inhabited (Fin b))
  exact NumericAtoms.compile_accepts_iff (b,s,k,i,j,d) tree

theorem neg_correct (s : Shape) (d : Data)
    (tree : LabeledTree (Fin b) (ValuationLabel (Fin (s.1+1)) s.2.1 s.2.2)) :
    Accepts b s (neg b s d) tree ↔ ¬ Accepts b s d tree := by
  letI : Nonempty (EncodedTreeComplement.Direction (EncodedTreeShape.resize b (count s - 1) d)) :=
    inferInstanceAs (Nonempty (Fin b))
  exact EncodedTreeComplement.compile_correct (EncodedTreeShape.resize b (count s - 1) d) _

omit [Inhabited (Fin b)] in
theorem conj_correct (s : Shape) (d e : Data)
    (tree : LabeledTree (Fin b) (ValuationLabel (Fin (s.1+1)) s.2.1 s.2.2)) :
    Accepts b s (conj b s d e) tree ↔ Accepts b s d tree ∧ Accepts b s e tree := by
  exact EncodedTreeIntersection.compile_correct (b,count s - 1,d,e) _

theorem map_correct (f : Fin n → Fin k) (g : Fin m → Fin l)
    (label : ValuationLabel (Fin (a+1)) k l) :
    EncodedTreeProjection.letterMap (count (a,n,m)-1)
      (NumericRenaming.table (NumericRenaming.input (a := a) f g)) (number (a,k,l) label) =
      number (a,n,m) (renameMarkers f g label) := by
  apply Fin.ext
  change _ % _ = _
  rw [NumericRenaming.table_correct, Nat.mod_eq_of_lt (number (a,n,m) (renameMarkers f g label)).isLt]

theorem rename_correct (d : Data) (f : Fin n → Fin k) (g : Fin m → Fin l)
    (tree : LabeledTree (Fin b) (ValuationLabel (Fin (a+1)) k l)) :
    Accepts b (a,k,l) (rename b (a,n,m) (a,k,l)
      (FiniteFunctionCoding.encode f) (FiniteFunctionCoding.encode g) d) tree ↔
      Accepts b (a,n,m) d (renameMarkers f g ∘ tree) := by
  letI : Inhabited (Fin (EncodedTreeNonemptiness.branches (monitorData
      (EncodedTreeShape.resize b (count (a,n,m)-1) d)))) := inferInstanceAs (Inhabited (Fin b))
  rw [show Accepts b (a,k,l) (rename b (a,n,m) (a,k,l)
      (FiniteFunctionCoding.encode f) (FiniteFunctionCoding.encode g) d) tree ↔
      (automaton (EncodedTreeShape.resize b (count (a,n,m)-1) d)).acceptsTree
        (EncodedTreeComap.letterMap (EncodedTreeShape.resize b (count (a,n,m)-1) d,
          count (a,k,l)-1, NumericRenaming.table (NumericRenaming.input f g)) ∘ number (a,k,l) ∘ tree)
    from EncodedTreeComap.compile_correct _ _]
  have h : EncodedTreeComap.letterMap (EncodedTreeShape.resize b (count (a,n,m)-1) d,
      count (a,k,l)-1, NumericRenaming.table (NumericRenaming.input f g)) ∘ number (a,k,l) ∘ tree =
      number (a,n,m) ∘ renameMarkers f g ∘ tree := funext (fun p => map_correct f g (tree p))
  exact Iff.of_eq (congrArg (fun t : LabeledTree (Fin b) (Fin (count (a,n,m)-1+1)) =>
    (automaton (EncodedTreeShape.resize b (count (a,n,m)-1) d)).acceptsTree t) h)

omit [Inhabited (Fin b)] in
theorem project_correct (d : Data) (f : Fin k → Fin n) (g : Fin l → Fin m)
    (tree : LabeledTree (Fin b) (ValuationLabel (Fin (a+1)) k l)) :
    Accepts b (a,k,l) (project b (a,n,m) (a,k,l)
      (FiniteFunctionCoding.encode f) (FiniteFunctionCoding.encode g) d) tree ↔
      ∃ original, renameMarkers f g ∘ original = tree ∧ Accepts b (a,n,m) d original := by
  have h := EncodedTreeProjection.accepts_iff
    (EncodedTreeShape.resize b (count (a,n,m)-1) d, count (a,k,l)-1,
      NumericRenaming.table (NumericRenaming.input (a := a) f g)) (number (a,k,l) ∘ tree)
  change _ ↔ _ at h
  refine h.trans ?_
  constructor
  · rintro ⟨original,labels,accepts⟩
    let decoded := (number (a,n,m)).symm ∘ original
    have he : number (a,n,m) ∘ decoded = original := funext (fun _ => Equiv.apply_symm_apply _ _)
    refine ⟨decoded, ?_, ?_⟩
    · funext p
      apply (number (a,k,l)).injective
      have hl := congrFun labels p
      rw [← he] at hl
      exact (map_correct f g (decoded p)).symm.trans hl
    · change (automaton (EncodedTreeShape.resize b (count (a,n,m)-1) d)).acceptsTree (number (a,n,m) ∘ decoded)
      exact (Iff.of_eq (congrArg (fun t : LabeledTree (Fin b) (Fin (count (a,n,m)-1+1)) =>
        (automaton (EncodedTreeShape.resize b (count (a,n,m)-1) d)).acceptsTree t) he)).mpr accepts
  · rintro ⟨original,labels,accepts⟩
    refine ⟨number (a,n,m) ∘ original, ?_, accepts⟩
    funext p
    exact (map_correct f g (original p)).trans (congrArg (number (a,k,l)) (congrFun labels p))

end DistributedSynthesis.MSO.Tree.NumericOperations
