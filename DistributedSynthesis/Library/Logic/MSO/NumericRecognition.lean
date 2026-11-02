/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Logic.MSO.NumericProgram

/-! # Verified numeric recognition of MSO valuation predicates -/
namespace DistributedSynthesis.MSO.Tree

variable {b a n m k l : Nat}

structure NumericRecognition (P : ValuationPredicate (Fin (b+1)) (Fin (a+1)) n m) where
  program : NumericProgram.Program (b+1)
  correct : ∀ tree nodes sets,
    NumericOperations.Accepts (b+1) (a,n,m) program.data (encode tree nodes sets) ↔ P tree nodes sets

namespace NumericRecognition
variable {P Q : ValuationPredicate (Fin (b+1)) (Fin (a+1)) n m}

def congr (h : NumericRecognition P) (same : ∀ tree nodes sets, P tree nodes sets ↔ Q tree nodes sets) :
    NumericRecognition Q := ⟨h.program,fun t ns ss => (h.correct t ns ss).trans (same t ns ss)⟩

def rename (h : NumericRecognition P) (f : Fin n → Fin k) (g : Fin m → Fin l) :
    NumericRecognition (fun t ns ss => P t (ns ∘ f) (ss ∘ g)) where
  program := h.program.rename (a,n,m) k l (FiniteFunctionCoding.encode f) (FiniteFunctionCoding.encode g)
  correct t ns ss := (NumericOperations.rename_correct h.program.data f g _).trans (h.correct t _ _)

def falsum : NumericRecognition (b := b) (a := a) (n := n) (m := m) (fun _ _ _ => False) where
  program := NumericProgram.Program.atom (a,n,m) 0 0 0 0 (by decide)
  correct t ns ss := (NumericOperations.atom_correct _ _ _ _ _ _).trans
    (iff_false_intro (NumericAtoms.false_accepts_iff _))

def membership (x : Fin n) (X : Fin m) : NumericRecognition (b := b) (a := a)
    (fun tree nodes sets => Realize tree (.mem x X) nodes sets) where
  program := NumericProgram.Program.atom (a,n,m) 1 x.val X.val 0 (by decide)
  correct t ns ss := (NumericOperations.atom_correct _ _ _ _ _ _).trans
    ((NumericAtoms.membership_accepts_iff _ x X).trans (membershipAutomaton_correct x X t ns ss))

def equal (x y : Fin n) : NumericRecognition (b := b) (a := a) (m := m)
    (fun _ nodes _ => nodes x = nodes y) where
  program := NumericProgram.Program.atom (a,n,m) 2 x.val y.val 0 (by decide)
  correct t ns ss := (NumericOperations.atom_correct _ _ _ _ _ _).trans
    ((NumericAtoms.equality_accepts_iff _ x y).trans (equalityAutomaton_correct x y t ns ss))

def label (letter : Fin (a+1)) (x : Fin n) : NumericRecognition (b := b) (m := m)
    (fun tree nodes _ => tree (nodes x) = letter) where
  program := NumericProgram.Program.atom (a,n,m) 3 x.val letter.val 0 (by decide)
  correct t ns ss := (NumericOperations.atom_correct _ _ _ _ _ _).trans
    ((NumericAtoms.label_accepts_iff _ x letter).trans (labelAutomaton_correct letter x t ns ss))

def root (x : Fin n) : NumericRecognition (b := b) (a := a) (m := m)
    (fun _ nodes _ => nodes x = []) where
  program := NumericProgram.Program.atom (a,n,m) 4 x.val 0 0 (by decide)
  correct t ns ss := (NumericOperations.atom_correct _ _ _ _ _ _).trans
    ((NumericAtoms.root_accepts_iff _ x).trans (rootAutomaton_correct x t ns ss))

def successor (direction : Fin (b+1)) (x y : Fin n) : NumericRecognition (a := a) (m := m)
    (fun _ nodes _ => nodes y = nodes x ++ [direction]) where
  program := NumericProgram.Program.atom (a,n,m) 5 x.val y.val direction.val (by decide)
  correct t ns ss := (NumericOperations.atom_correct _ _ _ _ _ _).trans
    ((NumericAtoms.successor_accepts_iff _ x y direction).trans ((Recognition.successor direction x y).correct t ns ss))

def child (x y : Fin n) : NumericRecognition (b := b) (a := a) (m := m)
    (fun _ nodes _ => ∃ d : Fin (b+1), nodes y = nodes x ++ [d]) where
  program := NumericProgram.Program.atom (a,n,m) 6 x.val y.val 0 (by decide)
  correct t ns ss := (NumericOperations.atom_correct _ _ _ _ _ _).trans
    ((NumericAtoms.child_accepts_iff _ x y).trans ((Recognition.child x y).correct t ns ss))

def neg (h : NumericRecognition P) : NumericRecognition (fun t ns ss => ¬ P t ns ss) :=
  ⟨h.program.neg (a,n,m),fun t ns ss => (NumericOperations.neg_correct _ _ _).trans
    (not_congr (h.correct t ns ss))⟩

def conj (h : NumericRecognition P) (j : NumericRecognition Q) :
    NumericRecognition (fun t ns ss => P t ns ss ∧ Q t ns ss) :=
  ⟨h.program.conj (a,n,m) j.program,fun t ns ss => (NumericOperations.conj_correct _ _ _ _).trans
    (and_congr (h.correct t ns ss) (j.correct t ns ss))⟩

def impl (h : NumericRecognition P) (j : NumericRecognition Q) :
    NumericRecognition (fun t ns ss => P t ns ss → Q t ns ss) :=
  (h.conj j.neg).neg.congr (fun _ _ _ => by tauto)

def existsSet {P : ValuationPredicate (Fin (b+1)) (Fin (a+1)) n (m+1)} (h : NumericRecognition P) :
    NumericRecognition (fun t ns ss => ∃ X, P t ns (Fin.snoc ss X)) where
  program := h.program.project (a,n,m+1) n m
    (FiniteFunctionCoding.encode (id : Fin n → Fin n)) (FiniteFunctionCoding.encode (Fin.castSucc : Fin m → Fin (m+1)))
  correct := by
    intro tree nodes sets
    refine (NumericOperations.project_correct (b := b+1) (a := a) h.program.data
      (id : Fin n → Fin n) (Fin.castSucc : Fin m → Fin (m+1)) (encode tree nodes sets)).trans ?_
    change (∃ lifted, dropSet ∘ lifted = encode tree nodes sets ∧ _) ↔ _
    constructor
    · rintro ⟨lifted,labels,accepts⟩
      obtain ⟨X,rfl⟩ := (dropSet_eq_encode_iff tree nodes sets lifted).mp labels
      exact ⟨X,(h.correct tree nodes (Fin.snoc sets X)).mp accepts⟩
    · rintro ⟨X,satisfies⟩
      exact ⟨encode tree nodes (Fin.snoc sets X),dropSet_encode tree nodes sets X,
        (h.correct tree nodes (Fin.snoc sets X)).mpr satisfies⟩

def forallSet {P : ValuationPredicate (Fin (b+1)) (Fin (a+1)) n (m+1)} (h : NumericRecognition P) :
    NumericRecognition (fun t ns ss => ∀ X, P t ns (Fin.snoc ss X)) :=
  h.neg.existsSet.neg.congr (fun _ _ _ => by simp)

def existsNode {P : ValuationPredicate (Fin (b+1)) (Fin (a+1)) (n+1) m} (h : NumericRecognition P) :
    NumericRecognition (fun t ns ss => ∃ x, P t (Fin.snoc ns x) ss) where
  program := (h.program.conj (a,n+1,m) (NumericProgram.Program.atom (a,n+1,m) 7 n 0 0 (by decide))).project
    (a,n+1,m) n m (FiniteFunctionCoding.encode (Fin.castSucc : Fin n → Fin (n+1)))
    (FiniteFunctionCoding.encode (id : Fin m → Fin m))
  correct := by
    intro tree nodes sets
    refine (NumericOperations.project_correct (b := b+1) (a := a)
      (NumericOperations.conj (b+1) (a,n+1,m) h.program.data (NumericOperations.atom (b+1) (a,n+1,m) 7 n 0 0))
      (Fin.castSucc : Fin n → Fin (n+1)) (id : Fin m → Fin m) (encode tree nodes sets)).trans ?_
    change (∃ lifted, dropNode ∘ lifted = encode tree nodes sets ∧ _) ↔ _
    constructor
    · rintro ⟨lifted,labels,accepts⟩
      obtain ⟨body,single⟩ := (NumericOperations.conj_correct _ _ _ _).mp accepts
      have hs := (NumericOperations.atom_correct _ _ _ _ _ _).mp single
      have marker := TreeSingleton.accepts_iff.mp ((NumericAtoms.singleton_accepts_iff lifted (Fin.last n)).mp hs)
      obtain ⟨x,rfl⟩ := (dropNode_eq_encode_iff tree nodes sets lifted).mp ⟨labels,marker⟩
      exact ⟨x,(h.correct tree _ sets).mp body⟩
    · rintro ⟨x,body⟩
      refine ⟨encode tree (Fin.snoc nodes x) sets,dropNode_encode tree nodes sets x,?_⟩
      apply (NumericOperations.conj_correct _ _ _ _).mpr
      refine ⟨(h.correct tree _ sets).mpr body,?_⟩
      apply (NumericOperations.atom_correct _ _ _ _ _ _).mpr
      apply (NumericAtoms.singleton_accepts_iff _ (Fin.last n)).mpr
      apply TreeSingleton.accepts_iff.mpr
      exact ((dropNode_eq_encode_iff tree nodes sets _).mpr ⟨x,rfl⟩).2

def forallNode {P : ValuationPredicate (Fin (b+1)) (Fin (a+1)) (n+1) m} (h : NumericRecognition P) :
    NumericRecognition (fun t ns ss => ∀ x, P t (Fin.snoc ns x) ss) :=
  h.neg.existsNode.neg.congr (fun _ _ _ => by simp)

end NumericRecognition
end DistributedSynthesis.MSO.Tree
