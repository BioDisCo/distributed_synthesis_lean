/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Logic.MSO.Recognizability
import DistributedSynthesis.Library.Automata.TreeComputable

/-! # Executable recognition of MSO valuation predicates

Unlike the proposition `Recognizable`, this structure retains the constructed
finite automaton and its transition deciders as data. Correctness is a proof
field and is erased by compilation.
-/
namespace DistributedSynthesis.MSO.Tree

variable {Branch Alphabet : Type*} {n m k l : Nat}

structure Recognition (P : ValuationPredicate Branch Alphabet n m) where
  data : TreeAutomatonData Branch (ValuationLabel Alphabet n m)
  correct : ∀ tree nodes sets, data.Accepts (encode tree nodes sets) ↔ P tree nodes sets

namespace Recognition
variable {P Q : ValuationPredicate Branch Alphabet n m}

def congr (h : Recognition P) (same : ∀ tree nodes sets, P tree nodes sets ↔ Q tree nodes sets) :
    Recognition Q := ⟨h.data,fun tree nodes sets => (h.correct tree nodes sets).trans (same tree nodes sets)⟩

def rename (h : Recognition P) (f : Fin n → Fin k) (g : Fin m → Fin l) :
    Recognition (fun tree nodes sets => P tree (nodes ∘ f) (sets ∘ g)) :=
  ⟨h.data.comap (renameMarkers f g),fun tree nodes sets => h.correct tree _ _⟩

def falsum : Recognition (Branch := Branch) (Alphabet := Alphabet) (n := n) (m := m)
    (fun _ _ _ => False) :=
  ⟨⟨falseAutomaton,inferInstanceAs (DecidableEq Unit),fun _ _ _ => inferInstanceAs (Decidable False)⟩,falseAutomaton_correct⟩

def membership (x : Fin n) (X : Fin m) : Recognition (Branch := Branch) (Alphabet := Alphabet)
    (fun tree nodes sets => Realize tree (.mem x X) nodes sets) :=
  ⟨⟨membershipAutomaton x X,inferInstanceAs (DecidableEq Unit),fun _ a _ => inferInstanceAs (Decidable (a.2.1 x = true → a.2.2 X = true))⟩,
    membershipAutomaton_correct x X⟩

def equal (x y : Fin n) : Recognition (Branch := Branch) (Alphabet := Alphabet) (m := m)
    (fun _ nodes _ => nodes x = nodes y) :=
  ⟨⟨equalityAutomaton x y,inferInstanceAs (DecidableEq Unit),fun _ a _ => inferInstanceAs (Decidable (a.2.1 x = a.2.1 y))⟩,
    equalityAutomaton_correct x y⟩

variable [Fintype Branch] [DecidableEq Branch] [Nonempty Branch]
variable [Fintype Alphabet] [DecidableEq Alphabet]

def label (letter : Alphabet) (x : Fin n) : Recognition (Branch := Branch) (m := m)
    (fun tree nodes _ => tree (nodes x) = letter) :=
  ⟨⟨labelAutomaton letter x,inferInstanceAs (DecidableEq Unit),fun _ a _ => inferInstanceAs (Decidable (a.2.1 x = true → a.1 = letter))⟩,
    labelAutomaton_correct letter x⟩

def root (x : Fin n) : Recognition (Branch := Branch) (Alphabet := Alphabet) (m := m)
    (fun _ nodes _ => nodes x = []) where
  data := ⟨rootAutomaton x,inferInstanceAs (DecidableEq Bool),fun (q : Bool) a (next : Branch → Bool) =>
    inferInstanceAs (Decidable ((q = true → a.2.1 x = true) ∧ ∀ b, next b = false))⟩
  correct := rootAutomaton_correct x

def successor (direction : Branch) (x y : Fin n) :
    Recognition (Branch := Branch) (Alphabet := Alphabet) (m := m)
      (fun _ nodes _ => nodes y = nodes x ++ [direction]) where
  data := ⟨RunParityTreeAutomaton.edgeTest (fun a => a.2.1 x) (fun a => a.2.1 y) direction,
    inferInstanceAs (DecidableEq Bool),fun (q : Bool) a (next : Branch → Bool) => inferInstanceAs
      (Decidable (a.2.1 y = q ∧ ∀ b, next b = (a.2.1 x && decide (b = direction))))⟩
  correct := by
    have same : RunParityTreeAutomaton.edgeTest (fun a : ValuationLabel Alphabet n m => a.2.1 x)
        (fun a => a.2.1 y) direction = successorAutomaton direction x y := by
      unfold successorAutomaton
      congr 1
      exact Subsingleton.elim _ _
    intro tree nodes sets
    change (RunParityTreeAutomaton.edgeTest _ _ _).acceptsTree _ ↔ _
    rw [same]
    exact successorAutomaton_correct direction x y tree nodes sets

def neg (h : Recognition P) : Recognition (fun tree nodes sets => ¬ P tree nodes sets) :=
  ⟨h.data.complement,fun tree nodes sets =>
    (TreeAutomatonData.complement_correct h.data _).trans (not_congr (h.correct tree nodes sets))⟩

def conj (hP : Recognition P) (hQ : Recognition Q) :
    Recognition (fun tree nodes sets => P tree nodes sets ∧ Q tree nodes sets) :=
  ⟨hP.data.inter hQ.data,fun tree nodes sets =>
    (TreeAutomatonData.inter_correct _ _ _).trans (and_congr (hP.correct tree nodes sets) (hQ.correct tree nodes sets))⟩

def impl (hP : Recognition P) (hQ : Recognition Q) :
    Recognition (fun tree nodes sets => P tree nodes sets → Q tree nodes sets) :=
  (hP.conj hQ.neg).neg.congr (fun _ _ _ => by tauto)

def existsSet {P : ValuationPredicate Branch Alphabet n (m+1)} (h : Recognition P) :
    Recognition (fun tree nodes sets => ∃ X, P tree nodes (Fin.snoc sets X)) where
  data := h.data.project dropSet
  correct := by
    intro tree nodes sets
    change (h.data.toAutomaton.project dropSet).acceptsTree _ ↔ _
    rw [RunParityTreeAutomaton.project_acceptsTree_iff]
    constructor
    · rintro ⟨lifted,labels,accepts⟩
      obtain ⟨X,rfl⟩ := (dropSet_eq_encode_iff tree nodes sets lifted).mp labels
      exact ⟨X,(h.correct tree nodes (Fin.snoc sets X)).mp accepts⟩
    · rintro ⟨X,satisfies⟩
      exact ⟨encode tree nodes (Fin.snoc sets X),dropSet_encode tree nodes sets X,
        (h.correct tree nodes (Fin.snoc sets X)).mpr satisfies⟩

def forallSet {P : ValuationPredicate Branch Alphabet n (m+1)} (h : Recognition P) :
    Recognition (fun tree nodes sets => ∀ X, P tree nodes (Fin.snoc sets X)) :=
  h.neg.existsSet.neg.congr (fun _ _ _ => by simp)

def singletonData (marked : ValuationLabel Alphabet n m → Bool) :
    TreeAutomatonData Branch (ValuationLabel Alphabet n m) where
  toAutomaton := TreeSingleton.automaton marked
  stateDecidableEq := inferInstanceAs (DecidableEq Bool)
  deltaDecidable := fun (q : Bool) a (next : Branch → Bool) => by
    change Decidable (if q then _ else _)
    split <;> infer_instance

def existsNode {P : ValuationPredicate Branch Alphabet (n+1) m} (h : Recognition P) :
    Recognition (fun tree nodes sets => ∃ x, P tree (Fin.snoc nodes x) sets) where
  data := (h.data.inter (singletonData (fun a => a.2.1 (Fin.last n)))).project dropNode
  correct := by
    intro tree nodes sets
    change (RunParityTreeAutomaton.project _ dropNode).acceptsTree _ ↔ _
    rw [RunParityTreeAutomaton.project_acceptsTree_iff]
    constructor
    · rintro ⟨lifted,labels,accepts⟩
      obtain ⟨body,single⟩ := (TreeAutomatonData.inter_correct _ _ lifted).mp accepts
      have marker := TreeSingleton.accepts_iff.mp single
      obtain ⟨x,rfl⟩ := (dropNode_eq_encode_iff tree nodes sets lifted).mp ⟨labels,marker⟩
      exact ⟨x,(h.correct tree _ sets).mp body⟩
    · rintro ⟨x,body⟩
      refine ⟨encode tree (Fin.snoc nodes x) sets,dropNode_encode tree nodes sets x,?_⟩
      apply (TreeAutomatonData.inter_correct _ _ _).mpr
      refine ⟨(h.correct tree _ sets).mpr body,TreeSingleton.accepts_iff.mpr ?_⟩
      exact ((dropNode_eq_encode_iff tree nodes sets _).mpr ⟨x,rfl⟩).2

def forallNode {P : ValuationPredicate Branch Alphabet (n+1) m} (h : Recognition P) :
    Recognition (fun tree nodes sets => ∀ x, P tree (Fin.snoc nodes x) sets) :=
  h.neg.existsNode.neg.congr (fun _ _ _ => by simp)

/-- Exactly one child of the source is marked as the target. Direction is
chosen in the finite transition relation, without choosing an enumeration. -/
def childData (x y : Fin n) : TreeAutomatonData Branch (ValuationLabel Alphabet n m) where
  toAutomaton := {
    State := Bool
    stateFinite := inferInstance
    initial := false
    delta q a next := a.2.1 y = q ∧
      (if a.2.1 x then ∃ d : Branch, ∀ b, next b = decide (b = d) else ∀ b, next b = false)
    priority _ := 0 }
  stateDecidableEq := inferInstance
  deltaDecidable q a next := by
    change Decidable (_ ∧ (if _ then _ else _))
    split <;> infer_instance

def child (x y : Fin n) : Recognition (Branch := Branch) (Alphabet := Alphabet) (m := m)
    (fun _ nodes _ => ∃ b : Branch, nodes y = nodes x ++ [b]) where
  data := childData x y
  correct := by
    intro tree nodes sets
    classical
    constructor
    · rintro ⟨run,⟨_,step⟩,_⟩
      have atSource := (step (nodes x)).2
      simp only [encode, decide_true, ↓reduceIte] at atSource
      obtain ⟨direction,children⟩ := atSource
      have hit := (step (nodes x ++ [direction])).1
      rw [children direction] at hit
      exact ⟨direction,(by simpa [encode] using hit : nodes x ++ [direction] = nodes y).symm⟩
    · rintro ⟨direction,equation⟩
      refine ⟨fun node => decide (node = nodes y),⟨?_,?_⟩,fun _ => ?_⟩
      · change decide ([] = nodes y) = false
        simp [equation]
      · intro node
        refine ⟨by simp [encode],?_⟩
        simp only [encode]
        by_cases h : node = nodes x
        · subst node
          simp only [decide_true, ↓reduceIte]
          refine ⟨direction,fun b => ?_⟩
          simp [equation]
        · simp only [h,decide_false,Bool.false_eq_true,↓reduceIte]
          intro b
          simp only [decide_eq_false_iff_not]
          intro same
          rw [equation] at same
          have lengths := congrArg List.length same
          simp only [List.length_append,List.length_singleton] at lengths
          exact h (List.append_inj_left same (by omega))
      · exact ⟨0,⟨0,rfl⟩,fun n => ⟨n,le_rfl,rfl⟩,fun _ _ => Nat.zero_le _⟩

end Recognition
end DistributedSynthesis.MSO.Tree
