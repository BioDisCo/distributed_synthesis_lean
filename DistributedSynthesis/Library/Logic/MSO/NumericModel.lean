/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Logic.MSO.PrimitiveRecursive
import DistributedSynthesis.Library.Automata.FiniteController

/-! Extract an actual finite model generator from the existing numeric
MSO compiler and finite-policy search. Neither a model nor a winning policy
is supplied as input. -/
namespace DistributedSynthesis.MSO.Tree.NumericModel
open scoped DistributedSynthesis.FiniteOrders
open EncodedProjectedTree
set_option maxHeartbeats 2400000
variable {b a : Nat}
variable (φ : Sentence (language (Fin (b+1)) (Fin (a+1))))

def data := Numeric.compile (Numeric.formulaInput φ)
def monitor := EncodedTreeNonemptiness.monitor (monitorData (data φ))

instance stateOrder : LinearOrder (monitor φ).State := inferInstanceAs (LinearOrder (Fin _))

/-- The finite table of labels, one per monitor state, is the generator.
Its successors are the existing monitor transitions for each direction. -/
def extract := FiniteController.extract (monitor φ)

def decodeLetter (k : Fin (NumericValuations.count (a,0,0)-1+1)) : Fin (a+1) :=
  ⟨NumericValuations.base (a,0,0) k.val % (a+1),Nat.mod_lt _ (Nat.succ_pos _)⟩

theorem decodeLetter_correct (k : Fin (NumericValuations.count (a,0,0)-1+1)) :
    decodeLetter k = ((NumericValuations.number (a,0,0)).symm k).1 := by
  obtain ⟨label,rfl⟩ := (NumericValuations.number (a,0,0)).surjective k
  rw [Equiv.symm_apply_apply]
  apply Fin.ext
  change NumericValuations.base (a,0,0) (NumericValuations.equiv (a,0,0) label).val % (a+1) = label.1.val
  rw [NumericValuations.base_encode]
  exact Nat.mod_eq_of_lt label.1.isLt

def model (policy : (monitor φ).State → Fin (EncodedTreeNonemptiness.labels (monitorData (data φ)))) :
    LabeledTree (Fin (b+1)) (Fin (a+1)) :=
  fun address => decodeLetter
    (letter (data φ) (FiniteController.tree (monitor φ) policy address))

theorem model_correct (policy : (monitor φ).State → Fin (EncodedTreeNonemptiness.labels (monitorData (data φ))))
    (found : extract φ = some policy) : Satisfies (model φ policy) φ := by
  have winning := FiniteController.extracted_tree_wins (monitor φ) policy found
  have accepts := ((monitor φ).acceptsTree_iff_winningTree _).mpr winning
  have projected : (automaton (data φ)).acceptsTree (letter (data φ) ∘ FiniteController.tree (monitor φ) policy) :=
    (accepts_iff (data φ) _).mpr ⟨_,rfl,accepts⟩
  apply (Numeric.compile_correct φ (model φ policy) Fin.elim0 Fin.elim0).mp
  have labels := Numeric.sentence_labels (a:=a) (b:=b) (letter (data φ) ∘ FiniteController.tree (monitor φ) policy)
  have same : model φ policy = fun p => ((NumericValuations.number (a,0,0)).symm
      ((letter (data φ) ∘ FiniteController.tree (monitor φ) policy) p)).1 :=
    funext (fun p => decodeLetter_correct _)
  rw [same]
  exact (congrArg (fun t => (automaton (data φ)).acceptsTree t) labels).mpr projected

theorem extract_complete : (∃ policy, extract φ = some policy) ↔ ∃ tree, Satisfies tree φ := by
  rw [extract,FiniteController.extract_complete]
  have equivalence : (∃ tree, (monitor φ).WinningTree tree) ↔
      ∃ tree, (automaton (data φ)).acceptsTree tree := by
    constructor
    · rintro ⟨tree,winning⟩
      exact ⟨letter (data φ) ∘ tree,(accepts_iff (data φ) _).mpr
        ⟨tree,rfl,((monitor φ).acceptsTree_iff_winningTree tree).mpr winning⟩⟩
    · rintro ⟨tree,accepting⟩
      obtain ⟨annotated,_,accepted⟩ := (accepts_iff (data φ) tree).mp accepting
      exact ⟨annotated,((monitor φ).acceptsTree_iff_winningTree annotated).mp accepted⟩
  exact equivalence.trans (Numeric.nonempty_correct φ)

end DistributedSynthesis.MSO.Tree.NumericModel
