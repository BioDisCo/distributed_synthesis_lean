/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Formalizations.ComponentTrees.FinitePositions
import DistributedSynthesis.Formalizations.ComponentTrees.FiniteRunMSO

/-! The finite letters record bounded positions, reductions, distributed
block rules, and every full successor component with its numbering.
Numbered copies of isomorphic positions may coexist; local transport starts
at the concrete initial position. No reachable-history enumeration is used.
-/
namespace Characterisation.ComponentTrees.FiniteAlphabet
open DistributedSynthesis Characterisation Characterisation.PeriodicBlocks
open Characterisation.ComponentGames
open scoped Characterisation.ComponentGames.Representation DistributedSynthesis.FiniteOrders
open scoped Characterisation.ComponentGames.FiniteEnumeration
open scoped Characterisation.ComponentGames.Representation.FiniteArena
set_option maxHeartbeats 1800000
set_option linter.unusedSectionVars false
variable {I₁ I₂ O₁ O₂ : Type} {D capacity : Nat}
variable [Fintype I₁] [Fintype I₂] [DecidableEq I₁] [DecidableEq I₂]
variable [Fintype O₁] [Fintype O₂] [DecidableEq O₁] [DecidableEq O₂]
variable (B : DetParityAutomaton (BlockWord (ContinuationLetter I₁ I₂ O₁ O₂) D))
variable [DecidableEq B.State]
variable (live : B.State → Bool) (bound : Nat)

abbrev Move := Representation.FiniteArena.Move I₁ I₂ O₁ O₂ Unit B.State D capacity
abbrev Child (m : Move (capacity:=capacity) B) :=
  (P : FinitePositions.Position B.State capacity) × (P.Root → m.End)
abbrev Raw := (m : Move (capacity:=capacity) B) × (Fin capacity → Option (Child B m))
abbrev Edge := (P : FinitePositions.Position B.State capacity) × P.Root

instance moveDecidableEq : DecidableEq (Move (capacity:=capacity) B) := by
  unfold Move Representation.FiniteArena.Move
  infer_instance

instance childDecidableEq (m : Move (capacity:=capacity) B) : DecidableEq (Child B m) := by
  unfold Child
  infer_instance

instance childFintype (m : Move (capacity:=capacity) B) : Fintype (Child B m) := by
  unfold Child
  infer_instance

instance rawDecidableEq : DecidableEq (Raw (capacity:=capacity) B) := by
  unfold Raw
  infer_instance

def endState (m : Move (capacity:=capacity) B) (e : m.End) : B.State :=
  blockSuccessor B m.source.2.state m.rule e

def liveEnd (m : Move (capacity:=capacity) B) (e : m.End) : Bool :=
  decide (m.replacement (closingLayerRoot D e) = closingLayerRoot D e) && live (endState B m e)

def Component (m : Move (capacity:=capacity) B) (K : Finset m.End) : Prop :=
  ∃ anchor, liveEnd B live m anchor = true ∧ ∀ e,
    e ∈ K ↔ closingComponentMask (closingLayerShape m.source.2.shape D) (liveEnd B live m) anchor e = true

instance componentDecidable (m : Move (capacity:=capacity) B) (K : Finset m.End) :
    Decidable (Component B live m K) := by
  unfold Component
  infer_instance

def childEdges (m : Move (capacity:=capacity) B) (c : Child B m) : Finset m.End :=
  Finset.univ.image c.2

/-- The numbering is bijective onto one entire component and preserves
both owner-view equalities and every successor state. -/
def ChildCorrect (m : Move (capacity:=capacity) B) (c : Child B m) : Prop :=
  Function.Injective c.2 ∧ Component B live m (childEdges B m c) ∧
  (∀ p h k, c.1.2.shape p h k = closingLayerShape m.source.2.shape D p (c.2 h) (c.2 k)) ∧
  ∀ h, c.1.2.state h = endState B m (c.2 h)

instance childCorrectDecidable (m : Move (capacity:=capacity) B) (c : Child B m) :
    Decidable (ChildCorrect B live m c) := by
  unfold ChildCorrect Function.Injective
  infer_instance

/-- Unused directions are padding. Each full component appears exactly
once, and the same reduction and block rule serve every direction. -/
def Legal (raw : Raw (capacity:=capacity) B) : Prop :=
  0 < raw.1.source.1.val ∧
  (∀ h, live (raw.1.source.2.state h) = true) ∧
  FinitePositions.ReductionChecks raw.1.source.2 bound raw.1.replacement ∧
  ClosingPolicyCoherent raw.1.source.2.shape raw.1.rule ∧
  (∀ d c, raw.2 d = some c → ChildCorrect B live raw.1 c) ∧
  (∀ K, Component B live raw.1 K → ∃ d c, raw.2 d = some c ∧ childEdges B raw.1 c = K) ∧
  ∀ d c f e, raw.2 d = some c → raw.2 f = some e →
    childEdges B raw.1 c = childEdges B raw.1 e → d = f

instance legalDecidable (raw : Raw (capacity:=capacity) B) : Decidable (Legal B live bound raw) := by
  letI : Decidable (FinitePositions.ReductionChecks raw.1.source.2 bound raw.1.replacement) := inferInstance
  letI : Decidable (ClosingPolicyCoherent raw.1.source.2.shape raw.1.rule) := inferInstance
  letI : Decidable (∀ d c, raw.2 d = some c → ChildCorrect B live raw.1 c) := inferInstance
  letI : Decidable (∀ K, Component B live raw.1 K → ∃ d c, raw.2 d = some c ∧ childEdges B raw.1 c = K) := inferInstance
  letI : Decidable (∀ d c f e, raw.2 d = some c → raw.2 f = some e →
    childEdges B raw.1 c = childEdges B raw.1 e → d = f) := inferInstance
  unfold Legal
  infer_instance

abbrev Letter := Option { raw : Raw (capacity:=capacity) B // Legal B live bound raw }

instance letterFintype : Fintype (Letter (capacity:=capacity) B live bound) := inferInstance
instance letterDecidableEq : DecidableEq (Letter (capacity:=capacity) B live bound) := inferInstance
instance edgeFintype : Fintype (Edge (capacity:=capacity) B) := inferInstance
instance edgeDecidableEq : DecidableEq (Edge (capacity:=capacity) B) := inferInstance

def initialPosition (positive : 0 < capacity) : FinitePositions.Position B.State capacity :=
  ⟨⟨1,by omega⟩,⟨fun _ _ _ => true,fun _ => (),fun _ => B.initial⟩⟩

def initialEdge (positive : 0 < capacity) : Edge (capacity:=capacity) B :=
  ⟨initialPosition B positive,⟨0,by change 0 < 1; omega⟩⟩

def rootTest (positive : 0 < capacity) : Letter (capacity:=capacity) B live bound → Bool
  | none => false
  | some a => decide (a.val.1.source = initialPosition B positive)

def childTest : Letter (capacity:=capacity) B live bound → Fin capacity →
    Letter (capacity:=capacity) B live bound → Bool
  | none, _, next => decide (next = none)
  | some a, d, next => match a.val.2 d, next with
    | none, none => true
    | some c, some b => decide (b.val.1.source = c.1)
    | _, _ => false

def edgeTest : Letter (capacity:=capacity) B live bound → Edge (capacity:=capacity) B → Bool
  | none, _ => false
  | some a, e => decide (e.1 = a.val.1.source)

def Step (a : { raw : Raw (capacity:=capacity) B // Legal B live bound raw })
    (d : Fin capacity) (e f : Edge (capacity:=capacity) B) : Prop :=
  ∃ h : a.val.1.source.Root, e = ⟨a.val.1.source,h⟩ ∧
    ∃ c : Child B a.val.1, a.val.2 d = some c ∧
      ∃ k : c.1.Root, f = ⟨c.1,k⟩ ∧
        closingLayerRoot D (c.2 k) = a.val.1.replacement h

instance stepDecidable (a : { raw : Raw (capacity:=capacity) B // Legal B live bound raw })
    (d : Fin capacity) (e f : Edge (capacity:=capacity) B) : Decidable (Step B live bound a d e f) := by
  unfold Step
  infer_instance

def stepTest : Letter (capacity:=capacity) B live bound → Fin capacity →
    Edge (capacity:=capacity) B → Edge (capacity:=capacity) B → Bool
  | none, _, _, _ => false
  | some a, d, e, f => decide (Step B live bound a d e f)

def tables (positive : 0 < capacity) :
    FiniteRunMSO.Tables (Fin capacity) (Letter (capacity:=capacity) B live bound) (Edge (capacity:=capacity) B) where
  initial := initialEdge B positive
  root := rootTest B live bound positive
  child := childTest B live bound
  allowed := edgeTest B live bound
  step := stepTest B live bound
  priority _ e := B.priority (e.1.2.state e.2)

/-- The finite transition test omits only the witnessing block. Recovering
it uses the library's exact scenario/block equivalence. -/
theorem step_word (a : { raw : Raw (capacity:=capacity) B // Legal B live bound raw })
    (d : Fin capacity) (e f : Edge (capacity:=capacity) B) :
    Step B live bound a d e f ↔
      ∃ h : a.val.1.source.Root, e = ⟨a.val.1.source,h⟩ ∧
        ∃ c : Child B a.val.1, a.val.2 d = some c ∧
          ∃ k : c.1.Root, f = ⟨c.1,k⟩ ∧
            ∃ u : BlockInput I₁ I₂ D, c.2 k = wordScenario (a.val.1.replacement h) u := by
  constructor
  · rintro ⟨h,rfl,c,child,k,rfl,root⟩
    refine ⟨h,rfl,c,child,k,rfl,scenarioWord D (c.2 k),?_⟩
    rw [← root]
    exact (wordScenario_scenarioWord D (c.2 k)).symm
  · rintro ⟨h,rfl,c,child,k,rfl,u,endpoint⟩
    refine ⟨h,rfl,c,child,k,rfl,?_⟩
    rw [endpoint,wordScenario_root]



/-- The completed block transition, including its state, is the finite
step's meaning. The reduction preserves the incoming automaton state. -/
theorem step_state (a : { raw : Raw (capacity:=capacity) B // Legal B live bound raw })
    (d : Fin capacity) (e f : Edge (capacity:=capacity) B)
    (step : Step B live bound a d e f) :
    ∃ h : a.val.1.source.Root, e = ⟨a.val.1.source,h⟩ ∧
      ∃ u : BlockInput I₁ I₂ D,
        f.1.2.state f.2 = B.step (e.1.2.state e.2)
          (ruleBlock a.val.1.rule (wordScenario (a.val.1.replacement h) u)) := by
  obtain ⟨h,rfl,c,child,k,rfl,u,endpoint⟩ := (step_word B live bound a d e f).mp step
  have childCorrect := a.property.2.2.2.2.1 d c child
  have labels := childCorrect.2.2.2 k
  have preserves := a.property.2.2.1.2.2.1 h
  refine ⟨h,rfl,u,?_⟩
  rw [labels, endState, blockSuccessor, endpoint, wordScenario_root, preserves]

/-- Every live endpoint starts at a fixed point of the idempotent
reduction, so it lies in the image times the complete block alphabet. -/
theorem liveEnd_card (m : Move (capacity:=capacity) B)
    (small : (Finset.univ.image m.replacement).card ≤ bound) :
    (Finset.univ.filter (fun e : m.End => liveEnd B live m e = true)).card ≤
      bound * Nat.card (RoundRecord I₁ I₂ Graph Unit Unit) ^ D := by
  let kept := ((Finset.univ.image m.replacement) ×ˢ
    (Finset.univ : Finset (BlockInput I₁ I₂ D))).image (blockScenarioEquiv m.source.Root I₁ I₂ D)
  have subset : (Finset.univ.filter (fun e : m.End => liveEnd B live m e = true)) ⊆ kept := by
    intro e mem
    have both : decide (m.replacement (closingLayerRoot D e) = closingLayerRoot D e) = true ∧
        live (endState B m e) = true := by
      simpa only [liveEnd,Bool.and_eq_true] using (Finset.mem_filter.mp mem).2
    have fixed := of_decide_eq_true both.1
    exact Finset.mem_image.mpr ⟨(closingLayerRoot D e, scenarioWord D e),
      Finset.mem_product.mpr ⟨Finset.mem_image.mpr ⟨closingLayerRoot D e, Finset.mem_univ _, fixed⟩,
        Finset.mem_univ _⟩, wordScenario_scenarioWord D e⟩
  calc
    _ ≤ kept.card := Finset.card_le_card subset
    _ ≤ (Finset.univ.image m.replacement).card * Fintype.card (BlockInput I₁ I₂ D) := by
      exact Finset.card_image_le.trans (by rw [Finset.card_product,Finset.card_univ])
    _ ≤ bound * Nat.card (RoundRecord I₁ I₂ Graph Unit Unit) ^ D := by
      rw [← Nat.card_eq_fintype_card, blockWord_card]
      exact Nat.mul_le_mul_right _ small

theorem component_card (m : Move (capacity:=capacity) B) (K : Finset m.End)
    (component : Component B live m K) (small : (Finset.univ.image m.replacement).card ≤ bound) :
    K.card ≤ bound * Nat.card (RoundRecord I₁ I₂ Graph Unit Unit) ^ D := by
  apply (Finset.card_le_card (t := Finset.univ.filter (fun e : m.End => liveEnd B live m e = true)) ?_).trans
    (liveEnd_card B live bound m small)
  intro e mem
  obtain ⟨anchor,_,members⟩ := component
  have reachable := (members e).mp mem
  simp only [closingComponentMask,Bool.and_eq_true] at reachable
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, reachable.1⟩

theorem padding_has_no_run (positive : 0 < capacity)
    (tree : LabeledTree (Fin capacity) (Letter (capacity:=capacity) B live bound))
    (branch : Nat → Fin capacity) (edges : Nat → Edge (capacity:=capacity) B)
    (run : FiniteRunMSO.Run (tables B live bound positive) tree branch edges) (n : Nat) :
    tree (branchNode branch n) ≠ none := by
  intro padding
  have allowed := run.2.1 n
  change edgeTest B live bound (tree (branchNode branch n)) (edges n) = true at allowed
  rw [padding] at allowed
  contradiction

section Ordered
variable [LinearOrder I₁] [LinearOrder I₂] [LinearOrder O₁] [LinearOrder O₂]
variable [LinearOrder B.State]

instance letterOrder : LinearOrder (Letter (capacity:=capacity) B live bound) := by
  unfold Letter Raw Move Representation.FiniteArena.Move Child
  infer_instance

instance edgeOrder : LinearOrder (Edge (capacity:=capacity) B) := by
  unfold Edge
  infer_instance

/-- The finite edge numbering is computed by sorting the existing carrier. -/
def edgeIndex : Edge (capacity:=capacity) B ≃ Fin (Fintype.card (Edge (capacity:=capacity) B)) :=
  (monoEquivOfFin (Edge (capacity:=capacity) B) rfl).toEquiv.symm

/-- The concrete syntax produced from the bounded letter data. The model/tree
correspondence is proved separately in `ModelEquivalence`. -/
def sentence (positive : 0 < capacity) :
    MSO.Sentence (MSO.Tree.language (Fin capacity) (Letter (capacity:=capacity) B live bound)) :=
  letI : Nonempty (Fin capacity) := ⟨⟨0,positive⟩⟩
  FiniteRunMSO.acceptanceFormula (tables B live bound positive) (edgeIndex B)

/-- Exact semantics for the finite letters. `ModelEquivalence` relates these
finite models to concrete compressed component trees. -/
theorem sentence_correct (positive : 0 < capacity)
    (tree : LabeledTree (Fin capacity) (Letter (capacity:=capacity) B live bound)) :
    MSO.Tree.Satisfies tree (sentence B live bound positive) ↔
      FiniteRunMSO.Accepting (tables B live bound positive) tree := by
  letI : Nonempty (Fin capacity) := ⟨⟨0,positive⟩⟩
  exact FiniteRunMSO.acceptanceFormula_correct (tables B live bound positive) (edgeIndex B) tree


/-- Executable decision of the finite-letter language.
`finite_satisfiable_correct` connects this test to concrete compressed trees. -/
def satisfiable (positive : 0 < capacity) : Bool :=
  letI : Inhabited (Fin capacity) := ⟨⟨0,positive⟩⟩
  MSO.Tree.Executable.satisfiable (sentence B live bound positive)

theorem satisfiable_correct (positive : 0 < capacity) :
    satisfiable B live bound positive = true ↔
      ∃ tree, FiniteRunMSO.Accepting (tables B live bound positive) tree := by
  letI : Inhabited (Fin capacity) := ⟨⟨0,positive⟩⟩
  rw [satisfiable,MSO.Tree.Executable.satisfiable_correct]
  exact exists_congr (sentence_correct B live bound positive)

end Ordered
end Characterisation.ComponentTrees.FiniteAlphabet
