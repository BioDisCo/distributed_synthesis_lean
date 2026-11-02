/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderPhases.ActiveRootBundles

/-! A window at the phase origin checks every positive offset up to D.
A later window checks only its last offset. This finite rule selects exactly
max(a,b-D) at a handover of physical depth b; it never changes physical time. -/
namespace Characterisation
open DistributedSynthesis

def closingWindowScheduled (initial : Bool) (D n : Nat) : Bool :=
  initial || decide (n = D)

theorem closingWindowScheduled_iff (a L b D : Nat)
    (before : a ≤ L) (positive : L < b) (bounded : b-L ≤ D) :
    closingWindowScheduled (decide (L = a)) D (b-L) = true ↔ L = max a (b-D) := by
  simp only [closingWindowScheduled,Bool.or_eq_true,decide_eq_true_eq]
  omega

/-- Every handover is assigned to one window already started in its phase.
The initial window handles short phases; a later window has age exactly D. -/
theorem canonical_closing_window_unique (a b D : Nat) (positive : a < b) (horizon : 0 < D) :
    ∃! L, a ≤ L ∧ L < b ∧ b-L ≤ D ∧
      closingWindowScheduled (decide (L = a)) D (b-L) = true := by
  refine ⟨max a (b-D),⟨by omega,by omega,by omega,?_⟩,?_⟩
  · apply (closingWindowScheduled_iff a _ b D (by omega) (by omega) (by omega)).mpr rfl
  · intro L h
    exact (closingWindowScheduled_iff a L b D h.1 h.2.1 h.2.2.1).mp h.2.2.2

/-- The test needs only the initial-window bit and the bounded window age. -/
theorem closingWindowScheduled_later (D n : Nat) :
    closingWindowScheduled false D n = true ↔ n = D := by
  simp [closingWindowScheduled]

/-- Keep every original boundary root, followed by the common word already
read when this window is launched. No future endpoint occurs in this definition. -/
def carriedBoundarySources {I₁ I₂ : Type} (P : List Graph → Prop)
    (u word : EnvHistory I₁ I₂) : InputHistoryComponent P u → EnvHistory I₁ I₂ :=
  fun s => s.val ++ word

theorem carriedBoundarySources_depth {I₁ I₂ : Type} (P : List Graph → Prop)
    (u word : EnvHistory I₁ I₂) (s : InputHistoryComponent P u) :
    List.length (carriedBoundarySources P u word s) = List.length u + List.length word := by
  have len := inputConnected_length P s.property
  simp only [carriedBoundarySources,List.length_append,← len]

theorem carriedBoundarySources_injective {I₁ I₂ : Type} (P : List Graph → Prop)
    (u word : EnvHistory I₁ I₂) : Function.Injective (carriedBoundarySources P u word) := by
  intro s t eq
  exact Subtype.ext (List.append_cancel_right eq)

/-- The canonical schedule supplies complete target coverage from the
carried full boundary family. Coverage is a conclusion, not a premise. -/
theorem scheduled_boundary_coverage {I₁ I₂ : Type}
    (P : List Graph → Prop) (closed : PrefixClosed P) (d : Nat)
    (recent : ∀ g, P g → ∃ p, RecentOther P d g p)
    (u word : EnvHistory I₁ I₂) (n : Nat) (positive : 0 < n) (bounded : n ≤ d+1)
    (scheduled : closingWindowScheduled (decide (List.length word = 0)) (d+1) n = true)
    (root : ClosingLayer (InputHistoryComponent P u) I₁ I₂ n)
    (live : P (History.graphSequence (closingLayerHistory (carriedBoundarySources P u word) n root)))
    (phase : ConsecutiveLeaderBoundaries P d
      (closingLayerHistory (carriedBoundarySources P u word) n root) (List.length u)) :
    ∀ k, InputConnected P (closingLayerHistory (carriedBoundarySources P u word) n root) k →
      ∃ s, closingLayerHistory (carriedBoundarySources P u word) n s = k := by
  let past := carriedBoundarySources P u word
  let h := closingLayerHistory past n root
  let a := List.length u
  let L := List.length u + List.length word
  have depth : ∀ s, List.length (past s) = L := carriedBoundarySources_depth P u word
  have len : List.length h = L+n := closingLayerHistory_length past L depth n root
  have cut : phaseClosingCut d h a = L := by
    have rule : L = a ∨ n = d+1 := by
      simpa only [closingWindowScheduled,Bool.or_eq_true,decide_eq_true_eq,
        L,a,Nat.add_eq_left] using scheduled
    unfold phaseClosingCut
    rw [len]
    dsimp [L,a] at *
    omega
  have rootLen : List.length (closingLayerRoot n root).val = a :=
    (inputConnected_length P (closingLayerRoot n root).property).symm
  have takeL : h.take L = past (closingLayerRoot n root) := closingLayerHistory_take_source past L depth n root
  have takeA : h.take a = (closingLayerRoot n root).val := by
    have eq := congrArg (List.take a) takeL
    rw [List.take_take,min_eq_left (show a ≤ L by dsimp [a,L]; omega)] at eq
    rw [eq]
    change ((closingLayerRoot n root).val ++ word).take a = _
    rw [← rootLen,List.take_left]
  have common : boundaryPhaseWord d h a = word := by
    rw [boundaryPhaseWord,cut,takeL]
    change ((closingLayerRoot n root).val ++ word).drop a = word
    rw [← rootLen,List.drop_left]
  intro k conn
  obtain ⟨s,old⟩ := boundaryRoots_cover_ancestors P closed d recent live conn a phase
  change boundaryPhaseSources P d h a s = k.take (phaseClosingCut d h a) at old
  have connRoot : InputConnected P u (h.take a) := by
    rw [takeA]
    exact (closingLayerRoot n root).property
  let t : InputHistoryComponent P u := ⟨s.val,connRoot.trans s.property⟩
  have source : past t = k.take L := by
    simpa only [boundaryPhaseSources,common,cut,past,carriedBoundarySources,t] using old
  have targetLen : List.length h = List.length k := inputConnected_length P conn
  obtain ⟨slot,eq⟩ := closingLayer_contains_append past t n (k.drop L)
    (by simp only [History.length,List.length_drop,← targetLen,len]; omega)
  exact ⟨slot,by rw [source,List.take_append_drop] at eq; exact eq⟩

end Characterisation
