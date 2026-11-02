/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Formalizations.ComponentGames.MoveLegality
import DistributedSynthesis.Formalizations.ComponentGames.BasicLemmas

/- Literal history-set games from main.tex. No theorem about the previous
PeriodicBlocks arena is used as a substitute for these definitions.
Positions contain actual histories, not padded slots; replacement takes
place BEFORE extension. All semantic primitives are the project's own. -/
namespace Characterisation.ComponentGames.HistoryGame
open DistributedSynthesis Characterisation Characterisation.PeriodicBlocks
noncomputable section
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 100000

structure Position (I₁ I₂ Q : Type) (D : Nat) where
  phase : Nat
  histories : Finset (EnvHistory I₁ I₂)
  nonempty : histories.Nonempty
  lengths : ∀ h ∈ histories, List.length h = phase * D
  state : histories → Q

namespace Position
variable {I₁ I₂ Q : Type} {D : Nat}
abbrev Root (P : Position I₁ I₂ Q D) := P.histories
abbrev End (P : Position I₁ I₂ Q D) := ClosingLayer P.Root I₁ I₂ D
def past (P : Position I₁ I₂ Q D) : P.Root → EnvHistory I₁ I₂ := Subtype.val
def shape (P : Position I₁ I₂ Q D) : InputShape P.Root := extractInputShape P.past
def history (P : Position I₁ I₂ Q D) : P.End → EnvHistory I₁ I₂ :=
  closingLayerHistory P.past D
theorem history_injective (P : Position I₁ I₂ Q D) : Function.Injective P.history :=
  closingLayerHistory_injective P.past Subtype.val_injective D
theorem history_length (P : Position I₁ I₂ Q D) (e : P.End) :
    List.length (P.history e) = (P.phase+1)*D := by
  simpa only [Nat.add_mul,one_mul] using
    closingLayerHistory_length P.past (P.phase*D) (fun h => P.lengths h.val h.property) D e
def initial (q₀ : Q) : Position I₁ I₂ Q D where
  phase := 0
  histories := {[]}
  nonempty := Finset.singleton_nonempty _
  lengths := by intro h mem; simpa using Finset.mem_singleton.mp mem
  state := fun _ => q₀
end Position

structure Move (I₁ I₂ O₁ O₂ Q : Type) (D : Nat) where
  source : Position I₁ I₂ Q D
  rule : ClosingPolicy source.Root I₁ I₂ O₁ O₂ D
  replacement : source.Root → source.Root

inductive Mode where
  | component
  | replacement
  | bounded (width : Nat)

section Arena
variable {I₁ I₂ O₁ O₂ G Q : Type} {D : Nat}
variable [Fintype I₁] [Fintype I₂] [DecidableEq I₁] [DecidableEq I₂]
variable (M : Recognizer Graph G) [DecidablePred (· ∈ M.accept)]
variable (step : Q → (I₁ × I₂ × Graph) → (O₁ × O₂) → Q)

def retained (m : Move I₁ I₂ O₁ O₂ Q D) : Finset m.source.Root :=
  Finset.univ.image m.replacement

def extensionLive (m : Move I₁ I₂ O₁ O₂ Q D) (e : m.source.End) : Bool :=
  decide (closingLayerRoot D e ∈ retained m ∧
    M.eval (History.graphSequence (m.source.history e)) ∈ M.accept)

def extensions (m : Move I₁ I₂ O₁ O₂ Q D) : Finset (EnvHistory I₁ I₂) :=
  (Finset.univ.filter (fun e => extensionLive M m e = true)).image m.source.history

def IsComponent (m : Move I₁ I₂ O₁ O₂ Q D) (K : Finset m.source.End) : Prop :=
  ∃ anchor, extensionLive M m anchor = true ∧ ∀ e,
    e ∈ K ↔ closingComponentMask (closingLayerShape m.source.shape D)
      (extensionLive M m) anchor e = true

def Next (m : Move I₁ I₂ O₁ O₂ Q D) (P : Position I₁ I₂ Q D) : Prop :=
  P.phase = m.source.phase+1 ∧ ∃ K : Finset m.source.End,
    IsComponent M m K ∧ P.histories = K.image m.source.history ∧
    ∀ (h : P.Root) (e : m.source.End), e ∈ K → h.val = m.source.history e →
      P.state h = closingLayerLabels step m.source.state m.rule D (Nat.le_refl D) e

def Legal (mode : Mode) (P : Position I₁ I₂ Q D) (m : Move I₁ I₂ O₁ O₂ Q D) : Prop :=
  m.source = P ∧ ClosingPolicyCoherent m.source.shape m.rule ∧
  match mode with
  | .component => m.replacement = id
  | .replacement => ReplacementChecks m.source.shape M
      (fun h => M.eval (History.graphSequence h.val)) step m.source.state m.rule m.replacement
  | .bounded W => ReplacementChecks m.source.shape M
      (fun h => M.eval (History.graphSequence h.val)) step m.source.state m.rule m.replacement ∧
      (retained m).card ≤ W

-- Existing public-support semantics rejects an illegal move even if it
-- offers no successor; an empty extension set terminates as a controller win.
def offers (m : Move I₁ I₂ O₁ O₂ Q D) (P : Position I₁ I₂ Q D) : Bool :=
  @decide (Next M step m P) (Classical.propDecidable _)

def stateAt (m : Move I₁ I₂ O₁ O₂ Q D) (h : m.source.Root)
    (w : BlockWord (RoundRecord I₁ I₂ Graph Unit Unit) D) (t : Nat) : Q :=
  let u : BlockWord (RoundRecord I₁ I₂ Graph Unit Unit) (min t D) :=
    ⟨w.val.take t, by simp [w.property]⟩
  closingLayerLabels step m.source.state m.rule (min t D) (Nat.min_le_right _ _)
    (wordScenario h u)

structure CompatibleRun
    (tree : LabeledTree (Position I₁ I₂ Q D) (Move I₁ I₂ O₁ O₂ Q D))
    (branch : Nat → Position I₁ I₂ Q D) where
  history : (n : Nat) → (tree (branchNode branch n)).source.Root
  word : Nat → BlockWord (RoundRecord I₁ I₂ Graph Unit Unit) D
  initial : (history 0).val = []
  next : ∀ n, (history (n+1)).val =
    ((tree (branchNode branch n)).replacement (history n)).val ++ (word n).val

def Winning (mode : Mode) (q₀ : Q) (χ : Q → Nat)
    (tree : LabeledTree (Position I₁ I₂ Q D) (Move I₁ I₂ O₁ O₂ Q D)) : Prop :=
  SupportedMovesValid (offers M step) (Position.initial q₀) (Legal M step mode) tree ∧
  ∀ (branch : Nat → Position I₁ I₂ Q D),
    (∀ n, publicSupport (offers M step) tree (branchNode branch n) = true) →
    ∀ run : CompatibleRun tree branch,
      NatSeqMinEvenParity (fun n => rangeMin
        (fun t => χ (stateAt step (tree (branchNode branch n)) (run.history n) (run.word n) t))
        0 (D-1))

theorem component_member_live (m : Move I₁ I₂ O₁ O₂ Q D)
    (K : Finset m.source.End) (component : IsComponent M m K)
    (e : m.source.End) (mem : e ∈ K) : extensionLive M m e = true := by
  obtain ⟨a,_,exact⟩ := component
  have h := (exact e).mp mem
  simp only [closingComponentMask,Bool.and_eq_true] at h
  exact h.1

theorem next_exists_of_component (m : Move I₁ I₂ O₁ O₂ Q D)
    (K : Finset m.source.End) (component : IsComponent M m K) :
    ∃ P : Position I₁ I₂ Q D, Next M step m P := by
  classical
  obtain ⟨a,alive,mask⟩ := component
  have inside : a ∈ K := (mask a).mpr (by
    simp only [closingComponentMask,alive,Bool.true_and,decide_eq_true_eq]
    exact SimpleGraph.Reachable.refl a)
  let histories := K.image m.source.history
  have witnesses (h : histories) : ∃ e, e ∈ K ∧ m.source.history e = h.val :=
    Finset.mem_image.mp h.property
  let pick (h : histories) := (witnesses h).choose
  let P : Position I₁ I₂ Q D :=
    { phase := m.source.phase+1
      histories := histories
      nonempty := ⟨m.source.history a,Finset.mem_image.mpr ⟨a,inside,rfl⟩⟩
      lengths := by
        intro h mem
        obtain ⟨e,_,rfl⟩ := Finset.mem_image.mp mem
        exact m.source.history_length e
      state := fun h => closingLayerLabels step m.source.state m.rule D (Nat.le_refl D) (pick h) }
  refine ⟨P,rfl,K,⟨a,alive,mask⟩,rfl,?_⟩
  intro h e _ eq
  have chosen : m.source.history (pick h) = h.val := (witnesses h).choose_spec.2
  have same : pick h = e := m.source.history_injective (chosen.trans eq)
  change closingLayerLabels step m.source.state m.rule D _ (pick h) = _
  rw [same]

theorem next_subset_extensions (m : Move I₁ I₂ O₁ O₂ Q D)
    (P : Position I₁ I₂ Q D) (next : Next M step m P) :
    P.histories ⊆ extensions M m := by
  obtain ⟨_,K,component,eq,_⟩ := next
  rw [eq]
  intro h mem
  obtain ⟨e,inside,rfl⟩ := Finset.mem_image.mp mem
  apply Finset.mem_image.mpr
  exact ⟨e,Finset.mem_filter.mpr ⟨Finset.mem_univ _,component_member_live M m K component e inside⟩,rfl⟩

-- Full existence, participating-root membership, and unique decomposition.
-- The environment-component clause is witnessed by Next itself.
/-- A legal environment continuation exists exactly when the extension set
is nonempty. Thus the game's finite-win convention has no extra dead ends. -/
theorem next_exists_iff_extensions_nonempty (m : Move I₁ I₂ O₁ O₂ Q D) :
    (∃ P, Next M step m P) ↔ (extensions M m).Nonempty := by
  classical
  constructor
  · rintro ⟨P,next⟩
    obtain ⟨h,hh⟩ := P.nonempty
    exact ⟨h,next_subset_extensions M step m P next hh⟩
  · rintro ⟨h,hh⟩
    obtain ⟨e,he,_⟩ := Finset.mem_image.mp hh
    have alive : extensionLive M m e = true := (Finset.mem_filter.mp he).2
    let K := Finset.univ.filter (fun f =>
      closingComponentMask (closingLayerShape m.source.shape D) (extensionLive M m) e f = true)
    have component : IsComponent M m K := ⟨e,alive,by intro f; simp only [K,Finset.mem_filter,Finset.mem_univ,true_and]⟩
    exact next_exists_of_component M step m K component

theorem previous_phase_extensions (m : Move I₁ I₂ O₁ O₂ Q D)
    (P : Position I₁ I₂ Q D) (next : Next M step m P) (h : P.Root) :
    ∃! x : m.source.Root × BlockWord (RoundRecord I₁ I₂ Graph Unit Unit) D,
      x.1 ∈ retained m ∧ h.val = x.1.val ++ x.2.val := by
  have mem := next_subset_extensions M step m P next h.property
  obtain ⟨e,inside,eq⟩ := Finset.mem_image.mp mem
  have live := (Finset.mem_filter.mp inside).2
  have rootRetained := (of_decide_eq_true live).1
  refine ⟨(closingLayerRoot D e,scenarioWord D e),⟨rootRetained,?_⟩,?_⟩
  · exact eq.symm.trans (scenarioWord_history m.source.past D e)
  · rintro ⟨root,word⟩ ⟨_,hex⟩
    have parts := Characterisation.ComponentGames.previous_phase_unique (m.source.phase*D) D h.val
      root.val (closingLayerRoot D e).val word.val (scenarioWord D e).val
      (m.source.lengths root.val root.property)
      (m.source.lengths _ (closingLayerRoot D e).property)
      word.property (scenarioWord D e).property hex
      (eq.symm.trans (scenarioWord_history m.source.past D e))
    exact Prod.ext (Subtype.ext parts.1) (Subtype.ext parts.2)

theorem extensions_card (m : Move I₁ I₂ O₁ O₂ Q D) :
    (extensions M m).card ≤ (retained m).card *
      Nat.card (BlockWord (RoundRecord I₁ I₂ Graph Unit Unit) D) := by
  classical
  let keptEnds : Finset m.source.End :=
    (retained m ×ˢ (Finset.univ : Finset (BlockWord (RoundRecord I₁ I₂ Graph Unit Unit) D))).image
      (blockScenarioEquiv m.source.Root I₁ I₂ D)
  have subset : (Finset.univ.filter (fun e => extensionLive M m e = true)) ⊆ keptEnds := by
    intro e mem
    have live := (Finset.mem_filter.mp mem).2
    apply Finset.mem_image.mpr
    exact ⟨(closingLayerRoot D e,scenarioWord D e),
      Finset.mem_product.mpr ⟨(of_decide_eq_true live).1,Finset.mem_univ _⟩,
      wordScenario_scenarioWord D e⟩
  calc
    (extensions M m).card ≤ (Finset.univ.filter (fun e => extensionLive M m e = true)).card :=
      Finset.card_image_le
    _ ≤ keptEnds.card := Finset.card_le_card subset
    _ ≤ (retained m ×ˢ (Finset.univ : Finset (BlockWord (RoundRecord I₁ I₂ Graph Unit Unit) D))).card :=
      Finset.card_image_le
    _ = _ := by rw [Finset.card_product,Finset.card_univ,Nat.card_eq_fintype_card]

theorem bounded_next_size (N : Nat) (m : Move I₁ I₂ O₁ O₂ Q D)
    (legal : Legal M step (.bounded (N * Nat.card (I₁ × I₂ × Graph)^D)) m.source m)
    (P : Position I₁ I₂ Q D) (next : Next M step m P) :
    (extensions M m).card ≤ N * Nat.card (I₁ × I₂ × Graph)^(2*D) ∧
    P.histories.card ≤ N * Nat.card (I₁ × I₂ × Graph)^(2*D) := by
  have ext := extensions_card M m
  rw [blockWord_card, Nat.card_congr (envRecordEquiv I₁ I₂).symm] at ext
  exact bounded_component_size_step N _ D _ _ _ legal.2.2.2 ext
    (Finset.card_le_card (next_subset_extensions M step m P next))

/-- Finite reachability does not require any future legal continuation. -/
inductive Reached (mode : Mode) (q₀ : Q) : Position I₁ I₂ Q D → Prop
  | initial : Reached mode q₀ (Position.initial q₀)
  | advance {P R : Position I₁ I₂ Q D} {m : Move I₁ I₂ O₁ O₂ Q D} :
      Reached mode q₀ P → Legal M step mode P m → Next M step m R → Reached mode q₀ R

/-- The position bound holds for EVERY finite legal play, even one for which
no legal strategy extension has been supplied. -/
theorem reached_component_size [Nonempty I₁] [Nonempty I₂]
    (N : Nat) (positiveN : 0 < N) (q₀ : Q) (P : Position I₁ I₂ Q D)
    (reached : Reached M step (.bounded (N * Nat.card (I₁ × I₂ × Graph)^D)) q₀ P) :
    P.histories.card ≤ N * Nat.card (I₁ × I₂ × Graph)^(2*D) := by
  cases reached with
  | initial =>
    change 1 ≤ N * Nat.card (I₁ × I₂ × Graph)^(2*D)
    letI : Nonempty Graph := ⟨.both⟩
    have pos : 0 < Nat.card (I₁ × I₂ × Graph) := Nat.card_pos
    exact Nat.succ_le_of_lt (Nat.mul_pos positiveN (Nat.pow_pos pos))
  | advance _ legal next =>
    exact (bounded_next_size M step N _ ⟨rfl,legal.2⟩ P next).2

-- The corresponding bounds along every fully legal strategy tree.
-- No bound on the source component is assumed as an input to the proof.
theorem bounded_component_size [Nonempty I₁] [Nonempty I₂]
    (N : Nat) (positiveN : 0 < N) (q₀ : Q)
    (tree : LabeledTree (Position I₁ I₂ Q D) (Move I₁ I₂ O₁ O₂ Q D))
    (legal : SupportedMovesValid (offers M step) (Position.initial q₀)
      (Legal M step (.bounded (N * Nat.card (I₁ × I₂ × Graph)^D))) tree)
    (node : List (Position I₁ I₂ Q D))
    (supported : publicSupport (offers M step) tree node = true) :
    (tree node).source.histories.card ≤ N * Nat.card (I₁ × I₂ × Graph)^(2*D) ∧
    (extensions M (tree node)).card ≤ N * Nat.card (I₁ × I₂ × Graph)^(2*D) := by
  classical
  have current := legal node supported
  have ext := extensions_card M (tree node)
  rw [blockWord_card,Nat.card_congr (envRecordEquiv I₁ I₂).symm] at ext
  have extBound := (bounded_component_size_step N _ D _ _ 0 current.2.2.2 ext (Nat.zero_le _)).1
  refine ⟨?_,extBound⟩
  rw [current.1]
  cases node using List.reverseRecOn with
  | nil =>
    change 1 ≤ N * Nat.card (I₁ × I₂ × Graph)^(2*D)
    letI : Nonempty Graph := ⟨.both⟩
    have pos : 0 < Nat.card (I₁ × I₂ × Graph) := Nat.card_pos
    exact Nat.succ_le_of_lt (Nat.mul_pos positiveN (Nat.pow_pos pos))
  | append_singleton previous P =>
    have both : publicSupport (offers M step) tree previous = true ∧
        offers M step (tree previous) P = true := by
      simpa only [publicSupport_append,Bool.and_eq_true] using supported
    have next : Next M step (tree previous) P := by
      simpa only [offers,decide_eq_true_eq] using both.2
    have prior := legal previous both.1
    have bound := (bounded_next_size M step N (tree previous)
      ⟨rfl,prior.2⟩ P next).2
    simpa [observableAt] using bound

end Arena
end
end Characterisation.ComponentGames.HistoryGame



