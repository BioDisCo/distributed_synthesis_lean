/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Definition.DefSynthesisProblem
import DistributedSynthesis.Formalizations.Definition.DefOmegaAutomata
import DistributedSynthesis.Formalizations.Lemma.LemJointviewsdeterminehistory
import DistributedSynthesis.Formalizations.Theorem.ThmThetaBar

/-!
# The blind class of a generated history at a receive round has at most two members

This file proves the strategy-relative foundation of the entry thread
(`def:entrythread`, `real_model/paper.tex`), the fact consumed by the
soundness and completeness arguments around the reversed-block game
(`prop:starsound`(i), `prop:starcomplete`(b)):

for a *fixed* strategy pair, the set of strategy-generated histories that
share the blind side's current view at a receive round has **at most two
elements** -- the two `b_old` variants, differing exactly in whether the
final round's graph was the one-way incoming edge or the bidirectional edge.

This is strictly stronger than the graph-sequence bound of
`thm:onebitfringe` (`ThmOnebitfringe`) and the context-parameterized entry
ambiguity of `ThmThetaBar`: here the *entire* history -- outputs included --
is pinned down, because under a fixed strategy the outputs are determined by
the views, and at a receive round the blind view contains the partner's full
prefix view (`lem:jointviewsdeterminehistory`).

Consequences packaged below: any function of the history (`f`) takes at most
two values on the blind class; instantiating `f` with the deterministic
parity automaton run (`DetParityAutomaton.entryState`) yields that the full
entry thread `θ` of a play is determined by the blind view up to `b_old`,
which is exactly Definition `def:entrythread`'s reduction `θ ↦ θ̄`.
-/

namespace DistributedSynthesis

universe u v x y s w

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}

/-- Two strategy-generated histories with the same graph sequence and the same
input sequences are equal: views are functions of graphs and inputs, so under a
fixed strategy the outputs are determined round by round. -/
theorem strategyGeneratedPrefix_ext
    (σ : StrategyPair In₁ In₂ Out₁ Out₂)
    {h h' : History In₁ In₂ Graph Out₁ Out₂}
    (hgen : StrategyGeneratedPrefix σ h)
    (hgen' : StrategyGeneratedPrefix σ h')
    (hgraph : History.graphSequence h = History.graphSequence h')
    (hone : h.map RoundRecord.inputOne = h'.map RoundRecord.inputOne)
    (htwo : h.map RoundRecord.inputTwo = h'.map RoundRecord.inputTwo) :
    h = h' := by
  induction hgen generalizing h' with
  | empty =>
      cases h' with
      | nil => rfl
      | cons r t => simp [History.graphSequence] at hgraph
  | @append h₀ hgen₀ env ih =>
      cases hgen' with
      | empty =>
          simp [History.graphSequence, History.append] at hgraph
      | @append h₀' hgen₀' env' =>
          obtain ⟨i₁, i₂, g⟩ := env
          obtain ⟨j₁, j₂, g'⟩ := env'
          simp only [History.graphSequence, History.append, List.map_append,
            List.map_cons, List.map_nil, nextRound] at hgraph hone htwo
          obtain ⟨hg₀, hgl⟩ := List.append_inj' hgraph rfl
          obtain ⟨hone₀, honel⟩ := List.append_inj' hone rfl
          obtain ⟨htwo₀, htwol⟩ := List.append_inj' htwo rfl
          have hg : g = g' := by simpa using hgl
          have hi₁ : i₁ = j₁ := by simpa using honel
          have hi₂ : i₂ = j₂ := by simpa using htwol
          have h₀eq : h₀ = h₀' :=
            ih hgen₀' (by simpa [History.graphSequence] using hg₀) hone₀ htwo₀
          subst h₀eq; subst hg; subst hi₁; subst hi₂
          rfl

/-- After a round in which process `1` receives (`left` or `both`), its
current view is the receive view of the round's inputs over the prefix
views. -/
theorem currentView_one_append_recv
    (h : History In₁ In₂ Graph Out₁ Out₂)
    (r : RoundRecord In₁ In₂ Graph Out₁ Out₂)
    (hg : r.graph = Graph.left ∨ r.graph = Graph.both) :
    currentView Proc.one (History.append h r) =
      View.recv (currentView Proc.one h) (PSum.inl r.inputOne)
        (currentView Proc.two h) (PSum.inr r.inputTwo) := by
  rcases hg with hg | hg <;> simp [currentView_one_append, hg]

/-- After a round in which process `2` receives (`right` or `both`), its
current view is the receive view of the round's inputs over the prefix
views. -/
theorem currentView_two_append_recv
    (h : History In₁ In₂ Graph Out₁ Out₂)
    (r : RoundRecord In₁ In₂ Graph Out₁ Out₂)
    (hg : r.graph = Graph.right ∨ r.graph = Graph.both) :
    currentView Proc.two (History.append h r) =
      View.recv (currentView Proc.two h) (PSum.inr r.inputTwo)
        (currentView Proc.one h) (PSum.inl r.inputOne) := by
  rcases hg with hg | hg <;> simp [currentView_two_append, hg]

/-- Blind-view determinacy across a process-`1` receive round: if two
generated histories end in receive rounds for process `1` and process `1`
has the same current view, then the prefixes are *equal* and the final
inputs agree; only the final graph bit (`left` versus `both`, the `b_old`
ambiguity) is free. -/
theorem recv_view_determines_prefix_one
    (σ : StrategyPair In₁ In₂ Out₁ Out₂)
    {h₀ h₀' : History In₁ In₂ Graph Out₁ Out₂}
    (hgen₀ : StrategyGeneratedPrefix σ h₀)
    (hgen₀' : StrategyGeneratedPrefix σ h₀')
    (i₁ j₁ : In₁) (i₂ j₂ : In₂) (g g' : Graph)
    (hg : g = Graph.left ∨ g = Graph.both)
    (hg' : g' = Graph.left ∨ g' = Graph.both)
    (hview :
      currentView Proc.one (History.append h₀' (nextRound σ h₀' ⟨j₁, j₂, g'⟩)) =
        currentView Proc.one (History.append h₀ (nextRound σ h₀ ⟨i₁, i₂, g⟩))) :
    h₀' = h₀ ∧ j₁ = i₁ ∧ j₂ = i₂ := by
  have hR :
      currentView Proc.one (History.append h₀ (nextRound σ h₀ ⟨i₁, i₂, g⟩)) =
        View.recv (currentView Proc.one h₀) (PSum.inl i₁)
          (currentView Proc.two h₀) (PSum.inr i₂) :=
    currentView_one_append_recv h₀ (nextRound σ h₀ ⟨i₁, i₂, g⟩) hg
  have hL :
      currentView Proc.one (History.append h₀' (nextRound σ h₀' ⟨j₁, j₂, g'⟩)) =
        View.recv (currentView Proc.one h₀') (PSum.inl j₁)
          (currentView Proc.two h₀') (PSum.inr j₂) :=
    currentView_one_append_recv h₀' (nextRound σ h₀' ⟨j₁, j₂, g'⟩) hg'
  rw [hL, hR, View.recv.injEq] at hview
  obtain ⟨hv₁, hx₁, hv₂, hx₂⟩ := hview
  have hj₁ : j₁ = i₁ := by simpa using hx₁
  have hj₂ : j₂ = i₂ := by simpa using hx₂
  obtain ⟨hgs, hin1, hin2⟩ :=
    jointViews_determine_inputGraphHistory h₀' h₀ hv₁ hv₂
  exact ⟨strategyGeneratedPrefix_ext σ hgen₀' hgen₀ hgs hin1 hin2, hj₁, hj₂⟩

/-- Mirror of `recv_view_determines_prefix_one` for process `2`: the free
final graph bit is `right` versus `both`. -/
theorem recv_view_determines_prefix_two
    (σ : StrategyPair In₁ In₂ Out₁ Out₂)
    {h₀ h₀' : History In₁ In₂ Graph Out₁ Out₂}
    (hgen₀ : StrategyGeneratedPrefix σ h₀)
    (hgen₀' : StrategyGeneratedPrefix σ h₀')
    (i₁ j₁ : In₁) (i₂ j₂ : In₂) (g g' : Graph)
    (hg : g = Graph.right ∨ g = Graph.both)
    (hg' : g' = Graph.right ∨ g' = Graph.both)
    (hview :
      currentView Proc.two (History.append h₀' (nextRound σ h₀' ⟨j₁, j₂, g'⟩)) =
        currentView Proc.two (History.append h₀ (nextRound σ h₀ ⟨i₁, i₂, g⟩))) :
    h₀' = h₀ ∧ j₁ = i₁ ∧ j₂ = i₂ := by
  have hR :
      currentView Proc.two (History.append h₀ (nextRound σ h₀ ⟨i₁, i₂, g⟩)) =
        View.recv (currentView Proc.two h₀) (PSum.inr i₂)
          (currentView Proc.one h₀) (PSum.inl i₁) :=
    currentView_two_append_recv h₀ (nextRound σ h₀ ⟨i₁, i₂, g⟩) hg
  have hL :
      currentView Proc.two (History.append h₀' (nextRound σ h₀' ⟨j₁, j₂, g'⟩)) =
        View.recv (currentView Proc.two h₀') (PSum.inr j₂)
          (currentView Proc.one h₀') (PSum.inl j₁) :=
    currentView_two_append_recv h₀' (nextRound σ h₀' ⟨j₁, j₂, g'⟩) hg'
  rw [hL, hR, View.recv.injEq] at hview
  obtain ⟨hv₂, hx₂, hv₁, hx₁⟩ := hview
  have hj₁ : j₁ = i₁ := by simpa using hx₁
  have hj₂ : j₂ = i₂ := by simpa using hx₂
  obtain ⟨hgs, hin1, hin2⟩ :=
    jointViews_determine_inputGraphHistory h₀' h₀ hv₁ hv₂
  exact ⟨strategyGeneratedPrefix_ext σ hgen₀' hgen₀ hgs hin1 hin2, hj₁, hj₂⟩

/-- **The blind class at a receive round has at most two members (process
`1`).**  For a fixed strategy pair, at most two generated histories carry the
blind side's current view when that view is a receive view: the two `b_old`
variants of one history.  This is the strategy-relative form of
`thm:onebitfringe` and the foundation of `def:entrythread`. -/
theorem blind_receive_class_le_two_one
    (σ : StrategyPair In₁ In₂ Out₁ Out₂)
    {h : History In₁ In₂ Graph Out₁ Out₂}
    (hgen : StrategyGeneratedPrefix σ h)
    (hrecv : ∃ (v₁ : View In₁ In₂ Proc.one) (x₁ : PSum In₁ In₂)
        (v₂ : View In₁ In₂ Proc.two) (x₂ : PSum In₁ In₂),
      currentView Proc.one h = View.recv v₁ x₁ v₂ x₂) :
    ∃ candidates : List (History In₁ In₂ Graph Out₁ Out₂),
      candidates.length ≤ 2 ∧
      h ∈ candidates ∧
      ∀ h' : History In₁ In₂ Graph Out₁ Out₂,
        StrategyGeneratedPrefix σ h' →
        currentView Proc.one h' = currentView Proc.one h →
        h' ∈ candidates := by
  cases hgen with
  | empty =>
      obtain ⟨v₁, x₁, v₂, x₂, hshape⟩ := hrecv
      simp [currentView, viewPair] at hshape
  | @append h₀ hgen₀ env =>
      obtain ⟨i₁, i₂, g⟩ := env
      have hg : g = Graph.left ∨ g = Graph.both := by
        cases g with
        | right =>
            obtain ⟨v₁, x₁, v₂, x₂, hshape⟩ := hrecv
            simp [currentView_one_append, nextRound] at hshape
        | left => exact Or.inl rfl
        | both => exact Or.inr rfl
      refine ⟨[History.append h₀ (nextRound σ h₀ ⟨i₁, i₂, Graph.left⟩),
               History.append h₀ (nextRound σ h₀ ⟨i₁, i₂, Graph.both⟩)],
        by simp, ?_, ?_⟩
      · rcases hg with rfl | rfl <;> simp
      · intro h' hgen' hview
        cases hgen' with
        | empty =>
            rw [currentView_one_append_recv h₀ (nextRound σ h₀ ⟨i₁, i₂, g⟩) hg]
              at hview
            simp [currentView, viewPair] at hview
        | @append h₀' hgen₀' env' =>
            obtain ⟨j₁, j₂, g'⟩ := env'
            have hg' : g' = Graph.left ∨ g' = Graph.both := by
              cases g' with
              | right =>
                  rw [currentView_one_append_recv h₀
                      (nextRound σ h₀ ⟨i₁, i₂, g⟩) hg] at hview
                  simp [currentView_one_append, nextRound] at hview
              | left => exact Or.inl rfl
              | both => exact Or.inr rfl
            obtain ⟨h₀eq, hj₁, hj₂⟩ :=
              recv_view_determines_prefix_one σ hgen₀ hgen₀' i₁ j₁ i₂ j₂ g g'
                hg hg' hview
            subst h₀eq; subst hj₁; subst hj₂
            rcases hg' with rfl | rfl <;> simp

/-- **The blind class at a receive round has at most two members (process
`2`).**  The orientation mirror of `blind_receive_class_le_two_one`. -/
theorem blind_receive_class_le_two_two
    (σ : StrategyPair In₁ In₂ Out₁ Out₂)
    {h : History In₁ In₂ Graph Out₁ Out₂}
    (hgen : StrategyGeneratedPrefix σ h)
    (hrecv : ∃ (v₂ : View In₁ In₂ Proc.two) (x₂ : PSum In₁ In₂)
        (v₁ : View In₁ In₂ Proc.one) (x₁ : PSum In₁ In₂),
      currentView Proc.two h = View.recv v₂ x₂ v₁ x₁) :
    ∃ candidates : List (History In₁ In₂ Graph Out₁ Out₂),
      candidates.length ≤ 2 ∧
      h ∈ candidates ∧
      ∀ h' : History In₁ In₂ Graph Out₁ Out₂,
        StrategyGeneratedPrefix σ h' →
        currentView Proc.two h' = currentView Proc.two h →
        h' ∈ candidates := by
  cases hgen with
  | empty =>
      obtain ⟨v₂, x₂, v₁, x₁, hshape⟩ := hrecv
      simp [currentView, viewPair] at hshape
  | @append h₀ hgen₀ env =>
      obtain ⟨i₁, i₂, g⟩ := env
      have hg : g = Graph.right ∨ g = Graph.both := by
        cases g with
        | left =>
            obtain ⟨v₂, x₂, v₁, x₁, hshape⟩ := hrecv
            simp [currentView_two_append, nextRound] at hshape
        | right => exact Or.inl rfl
        | both => exact Or.inr rfl
      refine ⟨[History.append h₀ (nextRound σ h₀ ⟨i₁, i₂, Graph.right⟩),
               History.append h₀ (nextRound σ h₀ ⟨i₁, i₂, Graph.both⟩)],
        by simp, ?_, ?_⟩
      · rcases hg with rfl | rfl <;> simp
      · intro h' hgen' hview
        cases hgen' with
        | empty =>
            rw [currentView_two_append_recv h₀ (nextRound σ h₀ ⟨i₁, i₂, g⟩) hg]
              at hview
            simp [currentView, viewPair] at hview
        | @append h₀' hgen₀' env' =>
            obtain ⟨j₁, j₂, g'⟩ := env'
            have hg' : g' = Graph.right ∨ g' = Graph.both := by
              cases g' with
              | left =>
                  rw [currentView_two_append_recv h₀
                      (nextRound σ h₀ ⟨i₁, i₂, g⟩) hg] at hview
                  simp [currentView_two_append, nextRound] at hview
              | right => exact Or.inl rfl
              | both => exact Or.inr rfl
            obtain ⟨h₀eq, hj₁, hj₂⟩ :=
              recv_view_determines_prefix_two σ hgen₀ hgen₀' i₁ j₁ i₂ j₂ g g'
                hg hg' hview
            subst h₀eq; subst hj₁; subst hj₂
            rcases hg' with rfl | rfl <;> simp

/-- Any function of the history takes at most two values on the blind
receive-round class of process `1`.  This is the generic entry-thread bound:
whatever finite coordinate the construction reads off the play, the blind
side pins it down to the two `b_old` variants. -/
theorem blind_receive_image_le_two_one {α : Type w}
    (σ : StrategyPair In₁ In₂ Out₁ Out₂)
    {h : History In₁ In₂ Graph Out₁ Out₂}
    (hgen : StrategyGeneratedPrefix σ h)
    (hrecv : ∃ (v₁ : View In₁ In₂ Proc.one) (x₁ : PSum In₁ In₂)
        (v₂ : View In₁ In₂ Proc.two) (x₂ : PSum In₁ In₂),
      currentView Proc.one h = View.recv v₁ x₁ v₂ x₂)
    (f : History In₁ In₂ Graph Out₁ Out₂ → α) :
    ∃ values : List α,
      values.length ≤ 2 ∧
      f h ∈ values ∧
      ∀ h' : History In₁ In₂ Graph Out₁ Out₂,
        StrategyGeneratedPrefix σ h' →
        currentView Proc.one h' = currentView Proc.one h →
        f h' ∈ values := by
  obtain ⟨cs, hlen, hmem, hall⟩ := blind_receive_class_le_two_one σ hgen hrecv
  refine ⟨cs.map f, by simpa using hlen,
    List.mem_map.mpr ⟨h, hmem, rfl⟩, fun h' hgen' hview =>
      List.mem_map.mpr ⟨h', hall h' hgen' hview, rfl⟩⟩

/-- Mirror of `blind_receive_image_le_two_one` for process `2`. -/
theorem blind_receive_image_le_two_two {α : Type w}
    (σ : StrategyPair In₁ In₂ Out₁ Out₂)
    {h : History In₁ In₂ Graph Out₁ Out₂}
    (hgen : StrategyGeneratedPrefix σ h)
    (hrecv : ∃ (v₂ : View In₁ In₂ Proc.two) (x₂ : PSum In₁ In₂)
        (v₁ : View In₁ In₂ Proc.one) (x₁ : PSum In₁ In₂),
      currentView Proc.two h = View.recv v₂ x₂ v₁ x₁)
    (f : History In₁ In₂ Graph Out₁ Out₂ → α) :
    ∃ values : List α,
      values.length ≤ 2 ∧
      f h ∈ values ∧
      ∀ h' : History In₁ In₂ Graph Out₁ Out₂,
        StrategyGeneratedPrefix σ h' →
        currentView Proc.two h' = currentView Proc.two h →
        f h' ∈ values := by
  obtain ⟨cs, hlen, hmem, hall⟩ := blind_receive_class_le_two_two σ hgen hrecv
  refine ⟨cs.map f, by simpa using hlen,
    List.mem_map.mpr ⟨h, hmem, rfl⟩, fun h' hgen' hview =>
      List.mem_map.mpr ⟨h', hall h' hgen' hview, rfl⟩⟩

namespace DetParityAutomaton

/-- **`def:entrythread` in strategy-relative form (process `1`).**  Under a
fixed strategy pair, at a receive round the full entry thread `θ` -- the
deterministic parity automaton state of the play -- is determined by the
blind side's own view up to at most two candidates, the two `b_old`
variants.  The reduction `θ ↦ θ̄` of `def:entrythread` forgets exactly this
one-bit ambiguity. -/
theorem entryState_blindClass_le_two_one
    {A : DetParityAutomaton.{max u v x y, s} (RoundRecord In₁ In₂ Graph Out₁ Out₂)}
    (σ : StrategyPair In₁ In₂ Out₁ Out₂)
    {h : History In₁ In₂ Graph Out₁ Out₂}
    (hgen : StrategyGeneratedPrefix σ h)
    (hrecv : ∃ (v₁ : View In₁ In₂ Proc.one) (x₁ : PSum In₁ In₂)
        (v₂ : View In₁ In₂ Proc.two) (x₂ : PSum In₁ In₂),
      currentView Proc.one h = View.recv v₁ x₁ v₂ x₂) :
    ∃ states : List A.State,
      states.length ≤ 2 ∧
      entryState (A := A) h ∈ states ∧
      ∀ h' : History In₁ In₂ Graph Out₁ Out₂,
        StrategyGeneratedPrefix σ h' →
        currentView Proc.one h' = currentView Proc.one h →
        entryState (A := A) h' ∈ states :=
  blind_receive_image_le_two_one σ hgen hrecv (entryState (A := A))

/-- Mirror of `entryState_blindClass_le_two_one` for process `2`. -/
theorem entryState_blindClass_le_two_two
    {A : DetParityAutomaton.{max u v x y, s} (RoundRecord In₁ In₂ Graph Out₁ Out₂)}
    (σ : StrategyPair In₁ In₂ Out₁ Out₂)
    {h : History In₁ In₂ Graph Out₁ Out₂}
    (hgen : StrategyGeneratedPrefix σ h)
    (hrecv : ∃ (v₂ : View In₁ In₂ Proc.two) (x₂ : PSum In₁ In₂)
        (v₁ : View In₁ In₂ Proc.one) (x₁ : PSum In₁ In₂),
      currentView Proc.two h = View.recv v₂ x₂ v₁ x₁) :
    ∃ states : List A.State,
      states.length ≤ 2 ∧
      entryState (A := A) h ∈ states ∧
      ∀ h' : History In₁ In₂ Graph Out₁ Out₂,
        StrategyGeneratedPrefix σ h' →
        currentView Proc.two h' = currentView Proc.two h →
        entryState (A := A) h' ∈ states :=
  blind_receive_image_le_two_two σ hgen hrecv (entryState (A := A))

end DetParityAutomaton

/-! ### The entry quotient is `A_φ`-faithful (`prop:starsound`(ii))

Acceptance of a play depends on its finite prefix only through the automaton
state the prefix reaches.  Two entries with the same thread `θ` are therefore
interchangeable: any continuation winning at one wins at the other.  Combined
with the class bound above, the blind side's `θ̄` conflates only the two
`b_old` variants of a single `θ`, and their differing `A_φ`-effect is a
matter for the informed side -- exactly the split `prop:starcomplete`
exploits. -/

namespace OmegaWord

/-- Prepend a finite word to an infinite word. -/
def prependList {Letter : Type w} : List Letter → OmegaWord Letter → OmegaWord Letter
  | [], word => word
  | a :: l, word => fun n =>
      match n with
      | 0 => a
      | k + 1 => prependList l word k

@[simp]
theorem prependList_nil {Letter : Type w} (word : OmegaWord Letter) :
    prependList [] word = word :=
  rfl

@[simp]
theorem prependList_cons_zero {Letter : Type w} (a : Letter) (l : List Letter)
    (word : OmegaWord Letter) :
    prependList (a :: l) word 0 = a :=
  rfl

@[simp]
theorem prependList_cons_succ {Letter : Type w} (a : Letter) (l : List Letter)
    (word : OmegaWord Letter) (n : Nat) :
    prependList (a :: l) word (n + 1) = prependList l word n :=
  rfl

/-- Dropping the prefix recovers the infinite tail. -/
theorem drop_length_prependList {Letter : Type w} (l : List Letter)
    (word : OmegaWord Letter) :
    OmegaWord.drop (prependList l word) l.length = word := by
  induction l with
  | nil =>
      funext n
      simp [OmegaWord.drop]
  | cons a l ih =>
      funext n
      have harith : (a :: l).length + n = (l.length + n) + 1 := by
        simp [List.length_cons]
        omega
      calc
        OmegaWord.drop (prependList (a :: l) word) (a :: l).length n
            = prependList (a :: l) word ((a :: l).length + n) := rfl
        _ = prependList (a :: l) word ((l.length + n) + 1) := by rw [harith]
        _ = prependList l word (l.length + n) := rfl
        _ = OmegaWord.drop (prependList l word) l.length n := rfl
        _ = word n := by rw [ih]

end OmegaWord

namespace DetParityAutomaton

variable {Alphabet : Type w}

/-- Running over the prepended prefix is the list fold of the step function. -/
theorem runFrom_prependList_length
    (A : DetParityAutomaton.{w, s} Alphabet)
    (l : List Alphabet) (word : OmegaWord Alphabet) (state : A.State) :
    A.runFrom state (OmegaWord.prependList l word) l.length =
      l.foldl A.step state := by
  induction l generalizing state with
  | nil => rfl
  | cons a l ih =>
      have hdrop :
          OmegaWord.drop (OmegaWord.prependList (a :: l) word) 1 =
            OmegaWord.prependList l word := by
        funext n
        show OmegaWord.prependList (a :: l) word (1 + n) =
          OmegaWord.prependList l word n
        rw [Nat.add_comm]
        exact OmegaWord.prependList_cons_succ a l word n
      calc
        A.runFrom state (OmegaWord.prependList (a :: l) word) (a :: l).length
            = A.runFrom state (OmegaWord.prependList (a :: l) word)
                (l.length + 1) := rfl
        _ = A.runFrom
              (A.step state (OmegaWord.prependList (a :: l) word 0))
              (OmegaWord.drop (OmegaWord.prependList (a :: l) word) 1)
              l.length :=
            (A.runFrom_step_drop state (OmegaWord.prependList (a :: l) word)
              l.length).symm
        _ = A.runFrom (A.step state a) (OmegaWord.prependList l word)
              l.length := by rw [OmegaWord.prependList_cons_zero, hdrop]
        _ = l.foldl A.step (A.step state a) := ih (A.step state a)
        _ = (a :: l).foldl A.step state := rfl

/-- **Acceptance depends on the prefix only through the reached state**
(`prop:starsound`(ii)).  Two finite prefixes reaching the same automaton
state are interchangeable in front of every infinite continuation. -/
theorem accepts_prependList_congr
    (A : DetParityAutomaton.{w, s} Alphabet)
    {l l' : List Alphabet}
    (hstate : l.foldl A.step A.initial = l'.foldl A.step A.initial)
    (word : OmegaWord Alphabet) :
    A.Accepts (OmegaWord.prependList l word) ↔
      A.Accepts (OmegaWord.prependList l' word) := by
  have h1 :=
    A.acceptsFrom_runFrom_drop_iff A.initial
      (OmegaWord.prependList l word) l.length
  rw [runFrom_prependList_length, OmegaWord.drop_length_prependList] at h1
  have h2 :=
    A.acceptsFrom_runFrom_drop_iff A.initial
      (OmegaWord.prependList l' word) l'.length
  rw [runFrom_prependList_length, OmegaWord.drop_length_prependList] at h2
  have hmid :
      A.AcceptsFrom (l.foldl A.step A.initial) word ↔
        A.AcceptsFrom (l'.foldl A.step A.initial) word := by
    rw [hstate]
  exact h1.symm.trans (hmid.trans h2)

/-- **Same-`θ` entries are interchangeable** (`prop:starcomplete`, the
sufficient-statistic step at the entry): under any strategy context, two
histories with equal entry thread `θ` score `A_φ` identically on every
continuation. -/
theorem accepts_congr_entryState
    {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
    {A : DetParityAutomaton.{max u v x y, s} (RoundRecord In₁ In₂ Graph Out₁ Out₂)}
    {h h' : History In₁ In₂ Graph Out₁ Out₂}
    (hθ : entryState (A := A) h = entryState (A := A) h')
    (word : OmegaWord (RoundRecord In₁ In₂ Graph Out₁ Out₂)) :
    A.Accepts (OmegaWord.prependList h word) ↔
      A.Accepts (OmegaWord.prependList h' word) :=
  accepts_prependList_congr A hθ word

end DetParityAutomaton

end DistributedSynthesis
