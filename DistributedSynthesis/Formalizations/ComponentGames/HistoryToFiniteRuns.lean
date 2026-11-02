/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Formalizations.ComponentGames.HistoryToFinite

namespace Characterisation.ComponentGames.Representation.HistoryToFinite
open scoped Characterisation.ComponentGames.Representation
open DistributedSynthesis Characterisation Characterisation.PeriodicBlocks
noncomputable section
set_option maxHeartbeats 2400000
set_option linter.unusedSectionVars false
variable {I₁ I₂ O₁ O₂ G Q : Type} {D B L : Nat}
variable [Fintype I₁] [Fintype I₂] [LinearOrder I₁] [LinearOrder I₂]
variable [Fintype O₁] [Fintype O₂] [DecidableEq O₁] [DecidableEq O₂]
variable [Fintype G] [Fintype Q] [DecidableEq G] [DecidableEq Q]
variable (M : Recognizer Graph G) [DecidablePred (· ∈ M.accept)]
variable (step : Q → (I₁ × I₂ × Graph) → (O₁ × O₂) → Q)
variable (χ : Q → Nat) (priorityBound : ∀ q, χ q ≤ L)
variable (W : Nat) (q₀ : Q) (positive : 0 < B)
variable (target : LabeledTree (HistoryGame.Position I₁ I₂ Q D) (HistoryGame.Move I₁ I₂ O₁ O₂ Q D))
variable (valid : SupportedMovesValid (HistoryGame.offers M step) (HistoryGame.Position.initial q₀)
    (HistoryGame.Legal M step (.bounded W)) target)

abbrev State.Position (s : State M step q₀ positive target) :=
  FiniteArena.observedPosition M step q₀ positive s.observed

theorem edge_source (s : State M step q₀ positive target)
    (o : FiniteArena.Observation I₁ I₂ O₁ O₂ G Q D B)
    (offered : FiniteArena.offers M (action M step q₀ positive target s) o = true)
    (h j : Fin (B+1)) (c : Fin (L+1))
    (edge : (h,c,j) ∈ FiniteArena.phaseRelation step χ priorityBound o) :
    ∃ a : (s.Position M step q₀ positive target).Root, h = FiniteArena.slot (s.Position M step q₀ positive target) a := by
  let data := advanceData M step q₀ positive target s o offered
  rw [data.observation] at edge
  simp only [FiniteArena.phaseRelation,dif_pos data.bound] at edge
  obtain ⟨a,_,_,_,source,_,_⟩ := (FiniteArena.mem_relation step χ priorityBound _ _ _ _ _ _).mp edge
  exact ⟨a,source⟩

include valid in
theorem advance_edge (s after : State M step q₀ positive target)
    (o : FiniteArena.Observation I₁ I₂ O₁ O₂ G Q D B)
    (offered : FiniteArena.offers M (action M step q₀ positive target s) o = true)
    (afterEq : after = advance M step W q₀ positive target valid s o offered)
    (i : (s.Position M step q₀ positive target).Root) (j : (after.Position M step q₀ positive target).Root)
    (c : Fin (L+1))
    (edge : (FiniteArena.slot (s.Position M step q₀ positive target) i,c,
      FiniteArena.slot (after.Position M step q₀ positive target) j) ∈ FiniteArena.phaseRelation step χ priorityBound o) :
    ∃ w : FiniteArena.Word I₁ I₂ D,
      (after.iso.toEquiv.symm j).val = ((target s.node).replacement (s.iso.toEquiv.symm i)).val ++ w.val ∧
      c.val = rangeMin (fun t => χ (HistoryGame.stateAt step (target s.node) (s.iso.toEquiv.symm i) w t)) 0 (D-1) := by
  subst after
  let data := advanceData M step q₀ positive target s o offered
  have edge' := edge
  rw [congrArg (FiniteArena.phaseRelation step χ priorityBound) data.observation] at edge'
  simp only [FiniteArena.phaseRelation,dif_pos data.bound] at edge'
  obtain ⟨a,w,e,endpoint,source,priority,last⟩ :=
    (FiniteArena.mem_relation step χ priorityBound _ _ _ _ _ _).mp edge'
  have same : i = a := FiniteArena.slot_injective _ source
  subst a
  refine ⟨w,?_,?_⟩
  · change ((castHistoryIso M data.iso _).toEquiv.symm j).val = _
    rw [castHistoryIso_inverse_val]
    apply data.trace (s.iso.toEquiv.symm i) j w e _ last
    simpa only [Equiv.apply_symm_apply] using endpoint
  · rw [priority]
    have eq := phaseMinimum_map step χ (ofHistory M (target s.node).source)
      (s.Position M step q₀ positive target).2 s.iso (target s.node).rule (s.iso.toEquiv.symm i) w
    simpa only [Equiv.apply_symm_apply] using eq

private theorem replacement_same_history (m m' : HistoryGame.Move I₁ I₂ O₁ O₂ Q D)
    (eq : m = m') (a : m.source.Root) (b : m'.source.Root) (same : a.val = b.val) :
    (m.replacement a).val = (m'.replacement b).val := by
  subst m'
  have ab : a = b := Subtype.ext same
  rw [ab]

private theorem stateAt_same_history (m m' : HistoryGame.Move I₁ I₂ O₁ O₂ Q D)
    (eq : m = m') (a : m.source.Root) (b : m'.source.Root) (same : a.val = b.val)
    (w : FiniteArena.Word I₁ I₂ D) (t : Nat) :
    HistoryGame.stateAt step m a w t = HistoryGame.stateAt step m' b w t := by
  subst m'
  have ab : a = b := Subtype.ext same
  rw [ab]

/-- Converse strategy transfer, with arbitrary finite-game plays and every
run admitted by their full ternary transition relations. -/
theorem winning (win : HistoryGame.Winning M step (.bounded W) q₀ χ target) :
    FiniteArena.Winning M step χ priorityBound W q₀ positive
      (interpreter M step W q₀ positive target win.1).tree := by
  let I := interpreter M step W q₀ positive target win.1
  refine ⟨I.tree_legal,?_⟩
  intro b supported h c _first edges
  obtain ⟨targetBranch,targetSupported,nodes,advances⟩ := I.branch b supported
  let st n := I.atState (branchNode b n)
  have offered n : FiniteArena.offers M (action M step q₀ positive target (st n)) (b n) = true :=
    (advances n).choose
  have after n : st (n+1) = advance M step W q₀ positive target win.1 (st n) (b n) (offered n) :=
    (advances n).choose_spec.1
  have roots n := edge_source M step χ priorityBound q₀ positive target (st n) (b n) (offered n) (h n) (h (n+1)) (c n) (edges n)
  choose root slots using roots
  have steps n := advance_edge M step χ priorityBound W q₀ positive target win.1
    (st n) (st (n+1)) (b n) (offered n) (after n) (root n) (root (n+1)) (c n)
    (by simpa only [slots] using edges n)
  choose word trace priority using steps
  let realRoot n := (st n).iso.toEquiv.symm (root n)
  let history n : (target (branchNode targetBranch n)).source.Root :=
    ⟨(realRoot n).val,by
      change (realRoot n).val ∈ (target (branchNode targetBranch n)).source.histories
      rw [← nodes n]
      exact (realRoot n).property⟩
  have initial : (history 0).val = [] := by
    have member := (history 0).property
    have start := (win.1 [] (publicSupport_nil _ _)).1
    change (target []).source = HistoryGame.Position.initial q₀ at start
    change (history 0).val ∈ (target []).source.histories at member
    rw [start] at member
    exact Finset.mem_singleton.mp member
  have move_eq n : ((target (st n).node).replacement (realRoot n)).val =
      ((target (branchNode targetBranch n)).replacement (history n)).val :=
    replacement_same_history _ _ (congrArg target (nodes n)) (realRoot n) (history n) rfl
  let run : HistoryGame.CompatibleRun target targetBranch :=
    {history := history,word := word,initial := initial
     next := fun n => (trace n).trans (by rw [move_eq n])}
  have parity := win.2 targetBranch targetSupported run
  have priorities n : (c n).val = rangeMin
      (fun t => χ (HistoryGame.stateAt step (target (branchNode targetBranch n)) (history n) (word n) t)) 0 (D-1) := by
    rw [priority n]
    apply rangeMin_congr
    intro t _
    simpa only [Nat.zero_add] using congrArg χ (stateAt_same_history step _ _ (congrArg target (nodes n)) (realRoot n) (history n) rfl (word n) t)
  simpa only [run,← priorities] using parity

end
end Characterisation.ComponentGames.Representation.HistoryToFinite
