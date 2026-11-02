/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Formalizations.ComponentGames.FiniteToHistory

namespace Characterisation.ComponentGames.Representation.FiniteToHistory
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
variable (capacity : W * Nat.card (FiniteArena.Word I₁ I₂ D) ≤ B)
variable (target : LabeledTree (FiniteArena.Observation I₁ I₂ O₁ O₂ G Q D B) (FiniteArena.Move I₁ I₂ O₁ O₂ G Q D B))
variable (valid : SupportedMovesValid (FiniteArena.offers M) none (FiniteArena.Legal M step W q₀ positive) target)

def State.slot (s : State M target) (h : s.real.Root) : Fin (B+1) :=
  FiniteArena.slot (target s.node).source (s.iso.toEquiv h)

def State.priority (s : State M target) (h : s.real.Root) (w : FiniteArena.Word I₁ I₂ D) : Fin (L+1) :=
  FiniteArena.phasePriority step χ priorityBound (target s.node) (s.iso.toEquiv h) w

theorem action_priority (s : State M target) (h : s.real.Root) (w : FiniteArena.Word I₁ I₂ D) :
    (s.priority M step χ priorityBound target h w).val =
      rangeMin (fun t => χ (HistoryGame.stateAt step (action M target s) h w t)) 0 (D-1) := by
  have eq := phaseMinimum_map step χ (target s.node).source.2 (ofHistory M s.real) s.iso.symm
    (target s.node).rule (s.iso.toEquiv h) w
  simpa only [Iso.symm,Equiv.symm_apply_apply] using eq.symm

theorem advance_edge (s after : State M target) (P : HistoryGame.Position I₁ I₂ Q D)
    (next : HistoryGame.Next M step (action M target s) P)
    (afterEq : after = advance M step W q₀ positive capacity target valid s P next)
    (h : after.real.Root) (a : s.real.Root) (w : FiniteArena.Word I₁ I₂ D)
    (trace : h.val = ((action M target s).replacement a).val ++ w.val) :
    (s.slot M target a,s.priority M step χ priorityBound target a w,after.slot M target h) ∈
      FiniteArena.phaseRelation step χ priorityBound
        (advanceData M step W q₀ positive capacity target valid s P next).observation := by
  subst after
  let data := advanceData M step W q₀ positive capacity target valid s P next
  obtain ⟨K,bound,e,observation,endpoint,last⟩ := data.trace h a w trace
  have last' : (advance M step W q₀ positive capacity target valid s P next).slot M target h =
      FiniteArena.endSlot (target s.node) K bound e := by
    change FiniteArena.slot _ ((castFiniteIso M data.iso _).toEquiv h) = _
    rw [castFiniteIso_slot]
    exact last
  change (_,_,_) ∈ FiniteArena.phaseRelation step χ priorityBound data.observation
  rw [last',observation]
  simp only [FiniteArena.phaseRelation,dif_pos bound]
  exact (FiniteArena.mem_relation step χ priorityBound _ _ _ _ _ _).mpr
    ⟨s.iso.toEquiv a,w,e,endpoint,rfl,rfl,rfl⟩

/-- Every winning finite controller pulls back to a winning controller of
the literal BoundedComponent game, for every supported play and run. -/
theorem winning (win : FiniteArena.Winning M step χ priorityBound W q₀ positive target) :
    HistoryGame.Winning M step (.bounded W) q₀ χ
      (interpreter M step W q₀ positive capacity target win.1).tree := by
  let I := interpreter M step W q₀ positive capacity target win.1
  refine ⟨I.tree_legal,?_⟩
  intro b supported run
  obtain ⟨c,targetSupported,nodes,advances⟩ := I.branch b supported
  let st n := I.atState (branchNode b n)
  let h n := (st n).slot M target (run.history n)
  let priorities n := (st n).priority M step χ priorityBound target (run.history n) (run.word n)
  have first : h 0 = 0 := by
    have source := (win.1 [] (publicSupport_nil _ _)).1
    change (target []).source = FiniteArena.initial M q₀ positive at source
    have small := ((st 0).iso.toEquiv (run.history 0)).isLt
    change ((st 0).iso.toEquiv (run.history 0)).val < (target []).source.1.val at small
    rw [source] at small
    apply Fin.ext
    change ((st 0).iso.toEquiv (run.history 0)).val = 0
    change ((st 0).iso.toEquiv (run.history 0)).val < 1 at small
    omega
  have edges n : (h n,priorities n,h (n+1)) ∈ FiniteArena.phaseRelation step χ priorityBound (c n) := by
    obtain ⟨offered,after,reply⟩ := advances n
    have next : HistoryGame.Next M step (action M target (st n)) (b n) :=
      @of_decide_eq_true _ (Classical.propDecidable _) offered
    have after' : st (n+1) = advance M step W q₀ positive capacity target win.1 (st n) (b n) next := after
    have edge := advance_edge M step χ priorityBound W q₀ positive capacity target win.1
      (st n) (st (n+1)) (b n) next after' (run.history (n+1)) (run.history n) (run.word n) (run.next n)
    have reply' : c n = (advanceData M step W q₀ positive capacity target win.1 (st n) (b n) next).observation := reply
    rw [reply']
    exact edge
  have parity := win.2 c targetSupported h priorities first edges
  have equality n := action_priority M step χ priorityBound target (st n) (run.history n) (run.word n)
  simpa only [priorities,equality] using parity

end
end Characterisation.ComponentGames.Representation.FiniteToHistory
