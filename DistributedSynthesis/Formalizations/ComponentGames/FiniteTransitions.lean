/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Formalizations.ComponentGames.FiniteArena

namespace Characterisation.ComponentGames.Representation.FiniteArena
open scoped Characterisation.ComponentGames.Representation
open DistributedSynthesis Characterisation Characterisation.PeriodicBlocks
set_option maxHeartbeats 2400000
set_option linter.unusedSectionVars false
variable {I₁ I₂ O₁ O₂ G Q : Type} {D B L : Nat}
variable [Fintype I₁] [Fintype I₂] [LinearOrder I₁] [LinearOrder I₂]
variable [Fintype O₁] [Fintype O₂] [DecidableEq O₁] [DecidableEq O₂]
variable [DecidableEq G] [DecidableEq Q]
variable (step : Q → (I₁ × I₂ × Graph) → (O₁ × O₂) → Q)
variable (χ : Q → Nat) (priorityBound : ∀ q, χ q ≤ L)

abbrev Word (I₁ I₂ : Type) (D : Nat) := BlockWord (RoundRecord I₁ I₂ Graph Unit Unit) D

def slot (P : Position G Q B) (h : P.Root) : Fin (B+1) := ⟨h.val,by have := h.isLt; have := P.1.isLt; omega⟩
theorem slot_injective (P : Position G Q B) : Function.Injective (slot P) := by
  intro h k eq; exact Fin.ext (congrArg (fun x : Fin (B+1) => x.val) eq)

def phasePriority (m : Move I₁ I₂ O₁ O₂ G Q D B) (h : m.source.Root) (w : Word I₁ I₂ D) : Fin (L+1) :=
  ⟨rangeMin (fun t => χ (stateAt step m.source.2 m.rule h w t)) 0 (D-1),by
    have small := rangeMin_le (fun t => χ (stateAt step m.source.2 m.rule h w t)) 0 (D-1) 0 (Nat.zero_le _)
    have large := priorityBound (stateAt step m.source.2 m.rule h w 0)
    simp only [Nat.zero_add] at small
    omega⟩

def endSlot (m : Move I₁ I₂ O₁ O₂ G Q D B) (K : Finset m.End) (bound : K.card ≤ B) (s : K) : Fin (B+1) :=
  ⟨(numberSubset K s).val,by have := (numberSubset K s).isLt; omega⟩

def relation (m : Move I₁ I₂ O₁ O₂ G Q D B) (K : Finset m.End) (bound : K.card ≤ B) : TransitionAlphabet B L :=
  Finset.univ.filter (fun edge => ∃ h : m.source.Root, ∃ w : Word I₁ I₂ D, ∃ s : K,
    s.val = wordScenario (m.replacement h) w ∧
    edge = (slot m.source h,phasePriority step χ priorityBound m h w,endSlot m K bound s))

theorem mem_relation (m : Move I₁ I₂ O₁ O₂ G Q D B) (K : Finset m.End) (bound : K.card ≤ B)
    (h : Fin (B+1)) (c : Fin (L+1)) (j : Fin (B+1)) :
    (h,c,j) ∈ relation step χ priorityBound m K bound ↔
      ∃ a : m.source.Root, ∃ w : Word I₁ I₂ D, ∃ s : K,
        s.val = wordScenario (m.replacement a) w ∧
        h = slot m.source a ∧ c = phasePriority step χ priorityBound m a w ∧ j = endSlot m K bound s := by
  simp only [relation,Finset.mem_filter,Finset.mem_univ,true_and,Prod.mk.injEq]

/-- All outgoing edges start at an actual root, and all incoming edges end
at a numbered member of the chosen component. Unused slots add no runs. -/
theorem relation_no_unused_slots (m : Move I₁ I₂ O₁ O₂ G Q D B) (K : Finset m.End) (bound : K.card ≤ B)
    (h : Fin (B+1)) (c : Fin (L+1)) (j : Fin (B+1))
    (edge : (h,c,j) ∈ relation step χ priorityBound m K bound) :
    h.val < m.source.1.val ∧ j.val < K.card := by
  obtain ⟨a,w,s,_,rfl,_,rfl⟩ := (mem_relation step χ priorityBound m K bound h c j).mp edge
  exact ⟨a.isLt,(numberSubset K s).isLt⟩

structure Run (moves : Nat → Move I₁ I₂ O₁ O₂ G Q D B)
    (components : ∀ n, Finset (moves n).End) (bounds : ∀ n, (components n).card ≤ B) where
  root : ∀ n, (moves n).source.Root
  word : Nat → Word I₁ I₂ D
  endpoint : ∀ n, components n
  endpoint_eq : ∀ n, (endpoint n).val = wordScenario ((moves n).replacement (root n)) (word n)
  initial : slot (moves 0).source (root 0) = 0
  next : ∀ n, slot (moves (n+1)).source (root (n+1)) = endSlot (moves n) (components n) (bounds n) (endpoint n)

def Run.Wins {moves : Nat → Move I₁ I₂ O₁ O₂ G Q D B}
    {components : ∀ n, Finset (moves n).End} {bounds : ∀ n, (components n).card ≤ B}
    (run : Run moves components bounds) : Prop :=
  NatSeqMinEvenParity (fun n => (phasePriority step χ priorityBound (moves n) (run.root n) (run.word n)).val)

/-- Exact monitor/run correspondence. In particular no uniform choice of
one priority for a source--target pair is made. -/
theorem accepts_iff_all_runs (moves : Nat → Move I₁ I₂ O₁ O₂ G Q D B)
    (components : ∀ n, Finset (moves n).End) (bounds : ∀ n, (components n).card ≤ B) :
    (MonitorCompiler.automaton (B:=B) (K:=L) 0).Accepts
      (fun n => relation step χ priorityBound (moves n) (components n) (bounds n)) ↔
      ∀ run : Run moves components bounds, run.Wins step χ priorityBound := by
  rw [MonitorCompiler.bounded_parity_monitor_effective]
  constructor
  · intro accepts run
    apply accepts (fun n => slot (moves n).source (run.root n))
      (fun n => phasePriority step χ priorityBound (moves n) (run.root n) (run.word n)) run.initial
    intro n
    exact (mem_relation step χ priorityBound _ _ _ _ _ _).mpr
      ⟨run.root n,run.word n,run.endpoint n,run.endpoint_eq n,rfl,rfl,run.next n⟩
  · intro wins h c initial edges
    have witnesses (n : Nat) := (mem_relation step χ priorityBound _ _ _ _ _ _).mp (edges n)
    choose root word endpoint eq source priority target using witnesses
    let run : Run moves components bounds :=
      { root := root, word := word, endpoint := endpoint, endpoint_eq := eq
        initial := (source 0).symm.trans initial
        next := fun n => (source (n+1)).symm.trans (target n) }
    have result := wins run
    simpa only [Run.Wins,run,← priority] using result

end Characterisation.ComponentGames.Representation.FiniteArena
