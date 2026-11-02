/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderPhases.LeaderBoundaryInstructions
import DistributedSynthesis.Library.Computability.FiniteSearch

/-! The input-dependent boundary width is an explicit arithmetic function.
The graph delay and graph-component bound remain fixed before the instance. -/
namespace Characterisation.EncodedBoundaryWidth
open DistributedSynthesis
attribute [local irreducible] Primrec

def width (graphBound delay one two : Nat) :=
  graphBound*((one+two+1)^delay)^2 + graphBound*((one+two+1)^(delay+1))^2
def bound (graphBound delay one two : Nat) := width graphBound delay one two+1

theorem width_primrec : Primrec (fun x : Nat × Nat × Nat × Nat => width x.1 x.2.1 x.2.2.1 x.2.2.2) := by
  have pow : Primrec₂ (fun a b : Nat => a ^ b) := Primrec₂.unpaired'.mp Nat.Primrec.pow
  have hK : Primrec (fun x : Nat × Nat × Nat × Nat => x.1) := Primrec.fst
  have hd : Primrec (fun x : Nat × Nat × Nat × Nat => x.2.1) := Primrec.fst.comp Primrec.snd
  have hbase : Primrec (fun x : Nat × Nat × Nat × Nat => x.2.2.1+x.2.2.2+1) :=
    Primrec.succ.comp (Primrec.nat_add.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
      (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
  exact Primrec.nat_add.comp
    (Primrec.nat_mul.comp hK (pow.comp (pow.comp hbase hd) (Primrec.const 2)))
    (Primrec.nat_mul.comp hK (pow.comp (pow.comp hbase (Primrec.succ.comp hd)) (Primrec.const 2)))
theorem bound_primrec : Primrec (fun x : Nat × Nat × Nat × Nat => bound x.1 x.2.1 x.2.2.1 x.2.2.2) :=
  Primrec.succ.comp width_primrec

theorem width_eq {I₁ I₂ : Type*} [Finite I₁] [Finite I₂] (K d : Nat) :
    width K d (Nat.card I₁) (Nat.card I₂) =
      K * (Nat.card (Fin d → Option (PSum I₁ I₂)))^2 +
      K * (Nat.card (Fin (d+1) → Option (PSum I₁ I₂)))^2 := by
  simp [width,Nat.card_fun,Nat.card_congr (Equiv.psumEquivSum I₁ I₂)]

/-- All leader boundaries fit the computed width, including early rounds,
delayed checkpoints, and switches of leader. -/
theorem boundary_bound {I₁ I₂ : Type*} [Finite I₁] [Finite I₂]
    (P : List Graph → Prop) (closed : PrefixClosed P) (K : Nat)
    (bounded : ∀ g, P g → Finite (HistoryComponent P g) ∧ Nat.card (HistoryComponent P g) ≤ K)
    (d : Nat) (recent : ∀ h, P h → ∃ p, RecentOther P d h p)
    (h : EnvHistory I₁ I₂) (live : P (History.graphSequence h)) (boundary : leaderBoundary P d h = true) :
    Finite (InputHistoryComponent P h) ∧ Nat.card (InputHistoryComponent P h) ≤
      bound K d (Nat.card I₁) (Nat.card I₂) := by
  obtain ⟨finite,size⟩ := bounded_leader_boundaries_of_bound P closed K bounded d recent h live boundary
  rw [← width_eq K d] at size
  exact ⟨finite,size.trans (Nat.le_succ _)⟩

end Characterisation.EncodedBoundaryWidth
