/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Formalizations.Lemma.LemScalingLTL
import DistributedSynthesis.Formalizations.Undecidability.OneCounterRows

/-!
# Position residues and orientation

Manuscript source label: `lem:posord`.

## Paper statement

Let $f$ realize $\posord$. For all $r\geq 1$, in the view complex of $f$ at round $r$, $\pos(r,i) \equiv i \bmod 3$ for all $0\leq i\leq 3^r$.
    Moreover, for all $h\in\Gamma^r$, the left endpoint of $J(h)$ is process 1's view if and only if  $\proj{f_2(v_2(h))}{\pos}\equiv \proj{f_1(v_1(h))}{\pos} +1 \bmod 3$.

## Correspondence

The position output uses modulo three. position_rows covers both endpoints of every
nonempty history; the orientation declarations identify the left endpoint. Paper rounds
start at 1; execution indices start at 0.

## Reading the proof

See the [proof locations](PROOFS.md#position-residues-and-orientation) for direct links to the
underlying declarations. The full Lean statements and proofs follow below.
-/

open DistributedSynthesis Characterisation
open DistributedSynthesis.CounterMachine.OneCounter

namespace DistributedSynthesis.Paper.PositionOrder

universe u_1

/-- Reuses `DistributedSynthesis.CounterMachine.OneCounter.position_rows`. -/
theorem position_rows :
    ∀ {Q : Type u_1}
      (σ : StrategyPair Unit Unit (Output Q) (Output Q)),
      (∀ (env : EnvironmentSequence Unit Unit), Position (execution σ env)) →
        ∀ (h : List Graph),
          0 < h.length →
            (σ.one (FullViewPath.evaluate h).one).residue =
                ScalingSafety.ResidueLTL.mod3 (ScalingSafety.coordinate (FullViewPath.evaluate h).one) ∧
              (σ.two (FullViewPath.evaluate h).two).residue =
                ScalingSafety.ResidueLTL.mod3 (ScalingSafety.coordinate (FullViewPath.evaluate h).two) :=
  @_root_.DistributedSynthesis.CounterMachine.OneCounter.position_rows

/-- Reuses `DistributedSynthesis.ScalingSafety.ResidueLTL.oriented_decode`. -/
theorem oriented_decode :
    ∀ (t : Bool) (xy : ScalingSafety.ResidueLTL.Residues),
      ScalingSafety.ResidueLTL.Oriented t xy → ScalingSafety.ResidueLTL.decode xy = t :=
  @_root_.DistributedSynthesis.ScalingSafety.ResidueLTL.oriented_decode

/-- Reuses `DistributedSynthesis.ScalingSafety.ResidueLTL.monitor_orientation`. -/
theorem monitor_orientation :
    ∀ (w : OmegaWord ScalingSafety.ResidueLTL.Letter),
      ScalingSafety.ResidueLTL.ResidueValid w →
        ∀ (n : ℕ),
          ScalingSafety.ResidueLTL.Oriented (ScalingSafety.ResidueLTL.monitor w (n + 1)).oneLeft
            (ScalingSafety.ResidueLTL.residues (w n)) :=
  @_root_.DistributedSynthesis.ScalingSafety.ResidueLTL.monitor_orientation


/-- The residue test gives the orientation of the actual execution edge.
Only the position formula is assumed, independently of every other clause. -/
theorem position_decodes_view_orientation {Q : Type*}
    (f : StrategyPair Unit Unit (Output Q) (Output Q))
    (env : EnvironmentSequence Unit Unit) (position : Position (execution f env)) (n : Nat) :
    oneLeft (execution f env n) =
      (FullViewPath.evaluate
        (BlockEmbedding.graphPrefix (fun k => (env k).graph) (n + 1))).oneLeft := by
  have lifted : CounterMachine.ResidueLTL.ResidueValid
      (execution (mapStrategy embed embed f) env) := by
    rw [map_execution]
    exact (position_embed_iff _).mpr position
  have orientation := CounterMachine.Paper.position_decodes_view_orientation
    (mapStrategy embed embed f) env lifted n
  rw [map_execution] at orientation
  exact orientation

end DistributedSynthesis.Paper.PositionOrder
