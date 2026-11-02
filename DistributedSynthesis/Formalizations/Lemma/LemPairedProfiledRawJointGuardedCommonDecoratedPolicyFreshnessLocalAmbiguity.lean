/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonDecoratedPolicyFreshnessCarrier

/-!
# The exact local ambiguity of the freshness phase

The two finite freshness tags jointly remember which physical receive pattern
occurred in the preceding round:

* `right` gives `(false, false)`;
* `left` gives `(true, true)`; and
* `both` gives `(true, false)`.

The pair is injective, and hence a receiving endpoint can distinguish the
three cases after the partner control is delivered.  Neither marginal is
injective.  Process one cannot distinguish `left` from `both` before a
receive, and process two cannot distinguish `right` from `both`.  The two
non-existence theorems below make that information boundary explicit: no
function of one local phase bit can recover the preceding graph.

These are statements about the finite tags produced by the already local
transition maps.  They do not pass a graph, orientation, leader bit, history,
or view to an executable process.
-/

namespace DistributedSynthesis

namespace DetParityAutomaton

/-! ## Joint phase code -/

/-- The proof-side phase pair produced by one honest physical round. -/
def decoratedFreshnessGraphSides : Graph → Bool × Bool
  | .right => (false, false)
  | .left => (true, true)
  | .both => (true, false)

@[simp] theorem decoratedFreshnessGraphSides_right :
    decoratedFreshnessGraphSides .right = (false, false) :=
  rfl

@[simp] theorem decoratedFreshnessGraphSides_left :
    decoratedFreshnessGraphSides .left = (true, true) :=
  rfl

@[simp] theorem decoratedFreshnessGraphSides_both :
    decoratedFreshnessGraphSides .both = (true, false) :=
  rfl

/-- Jointly, the two locally maintained phase tags identify the physical
receive pattern. -/
theorem decoratedFreshnessGraphSides_injective :
    Function.Injective decoratedFreshnessGraphSides := by
  intro first second h
  cases first <;> cases second <;>
    simp [decoratedFreshnessGraphSides] at h ⊢

/-- Total proof-side decoder.  The `(false, true)` case is unreachable under
the freshness invariant and is harmlessly totalized by `both`. -/
def graphOfDecoratedFreshnessSides : Bool × Bool → Graph
  | (false, false) => .right
  | (true, true) => .left
  | _ => .both

@[simp] theorem graphOfDecoratedFreshnessSides_graphSides (graph : Graph) :
    graphOfDecoratedFreshnessSides (decoratedFreshnessGraphSides graph) =
      graph := by
  cases graph <;> rfl

/-! ## The two unavoidable marginal collisions -/

/-- Process one's local bit conflates a preceding strict-left round with a
preceding simultaneous round. -/
@[simp] theorem decoratedFreshnessGraphSides_one_left_eq_both :
    (decoratedFreshnessGraphSides .left).1 =
      (decoratedFreshnessGraphSides .both).1 :=
  rfl

/-- Process two's local bit conflates a preceding strict-right round with a
preceding simultaneous round. -/
@[simp] theorem decoratedFreshnessGraphSides_two_right_eq_both :
    (decoratedFreshnessGraphSides .right).2 =
      (decoratedFreshnessGraphSides .both).2 :=
  rfl

/-- No process-one-local phase decoder can recover the preceding graph. -/
theorem no_graph_decoder_from_decoratedFreshnessOnePhase :
    ¬ ∃ decode : Bool → Graph,
      ∀ graph, decode (decoratedFreshnessGraphSides graph).1 = graph := by
  rintro ⟨decode, hdecode⟩
  have hleft := hdecode .left
  have hboth := hdecode .both
  have : Graph.left = Graph.both := hleft.symm.trans hboth
  cases this

/-- No process-two-local phase decoder can recover the preceding graph. -/
theorem no_graph_decoder_from_decoratedFreshnessTwoPhase :
    ¬ ∃ decode : Bool → Graph,
      ∀ graph, decode (decoratedFreshnessGraphSides graph).2 = graph := by
  rintro ⟨decode, hdecode⟩
  have hright := hdecode .right
  have hboth := hdecode .both
  have : Graph.right = Graph.both := hright.symm.trans hboth
  cases this

end DetParityAutomaton

end DistributedSynthesis
