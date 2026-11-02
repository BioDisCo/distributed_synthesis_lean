/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemSourceFreeBeliefNodeRationalization

/-!
# Reading a source-free move from the rational policy

`SourceFreeBeliefSemanticCertificate.hasRationalRun` produces a rational run,
and hence a finite-state rational transition policy.  This file records the
small, unconditional adapter that can legitimately be read from such a
policy: at every reachable finite policy state there is one finite move whose
complete successor table is exactly the advertised source-free `next` table
together with the universal hidden-thread update.

This does not claim that the arbitrary proof-side `Direction` is a finite
runtime observation.  A model instantiation must still show that the concrete
successor table is implemented by finite local controls (or, equivalently,
provide a finite global round machine and a local presentation of it).
-/

namespace DistributedSynthesis

universe u v w x z a

section

variable {Direction : Type u} {Move : Type v} {BeliefCode : Type z}
variable [Fintype BeliefCode]
variable
  (U : FiniteThreadSystem.{max u v, w, x} (Move × Direction))
  (initialCode : BeliefCode)
  (Valid : BeliefCode → Move → Prop)
  (next : BeliefCode → Move → Direction → BeliefCode)

abbrev SourceFreeBeliefRationalPolicy :=
  (sourceFreeBeliefNodeRunAutomaton U initialCode Valid next)
    |>.RationalTransitionPolicy

namespace SourceFreeBeliefRationalPolicy

/-- A finite policy state is reachable when it labels a node of the selected
rational run. -/
def Reachable
    (policy : SourceFreeBeliefRationalPolicy U initialCode Valid next)
    (state :
      (sourceFreeBeliefNodeRunAutomaton U initialCode Valid next).State) :
    Prop :=
  ∃ node, policy.run node = state

/-- A move realizes the complete source-free transition selected by the
rational policy at one finite state. -/
def MoveRealizesAt
    (policy : SourceFreeBeliefRationalPolicy U initialCode Valid next)
    (state :
      (sourceFreeBeliefNodeRunAutomaton U initialCode Valid next).State)
    (move : Move) : Prop :=
  Valid state.1 move ∧
    ∀ direction,
      policy.successor state direction =
        (next state.1 move direction,
          U.universalRunDPA.step state.2 (move, direction))

/-- At a reachable state, policy legality exposes one finite move whose whole
successor function is the source-free code update and hidden-thread update.
The move is shared by all directions and contains no semantic representative.
-/
theorem exists_sourceFreeMove
    (policy : SourceFreeBeliefRationalPolicy U initialCode Valid next)
    (state :
      (sourceFreeBeliefNodeRunAutomaton U initialCode Valid next).State)
    (hreachable : policy.Reachable U initialCode Valid next state) :
    ∃ move : Move,
      policy.MoveRealizesAt U initialCode Valid next state move := by
  rcases hreachable with ⟨node, hnode⟩
  have hlegal := policy.legal_at node
  rw [hnode] at hlegal
  simpa [sourceFreeBeliefNodeRunAutomaton] using hlegal

/-- In particular, the public-code component of every reachable successor is
literally the source-free `next` function for the selected shared move. -/
theorem exists_sourceFreeMove_code
    (policy : SourceFreeBeliefRationalPolicy U initialCode Valid next)
    (state :
      (sourceFreeBeliefNodeRunAutomaton U initialCode Valid next).State)
    (hreachable : policy.Reachable U initialCode Valid next state) :
    ∃ move : Move,
      Valid state.1 move ∧
        ∀ direction,
          (policy.successor state direction).1 =
            next state.1 move direction := by
  rcases policy.exists_sourceFreeMove U initialCode Valid next state hreachable
      with ⟨move, hvalid, hsuccessor⟩
  exact ⟨move, hvalid, fun direction =>
    congrArg Prod.fst (hsuccessor direction)⟩

end SourceFreeBeliefRationalPolicy

namespace SourceFreeBeliefSemanticCertificate

variable
  (raw : SourceFreeBeliefSemanticTree.{u, v, z, a}
    Direction Move BeliefCode)
  (certificate : SourceFreeBeliefSemanticCertificate U initialCode Valid next
    raw)

include certificate

/-- The exact checked post-certificate endpoint: one application of the
input-free basis yields a finite-state rational transition policy. -/
theorem nonempty_rationalPolicy
    (basis :
      (sourceFreeBeliefNodeRunAutomaton U initialCode Valid next)
        |>.RationalRunBasis) :
    Nonempty (SourceFreeBeliefRationalPolicy U initialCode Valid next) := by
  exact
    InputFreeRunParityTreeAutomaton.nonempty_rationalTransitionPolicy_of_hasRationalRun
      (sourceFreeBeliefNodeRunAutomaton U initialCode Valid next)
      (SourceFreeBeliefSemanticCertificate.hasRationalRun
        U initialCode Valid next raw certificate basis)

end SourceFreeBeliefSemanticCertificate

end

end DistributedSynthesis
