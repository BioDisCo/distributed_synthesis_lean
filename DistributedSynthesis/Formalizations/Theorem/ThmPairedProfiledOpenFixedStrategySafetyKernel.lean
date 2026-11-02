/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemSafetyTreePositionalization
import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledOpenPolicyFreeFamilyStep
import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledOpenObservableThreads

/-!
# A fixed-strategy semantic safety kernel for open family blocks

This is the Bérard-style construction before runtime-controller compilation.
The move at a public epoch observation is an entire finite
synchronization-to-synchronization block table.  Proof state remembers that
the public family is realized by one *fixed* winning distributed strategy.
It is never a distinguished root, orientation flag, or strict-leader bit.

The public successor check below uses the literal view class emitted by the
table, rather than only its root set.  A consistent successor is equipped by
the existing pointed-child theorem with a realization by the same strategy;
an inconsistent announcement goes to the harmless sink.  Thus the semantic
kernel cannot reselect a root or change the realizing strategy at an
alternating boundary.
-/

namespace DistributedSynthesis

universe u v x y s

namespace DetParityAutomaton

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable
  (A : DetParityAutomaton.{max u v x y, s}
    (RoundRecord In₁ In₂ Graph Out₁ Out₂))

section

noncomputable section

variable [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]
variable [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
variable [DecidableEq In₁] [DecidableEq In₂]

/-! ## Literal public successor -/

/-- Public view class literally emitted by one finite block resolution.
Unlike `ProfiledOpenRepresentableMove.successor`, this keeps the class itself,
not only its finite root image. -/
noncomputable def ProfiledOpenRepresentableMove.successorObservation
    (move : ProfiledOpenRepresentableMove A)
    (direction : ProfiledOpenClassifiedDirection A) :
    ProfiledOpenObservation A := by
  classical
  cases move with
  | sink => exact .sink
  | right source table =>
      if hvalid : ProfiledOpenRepresentableMove.Valid A (.right source table)
      then
        match direction with
        | .fromOne root row past input =>
            if hmem : root ∈ source.1 then
              let member : {root // root ∈ source.1} := ⟨root, hmem⟩
              let output := profiledOpenRightRepresentableOutputAt A source
                table member (omegaOfList (past ++ [input])) past.length
              exact .left (output.2 row).2
            else exact .sink
        | .fromTwo _ _ _ _ => exact .sink
      else exact .sink
  | left source table =>
      if hvalid : ProfiledOpenRepresentableMove.Valid A (.left source table)
      then
        match direction with
        | .fromTwo root row past input =>
            if hmem : root ∈ source.1 then
              let member : {root // root ∈ source.1} := ⟨root, hmem⟩
              let output := profiledOpenLeftRepresentableOutputAt A source
                table member (omegaOfList (past ++ [input])) past.length
              exact .right (output.2 row).2
            else exact .sink
        | .fromOne _ _ _ _ => exact .sink
      else exact .sink

/-! ## Same-strategy realizability -/

/-- A public family is realized by the fixed raw winning strategy and basis.
The `Nonempty` wrapper keeps semantic representatives proof-only. -/
def ProfiledOpenFixedStrategyGood
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (basis : ∀ state : PairedProfiledTreeState A,
      (pairedProfiledEntryRunAutomaton A state).RationalRunBasis) :
    ProfiledOpenObservation A → Prop
  | .sink => True
  | .right source =>
      Nonempty (ProfiledOpenRightRealization A strategy hwin basis source)
  | .left source =>
      Nonempty (ProfiledOpenLeftRealization A strategy hwin basis source)

/-- Whole-block move selected from a same-strategy realization. -/
noncomputable def profiledOpenFixedStrategyMove
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (basis : ∀ state : PairedProfiledTreeState A,
      (pairedProfiledEntryRunAutomaton A state).RationalRunBasis)
    (observation : ProfiledOpenObservation A)
    (hgood : ProfiledOpenFixedStrategyGood A strategy hwin basis observation) :
    ProfiledOpenRepresentableMove A :=
  match observation with
  | .sink => .sink
  | .right _ => (Classical.choice hgood).representableMove A
  | .left _ => (Classical.choice hgood).representableMove A

/-- The fixed-strategy move is legal at exactly its public family. -/
theorem profiledOpenFixedStrategyMove_valid
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (basis : ∀ state : PairedProfiledTreeState A,
      (pairedProfiledEntryRunAutomaton A state).RationalRunBasis)
    (observation : ProfiledOpenObservation A)
    (hgood : ProfiledOpenFixedStrategyGood A strategy hwin basis observation) :
    ProfiledOpenObservableMoveValid A observation
      (profiledOpenFixedStrategyMove A strategy hwin basis observation
        hgood) := by
  cases observation with
  | sink => exact ⟨trivial, rfl⟩
  | right source =>
      let realization : ProfiledOpenRightRealization A strategy hwin basis
          source := Classical.choice hgood
      simpa [profiledOpenFixedStrategyMove, realization] using
        realization.observableMove_valid A
  | left source =>
      let realization : ProfiledOpenLeftRealization A strategy hwin basis
          source := Classical.choice hgood
      simpa [profiledOpenFixedStrategyMove, realization] using
        realization.observableMove_valid A

/-! ## Public graph-blind successor and closure -/

/-- Accept an announced next class exactly when some proof-side resolution of
the current whole-block table literally emits it.  Otherwise enter `sink`.
The existential direction is used only to prove semantic closure; it is not
part of the returned finite state. -/
noncomputable def profiledOpenFixedStrategySafetyNext
    (observation : ProfiledOpenObservation A)
    (move : ProfiledOpenRepresentableMove A)
    (announced : ProfiledOpenObservation A) : ProfiledOpenObservation A := by
  classical
  if ∃ direction : ProfiledOpenClassifiedDirection A,
      direction.anchor A ∈ observation.roots A ∧
        move.successorObservation A direction = announced
  then exact announced
  else exact .sink

/-- The decisive closure law.  Every consistent alternating successor of a
fixed-strategy whole-block move is again realized by that same strategy.
No root is chosen at the successor boundary: the pointed child returned by
the literal parent resolution supplies the realization. -/
theorem profiledOpenFixedStrategyGood_next
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (basis : ∀ state : PairedProfiledTreeState A,
      (pairedProfiledEntryRunAutomaton A state).RationalRunBasis)
    (observation : ProfiledOpenObservation A)
    (hgood : ProfiledOpenFixedStrategyGood A strategy hwin basis observation)
    (announced : ProfiledOpenObservation A) :
    ProfiledOpenFixedStrategyGood A strategy hwin basis
      (profiledOpenFixedStrategySafetyNext A observation
        (profiledOpenFixedStrategyMove A strategy hwin basis observation
          hgood) announced) := by
  classical
  unfold profiledOpenFixedStrategySafetyNext
  split_ifs with hconsistent
  · rcases hconsistent with ⟨direction, hsource, hnext⟩
    cases observation with
    | sink =>
        cases direction <;>
          simp [ProfiledOpenObservation.roots,
            ProfiledOpenClassifiedDirection.anchor] at hsource
    | right source =>
        let realization : ProfiledOpenRightRealization A strategy hwin basis
            source := Classical.choice hgood
        cases direction with
        | fromTwo root row past input =>
            simp [ProfiledOpenObservation.roots,
              profiledOpenRightClassifiedRoots,
              ProfiledOpenClassifiedDirection.anchor] at hsource
        | fromOne root row past input =>
            have hmem : root ∈ source.1 := by
              simpa [ProfiledOpenObservation.roots,
                profiledOpenRightClassifiedRoots,
                ProfiledOpenClassifiedDirection.anchor] using hsource
            let member : {root // root ∈ source.1} := ⟨root, hmem⟩
            let output := profiledOpenRightRepresentableOutputAt A source
              (realization.coherentTable A).table member
              (omegaOfList (past ++ [input])) past.length
            have hmove :
                profiledOpenFixedStrategyMove A strategy hwin basis
                    (.right source) hgood =
                  .right source (realization.coherentTable A).table := by
              rfl
            have hvalid : ProfiledOpenRepresentableMove.Valid A
                (.right source (realization.coherentTable A).table) := by
              exact realization.representableMove_valid A
            have hsuccessor :
                (profiledOpenFixedStrategyMove A strategy hwin basis
                    (.right source) hgood).successorObservation A
                    (.fromOne root row past input) =
                  .left (output.2 row).2 := by
              rw [hmove]
              simp [
                ProfiledOpenRepresentableMove.successorObservation,
                member, output, hvalid, hmem]
            rw [hsuccessor] at hnext
            subst announced
            obtain ⟨semanticPast, child, _hsuccessor, _houtput, _hmemory⟩ :=
              exists_profiledOpenRightPolicyFreeFamilyStep A realization
                member row past input
            exact ⟨child.realization⟩
    | left source =>
        let realization : ProfiledOpenLeftRealization A strategy hwin basis
            source := Classical.choice hgood
        cases direction with
        | fromOne root row past input =>
            simp [ProfiledOpenObservation.roots,
              profiledOpenLeftClassifiedRoots,
              ProfiledOpenClassifiedDirection.anchor] at hsource
        | fromTwo root row past input =>
            have hmem : root ∈ source.1 := by
              simpa [ProfiledOpenObservation.roots,
                profiledOpenLeftClassifiedRoots,
                ProfiledOpenClassifiedDirection.anchor] using hsource
            let member : {root // root ∈ source.1} := ⟨root, hmem⟩
            let output := profiledOpenLeftRepresentableOutputAt A source
              (realization.coherentTable A).table member
              (omegaOfList (past ++ [input])) past.length
            have hmove :
                profiledOpenFixedStrategyMove A strategy hwin basis
                    (.left source) hgood =
                  .left source (realization.coherentTable A).table := by
              rfl
            have hvalid : ProfiledOpenRepresentableMove.Valid A
                (.left source (realization.coherentTable A).table) := by
              exact realization.representableMove_valid A
            have hsuccessor :
                (profiledOpenFixedStrategyMove A strategy hwin basis
                    (.left source) hgood).successorObservation A
                    (.fromTwo root row past input) =
                  .right (output.2 row).2 := by
              rw [hmove]
              simp [
                ProfiledOpenRepresentableMove.successorObservation,
                member, output, hvalid, hmem]
            rw [hsuccessor] at hnext
            subst announced
            obtain ⟨semanticPast, child, _hsuccessor, _houtput, _hmemory⟩ :=
              exists_profiledOpenLeftPolicyFreeFamilyStep A realization
                member row past input
            exact ⟨child.realization⟩
  · trivial

/-- The closed semantic kernel, ready for generic safety positionalization.
Its public state and move types are finite; all raw histories stay in `Good`.
-/
noncomputable def profiledOpenFixedStrategySafetyKernel
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (basis : ∀ state : PairedProfiledTreeState A,
      (pairedProfiledEntryRunAutomaton A state).RationalRunBasis)
    (initial : ProfiledOpenObservation A)
    (hinitial : ProfiledOpenFixedStrategyGood A strategy hwin basis initial) :
    SafetyKernel initial (profiledOpenFixedStrategySafetyNext A)
      (ProfiledOpenObservableMoveValid A) where
  Good := ProfiledOpenFixedStrategyGood A strategy hwin basis
  initial_good := hinitial
  move := fun state =>
    profiledOpenFixedStrategyMove A strategy hwin basis state.1 state.2
  legal := fun state =>
    profiledOpenFixedStrategyMove_valid A strategy hwin basis state.1 state.2
  closed := fun state announced =>
    profiledOpenFixedStrategyGood_next A strategy hwin basis state.1 state.2
      announced

end

end


end DetParityAutomaton

end DistributedSynthesis
