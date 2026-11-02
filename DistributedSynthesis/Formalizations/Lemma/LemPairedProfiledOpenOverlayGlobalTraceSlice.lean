/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledOpenOverlayEpochSlice
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledOpenRecurrentEnvironmentRecut

/-!
# Installed overlay slices inside a finite global-machine trace

`FiniteGlobalRoundMachine` exposes only its state trace and two Moore output
maps.  It does not record which witnessed overlay is installed during a given
epoch.  Consequently the exact trace/overlay join has one genuine operational
input: the global outputs during the interval agree with the outputs of the
installed overlay.

The predicates `ProfiledOpenWitnessedRightOverlayEpochOutputAgreement` and
its left mirror name exactly that input and nothing more: they compare only
the two output-coordinate lists.  Inputs and graphs are proved separately
from the literal environment slice.  Thus the main equalities below are pure
data plumbing once the final controller exposes its installed-overlay output
law.
-/

namespace DistributedSynthesis

universe i u v w x y s

/-! ## Record extensionality split into environment and outputs -/

/-- The two physical outputs of one round. -/
def RoundRecord.outputPair
    {In₁ : Type u} {In₂ : Type v} {G : Type w}
    {Out₁ : Type x} {Out₂ : Type y}
    (round : RoundRecord In₁ In₂ G Out₁ Out₂) : Out₁ × Out₂ :=
  (round.outputOne, round.outputTwo)

theorem RoundRecord.eq_of_environment_eq_of_outputPair_eq
    {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
    {left right : RoundRecord In₁ In₂ Graph Out₁ Out₂}
    (henvironment : left.environment = right.environment)
    (houtputs : left.outputPair = right.outputPair) :
    left = right := by
  cases left
  cases right
  simp_all [RoundRecord.environment, RoundRecord.outputPair]

/-- Lists of round records are determined by their environment and output
projections. -/
theorem roundRecordList_eq_of_environment_map_eq_of_outputPair_map_eq
    {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
    {left right : List (RoundRecord In₁ In₂ Graph Out₁ Out₂)}
    (henvironment : left.map RoundRecord.environment =
      right.map RoundRecord.environment)
    (houtputs : left.map RoundRecord.outputPair =
      right.map RoundRecord.outputPair) :
    left = right := by
  induction left generalizing right with
  | nil =>
      cases right with
      | nil => rfl
      | cons head tail => simp at henvironment
  | cons head tail ih =>
      cases right with
      | nil => simp at henvironment
      | cons other rest =>
          simp only [List.map_cons, List.cons.injEq] at henvironment houtputs
          rw [RoundRecord.eq_of_environment_eq_of_outputPair_eq
            henvironment.1 houtputs.1]
          rw [ih henvironment.2 houtputs.2]

namespace DetParityAutomaton

variable {I : Type i}
variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable
  (A : DetParityAutomaton.{max u v x y, s}
    (RoundRecord In₁ In₂ Graph Out₁ Out₂))

noncomputable section

variable [Fintype I] [Inhabited I]
variable [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁]
  [Inhabited Out₂]
variable [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
variable [DecidableEq In₁] [DecidableEq In₂]

variable (initialCode : ProfiledOpenIndexedBiBeliefCode A (I := I))

/-! ## Environment projections of physical overlay slices -/

omit [Inhabited I] [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
/-- A right overlay over a uniformly right-strict environment slice emits
records whose environment projection is exactly the original slice. -/
theorem profiledOpenWitnessedRightOverlayPhysicalRecords_environment
    (overlay : ProfiledOpenWitnessedRightRoundOverlay A initialCode) :
    ∀ rounds : List (EnvironmentRound In₁ In₂),
      (∀ round ∈ rounds, round.graph = .right) →
      (profiledOpenWitnessedRightOverlayPhysicalRecords A initialCode overlay
          (leftMovesOfRounds rounds)).map RoundRecord.environment = rounds := by
  intro rounds hright
  induction rounds generalizing overlay with
  | nil => rfl
  | cons round rest ih =>
      have hhead : round.graph = .right := hright round (by simp)
      have hrest : ∀ next ∈ rest, next.graph = .right := by
        intro next hnext
        exact hright next (by simp [hnext])
      cases round with
      | mk inputOne inputTwo graph =>
          simp only at hhead
          subst graph
          simp only [leftMovesOfRounds, List.map_cons,
            profiledOpenWitnessedRightOverlayPhysicalRecords_cons,
            RoundRecord.environment, rightRoundRecord]
          congr 1
          exact ih (overlay := overlay.step A initialCode inputOne inputTwo)
            hrest

omit [Inhabited I] [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
/-- Left overlay/environment mirror. -/
theorem profiledOpenWitnessedLeftOverlayPhysicalRecords_environment
    (overlay : ProfiledOpenWitnessedLeftRoundOverlay A initialCode) :
    ∀ rounds : List (EnvironmentRound In₁ In₂),
      (∀ round ∈ rounds, round.graph = .left) →
      (profiledOpenWitnessedLeftOverlayPhysicalRecords A initialCode overlay
          (leftMovesOfRounds rounds)).map RoundRecord.environment = rounds := by
  intro rounds hleft
  induction rounds generalizing overlay with
  | nil => rfl
  | cons round rest ih =>
      have hhead : round.graph = .left := hleft round (by simp)
      have hrest : ∀ next ∈ rest, next.graph = .left := by
        intro next hnext
        exact hleft next (by simp [hnext])
      cases round with
      | mk inputOne inputTwo graph =>
          simp only at hhead
          subst graph
          simp only [leftMovesOfRounds, List.map_cons,
            profiledOpenWitnessedLeftOverlayPhysicalRecords_cons,
            RoundRecord.environment, leftRoundRecord]
          congr 1
          exact ih (overlay := overlay.step A initialCode inputOne inputTwo)
            hrest

end

end DetParityAutomaton

namespace FiniteGlobalRoundMachine

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable [Fintype In₁] [Fintype In₂]
variable (G : FiniteGlobalRoundMachine.{u, v, w} In₁ In₂)

omit [Fintype In₁] [Fintype In₂] in
/-- The environment projection of a global-machine trace is definitionally
the supplied environment. -/
@[simp] theorem globalMachineTraceWord_environment
    (outputOne : G.State → Out₁) (outputTwo : G.State → Out₂)
    (env : EnvironmentSequence In₁ In₂) (n : Nat) :
    (G.globalMachineTraceWord outputOne outputTwo env n).environment = env n :=
  rfl

omit [Fintype In₁] [Fintype In₂] in
/-- The finite global trace slice has exactly the environment slice supplied
to the machine. -/
theorem globalMachineTraceWord_slice_environment
    (outputOne : G.State → Out₁) (outputTwo : G.State → Out₂)
    (env : EnvironmentSequence In₁ In₂) (start stop : Nat) :
    (DetParityAutomaton.omegaPrefix
        (OmegaWord.drop (G.globalMachineTraceWord outputOne outputTwo env) start)
        (stop - start)).map RoundRecord.environment =
      environmentSlice env start stop := by
  simp [DetParityAutomaton.omegaPrefix, OmegaWord.drop, environmentSlice,
    globalMachineTraceWord]
  funext i
  rfl

end FiniteGlobalRoundMachine

namespace DetParityAutomaton

variable {I : Type i}
variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable
  (A : DetParityAutomaton.{max u v x y, s}
    (RoundRecord In₁ In₂ Graph Out₁ Out₂))

noncomputable section

variable [Fintype I] [Inhabited I]
variable [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁]
  [Inhabited Out₂]
variable [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
variable [DecidableEq In₁] [DecidableEq In₂]

variable (initialCode : ProfiledOpenIndexedBiBeliefCode A (I := I))

/-! ## The one genuinely missing global-controller field -/

/-- During `[start, stop)`, the global machine emits exactly the two output
coordinates of the installed right overlay.  No input, graph, DPA, semantic
history, or acceptance fact is included in this predicate. -/
def ProfiledOpenWitnessedRightOverlayEpochOutputAgreement
    (G : FiniteGlobalRoundMachine.{u, v, w} In₁ In₂)
    (outputOne : G.State → Out₁) (outputTwo : G.State → Out₂)
    (env : EnvironmentSequence In₁ In₂) (start stop : Nat)
    (overlay : ProfiledOpenWitnessedRightRoundOverlay A initialCode) : Prop :=
  let rounds := environmentSlice env start stop
  (omegaPrefix
      (OmegaWord.drop (G.globalMachineTraceWord outputOne outputTwo env) start)
      rounds.length).map RoundRecord.outputPair =
    (profiledOpenWitnessedRightOverlayPhysicalRecords A initialCode overlay
      (leftMovesOfRounds rounds)).map RoundRecord.outputPair

/-- Left installed-overlay output agreement. -/
def ProfiledOpenWitnessedLeftOverlayEpochOutputAgreement
    (G : FiniteGlobalRoundMachine.{u, v, w} In₁ In₂)
    (outputOne : G.State → Out₁) (outputTwo : G.State → Out₂)
    (env : EnvironmentSequence In₁ In₂) (start stop : Nat)
    (overlay : ProfiledOpenWitnessedLeftRoundOverlay A initialCode) : Prop :=
  let rounds := environmentSlice env start stop
  (omegaPrefix
      (OmegaWord.drop (G.globalMachineTraceWord outputOne outputTwo env) start)
      rounds.length).map RoundRecord.outputPair =
    (profiledOpenWitnessedLeftOverlayPhysicalRecords A initialCode overlay
      (leftMovesOfRounds rounds)).map RoundRecord.outputPair

/-! ## Exact global trace/overlay joins -/

omit [Inhabited I] [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
/-- Once the controller's output-coordinate law is exposed, the complete
right-oriented global trace slice is the installed overlay's physical record
list. -/
theorem globalMachineTraceWord_slice_eq_rightOverlayPhysicalRecords
    (G : FiniteGlobalRoundMachine.{u, v, w} In₁ In₂)
    (outputOne : G.State → Out₁) (outputTwo : G.State → Out₂)
    (env : EnvironmentSequence In₁ In₂) (start stop : Nat)
    (overlay : ProfiledOpenWitnessedRightRoundOverlay A initialCode)
    (hright : ∀ round ∈ environmentSlice env start stop,
      round.graph = .right)
    (houtputs : ProfiledOpenWitnessedRightOverlayEpochOutputAgreement A
      initialCode G outputOne outputTwo env start stop overlay) :
    omegaPrefix
        (OmegaWord.drop (G.globalMachineTraceWord outputOne outputTwo env) start)
        (stop - start) =
      profiledOpenWitnessedRightOverlayPhysicalRecords A initialCode overlay
        (leftMovesOfRounds (environmentSlice env start stop)) := by
  apply roundRecordList_eq_of_environment_map_eq_of_outputPair_map_eq
  · rw [FiniteGlobalRoundMachine.globalMachineTraceWord_slice_environment]
    exact (profiledOpenWitnessedRightOverlayPhysicalRecords_environment A
      initialCode overlay (environmentSlice env start stop) hright).symm
  · simpa only [ProfiledOpenWitnessedRightOverlayEpochOutputAgreement,
      environmentSlice_length] using houtputs

omit [Inhabited I] [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
/-- Left-oriented exact trace join. -/
theorem globalMachineTraceWord_slice_eq_leftOverlayPhysicalRecords
    (G : FiniteGlobalRoundMachine.{u, v, w} In₁ In₂)
    (outputOne : G.State → Out₁) (outputTwo : G.State → Out₂)
    (env : EnvironmentSequence In₁ In₂) (start stop : Nat)
    (overlay : ProfiledOpenWitnessedLeftRoundOverlay A initialCode)
    (hleft : ∀ round ∈ environmentSlice env start stop,
      round.graph = .left)
    (houtputs : ProfiledOpenWitnessedLeftOverlayEpochOutputAgreement A
      initialCode G outputOne outputTwo env start stop overlay) :
    omegaPrefix
        (OmegaWord.drop (G.globalMachineTraceWord outputOne outputTwo env) start)
        (stop - start) =
      profiledOpenWitnessedLeftOverlayPhysicalRecords A initialCode overlay
        (leftMovesOfRounds (environmentSlice env start stop)) := by
  apply roundRecordList_eq_of_environment_map_eq_of_outputPair_map_eq
  · rw [FiniteGlobalRoundMachine.globalMachineTraceWord_slice_environment]
    exact (profiledOpenWitnessedLeftOverlayPhysicalRecords_environment A
      initialCode overlay (environmentSlice env start stop) hleft).symm
  · simpa only [ProfiledOpenWitnessedLeftOverlayEpochOutputAgreement,
      environmentSlice_length] using houtputs

end

end DetParityAutomaton

end DistributedSynthesis
