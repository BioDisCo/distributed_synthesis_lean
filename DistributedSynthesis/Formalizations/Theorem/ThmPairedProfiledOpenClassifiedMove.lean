/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledOpenViewClassMove
import DistributedSynthesis.Formalizations.Lemma.LemLocallyConsistentStateControlled

/-!
# Successor-classified profiled moves

A recursive open-family move must carry more than individually safe child
roots.  Each emitted row names the opposite-orientation canonical information
class that contains its child.  The law is imposed on the complete receiver
table before the environment chooses the current input, then preserved by the
fixed locally-consistent Rabin extraction.
-/

namespace DistributedSynthesis

universe u v x y w z

namespace BlockRecordMonitor

variable {RIn : Type u} {SIn : Type v} {ROut : Type x} {ROut' : Type z}
variable {SOut : Type y}

/-- Change only the receiver-output alphabet of a block monitor by a fixed
projection. -/
def comapReceiverOutput
    (base : BlockRecordMonitor.{u, v, x, y, w} RIn SIn ROut SOut)
    (project : ROut' → ROut) :
    BlockRecordMonitor.{u, v, z, y, w} RIn SIn ROut' SOut where
  State := base.State
  stateFinite := base.stateFinite
  initial := base.initial
  step := fun state letter =>
    base.step state (letter.1, project letter.2.1, letter.2.2)
  priority := base.priority

/-- Project a realized play to the old receiver-output alphabet. -/
def projectReceiverPlay
    (project : ROut' → ROut)
    (play : Nat → RealizedBlockRound RIn SIn ROut' SOut) :
    Nat → RealizedBlockRound RIn SIn ROut SOut :=
  fun n => ((play n).1, project (play n).2.1, (play n).2.2)

theorem comapReceiverOutput_run
    (base : BlockRecordMonitor.{u, v, x, y, w} RIn SIn ROut SOut)
    (project : ROut' → ROut)
    (play : Nat → RealizedBlockRound RIn SIn ROut' SOut) : ∀ n,
    (base.comapReceiverOutput project).run play n =
      base.run (projectReceiverPlay project play) n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [BlockRecordMonitor.run, BlockRecordMonitor.run, ih]
      rfl

theorem comapReceiverOutput_wins_iff
    (base : BlockRecordMonitor.{u, v, x, y, w} RIn SIn ROut SOut)
    (project : ROut' → ROut)
    (play : Nat → RealizedBlockRound RIn SIn ROut' SOut) :
    (base.comapReceiverOutput project).WinsPlay play ↔
      base.WinsPlay (projectReceiverPlay project play) := by
  change NatSeqMinEvenParity
      (fun n => base.priority
        ((base.comapReceiverOutput project).run play n)) ↔
    NatSeqMinEvenParity
      (fun n => base.priority
        (base.run (projectReceiverPlay project play) n))
  rw [show (fun n => base.priority
      ((base.comapReceiverOutput project).run play n)) =
      (fun n => base.priority
        (base.run (projectReceiverPlay project play) n)) by
    funext n
    rw [comapReceiverOutput_run base project play n]]

end BlockRecordMonitor

namespace DetParityAutomaton

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable
  (A : DetParityAutomaton.{max u v x y, w}
    (RoundRecord In₁ In₂ Graph Out₁ Out₂))

section

noncomputable section

variable [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]
variable [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
variable [DecidableEq In₁] [DecidableEq In₂]

/-- A right-block output plus, for each resolved old row, the exact open left
root and canonical new process-two information class selected at the
reversal. -/
abbrev ProfiledOpenRightClassifiedOutput :=
  ProfiledRightReceiverOutput A ×
    (PairedEntryRow → ProfiledOpenLeftRoot A × ProfiledOpenLeftViewClass A)

/-- Left-oriented mirror. -/
abbrev ProfiledOpenLeftClassifiedOutput :=
  ProfiledLeftReceiverOutput A ×
    (PairedEntryRow → ProfiledOpenRightRoot A × ProfiledOpenRightViewClass A)

noncomputable abbrev profiledOpenRightClassifiedRootMonitor
    (root : ProfiledOpenRightRoot A) :=
  (profiledOpenRightRootMonitor A root).comapReceiverOutput
    (fun output : ProfiledOpenRightClassifiedOutput A => output.1)

noncomputable abbrev profiledOpenLeftClassifiedRootMonitor
    (root : ProfiledOpenLeftRoot A) :=
  (profiledOpenLeftRootMonitor A root).comapReceiverOutput
    (fun output : ProfiledOpenLeftClassifiedOutput A => output.1)

/-- Complete-table right-to-left handoff law.  Every response, including all
hidden source members and current inputs, names an exact target root contained
in its advertised canonical successor class. -/
def ProfiledOpenRightClassifiedTableAllowed
    (source : ProfiledOpenRightViewClass A)
    (responses :
      ({root // root ∈ source.1} × In₂) × In₁ →
        ProfiledOpenRightClassifiedOutput A) : Prop :=
  ∀ member (move : In₂ × In₁) row,
    let output := responses ((member, move.1), move.2)
    output.1.target row = .inr (.inr (output.2 row).1.1) ∧
      (output.2 row).1 ∈ (output.2 row).2.1

/-- Left-to-right classified table law. -/
def ProfiledOpenLeftClassifiedTableAllowed
    (source : ProfiledOpenLeftViewClass A)
    (responses :
      ({root // root ∈ source.1} × In₁) × In₂ →
        ProfiledOpenLeftClassifiedOutput A) : Prop :=
  ∀ member (move : In₁ × In₂) row,
    let output := responses ((member, move.1), move.2)
    output.1.target row = .inr (.inl (output.2 row).1.1) ∧
      (output.2 row).1 ∈ (output.2 row).2.1

noncomputable local instance rightClassifiedAllowedDecidable
    (source : ProfiledOpenRightViewClass A) :
    DecidablePred (ProfiledOpenRightClassifiedTableAllowed A source) :=
  fun _ => Classical.propDecidable _

noncomputable local instance leftClassifiedAllowedDecidable
    (source : ProfiledOpenLeftViewClass A) :
    DecidablePred (ProfiledOpenLeftClassifiedTableAllowed A source) :=
  fun _ => Classical.propDecidable _

/-- Fixed finite right move table carrying a checked successor class on every
receiver-table entry. -/
noncomputable abbrev ProfiledOpenRightClassifiedTable
    (source : ProfiledOpenRightViewClass A) :=
  LocallyConsistentNarrowedTable
    (finiteRootFamilyMonitor
      (fun member : {root // root ∈ source.1} =>
        profiledOpenRightClassifiedRootMonitor A member.1))
    (ProfiledOpenRightClassifiedTableAllowed A source)

/-- Left classified finite table. -/
noncomputable abbrev ProfiledOpenLeftClassifiedTable
    (source : ProfiledOpenLeftViewClass A) :=
  LocallyConsistentNarrowedTable
    (finiteRootFamilyMonitor
      (fun member : {root // root ∈ source.1} =>
        profiledOpenLeftClassifiedRootMonitor A member.1))
    (ProfiledOpenLeftClassifiedTableAllowed A source)

noncomputable instance (source : ProfiledOpenRightViewClass A) :
    Fintype (ProfiledOpenRightClassifiedTable A source) := by
  classical
  infer_instance

noncomputable instance (source : ProfiledOpenLeftViewClass A) :
    Fintype (ProfiledOpenLeftClassifiedTable A source) := by
  classical
  infer_instance

end

end


end DetParityAutomaton

end DistributedSynthesis
