/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemFiniteCrossAnchorLocalCarrier

/-!
# Finite descriptors pinned to two literal semantic records

At a hidden cross anchor, acceptance of the two restarted monitors is not by
itself enough: the finite replacement must begin with the two records of the
literal semantic blocks from which it was extracted.  This file packages
those record predicates into the finite descriptor, before simultaneous
rationalization.

The first predicate reconstructs the root record from its input.  The second
reconstructs the next record from the two inputs carried by the candidate
records.  Thus both predicates are finite truth tables.  Histories, graphs,
orientations, leaders, and the hidden member never occur in the resulting
sender state or transition.
-/

namespace DistributedSynthesis

universe u v x y w d z

noncomputable section

variable {RIn : Type u} {SIn : Type v} {ROut : Type x} {SOut : Type y}
variable [Inhabited RIn] [Inhabited SIn] [Inhabited ROut]
variable [Fintype RIn] [Fintype SIn] [Fintype ROut] [Fintype SOut]
variable [DecidableEq RIn] [DecidableEq SIn]

/-! ## Exact finite prefix predicates -/

/-- A record is the literal root record of the supplied semantic receiver and
sender.  Its input coordinate supplies everything needed to recompute it. -/
def finiteCrossAnchorLiteralFirstAllowed
    (receiver : ReceiverBlockStrategy RIn SIn ROut)
    (sender : SenderBlockStrategy SIn SOut)
    (record : RealizedBlockRound RIn SIn ROut SOut) : Bool := by
  classical
  exact decide
    (record = (record.1, receiver [] record.1, sender [] record.1.2))

/-- The second literal record is reconstructible from the two input
coordinates: the first input is the one-element past, and the second is the
current input. -/
def finiteCrossAnchorLiteralSecondAllowed
    (receiver : ReceiverBlockStrategy RIn SIn ROut)
    (sender : SenderBlockStrategy SIn SOut)
    (first second : RealizedBlockRound RIn SIn ROut SOut) : Bool := by
  classical
  exact decide
    (second =
      (second.1, receiver [first.1] second.1,
        sender [first.1.2] second.1.2))

omit [Inhabited RIn] [Inhabited SIn] [Inhabited ROut] [Fintype RIn] [Fintype SIn]
    [Fintype ROut] [Fintype SOut] in
@[simp] theorem finiteCrossAnchorLiteralFirstAllowed_pairPlay
    (receiver : ReceiverBlockStrategy RIn SIn ROut)
    (sender : SenderBlockStrategy SIn SOut)
    (env : Nat → RIn × SIn) :
    finiteCrossAnchorLiteralFirstAllowed receiver sender
      (pairPlay receiver sender env 0) = true := by
  simp [finiteCrossAnchorLiteralFirstAllowed, pairPlay, treePlay, treeOfPair,
    blockLabelApply, branchNode, senderWord]

omit [Inhabited RIn] [Inhabited SIn] [Inhabited ROut] [Fintype RIn] [Fintype SIn]
    [Fintype ROut] [Fintype SOut] in
@[simp] theorem finiteCrossAnchorLiteralSecondAllowed_pairPlay
    (receiver : ReceiverBlockStrategy RIn SIn ROut)
    (sender : SenderBlockStrategy SIn SOut)
    (env : Nat → RIn × SIn) :
    finiteCrossAnchorLiteralSecondAllowed receiver sender
      (pairPlay receiver sender env 0) (pairPlay receiver sender env 1) =
        true := by
  simp [finiteCrossAnchorLiteralSecondAllowed, pairPlay, treePlay, treeOfPair,
    blockLabelApply, branchNode, senderWord]

/-! ## Descriptor wrapper -/

namespace BlockRecordMonitor

/-- Raise a finite record monitor's state universe without changing its
physical run or priority sequence. -/
def raiseState
    (M : BlockRecordMonitor.{u, v, x, y, w} RIn SIn ROut SOut) :
    BlockRecordMonitor.{u, v, x, y, max w z} RIn SIn ROut SOut where
  State := ULift.{z, w} M.State
  stateFinite := inferInstance
  initial := ULift.up M.initial
  step := fun state record ↦ ULift.up (M.step state.down record)
  priority := fun state ↦ M.priority state.down

omit [Inhabited RIn] [Inhabited SIn] [Inhabited ROut] [Fintype RIn] [Fintype SIn]
    [Fintype ROut] [Fintype SOut] [DecidableEq RIn] [DecidableEq SIn] in
@[simp] theorem raiseState_run_down
    (M : BlockRecordMonitor.{u, v, x, y, w} RIn SIn ROut SOut)
    (play : Nat → RealizedBlockRound RIn SIn ROut SOut) :
    ∀ n, ((raiseState.{u, v, x, y, w, z} M).run play n).down =
      M.run play n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [BlockRecordMonitor.run]
      change M.step
          (((raiseState.{u, v, x, y, w, z} M).run play n).down)
          (play n) = M.step (M.run play n) (play n)
      rw [ih]

omit [Inhabited RIn] [Inhabited SIn] [Inhabited ROut] [Fintype RIn] [Fintype SIn]
    [Fintype ROut] [Fintype SOut] [DecidableEq RIn] [DecidableEq SIn] in
/-- Raising the state universe preserves the accepted plays exactly. -/
theorem raiseState_winsPlay_iff
    (M : BlockRecordMonitor.{u, v, x, y, w} RIn SIn ROut SOut)
    (play : Nat → RealizedBlockRound RIn SIn ROut SOut) :
    (raiseState.{u, v, x, y, w, z} M).WinsPlay play ↔
      M.WinsPlay play := by
  unfold BlockRecordMonitor.WinsPlay
  have hseq :
      (fun n ↦ (raiseState.{u, v, x, y, w, z} M).priority
        ((raiseState.{u, v, x, y, w, z} M).run play n)) =
      (fun n ↦ M.priority (M.run play n)) := by
    funext n
    change M.priority
        (((raiseState.{u, v, x, y, w, z} M).run play n).down) =
      M.priority (M.run play n)
    rw [raiseState_run_down]
  rw [hseq]

end BlockRecordMonitor

variable {Descriptor : Type d} [Fintype Descriptor]
variable (monitor : Descriptor →
  BlockRecordMonitor.{u, v, x, y, max u v x y d} RIn SIn ROut SOut)

/-- A finite monitor descriptor together with the two exact prefix truth
tables which must survive its simultaneous narrowing. -/
structure FiniteCrossAnchorLiteralPrefixDescriptorData
    (Descriptor : Type d) where
  base : Descriptor
  firstAllowed : RealizedBlockRound RIn SIn ROut SOut → Bool
  secondAllowed : RealizedBlockRound RIn SIn ROut SOut →
    RealizedBlockRound RIn SIn ROut SOut → Bool

/-- The descriptor lives in the joint universe of its finite truth tables and
the underlying finite monitor descriptor. -/
abbrev FiniteCrossAnchorLiteralPrefixDescriptor :=
  FiniteCrossAnchorLiteralPrefixDescriptorData
    (RIn := RIn) (SIn := SIn) (ROut := ROut) (SOut := SOut) Descriptor

noncomputable instance finiteCrossAnchorLiteralPrefixDescriptorFintype :
    Fintype (FiniteCrossAnchorLiteralPrefixDescriptor
      (RIn := RIn) (SIn := SIn) (ROut := ROut) (SOut := SOut)
      (Descriptor := Descriptor)) := by
  classical
  let Record := RealizedBlockRound RIn SIn ROut SOut
  let Rep := Descriptor × (Record → Bool) × (Record → Record → Bool)
  let equiv :
      FiniteCrossAnchorLiteralPrefixDescriptorData
          (RIn := RIn) (SIn := SIn) (ROut := ROut) (SOut := SOut)
          Descriptor ≃ Rep :=
    { toFun := fun descriptor ↦
        (descriptor.base, descriptor.firstAllowed, descriptor.secondAllowed)
      invFun := fun descriptor ↦
        ⟨descriptor.1, descriptor.2.1, descriptor.2.2⟩
      left_inv := by intro descriptor; cases descriptor; rfl
      right_inv := by
        intro descriptor
        rcases descriptor with ⟨base, first, second⟩
        rfl }
  letI : Fintype
      (FiniteCrossAnchorLiteralPrefixDescriptorData
        (RIn := RIn) (SIn := SIn) (ROut := ROut) (SOut := SOut)
        Descriptor) := Fintype.ofEquiv Rep equiv.symm
  infer_instance

/-- The wrapped monitor ignores the prefix truth tables; they are consumed by
`FiniteCrossAnchorDescriptorFirstTwoMove` outside the base monitor. -/
abbrev finiteCrossAnchorLiteralPrefixMonitor
    (descriptor : FiniteCrossAnchorLiteralPrefixDescriptor
      (RIn := RIn) (SIn := SIn) (ROut := ROut) (SOut := SOut)
      (Descriptor := Descriptor)) :=
  monitor descriptor.base

/-- Read the first-record table stored in the selected descriptor. -/
def finiteCrossAnchorLiteralPrefixFirstAllowed
    (pair : FiniteCrossAnchorDescriptorPair
      (finiteCrossAnchorLiteralPrefixMonitor monitor))
    (anchor : Bool) : RealizedBlockRound RIn SIn ROut SOut → Bool :=
  (pair.descriptor anchor).firstAllowed

/-- Read the second-record table stored in the selected descriptor. -/
def finiteCrossAnchorLiteralPrefixSecondAllowed
    (pair : FiniteCrossAnchorDescriptorPair
      (finiteCrossAnchorLiteralPrefixMonitor monitor))
    (anchor : Bool) : RealizedBlockRound RIn SIn ROut SOut →
      RealizedBlockRound RIn SIn ROut SOut → Bool :=
  (pair.descriptor anchor).secondAllowed

/-- The fixed finite outer alphabet of prefix-pinned cross-anchor tables over
one finite base-monitor descriptor family. -/
noncomputable abbrev FiniteCrossAnchorLiteralPrefixMove :=
  FiniteCrossAnchorDescriptorFirstTwoMove
    (finiteCrossAnchorLiteralPrefixMonitor monitor)
    (finiteCrossAnchorLiteralPrefixFirstAllowed monitor)
    (finiteCrossAnchorLiteralPrefixSecondAllowed monitor)

noncomputable instance finiteCrossAnchorLiteralPrefixMoveFintype :
    Fintype (FiniteCrossAnchorLiteralPrefixMove monitor) := by
  classical
  infer_instance

/-! ## Occurrence-level construction -/

/-- Package two concrete base descriptors and their two literal semantic
blocks into one member of the fixed finite move alphabet.  The common sender
is chosen once, before the hidden Boolean is resolved. -/
noncomputable def finiteCrossAnchorLiteralPrefixMove
    (baseDescriptor : Bool → Descriptor)
    (start : ∀ anchor, (monitor (baseDescriptor anchor)).State)
    (receiver : Bool → ReceiverBlockStrategy RIn SIn ROut)
    (sender : SenderBlockStrategy SIn SOut)
    (hwin : ∀ anchor env,
      ((monitor (baseDescriptor anchor)).restartAt (start anchor)).WinsPlay
        (pairPlay (receiver anchor) sender env)) :
    FiniteCrossAnchorLiteralPrefixMove monitor := by
  let descriptor : Bool →
      FiniteCrossAnchorLiteralPrefixDescriptor
        (RIn := RIn) (SIn := SIn) (ROut := ROut) (SOut := SOut)
        (Descriptor := Descriptor) := fun anchor ↦
    { base := baseDescriptor anchor
      firstAllowed := finiteCrossAnchorLiteralFirstAllowed
        (receiver anchor) sender
      secondAllowed := finiteCrossAnchorLiteralSecondAllowed
        (receiver anchor) sender }
  let pair : FiniteCrossAnchorDescriptorPair
      (finiteCrossAnchorLiteralPrefixMonitor monitor) :=
    { descriptor := descriptor
      start := start }
  apply finiteCrossAnchorDescriptorFirstTwoMove
    (finiteCrossAnchorLiteralPrefixMonitor monitor)
    (finiteCrossAnchorLiteralPrefixFirstAllowed monitor)
    (finiteCrossAnchorLiteralPrefixSecondAllowed monitor)
    pair receiver sender
  · intro anchor env
    exact hwin anchor env
  · intro anchor env
    exact finiteCrossAnchorLiteralFirstAllowed_pairPlay
      (receiver anchor) sender env
  · intro anchor env
    exact finiteCrossAnchorLiteralSecondAllowed_pairPlay
      (receiver anchor) sender env

end

end DistributedSynthesis
