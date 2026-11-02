/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartCutOutput

/-!
# Audit of the first-then-both DPA scan

The full-restart controller's literal strict-block row sequence is `.first`
at the cut and `.both` thereafter.  The existing paired block monitor instead
tracks two constant rows.  This file isolates the exact one-record seed law
which would identify the literal mixed scan with the monitor's constant
`.both` scan.

The seed law is sufficient by plain fold congruence, but it is not implied by
the current paired-lambda interface, even together with both fixed-row
forever-acceptance and the exact initial output profile.  A two-state,
all-even DPA below gives a kernel-reduced counterexample.  Thus a successful
handoff must carry an additional mixed scan or prove a model-specific seed
law; it cannot obtain the equality from fixed-row acceptance alone.
-/

namespace DistributedSynthesis

universe u v x y s

namespace DetParityAutomaton

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable
  (A : DetParityAutomaton.{max u v x y, s}
    (RoundRecord In₁ In₂ Graph Out₁ Out₂))

/-! ## The exact missing fold law -/

/-- Physical right-block records with the operational row schedule: the
first record uses `.first`, and the remaining records use `.both`. -/
def profiledRawJointRightFirstThenBothRecords
    (letters : List (PairedRightBlockLetter
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))) :
    List (RoundRecord In₁ In₂ Graph Out₁ Out₂) :=
  match letters with
  | [] => []
  | first :: rest =>
      pairedRightRecordForRow .first first ::
        rest.map (pairedRightRecordForRow .both)

/-- Left-block mirror. -/
def profiledRawJointLeftFirstThenBothRecords
    (letters : List (PairedLeftBlockLetter
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))) :
    List (RoundRecord In₁ In₂ Graph Out₁ Out₂) :=
  match letters with
  | [] => []
  | first :: rest =>
      pairedLeftRecordForRow .first first ::
        rest.map (pairedLeftRecordForRow .both)

/-- The one-record state-and-minimum equality required before a shifted
constant-`.both` right segment can start at the actual DPA state. -/
def ProfiledRawJointRightFirstBothSeedAligned
    (code : A.State × A.State)
    (first : PairedRightBlockLetter
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)) : Prop :=
  blockEndAndMin A code.1 [pairedRightRecordForRow .first first] =
    blockEndAndMin A code.2 [pairedRightRecordForRow .both first]

/-- Left seed mirror. -/
def ProfiledRawJointLeftFirstBothSeedAligned
    (code : A.State × A.State)
    (first : PairedLeftBlockLetter
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)) : Prop :=
  blockEndAndMin A code.1 [pairedLeftRecordForRow .first first] =
    blockEndAndMin A code.2 [pairedLeftRecordForRow .both first]

/-- Once the seed state *and* accumulated minimum agree, the remaining
`.both` suffix is literally the same fold on both sides. -/
theorem profiledRawJointRightFirstThenBoth_blockEndAndMin_eq_fixedBoth_of_seed
    (code : A.State × A.State)
    (first : PairedRightBlockLetter
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (rest : List (PairedRightBlockLetter
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)))
    (hseed : ProfiledRawJointRightFirstBothSeedAligned A code first) :
    blockEndAndMin A code.1
        (profiledRawJointRightFirstThenBothRecords (first :: rest)) =
    blockEndAndMin A code.2
        ((first :: rest).map (pairedRightRecordForRow .both)) := by
  unfold ProfiledRawJointRightFirstBothSeedAligned at hseed
  simp only [profiledRawJointRightFirstThenBothRecords, List.map_cons]
  unfold blockEndAndMin at hseed ⊢
  simp only [List.foldl_cons, List.foldl_nil] at hseed ⊢
  rw [hseed]

/-- Left fold mirror. -/
theorem profiledRawJointLeftFirstThenBoth_blockEndAndMin_eq_fixedBoth_of_seed
    (code : A.State × A.State)
    (first : PairedLeftBlockLetter
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (rest : List (PairedLeftBlockLetter
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)))
    (hseed : ProfiledRawJointLeftFirstBothSeedAligned A code first) :
    blockEndAndMin A code.1
        (profiledRawJointLeftFirstThenBothRecords (first :: rest)) =
    blockEndAndMin A code.2
        ((first :: rest).map (pairedLeftRecordForRow .both)) := by
  unfold ProfiledRawJointLeftFirstBothSeedAligned at hseed
  simp only [profiledRawJointLeftFirstThenBothRecords, List.map_cons]
  unfold blockEndAndMin at hseed ⊢
  simp only [List.foldl_cons, List.foldl_nil] at hseed ⊢
  rw [hseed]

/-! ## Kernel-checked failure under the present fixed-row interface -/

namespace FirstThenBothScanAudit

/-- A two-state DPA whose transition remembers process two's current output.
Both priorities are even, but the first and both output rows have different
finite minima. -/
def automaton :
    DetParityAutomaton (RoundRecord Unit Unit Graph Unit Bool) where
  State := Bool
  stateFinite := inferInstance
  initial := false
  step _ record := record.outputTwo
  priority state := if state then 0 else 2

/-- A paired lambda with identical blind behavior, but distinct informed
outputs on its two permitted rows. -/
def lambda : ProcOnePairedRightLambda
    (In₁ := Unit) (In₂ := Unit) (Out₁ := Unit) (Out₂ := Bool) where
  blind _ _ := ()
  informedLeft _ _ := false
  informedBoth _ _ := true
  bothOneLeft _ _ := ()
  bothOneBoth _ _ := ()

def code : automaton.State × automaton.State := (false, false)

def source : ProfiledRawRightSlot automaton :=
  (((code, false)), fun _ ↦ false)

def letter : PairedRightBlockLetter
    (In₁ := Unit) (In₂ := Unit) (Out₁ := Unit) (Out₂ := Bool) :=
  (((), ()),
    { informedFirst := false
      informedBoth := true
      closingFirst := ()
      closingBoth := () },
    ())

@[simp] theorem initial_profile :
    rightInitialFirstProfile lambda = source.2 := by
  rfl

theorem runFrom_left
    (env : Nat → Unit × Unit) (n : Nat) :
    automaton.runFrom false
        (pairedRightOmegaWord lambda.blind lambda.informedLeft env) n =
      false := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [DetParityAutomaton.runFrom]
      rw [ih]
      rfl

theorem runFrom_both_succ
    (env : Nat → Unit × Unit) (n : Nat) :
    automaton.runFrom false
        (pairedRightOmegaWord lambda.blind lambda.informedBoth env) (n + 1) =
      true := by
  rfl

theorem acceptsFrom_left
    (env : Nat → Unit × Unit) :
    automaton.AcceptsFrom false
      (pairedRightOmegaWord lambda.blind lambda.informedLeft env) := by
  refine ⟨2, ⟨1, rfl⟩, ?_, ?_⟩
  · intro n
    refine ⟨n, Nat.le_refl n, ?_⟩
    rw [runFrom_left]
    rfl
  · intro q hq
    rcases hq 0 with ⟨k, _hk, hk⟩
    rw [runFrom_left] at hk
    change 2 = q at hk
    omega

theorem acceptsFrom_both
    (env : Nat → Unit × Unit) :
    automaton.AcceptsFrom false
      (pairedRightOmegaWord lambda.blind lambda.informedBoth env) := by
  refine ⟨0, ⟨0, rfl⟩, ?_, ?_⟩
  · intro n
    refine ⟨n + 1, Nat.le_succ n, ?_⟩
    rw [runFrom_both_succ]
    rfl
  · intro q _hq
    omega

/-- Both constant-row threads meet the published/current acceptance premise.
The property says nothing about switching from the first thread to the both
thread after one record. -/
theorem forever : PairedRightForeverAccepts automaton code lambda := by
  constructor
  · intro env
    exact acceptsFrom_left env
  · intro env
    exact acceptsFrom_both env

theorem first_seed_value :
    blockEndAndMin automaton code.1
        [pairedRightRecordForRow .first letter] = (false, false) := by
  rfl

theorem both_seed_value :
    blockEndAndMin automaton code.2
        [pairedRightRecordForRow .both letter] = (true, true) := by
  rfl

/-- Nevertheless the exact seed equation is false: the literal first record
keeps state `false` with minimum priority `2`, whereas the monitor's both
record moves to `true` with minimum priority `0`. -/
theorem not_seed_aligned :
    ¬ ProfiledRawJointRightFirstBothSeedAligned automaton code letter := by
  intro hseed
  unfold ProfiledRawJointRightFirstBothSeedAligned at hseed
  rw [first_seed_value, both_seed_value] at hseed
  exact Bool.noConfusion (congrArg Prod.fst hseed)

end FirstThenBothScanAudit

end DetParityAutomaton

end DistributedSynthesis
