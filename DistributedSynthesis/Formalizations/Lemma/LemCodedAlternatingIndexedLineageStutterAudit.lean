/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemCodedAlternatingIndexedLineageCodeParity

/-!
# Alternating-lineage acceptance does not imply same-side stutter acceptance

The code-lineage objective checks a hidden thread which changes side at every
letter.  A physical epoch clock may instead close twice on the same side.  It
is tempting to repair the clock mismatch by letting the hidden thread retain
its side on such a step and to inherit acceptance from the alternating
monitor.  This file records a finite counterexample to that inheritance.

There is one public code and one lineage.  The right slot has odd priority
`3`, while the left slot has smaller even priority `2`.  Every alternating
thread sees both priorities forever, hence is min-even accepting.  The thread
which retains the right side forever sees only `3`, hence is rejecting.

Thus a side-stuttering handoff needs an additional theorem, for example that
every inserted priority equals (or is parity-neutral relative to) the
physical epoch priority.  It cannot follow from the current alternating-code
DPA alone.
-/

namespace DistributedSynthesis

namespace DetParityAutomaton

/-! ## The parity-safe form of stuttering -/

/-- Min-even parity is invariant under any monotone, surjective clock which
never runs ahead of physical time.  This is the reusable positive repair:
an expanded hidden priority sequence may repeat physical priorities, but
every inserted position must literally carry the priority of the physical
epoch selected by `clock`.

The counterexample below shows that the alternating lineage monitor does not
by itself provide this literal-priority premise. -/
theorem natSeqMinEvenParity_comp_iff_of_monotone_surjective
    (priorities clock : Nat → Nat)
    (hmono : Monotone clock)
    (hle : ∀ n : Nat, clock n ≤ n)
    (hsurj : ∀ k : Nat, ∃ n : Nat, clock n = k) :
    NatSeqMinEvenParity (fun n ↦ priorities (clock n)) ↔
      NatSeqMinEvenParity priorities := by
  have hseen : ∀ p : Nat,
      NatSeqSeenInfinitelyOften (fun n ↦ priorities (clock n)) p ↔
        NatSeqSeenInfinitelyOften priorities p := by
    intro p
    constructor
    · intro hexpanded base
      obtain ⟨m, hm⟩ := hsurj base
      obtain ⟨n, hn, hpriority⟩ := hexpanded m
      exact ⟨clock n, by rw [← hm]; exact hmono hn, hpriority⟩
    · intro hphysical base
      obtain ⟨k, hk, hpriority⟩ := hphysical base
      obtain ⟨n, hn⟩ := hsurj k
      refine ⟨n, ?_, ?_⟩
      · calc
          base ≤ k := hk
          _ = clock n := hn.symm
          _ ≤ n := hle n
      · simpa [hn] using hpriority
  constructor
  · rintro ⟨p, hpEven, hpSeen, hpMin⟩
    exact ⟨p, hpEven, (hseen p).mp hpSeen,
      fun q hq ↦ hpMin q ((hseen q).mpr hq)⟩
  · rintro ⟨p, hpEven, hpSeen, hpMin⟩
    exact ⟨p, hpEven, (hseen p).mpr hpSeen,
      fun q hq ↦ hpMin q ((hseen q).mp hq)⟩

private def stutterAuditSlots
    (side : IndexedLineageSide) (_code : Unit) (_lineage : Unit) :
    Option IndexedLineageSide :=
  some side

private def stutterAuditPriority : IndexedLineageSide → Nat
  | .right => 3
  | .left => 2

private def stutterAuditWord : OmegaWord Unit := fun _ => Unit.unit

private theorem stutterAuditRun_succ
    (initialSide : IndexedLineageSide) (n : Nat) :
    codedAlternatingIndexedLineageCodeRun Unit.unit stutterAuditSlots
        stutterAuditWord initialSide Unit.unit (n + 1) =
      codedAlternatingIndexedLineageStep
        (fun _ (_ : Unit) childCode => childCode)
        stutterAuditSlots
        (codedAlternatingIndexedLineageCodeChild stutterAuditSlots)
        (codedAlternatingIndexedLineageCodeRun Unit.unit stutterAuditSlots
          stutterAuditWord initialSide Unit.unit n)
        (Unit.unit, Unit.unit) (initialSide, Unit.unit) := by
  rfl

private theorem stutterAuditRun_right_odd (n : Nat) :
    codedAlternatingIndexedLineageCodeRun Unit.unit stutterAuditSlots
        stutterAuditWord .right Unit.unit (2 * n + 1) =
      (Unit.unit, .live .left Unit.unit .left) := by
  induction n with
  | zero =>
      simp [codedAlternatingIndexedLineageCodeRun,
        codedAlternatingIndexedLineageRun,
        codedAlternatingIndexedLineageStep,
        codedAlternatingIndexedLineageCodeChild, stutterAuditSlots,
        stutterAuditWord, IndexedLineageSide.other]
  | succ n ih =>
      rw [show 2 * (n + 1) + 1 = (2 * n + 1) + 2 by omega]
      rw [show (2 * n + 1) + 2 = ((2 * n + 1) + 1) + 1 by omega]
      rw [stutterAuditRun_succ, stutterAuditRun_succ, ih]
      simp [codedAlternatingIndexedLineageStep,
        codedAlternatingIndexedLineageCodeChild, stutterAuditSlots,
        IndexedLineageSide.other]

private theorem stutterAuditRun_right_even (n : Nat) :
    codedAlternatingIndexedLineageCodeRun Unit.unit stutterAuditSlots
        stutterAuditWord .right Unit.unit (2 * n + 2) =
      (Unit.unit, .live .right Unit.unit .right) := by
  rw [show 2 * n + 2 = (2 * n + 1) + 1 by omega,
    stutterAuditRun_succ,
    stutterAuditRun_right_odd]
  simp [codedAlternatingIndexedLineageStep,
    codedAlternatingIndexedLineageCodeChild, stutterAuditSlots,
    IndexedLineageSide.other]

private theorem stutterAuditRun_left_odd (n : Nat) :
    codedAlternatingIndexedLineageCodeRun Unit.unit stutterAuditSlots
        stutterAuditWord .left Unit.unit (2 * n + 1) =
      (Unit.unit, .live .right Unit.unit .right) := by
  induction n with
  | zero =>
      simp [codedAlternatingIndexedLineageCodeRun,
        codedAlternatingIndexedLineageRun,
        codedAlternatingIndexedLineageStep,
        codedAlternatingIndexedLineageCodeChild, stutterAuditSlots,
        stutterAuditWord, IndexedLineageSide.other]
  | succ n ih =>
      rw [show 2 * (n + 1) + 1 = (2 * n + 1) + 2 by omega]
      rw [show (2 * n + 1) + 2 = ((2 * n + 1) + 1) + 1 by omega]
      rw [stutterAuditRun_succ, stutterAuditRun_succ, ih]
      simp [codedAlternatingIndexedLineageStep,
        codedAlternatingIndexedLineageCodeChild, stutterAuditSlots,
        IndexedLineageSide.other]

private theorem stutterAuditRun_left_even (n : Nat) :
    codedAlternatingIndexedLineageCodeRun Unit.unit stutterAuditSlots
        stutterAuditWord .left Unit.unit (2 * n + 2) =
      (Unit.unit, .live .left Unit.unit .left) := by
  rw [show 2 * n + 2 = (2 * n + 1) + 1 by omega,
    stutterAuditRun_succ,
    stutterAuditRun_left_odd]
  simp [codedAlternatingIndexedLineageStep,
    codedAlternatingIndexedLineageCodeChild, stutterAuditSlots,
    IndexedLineageSide.other]

private theorem stutterAuditRun_positive_live
    (initialSide : IndexedLineageSide) (n : Nat) :
    ∃ side : IndexedLineageSide,
      codedAlternatingIndexedLineageCodeRun Unit.unit stutterAuditSlots
          stutterAuditWord initialSide Unit.unit (n + 1) =
        (Unit.unit, .live side Unit.unit side) := by
  induction n with
  | zero =>
      cases initialSide <;>
        simp [codedAlternatingIndexedLineageCodeRun,
          codedAlternatingIndexedLineageRun,
          codedAlternatingIndexedLineageStep,
          codedAlternatingIndexedLineageCodeChild, stutterAuditSlots,
          stutterAuditWord, IndexedLineageSide.other]
  | succ n ih =>
      obtain ⟨side, hside⟩ := ih
      rw [show n + 1 + 1 = (n + 1) + 1 by rfl, stutterAuditRun_succ,
        hside]
      cases side <;>
        simp [codedAlternatingIndexedLineageStep,
          codedAlternatingIndexedLineageCodeChild, stutterAuditSlots,
          IndexedLineageSide.other]

private theorem stutterAuditPriority_positive
    (initialSide : IndexedLineageSide) (n : Nat) :
    (codedAlternatingIndexedLineageCodeThreadSystem Unit.unit
        stutterAuditSlots stutterAuditPriority).priority
      (codedAlternatingIndexedLineageCodeRun Unit.unit stutterAuditSlots
        stutterAuditWord initialSide Unit.unit (n + 1)) = 2 ∨
    (codedAlternatingIndexedLineageCodeThreadSystem Unit.unit
        stutterAuditSlots stutterAuditPriority).priority
      (codedAlternatingIndexedLineageCodeRun Unit.unit stutterAuditSlots
        stutterAuditWord initialSide Unit.unit (n + 1)) = 3 := by
  obtain ⟨side, hside⟩ := stutterAuditRun_positive_live initialSide n
  rw [hside]
  cases side <;> simp [codedAlternatingIndexedLineageCodeThreadSystem,
    codedAlternatingIndexedLineageThreadSystem, stutterAuditPriority]

private theorem stutterAuditAlternatingParity
    (initialSide : IndexedLineageSide) :
    NatSeqMinEvenParity (fun n =>
      (codedAlternatingIndexedLineageCodeThreadSystem Unit.unit
          stutterAuditSlots stutterAuditPriority).priority
        (codedAlternatingIndexedLineageCodeRun Unit.unit stutterAuditSlots
          stutterAuditWord initialSide Unit.unit n)) := by
  refine ⟨2, ⟨1, rfl⟩, ?_, ?_⟩
  · intro base
    cases initialSide with
    | right =>
        refine ⟨2 * base + 1, by omega, ?_⟩
        change
          (codedAlternatingIndexedLineageCodeThreadSystem Unit.unit
              stutterAuditSlots stutterAuditPriority).priority
            (codedAlternatingIndexedLineageCodeRun Unit.unit stutterAuditSlots
              stutterAuditWord .right Unit.unit (2 * base + 1)) = 2
        rw [stutterAuditRun_right_odd]
        rfl
    | left =>
        refine ⟨2 * base + 2, by omega, ?_⟩
        change
          (codedAlternatingIndexedLineageCodeThreadSystem Unit.unit
              stutterAuditSlots stutterAuditPriority).priority
            (codedAlternatingIndexedLineageCodeRun Unit.unit stutterAuditSlots
              stutterAuditWord .left Unit.unit (2 * base + 2)) = 2
        rw [stutterAuditRun_left_even]
        rfl
  · intro priority hseen
    obtain ⟨k, hk, hpriority⟩ := hseen 1
    cases k with
    | zero => omega
    | succ k =>
        change
          (codedAlternatingIndexedLineageCodeThreadSystem Unit.unit
              stutterAuditSlots stutterAuditPriority).priority
            (codedAlternatingIndexedLineageCodeRun Unit.unit
              stutterAuditSlots stutterAuditWord initialSide Unit.unit
              (k + 1)) = priority at hpriority
        have hrange := stutterAuditPriority_positive initialSide k
        rcases hrange with htwo | hthree
        · omega
        · omega

/-- The existing code-observable alternating-lineage DPA accepts the unique
public word in the audit instance. -/
theorem codedAlternatingIndexedLineageDPA_accepts_stutterAuditWord :
    (codedAlternatingIndexedLineageCodeDPA Unit.unit stutterAuditSlots
      stutterAuditPriority).Accepts stutterAuditWord := by
  rw [codedAlternatingIndexedLineageCodeDPA_accepts_iff]
  intro initialSide lineage
  cases lineage
  exact stutterAuditAlternatingParity initialSide

/-- The priority sequence obtained by retaining the right-side root forever
is rejecting. -/
theorem not_natSeqMinEvenParity_stutterAuditRetainRight :
    ¬ NatSeqMinEvenParity (fun _ => stutterAuditPriority .right) := by
  rintro ⟨p, hpEven, hpSeen, hpMin⟩
  obtain ⟨k, _hk, hpk⟩ := hpSeen 0
  have hp : p = 3 := by simpa [stutterAuditPriority] using hpk.symm
  subst p
  rcases hpEven with ⟨k, hk⟩
  omega

/-- A concrete implication refuting any unconditional transfer from the
alternating monitor to an arbitrary same-side-retaining thread. -/
theorem alternatingAcceptance_does_not_imply_retainSideAcceptance :
    (codedAlternatingIndexedLineageCodeDPA Unit.unit stutterAuditSlots
        stutterAuditPriority).Accepts stutterAuditWord ∧
      ¬ NatSeqMinEvenParity (fun _ => stutterAuditPriority .right) :=
  ⟨codedAlternatingIndexedLineageDPA_accepts_stutterAuditWord,
    not_natSeqMinEvenParity_stutterAuditRetainRight⟩

end DetParityAutomaton

end DistributedSynthesis
