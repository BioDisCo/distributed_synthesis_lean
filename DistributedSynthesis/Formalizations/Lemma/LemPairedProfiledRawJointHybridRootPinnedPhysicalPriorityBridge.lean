/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridRootPinnedCarrierPathAcceptance
import DistributedSynthesis.Formalizations.Theorem.ThmParityBlockPasting

/-!
# Physical parity below an actual root-pinned hybrid child

The guarded hybrid carrier starts its recurrent proof after one literal child
of the unique root-pinned policy.  The code objective must therefore continue
from the control reached by that child; it must not be restarted at its
initial state.

This file turns that state-relative code acceptance into physical tail
acceptance.  The only physical premise is the standard epoch law: at each
proof-side close cut, the minimum original-DPA priority of the emitted block
equals the priority of one hidden alternating lineage of the complete hybrid
code word.  Cuts, the hidden side, and the lineage are proof objects.  They
are not graph/orientation signals available to either local controller.

The close path is stated with the generic guarded `AllowedTarget` relation.
In particular, a narrowed sender may emit any literal certified target; no
equality with a separately chosen canonical `closeKey` is assumed.
-/

namespace DistributedSynthesis

universe u v w x y s

namespace DetParityAutomaton

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable
  (A : DetParityAutomaton.{max u v x y, s}
    (RoundRecord In₁ In₂ Graph Out₁ Out₂))

noncomputable section

variable [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁]
  [Inhabited Out₂]
variable [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]

variable
  (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
  (hwin : ∀ env : EnvironmentSequence In₁ In₂,
    A.Accepts (execution strategy env))

/-! ## State-relative hybrid-code parity -/

/-- Restore the literal first child in front of the positive-time close-code
tail.  Its one-step drop is definitionally `tail`. -/
def profiledRawJointHybridFirstChildCodeWord
    (firstChild : ProfiledRawJointHybridCode A)
    (tail : OmegaWord (ProfiledRawJointHybridCode A)) :
    OmegaWord (ProfiledRawJointHybridCode A)
  | 0 => firstChild
  | n + 1 => tail n

section
omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁]
    [Fintype In₂] [Fintype Out₁] [Fintype Out₂]

@[simp] theorem profiledRawJointHybridFirstChildCodeWord_zero
    (firstChild : ProfiledRawJointHybridCode A)
    (tail : OmegaWord (ProfiledRawJointHybridCode A)) :
    profiledRawJointHybridFirstChildCodeWord A firstChild tail 0 =
      firstChild :=
  rfl

@[simp] theorem profiledRawJointHybridFirstChildCodeWord_succ
    (firstChild : ProfiledRawJointHybridCode A)
    (tail : OmegaWord (ProfiledRawJointHybridCode A)) (n : Nat) :
    profiledRawJointHybridFirstChildCodeWord A firstChild tail (n + 1) =
      tail n :=
  rfl

@[simp] theorem profiledRawJointHybridFirstChildCodeWord_drop_one
    (firstChild : ProfiledRawJointHybridCode A)
    (tail : OmegaWord (ProfiledRawJointHybridCode A)) :
    OmegaWord.drop
        (profiledRawJointHybridFirstChildCodeWord A firstChild tail) 1 =
      tail := by
  funext n
  simp [OmegaWord.drop, Nat.add_comm,
    profiledRawJointHybridFirstChildCodeWord]

end

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
/-- Acceptance from the exact child control restores ordinary acceptance of
the complete code word.  This is just finite-prefix invariance for one
letter, with the control equality kept explicit so callers cannot reset the
code DPA accidentally. -/
theorem profiledRawJointHybridCode_accepts_of_acceptsFrom_firstChild
    (initialCode firstChild : ProfiledRawJointHybridCode A)
    (control :
      (profiledRawJointHybridCodeParityDPA A initialCode).State)
    (tail : OmegaWord (ProfiledRawJointHybridCode A))
    (hcontrol : control =
      (profiledRawJointHybridCodeParityDPA A initialCode).step
        (profiledRawJointHybridCodeParityDPA A initialCode).initial
        firstChild)
    (haccepts :
      (profiledRawJointHybridCodeParityDPA A initialCode).AcceptsFrom control
        tail) :
    (profiledRawJointHybridCodeParityDPA A initialCode).Accepts
      (profiledRawJointHybridFirstChildCodeWord A firstChild tail) := by
  let D := profiledRawJointHybridCodeParityDPA A initialCode
  let word := profiledRawJointHybridFirstChildCodeWord A firstChild tail
  apply (D.acceptsFrom_step_drop_iff D.initial word).mp
  simpa [D, word, hcontrol] using haccepts

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
/-- Every hidden alternating lineage of the restored code word has min-even
parity, also after an arbitrary finite proof-side offset. -/
theorem profiledRawJointHybridThreadParity_of_acceptsFrom_firstChild
    (initialCode firstChild : ProfiledRawJointHybridCode A)
    (control :
      (profiledRawJointHybridCodeParityDPA A initialCode).State)
    (tail : OmegaWord (ProfiledRawJointHybridCode A))
    (hcontrol : control =
      (profiledRawJointHybridCodeParityDPA A initialCode).step
        (profiledRawJointHybridCodeParityDPA A initialCode).initial
        firstChild)
    (haccepts :
      (profiledRawJointHybridCodeParityDPA A initialCode).AcceptsFrom control
        tail)
    (initialSide : IndexedLineageSide) (offset : Nat) :
    NatSeqMinEvenParity (fun k ↦
      (codedAlternatingIndexedLineageCodeThreadSystem initialCode
          (profiledRawJointHybridCurrentSlots A)
          (profiledRawJointThreadRootPriority A)).priority
        (codedAlternatingIndexedLineageCodeRun initialCode
          (profiledRawJointHybridCurrentSlots A)
          (profiledRawJointHybridFirstChildCodeWord A firstChild tail)
          initialSide () (offset + k))) := by
  have hfull :=
    profiledRawJointHybridCode_accepts_of_acceptsFrom_firstChild A initialCode
      firstChild control tail hcontrol haccepts
  have hall : ∀ side lineage,
      NatSeqMinEvenParity (fun n ↦
        (codedAlternatingIndexedLineageCodeThreadSystem initialCode
            (profiledRawJointHybridCurrentSlots A)
            (profiledRawJointThreadRootPriority A)).priority
          (codedAlternatingIndexedLineageCodeRun initialCode
            (profiledRawJointHybridCurrentSlots A)
            (profiledRawJointHybridFirstChildCodeWord A firstChild tail)
            side lineage n)) :=
    (codedAlternatingIndexedLineageCodeDPA_accepts_iff initialCode
      (profiledRawJointHybridCurrentSlots A)
      (profiledRawJointThreadRootPriority A)
      (profiledRawJointHybridFirstChildCodeWord A firstChild tail)).mp hfull
  let priorities := fun n ↦
    (codedAlternatingIndexedLineageCodeThreadSystem initialCode
        (profiledRawJointHybridCurrentSlots A)
        (profiledRawJointThreadRootPriority A)).priority
      (codedAlternatingIndexedLineageCodeRun initialCode
        (profiledRawJointHybridCurrentSlots A)
        (profiledRawJointHybridFirstChildCodeWord A firstChild tail)
        initialSide () n)
  exact (natSeqMinEvenParity_shift priorities offset).mpr
    (hall initialSide ())

/-! ## Generic physical-tail pasting -/

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
/-- State-relative code acceptance plus exact physical block minima yields
min-even parity of the original DPA tail. -/
theorem profiledRawJointHybridPhysicalTail_minEven_of_codeAcceptsFrom
    (initialCode firstChild : ProfiledRawJointHybridCode A)
    (control :
      (profiledRawJointHybridCodeParityDPA A initialCode).State)
    (codeTail : OmegaWord (ProfiledRawJointHybridCode A))
    (hcontrol : control =
      (profiledRawJointHybridCodeParityDPA A initialCode).step
        (profiledRawJointHybridCodeParityDPA A initialCode).initial
        firstChild)
    (hcode :
      (profiledRawJointHybridCodeParityDPA A initialCode).AcceptsFrom control
        codeTail)
    (physicalState : A.State)
    (physicalTail : OmegaWord (RoundRecord In₁ In₂ Graph Out₁ Out₂))
    (cuts : Nat → Nat) (cuts_strictMono : StrictMono cuts)
    (cuts_zero : cuts 0 = 0)
    (initialSide : IndexedLineageSide) (offset : Nat)
    (blockMin_eq_threadPriority : ∀ k : Nat,
      cutBlockMin
          (fun n ↦ A.priority (A.runFrom physicalState physicalTail n))
          cuts k =
        (codedAlternatingIndexedLineageCodeThreadSystem initialCode
            (profiledRawJointHybridCurrentSlots A)
            (profiledRawJointThreadRootPriority A)).priority
          (codedAlternatingIndexedLineageCodeRun initialCode
            (profiledRawJointHybridCurrentSlots A)
            (profiledRawJointHybridFirstChildCodeWord A firstChild codeTail)
            initialSide () (offset + k))) :
    NatSeqMinEvenParity
      (fun n ↦ A.priority (A.runFrom physicalState physicalTail n)) := by
  have hthread :=
    profiledRawJointHybridThreadParity_of_acceptsFrom_firstChild A initialCode
      firstChild control codeTail hcontrol hcode initialSide offset
  have hblocks : NatSeqMinEvenParity
      (cutBlockMin
        (fun n ↦ A.priority (A.runFrom physicalState physicalTail n))
        cuts) := by
    convert hthread using 1
    funext k
    exact blockMin_eq_threadPriority k
  exact
    (natSeqMinEvenParity_cutBlockMin
      (fun n ↦ A.priority (A.runFrom physicalState physicalTail n))
      cuts_strictMono cuts_zero).mp hblocks

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
/-- Acceptance-form companion of the physical-tail parity bridge. -/
theorem profiledRawJointHybridPhysicalTail_acceptsFrom_of_codeAcceptsFrom
    (initialCode firstChild : ProfiledRawJointHybridCode A)
    (control :
      (profiledRawJointHybridCodeParityDPA A initialCode).State)
    (codeTail : OmegaWord (ProfiledRawJointHybridCode A))
    (hcontrol : control =
      (profiledRawJointHybridCodeParityDPA A initialCode).step
        (profiledRawJointHybridCodeParityDPA A initialCode).initial
        firstChild)
    (hcode :
      (profiledRawJointHybridCodeParityDPA A initialCode).AcceptsFrom control
        codeTail)
    (physicalState : A.State)
    (physicalTail : OmegaWord (RoundRecord In₁ In₂ Graph Out₁ Out₂))
    (cuts : Nat → Nat) (cuts_strictMono : StrictMono cuts)
    (cuts_zero : cuts 0 = 0)
    (initialSide : IndexedLineageSide) (offset : Nat)
    (blockMin_eq_threadPriority : ∀ k : Nat,
      cutBlockMin
          (fun n ↦ A.priority (A.runFrom physicalState physicalTail n))
          cuts k =
        (codedAlternatingIndexedLineageCodeThreadSystem initialCode
            (profiledRawJointHybridCurrentSlots A)
            (profiledRawJointThreadRootPriority A)).priority
          (codedAlternatingIndexedLineageCodeRun initialCode
            (profiledRawJointHybridCurrentSlots A)
            (profiledRawJointHybridFirstChildCodeWord A firstChild codeTail)
            initialSide () (offset + k))) :
    A.AcceptsFrom physicalState physicalTail := by
  change NatSeqMinEvenParity
    (fun n ↦ A.priority (A.runFrom physicalState physicalTail n))
  exact
    profiledRawJointHybridPhysicalTail_minEven_of_codeAcceptsFrom A initialCode
      firstChild control codeTail hcontrol hcode physicalState physicalTail
      cuts cuts_strictMono cuts_zero initialSide offset
      blockMin_eq_threadPriority

/-! ## Direct consumption of a generic guarded close path -/

section
omit [Inhabited Out₁] [Inhabited Out₂]

/-- The named simultaneous child carries exactly the code-DPA control reached
by consuming its literal child code. -/
theorem
    profiledRawJointHybridInitialRootPinned_simultaneousChild_control
    (first current : In₁ × In₂) :
    let childCode :=
      profiledRawJointHybridInitialSimultaneousChildCode A strategy first
        current
    ((profiledRawJointHybridInitialRootPinnedPolicy A strategy hwin first
      ).policy.run [childCode]).2.2 =
      (profiledRawJointHybridCodeParityDPA A
        (ProfiledRawJointHybridInitialRootPinnedCode A strategy first)).step
          (profiledRawJointHybridCodeParityDPA A
            (ProfiledRawJointHybridInitialRootPinnedCode A strategy first)
            ).initial childCode := by
  let package :=
    profiledRawJointHybridInitialRootPinnedPolicy A strategy hwin first
  let childCode :=
    profiledRawJointHybridInitialSimultaneousChildCode A strategy first current
  have hrun : package.policy.run [childCode] =
      package.policy.successor (package.policy.run []) childCode := by
    simpa using (package.policy.successor_at [] childCode).symm
  change (package.policy.run [childCode]).2.2 =
    (profiledRawJointHybridCodeParityDPA A
      (ProfiledRawJointHybridInitialRootPinnedCode A strategy first)).step
        (profiledRawJointHybridCodeParityDPA A
          (ProfiledRawJointHybridInitialRootPinnedCode A strategy first)
          ).initial childCode
  rw [hrun, package.policy.accepts.1.1]
  exact congrArg (fun state ↦ state.2.2)
    (profiledRawJointHybridInitialRootPinnedPolicy_successor_simultaneous A
      strategy hwin first current)

/-- Strict-child mirror of the exact first-child control equation. -/
theorem profiledRawJointHybridInitialRootPinned_strictChild_control
    (first : In₁ × In₂)
    (actual : ProfiledRawJointActualDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂)) :
    let childCode :=
      profiledRawJointHybridInitialStrictChildCode A strategy first actual
    ((profiledRawJointHybridInitialRootPinnedPolicy A strategy hwin first
      ).policy.run [childCode]).2.2 =
      (profiledRawJointHybridCodeParityDPA A
        (ProfiledRawJointHybridInitialRootPinnedCode A strategy first)).step
          (profiledRawJointHybridCodeParityDPA A
            (ProfiledRawJointHybridInitialRootPinnedCode A strategy first)
            ).initial childCode := by
  let package :=
    profiledRawJointHybridInitialRootPinnedPolicy A strategy hwin first
  let childCode :=
    profiledRawJointHybridInitialStrictChildCode A strategy first actual
  have hrun : package.policy.run [childCode] =
      package.policy.successor (package.policy.run []) childCode := by
    simpa using (package.policy.successor_at [] childCode).symm
  change (package.policy.run [childCode]).2.2 =
    (profiledRawJointHybridCodeParityDPA A
      (ProfiledRawJointHybridInitialRootPinnedCode A strategy first)).step
        (profiledRawJointHybridCodeParityDPA A
          (ProfiledRawJointHybridInitialRootPinnedCode A strategy first)
          ).initial childCode
  rw [hrun, package.policy.accepts.1.1]
  exact congrArg (fun state ↦ state.2.2)
    (profiledRawJointHybridInitialRootPinnedPolicy_successor_strict A strategy
      hwin first actual)

/-- Exact guarded close cuts and their physical block-minimum law close the
original DPA tail objective.  The sole first-child control premise says that
the chosen child is a literal root successor, rather than an arbitrary code
direction of the completed finite table. -/
theorem
    profiledRawJointHybridInitialRootPinnedPhysicalTail_acceptsFrom_of_closePath
    (first : In₁ × In₂)
    (firstChild : ProfiledRawJointHybridCode A)
    (states : Nat →
      ProfiledRawJointHybridInitialRootPinnedGuardedState A strategy first)
    (hzero : states 0 =
      (profiledRawJointHybridInitialRootPinnedPolicy A strategy hwin first
        ).policy.run [firstChild])
    (hstep : ∀ n,
      ProfiledRawJointHybridInitialRootPinnedAllowedTarget A strategy hwin
        first (states n) (states (n + 1)))
    (hfirstControl :
      ((profiledRawJointHybridInitialRootPinnedPolicy A strategy hwin first
        ).policy.run [firstChild]).2.2 =
      (profiledRawJointHybridCodeParityDPA A
        (ProfiledRawJointHybridInitialRootPinnedCode A strategy first)).step
          (profiledRawJointHybridCodeParityDPA A
            (ProfiledRawJointHybridInitialRootPinnedCode A strategy first)
            ).initial firstChild)
    (physicalState : A.State)
    (physicalTail : OmegaWord (RoundRecord In₁ In₂ Graph Out₁ Out₂))
    (cuts : Nat → Nat) (cuts_strictMono : StrictMono cuts)
    (cuts_zero : cuts 0 = 0)
    (initialSide : IndexedLineageSide) (offset : Nat)
    (blockMin_eq_threadPriority : ∀ k : Nat,
      cutBlockMin
          (fun n ↦ A.priority (A.runFrom physicalState physicalTail n))
          cuts k =
        (codedAlternatingIndexedLineageCodeThreadSystem
            (ProfiledRawJointHybridInitialRootPinnedCode A strategy first)
            (profiledRawJointHybridCurrentSlots A)
            (profiledRawJointThreadRootPriority A)).priority
          (codedAlternatingIndexedLineageCodeRun
            (ProfiledRawJointHybridInitialRootPinnedCode A strategy first)
            (profiledRawJointHybridCurrentSlots A)
            (profiledRawJointHybridFirstChildCodeWord A firstChild
              (fun n ↦ (states (n + 1)).2.1))
            initialSide () (offset + k))) :
    A.AcceptsFrom physicalState physicalTail := by
  have hcode :=
    profiledRawJointHybridInitialRootPinned_acceptsFrom_actualFirstChild_of_closePath
      A strategy hwin first firstChild states hzero hstep
  exact
    profiledRawJointHybridPhysicalTail_acceptsFrom_of_codeAcceptsFrom A
      (ProfiledRawJointHybridInitialRootPinnedCode A strategy first)
      firstChild
      ((profiledRawJointHybridInitialRootPinnedPolicy A strategy hwin first
        ).policy.run [firstChild]).2.2
      (fun n ↦ (states (n + 1)).2.1) hfirstControl hcode physicalState
      physicalTail cuts cuts_strictMono cuts_zero initialSide offset
      blockMin_eq_threadPriority

end

/-! ## Finite-global-machine close cuts -/

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- Machine-facing form of the generic bridge.  Close states are sampled
from proof-side cuts of the actual global trace, while the physical minimum
is stated directly on the original DPA run at `start + n`.  Neither the cuts
nor `initialSide` are fields of a local controller. -/
theorem
    finiteGlobalMachine_profiledRawJointHybridInitialRootPinnedPhysicalTail_acceptsFrom_of_closePath
    (first : In₁ × In₂)
    (firstChild : ProfiledRawJointHybridCode A)
    (G : FiniteGlobalRoundMachine.{u, v, w} In₁ In₂)
    (outputOne : G.State → Out₁) (outputTwo : G.State → Out₂)
    (env : EnvironmentSequence In₁ In₂)
    (start : Nat) (cuts : Nat → Nat)
    (cuts_strictMono : StrictMono cuts) (cuts_zero : cuts 0 = 0)
    (closeState : G.State →
      ProfiledRawJointHybridInitialRootPinnedGuardedState A strategy first)
    (hzero :
      closeState (G.globalStateTrace env (start + cuts 0)) =
        (profiledRawJointHybridInitialRootPinnedPolicy A strategy hwin first
          ).policy.run [firstChild])
    (hstep : ∀ n,
      ProfiledRawJointHybridInitialRootPinnedAllowedTarget A strategy hwin
        first
          (closeState (G.globalStateTrace env (start + cuts n)))
          (closeState (G.globalStateTrace env (start + cuts (n + 1)))))
    (hfirstControl :
      ((profiledRawJointHybridInitialRootPinnedPolicy A strategy hwin first
        ).policy.run [firstChild]).2.2 =
      (profiledRawJointHybridCodeParityDPA A
        (ProfiledRawJointHybridInitialRootPinnedCode A strategy first)).step
          (profiledRawJointHybridCodeParityDPA A
            (ProfiledRawJointHybridInitialRootPinnedCode A strategy first)
            ).initial firstChild)
    (initialSide : IndexedLineageSide) (offset : Nat)
    (blockMin_eq_threadPriority : ∀ k : Nat,
      cutBlockMin
          (fun n ↦ A.priority
            (A.run (G.globalMachineTraceWord outputOne outputTwo env)
              (start + n)))
          cuts k =
        (codedAlternatingIndexedLineageCodeThreadSystem
            (ProfiledRawJointHybridInitialRootPinnedCode A strategy first)
            (profiledRawJointHybridCurrentSlots A)
            (profiledRawJointThreadRootPriority A)).priority
          (codedAlternatingIndexedLineageCodeRun
            (ProfiledRawJointHybridInitialRootPinnedCode A strategy first)
            (profiledRawJointHybridCurrentSlots A)
            (profiledRawJointHybridFirstChildCodeWord A firstChild
              (fun n ↦
                (closeState
                  (G.globalStateTrace env
                    (start + cuts (n + 1)))).2.1))
            initialSide () (offset + k))) :
    A.AcceptsFrom
      (A.run (G.globalMachineTraceWord outputOne outputTwo env) start)
      (OmegaWord.drop
        (G.globalMachineTraceWord outputOne outputTwo env) start) := by
  let word := G.globalMachineTraceWord outputOne outputTwo env
  let states := fun n ↦
    closeState (G.globalStateTrace env (start + cuts n))
  apply
    profiledRawJointHybridInitialRootPinnedPhysicalTail_acceptsFrom_of_closePath
      A strategy hwin first firstChild states hzero hstep hfirstControl
        (A.run word start) (OmegaWord.drop word start) cuts cuts_strictMono
          cuts_zero initialSide offset
  intro k
  have hrun :
      (fun n ↦ A.priority
        (A.runFrom (A.run word start) (OmegaWord.drop word start) n)) =
      (fun n ↦ A.priority (A.run word (start + n))) := by
    funext n
    exact congrArg A.priority (A.runFrom_drop A.initial word start n)
  rw [hrun]
  exact blockMin_eq_threadPriority k

end

end DetParityAutomaton

end DistributedSynthesis
