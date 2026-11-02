/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridInitialPolicyBank
import DistributedSynthesis.Formalizations.Lemma.LemSourceFreeBeliefCodePolicyPathAcceptance

/-!
# Acceptance of the forever-common hybrid controller

This file isolates the omega seam for a run which remains in the common
phase forever.  The proof-side trace follows one selected finite hybrid
policy.  Its physical rounds use the installed common move's literal
`.both` output.  No graph, orientation, or strict-leader bit is supplied to
either local transition.

The first layer below is deliberately independent of semantic representative
continuity: successive installed worlds may differ.  Only the finite policy
state is required to follow its actual successor table.
-/

namespace DistributedSynthesis

universe u v x y s

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

private abbrev CommonKey (first : In₁ × In₂) :=
  ProfiledRawJointHybridCommonPolicyKey A strategy
    (ProfiledRawJointHybridInitialCode A strategy first)
    (profiledRawJointHybridInitialPolicy A strategy hwin first)

private abbrev CommonControl :=
  ProfiledRawJointHybridCommonControl A strategy hwin

/-! ## The exact finite common-policy path -/

/-- Common policy key before physical round `n + 1`.  Round zero has already
selected the bank indexed by `inputs 0`. -/
noncomputable def profiledRawJointHybridForeverCommonKeyTrace
    (inputs : Nat → In₁ × In₂) : Nat → CommonKey A strategy hwin (inputs 0)
  | 0 => profiledRawJointHybridInitialCommonKey A strategy hwin (inputs 0)
  | n + 1 =>
      (profiledRawJointHybridCommonControlInstalled A strategy hwin
        ⟨inputs 0,
          profiledRawJointHybridForeverCommonKeyTrace inputs n⟩
        ).simultaneousSuccessorKey A (inputs (n + 1))

/-- The same trace packaged in the finite common-control bank used by the
local controller. -/
noncomputable def profiledRawJointHybridForeverCommonControlTrace
    (inputs : Nat → In₁ × In₂) (n : Nat) : CommonControl A strategy hwin :=
  ⟨inputs 0, profiledRawJointHybridForeverCommonKeyTrace A strategy hwin inputs n⟩

omit [Inhabited Out₁] [Inhabited Out₂] in
@[simp] theorem profiledRawJointHybridForeverCommonControlTrace_zero
    (inputs : Nat → In₁ × In₂) :
    profiledRawJointHybridForeverCommonControlTrace A strategy hwin inputs 0 =
      profiledRawJointHybridInitialCommonControl A strategy hwin (inputs 0) :=
  rfl

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- The packaged trace is literally driven by the executable common-control
successor. -/
theorem profiledRawJointHybridForeverCommonControlTrace_succ
    (inputs : Nat → In₁ × In₂) (n : Nat) :
    profiledRawJointHybridForeverCommonControlTrace A strategy hwin inputs
        (n + 1) =
      profiledRawJointHybridCommonControlNext A strategy hwin
        (profiledRawJointHybridForeverCommonControlTrace A strategy hwin
          inputs n) (inputs (n + 1)) :=
  rfl

/-- The finite child code requested by physical round `n + 1`. -/
noncomputable def profiledRawJointHybridForeverCommonChildCode
    (inputs : Nat → In₁ × In₂) (n : Nat) :
    ProfiledRawJointHybridCode A :=
  (profiledRawJointHybridCommonControlInstalled A strategy hwin
    (profiledRawJointHybridForeverCommonControlTrace A strategy hwin inputs n)
    ).simultaneousChildCode A (inputs (n + 1))

/-- The common controller's key trace is one coherent path of the single
policy selected by the first input pair. -/
noncomputable def profiledRawJointHybridForeverCommonPolicyPath
    (inputs : Nat → In₁ × In₂) :
    SourceFreeBeliefCodeParityPolicyPath
      (profiledRawJointHybridCodeParityDPA A
        (ProfiledRawJointHybridInitialCode A strategy (inputs 0)))
      (ProfiledRawJointHybridInitialCode A strategy (inputs 0))
      (ProfiledRawJointHybridProvenanceValid A strategy)
      (profiledRawJointHybridFiniteCodeNext A)
      (profiledRawJointHybridInitialPolicy A strategy hwin (inputs 0)) where
  state := fun n ↦
    (profiledRawJointHybridForeverCommonKeyTrace A strategy hwin inputs n).state
  direction := profiledRawJointHybridForeverCommonChildCode A strategy hwin
    inputs
  initial := rfl
  successor := by
    intro n
    rfl

/-- Positive-time child-code word of the common policy path. -/
noncomputable def profiledRawJointHybridForeverCommonCodeWord
    (inputs : Nat → In₁ × In₂) : OmegaWord (ProfiledRawJointHybridCode A) :=
  (profiledRawJointHybridForeverCommonPolicyPath A strategy hwin inputs
    ).childCodeWord
      (profiledRawJointHybridCodeParityDPA A
        (ProfiledRawJointHybridInitialCode A strategy (inputs 0)))
      (ProfiledRawJointHybridInitialCode A strategy (inputs 0))
      (ProfiledRawJointHybridProvenanceValid A strategy)
      (profiledRawJointHybridFiniteCodeNext A)
      (profiledRawJointHybridInitialPolicy A strategy hwin (inputs 0))

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- The `n`-th code letter is the explicit common incidence code stored in
the next finite key. -/
theorem profiledRawJointHybridForeverCommonCodeWord_eq_key
    (inputs : Nat → In₁ × In₂) (n : Nat) :
    profiledRawJointHybridForeverCommonCodeWord A strategy hwin inputs n =
      .common
        (profiledRawJointHybridForeverCommonKeyTrace A strategy hwin inputs
          (n + 1)).incidenceCode := by
  change
    (profiledRawJointHybridForeverCommonKeyTrace A strategy hwin inputs
      (n + 1)).state.1 = _
  exact (profiledRawJointHybridForeverCommonKeyTrace A strategy hwin inputs
    (n + 1)).state_code

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- **Unconditional finite-code acceptance.**  Representative worlds may be
reselected at every control; acceptance follows solely from the coherent
finite-policy path. -/
theorem profiledRawJointHybridForeverCommon_childCode_accepts
    (inputs : Nat → In₁ × In₂) :
    (profiledRawJointHybridCodeParityDPA A
      (ProfiledRawJointHybridInitialCode A strategy (inputs 0))).Accepts
      ((profiledRawJointHybridForeverCommonPolicyPath A strategy hwin inputs
        ).childCodeWord
          (profiledRawJointHybridCodeParityDPA A
            (ProfiledRawJointHybridInitialCode A strategy (inputs 0)))
          (ProfiledRawJointHybridInitialCode A strategy (inputs 0))
          (ProfiledRawJointHybridProvenanceValid A strategy)
          (profiledRawJointHybridFiniteCodeNext A)
          (profiledRawJointHybridInitialPolicy A strategy hwin (inputs 0))) := by
  exact (profiledRawJointHybridForeverCommonPolicyPath A strategy hwin inputs
    ).accepts
      (profiledRawJointHybridCodeParityDPA A
        (ProfiledRawJointHybridInitialCode A strategy (inputs 0)))
      (ProfiledRawJointHybridInitialCode A strategy (inputs 0))
      (ProfiledRawJointHybridProvenanceValid A strategy)
      (profiledRawJointHybridFiniteCodeNext A)
      (profiledRawJointHybridInitialPolicy A strategy hwin (inputs 0))

/-! ## Incidence-level representative coupling -/

section
omit [Inhabited Out₁] [Inhabited Out₂]

/-- Although the policy may choose a fresh semantic representative at the
successor key, its complete process-one slot is exactly the slot of the
literal simultaneous child of the current representative.  This is the
anti-mosaic equation: it follows from the source-free incidence successor,
not from equality of the two hidden histories. -/
theorem ProfiledRawJointHybridCommonInstalledMove.simultaneousSuccessor_procOneSlot
    {initialCode : ProfiledRawJointHybridCode A}
    {policy : ProfiledRawJointHybridProvenanceRationalPolicy A strategy
      initialCode}
    {key : ProfiledRawJointHybridCommonPolicyKey A strategy initialCode policy}
    (installed : ProfiledRawJointHybridCommonInstalledMove A strategy
      initialCode policy key)
    (input : In₁ × In₂)
    (nextInstalled : ProfiledRawJointHybridCommonInstalledMove A strategy
      initialCode policy (installed.simultaneousSuccessorKey A input)) :
    nextInstalled.world.procOneSlot A =
      (profiledRawJointCommonWorldAfterBoth A installed.world input
        ).procOneSlot A := by
  have hfamily :
      (profiledRawJointCommonWorldFamily A installed.world).code A =
        key.incidenceCode.family :=
    congrArg ProfiledRawJointIncidenceCode.family installed.incidence_eq
  have hincidence :
      (profiledRawJointCommonWorldFamily A nextInstalled.world).incidenceCode A =
        (profiledRawJointCommonWorldFamily A
          (profiledRawJointCommonWorldAfterBoth A installed.world input)
          ).incidenceCode A := by
    calc
      (profiledRawJointCommonWorldFamily A nextInstalled.world).incidenceCode A
          = (installed.simultaneousSuccessorKey A input).incidenceCode :=
            nextInstalled.incidence_eq
      _ = profiledRawJointIncidenceNext A key.incidenceCode.family
          installed.rawMove (profiledRawJointBothRestartDirection input) := rfl
      _ = profiledRawJointIncidenceNext A
          ((profiledRawJointCommonWorldFamily A installed.world).code A)
          ((profiledRawJointCommonWorldFamily A installed.world).move A)
          (profiledRawJointBothRestartDirection input) := by
            rw [hfamily, installed.move_eq]
      _ = (profiledRawJointCommonWorldFamily A
          (profiledRawJointCommonWorldAfterBoth A installed.world input)
          ).incidenceCode A :=
            (profiledRawJointCommonWorldAfterBoth_incidenceCode A
              installed.world input).symm
  have hright := congrArg
    (fun code : ProfiledRawJointIncidenceCode A (I := Unit) ↦
      code.family.right ()) hincidence
  exact Option.some.inj (by
    simpa [ProfiledRawJointSemanticFamily.incidenceCode,
      ProfiledRawJointSemanticFamily.code,
      profiledRawJointCommonWorldFamily,
      ProfiledRawJointCommonBaseWorld.procOneSlot,
      profiledRawRightSlotOfSemanticPair] using hright)

/-- The successor representative's epoch root is the current
representative's literal `.both` DPA state. -/
theorem ProfiledRawJointHybridCommonInstalledMove.simultaneousSuccessor_root
    {initialCode : ProfiledRawJointHybridCode A}
    {policy : ProfiledRawJointHybridProvenanceRationalPolicy A strategy
      initialCode}
    {key : ProfiledRawJointHybridCommonPolicyKey A strategy initialCode policy}
    (installed : ProfiledRawJointHybridCommonInstalledMove A strategy
      initialCode policy key)
    (input : In₁ × In₂)
    (nextInstalled : ProfiledRawJointHybridCommonInstalledMove A strategy
      initialCode policy (installed.simultaneousSuccessorKey A input)) :
    nextInstalled.world.root =
      ((installed.world.procOne A).code (A := A)).2 := by
  have hslot := installed.simultaneousSuccessor_procOneSlot A strategy input
    nextInstalled
  exact congrArg (fun slot : ProfiledRawRightSlot A ↦ slot.1.2) hslot

/-- The successor representative's `.both` entry state is the literal DPA
step produced by the current representative and the installed physical
output. -/
theorem ProfiledRawJointHybridCommonInstalledMove.simultaneousSuccessor_bothState
    {initialCode : ProfiledRawJointHybridCode A}
    {policy : ProfiledRawJointHybridProvenanceRationalPolicy A strategy
      initialCode}
    {key : ProfiledRawJointHybridCommonPolicyKey A strategy initialCode policy}
    (installed : ProfiledRawJointHybridCommonInstalledMove A strategy
      initialCode policy key)
    (input : In₁ × In₂)
    (nextInstalled : ProfiledRawJointHybridCommonInstalledMove A strategy
      initialCode policy (installed.simultaneousSuccessorKey A input)) :
    ((nextInstalled.world.procOne A).code (A := A)).2 =
      A.step ((installed.world.procOne A).code (A := A)).2
        (bothRoundRecord input
          (installed.literalBothOutput A input).1
          (installed.literalBothOutput A input).2) := by
  have hslot := installed.simultaneousSuccessor_procOneSlot A strategy input
    nextInstalled
  have hcode := congrArg
    (fun slot : ProfiledRawRightSlot A ↦ slot.1.1.2) hslot
  change ((nextInstalled.world.procOne A).code (A := A)).2 =
    (((profiledRawJointCommonWorldAfterBoth A installed.world input
      ).procOne A).code (A := A)).2 at hcode
  rw [hcode]
  simp [profiledRawJointCommonWorldAfterBoth,
    profiledRawRightCommonBaseWorld,
    ProfiledRawJointCommonBaseWorld.procOne,
    ProfiledRawJointCommonBaseWorld.procOneMember,
    profiledRawProcOneRowHistory, procOneFreshPair,
    ProcOnePairedEntryRep.code, entryState, History.append,
    List.foldl_append, ProfiledRawJointHybridCommonInstalledMove.literalBothOutput,
    bothRoundRecord, nextRound]

end

/-! ## Literal physical word and DPA-state alignment -/

/-- Installed representative used before physical round `n + 1`. -/
noncomputable def profiledRawJointHybridForeverCommonInstalled
    (inputs : Nat → In₁ × In₂) (n : Nat) :=
  profiledRawJointHybridCommonControlInstalled A strategy hwin
    (profiledRawJointHybridForeverCommonControlTrace A strategy hwin inputs n)

/-- Physical all-`.both` word emitted by the initial literal strategy round
and then by the installed common controls. -/
noncomputable def profiledRawJointHybridForeverCommonPhysicalWord
    (inputs : Nat → In₁ × In₂) :
    OmegaWord (RoundRecord In₁ In₂ Graph Out₁ Out₂)
  | 0 => nextRound strategy []
      ⟨(inputs 0).1, (inputs 0).2, Graph.both⟩
  | n + 1 =>
      let installed :=
        profiledRawJointHybridForeverCommonInstalled A strategy hwin inputs n
      bothRoundRecord (inputs (n + 1))
        (installed.literalBothOutput A (inputs (n + 1))).1
        (installed.literalBothOutput A (inputs (n + 1))).2

section
omit [Inhabited Out₁] [Inhabited Out₂]

/-- At round zero the installed representative has exactly the finite slot
of the literal initial common world. -/
theorem profiledRawJointHybridForeverCommonInstalled_zero_procOneSlot
    (inputs : Nat → In₁ × In₂) :
    (profiledRawJointHybridForeverCommonInstalled A strategy hwin inputs 0
      ).world.procOneSlot A =
      (profiledRawJointInitialCommonBaseWorld A strategy
        (inputs 0).1 (inputs 0).2).procOneSlot A := by
  let installed :=
    profiledRawJointHybridForeverCommonInstalled A strategy hwin inputs 0
  have hright := congrArg
    (fun code : ProfiledRawJointIncidenceCode A (I := Unit) ↦
      code.family.right ()) installed.incidence_eq
  exact Option.some.inj (by simpa [installed,
    profiledRawJointHybridForeverCommonInstalled,
    profiledRawJointHybridForeverCommonControlTrace,
    profiledRawJointHybridForeverCommonKeyTrace,
    profiledRawJointHybridInitialCommonControl,
    profiledRawJointHybridInitialCommonKey,
    ProfiledRawJointHybridInitialCode,
    ProfiledRawJointSemanticFamily.incidenceCode,
    ProfiledRawJointSemanticFamily.code,
    profiledRawJointCommonWorldFamily,
    ProfiledRawJointCommonBaseWorld.procOneSlot,
    profiledRawRightSlotOfSemanticPair] using hright)

/-- Consecutive installed representatives satisfy the exact slot coupling. -/
theorem profiledRawJointHybridForeverCommonInstalled_succ_procOneSlot
    (inputs : Nat → In₁ × In₂) (n : Nat) :
    (profiledRawJointHybridForeverCommonInstalled A strategy hwin inputs
      (n + 1)).world.procOneSlot A =
      (profiledRawJointCommonWorldAfterBoth A
        (profiledRawJointHybridForeverCommonInstalled A strategy hwin inputs n
          ).world (inputs (n + 1))).procOneSlot A := by
  exact
    (profiledRawJointHybridForeverCommonInstalled A strategy hwin inputs n
      ).simultaneousSuccessor_procOneSlot A strategy (inputs (n + 1))
        (profiledRawJointHybridForeverCommonInstalled A strategy hwin inputs
          (n + 1))

/-- The physical DPA state after round `n` is exactly the installed
representative's `.both` state.  This is the crucial representative-mosaic
repair: only the finite slot, not the hidden history, is threaded. -/
theorem profiledRawJointHybridForeverCommon_run_succ
    (inputs : Nat → In₁ × In₂) : ∀ n,
    A.run (profiledRawJointHybridForeverCommonPhysicalWord A strategy hwin
        inputs) (n + 1) =
      ((profiledRawJointHybridForeverCommonInstalled A strategy hwin inputs n
        ).world.procOne A).code.2 := by
  intro n
  induction n with
  | zero =>
      rw [A.run_succ]
      have hslot :=
        profiledRawJointHybridForeverCommonInstalled_zero_procOneSlot A
          strategy hwin inputs
      have hboth := congrArg
        (fun slot : ProfiledRawRightSlot A ↦ slot.1.1.2) hslot
      simpa [profiledRawJointHybridForeverCommonPhysicalWord,
        ProfiledRawJointCommonBaseWorld.procOneSlot,
        profiledRawRightSlotOfSemanticPair,
        ProfiledRawJointCommonBaseWorld.procOneMember,
        ProfiledRawJointCommonBaseWorld.procOne,
        ProcOnePairedEntryRep.code, entryState, History.append,
        List.foldl_append] using hboth.symm
  | succ n ih =>
      rw [A.run_succ, ih]
      exact
        (profiledRawJointHybridForeverCommonInstalled A strategy hwin inputs n
          ).simultaneousSuccessor_bothState A strategy (inputs (n + 1))
            (profiledRawJointHybridForeverCommonInstalled A strategy hwin
              inputs (n + 1)) |>.symm

end

/-! ## Canonical hidden-thread alignment -/

/-- The finite root carried by one side of an installed common world. -/
def profiledRawJointHybridForeverCommonThreadRoot
    {initialCode : ProfiledRawJointHybridCode A}
    {policy : ProfiledRawJointHybridProvenanceRationalPolicy A strategy
      initialCode}
    {key : ProfiledRawJointHybridCommonPolicyKey A strategy initialCode policy}
    (installed : ProfiledRawJointHybridCommonInstalledMove A strategy
      initialCode policy key) :
    IndexedLineageSide → ProfiledRawJointThreadRoot A
  | .right => .inl (installed.world.procOneSlot A)
  | .left => .inr (installed.world.procTwoSlot A)

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- Both common slots carry the same epoch root priority. -/
theorem profiledRawJointHybridForeverCommonThreadRoot_priority
    {initialCode : ProfiledRawJointHybridCode A}
    {policy : ProfiledRawJointHybridProvenanceRationalPolicy A strategy
      initialCode}
    {key : ProfiledRawJointHybridCommonPolicyKey A strategy initialCode policy}
    (installed : ProfiledRawJointHybridCommonInstalledMove A strategy
      initialCode policy key)
    (side : IndexedLineageSide) :
    profiledRawJointThreadRootPriority A
        (profiledRawJointHybridForeverCommonThreadRoot A strategy installed
          side) =
      A.priority installed.world.root := by
  cases side <;> rfl

/-- Side of the hidden thread at positive monitor time `n + 1`, starting
from the proof-side resolution `.right`. -/
def profiledRawJointHybridForeverCommonPositiveSide : Nat → IndexedLineageSide
  | 0 => .left
  | n + 1 => (profiledRawJointHybridForeverCommonPositiveSide n).other

@[simp] theorem profiledRawJointHybridForeverCommonPositiveSide_succ
    (n : Nat) :
    profiledRawJointHybridForeverCommonPositiveSide (n + 1) =
      (profiledRawJointHybridForeverCommonPositiveSide n).other :=
  rfl

section
omit [Inhabited Out₁] [Inhabited Out₂]

/-- Every side of the initial common code exposes the corresponding slot of
the representative installed at the root key. -/
theorem profiledRawJointHybridForeverCommon_initialSlot
    (inputs : Nat → In₁ × In₂) (side : IndexedLineageSide) :
    profiledRawJointHybridCurrentSlots A side
        (ProfiledRawJointHybridInitialCode A strategy (inputs 0)) () =
      some (profiledRawJointHybridForeverCommonThreadRoot A strategy
        (profiledRawJointHybridForeverCommonInstalled A strategy hwin inputs
          0) side) := by
  let installed :=
    profiledRawJointHybridForeverCommonInstalled A strategy hwin inputs 0
  cases side with
  | right =>
      simpa [profiledRawJointHybridCurrentSlots,
        profiledRawJointOneSidedCurrentSlots,
        ProfiledRawJointHybridInitialCode,
        profiledRawJointHybridForeverCommonThreadRoot,
        profiledRawJointHybridForeverCommonInstalled,
        profiledRawJointHybridForeverCommonControlTrace,
        profiledRawJointHybridForeverCommonKeyTrace,
        profiledRawJointHybridInitialCommonControl,
        profiledRawJointHybridInitialCommonKey] using installed.right_slot A
  | left =>
      simpa [profiledRawJointHybridCurrentSlots,
        profiledRawJointOneSidedCurrentSlots,
        ProfiledRawJointHybridInitialCode,
        profiledRawJointHybridForeverCommonThreadRoot,
        profiledRawJointHybridForeverCommonInstalled,
        profiledRawJointHybridForeverCommonControlTrace,
        profiledRawJointHybridForeverCommonKeyTrace,
        profiledRawJointHybridInitialCommonControl,
        profiledRawJointHybridInitialCommonKey] using installed.left_slot A

/-- Every positive code letter exposes the slots of the representative
installed at the corresponding next common key. -/
theorem profiledRawJointHybridForeverCommon_codeSlot
    (inputs : Nat → In₁ × In₂) (n : Nat)
    (side : IndexedLineageSide) :
    profiledRawJointHybridCurrentSlots A side
        (profiledRawJointHybridForeverCommonCodeWord A strategy hwin inputs n)
        () =
      some (profiledRawJointHybridForeverCommonThreadRoot A strategy
        (profiledRawJointHybridForeverCommonInstalled A strategy hwin inputs
          (n + 1)) side) := by
  rw [profiledRawJointHybridForeverCommonCodeWord_eq_key A strategy hwin
    inputs n]
  let installed :=
    profiledRawJointHybridForeverCommonInstalled A strategy hwin inputs
      (n + 1)
  cases side with
  | right =>
      simpa [profiledRawJointHybridCurrentSlots,
        profiledRawJointOneSidedCurrentSlots,
        profiledRawJointHybridForeverCommonThreadRoot, installed,
        profiledRawJointHybridForeverCommonInstalled,
        profiledRawJointHybridForeverCommonControlTrace] using
          installed.right_slot A
  | left =>
      simpa [profiledRawJointHybridCurrentSlots,
        profiledRawJointOneSidedCurrentSlots,
        profiledRawJointHybridForeverCommonThreadRoot, installed,
        profiledRawJointHybridForeverCommonInstalled,
        profiledRawJointHybridForeverCommonControlTrace] using
          installed.left_slot A

/-- The canonical `.right`-resolved code thread remains live forever and at
time `n + 1` names exactly the installed common root at the alternating side.
This is a finite-code calculation; no semantic witnesses at consecutive
states are equated. -/
theorem profiledRawJointHybridForeverCommon_codeRun_succ
    (inputs : Nat → In₁ × In₂) : ∀ n,
    codedAlternatingIndexedLineageCodeRun
        (ProfiledRawJointHybridInitialCode A strategy (inputs 0))
        (profiledRawJointHybridCurrentSlots A)
        (profiledRawJointHybridForeverCommonCodeWord A strategy hwin inputs)
        .right () (n + 1) =
      (profiledRawJointHybridForeverCommonCodeWord A strategy hwin inputs n,
        .live (profiledRawJointHybridForeverCommonPositiveSide n) ()
          (profiledRawJointHybridForeverCommonThreadRoot A strategy
            (profiledRawJointHybridForeverCommonInstalled A strategy hwin
              inputs (n + 1))
            (profiledRawJointHybridForeverCommonPositiveSide n))) := by
  intro n
  induction n with
  | zero =>
      unfold codedAlternatingIndexedLineageCodeRun
      rw [codedAlternatingIndexedLineageRun_succ]
      change codedAlternatingIndexedLineageStep
          (fun _ (_ : Unit) nextCode ↦ nextCode)
          (profiledRawJointHybridCurrentSlots A)
          (codedAlternatingIndexedLineageCodeChild
            (profiledRawJointHybridCurrentSlots A))
          ((ProfiledRawJointHybridInitialCode A strategy (inputs 0)), .initial)
          (Unit.unit,
            profiledRawJointHybridForeverCommonCodeWord A strategy hwin inputs
              0)
          (.right, ()) = _
      apply codedAlternatingIndexedLineageCodeStep_initial_of
        (profiledRawJointHybridCurrentSlots A)
        (ProfiledRawJointHybridInitialCode A strategy (inputs 0))
        (profiledRawJointHybridForeverCommonCodeWord A strategy hwin inputs 0)
        .right ()
        (profiledRawJointHybridForeverCommonThreadRoot A strategy
          (profiledRawJointHybridForeverCommonInstalled A strategy hwin inputs
            0) .right)
        (profiledRawJointHybridForeverCommonThreadRoot A strategy
          (profiledRawJointHybridForeverCommonInstalled A strategy hwin inputs
            1) .left)
      · exact profiledRawJointHybridForeverCommon_initialSlot A strategy hwin
          inputs .right
      · exact profiledRawJointHybridForeverCommon_codeSlot A strategy hwin
          inputs 0 .left
  | succ n ih =>
      unfold codedAlternatingIndexedLineageCodeRun at ih ⊢
      rw [show n + 1 + 1 = (n + 1) + 1 by omega,
        codedAlternatingIndexedLineageRun_succ, ih]
      apply codedAlternatingIndexedLineageCodeStep_live_of
        (profiledRawJointHybridCurrentSlots A)
        (profiledRawJointHybridForeverCommonCodeWord A strategy hwin inputs n)
        (profiledRawJointHybridForeverCommonCodeWord A strategy hwin inputs
          (n + 1))
        (profiledRawJointHybridForeverCommonPositiveSide n) ()
        (profiledRawJointHybridForeverCommonThreadRoot A strategy
          (profiledRawJointHybridForeverCommonInstalled A strategy hwin inputs
            (n + 1))
          (profiledRawJointHybridForeverCommonPositiveSide n))
        (profiledRawJointHybridForeverCommonThreadRoot A strategy
          (profiledRawJointHybridForeverCommonInstalled A strategy hwin inputs
            (n + 2))
          (profiledRawJointHybridForeverCommonPositiveSide (n + 1)))
        (.right, ())
      · exact profiledRawJointHybridForeverCommon_codeSlot A strategy hwin
          inputs n (profiledRawJointHybridForeverCommonPositiveSide n)
      · rw [profiledRawJointHybridForeverCommonPositiveSide_succ]
        exact profiledRawJointHybridForeverCommon_codeSlot A strategy hwin
          inputs (n + 1)
          (profiledRawJointHybridForeverCommonPositiveSide n).other

end

/-- Priority sequence of the canonical `.right`-resolved hidden code thread. -/
noncomputable def profiledRawJointHybridForeverCommonCodePriorities
    (inputs : Nat → In₁ × In₂) : Nat → Nat :=
  fun n ↦
    (codedAlternatingIndexedLineageCodeThreadSystem
      (ProfiledRawJointHybridInitialCode A strategy (inputs 0))
      (profiledRawJointHybridCurrentSlots A)
      (profiledRawJointThreadRootPriority A)).priority
      (codedAlternatingIndexedLineageCodeRun
        (ProfiledRawJointHybridInitialCode A strategy (inputs 0))
        (profiledRawJointHybridCurrentSlots A)
        (profiledRawJointHybridForeverCommonCodeWord A strategy hwin inputs)
        .right () n)

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- At every positive time, the canonical finite-code priority is exactly
the original DPA priority of the emitted physical word.  The equality uses
only the successor-slot law and determinism of `A`; hidden representative
histories need not agree. -/
theorem profiledRawJointHybridForeverCommonCodePriorities_succ
    (inputs : Nat → In₁ × In₂) (n : Nat) :
    profiledRawJointHybridForeverCommonCodePriorities A strategy hwin inputs
        (n + 1) =
      A.priority
        (A.run (profiledRawJointHybridForeverCommonPhysicalWord A strategy
          hwin inputs) (n + 1)) := by
  rw [profiledRawJointHybridForeverCommonCodePriorities,
    profiledRawJointHybridForeverCommon_codeRun_succ A strategy hwin inputs n]
  change profiledRawJointThreadRootPriority A
      (profiledRawJointHybridForeverCommonThreadRoot A strategy
        (profiledRawJointHybridForeverCommonInstalled A strategy hwin inputs
          (n + 1))
        (profiledRawJointHybridForeverCommonPositiveSide n)) = _
  rw [profiledRawJointHybridForeverCommonThreadRoot_priority A strategy]
  apply congrArg A.priority
  have hroot :=
    (profiledRawJointHybridForeverCommonInstalled A strategy hwin inputs n
      ).simultaneousSuccessor_root A strategy (inputs (n + 1))
        (profiledRawJointHybridForeverCommonInstalled A strategy hwin inputs
          (n + 1))
  have hrun := profiledRawJointHybridForeverCommon_run_succ A strategy hwin
    inputs n
  exact hroot.trans hrun.symm

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- **Forever-common physical acceptance.**  The finite common controller's
literal all-`.both` output word is accepted by the original DPA.  This closes
the equality between code and physical parity without a semantic
continuity hypothesis. -/
theorem profiledRawJointHybridForeverCommonPhysicalWord_accepts
    (inputs : Nat → In₁ × In₂) :
    A.Accepts
      (profiledRawJointHybridForeverCommonPhysicalWord A strategy hwin
        inputs) := by
  let codeWord :=
    profiledRawJointHybridForeverCommonCodeWord A strategy hwin inputs
  let codePriorities :=
    profiledRawJointHybridForeverCommonCodePriorities A strategy hwin inputs
  let physicalWord :=
    profiledRawJointHybridForeverCommonPhysicalWord A strategy hwin inputs
  let physicalPriorities := fun n ↦ A.priority (A.run physicalWord n)
  have hcodeAccepts :
      (profiledRawJointHybridCodeParityDPA A
        (ProfiledRawJointHybridInitialCode A strategy (inputs 0))).Accepts
          codeWord := by
    simpa [codeWord, profiledRawJointHybridForeverCommonCodeWord] using
      profiledRawJointHybridForeverCommon_childCode_accepts A strategy hwin
        inputs
  have hcodeParity : NatSeqMinEvenParity codePriorities := by
    have hall := (codedAlternatingIndexedLineageCodeDPA_accepts_iff
      (ProfiledRawJointHybridInitialCode A strategy (inputs 0))
      (profiledRawJointHybridCurrentSlots A)
      (profiledRawJointThreadRootPriority A) codeWord).1 hcodeAccepts
    simpa [codePriorities,
      profiledRawJointHybridForeverCommonCodePriorities, codeWord] using
      hall IndexedLineageSide.right ()
  have hcodeTail :
      NatSeqMinEvenParity (fun n ↦ codePriorities (1 + n)) :=
    (natSeqMinEvenParity_shift codePriorities 1).mpr hcodeParity
  have hphysicalTail :
      NatSeqMinEvenParity (fun n ↦ physicalPriorities (1 + n)) := by
    convert hcodeTail using 1
    funext n
    simpa [codePriorities, physicalPriorities, physicalWord, Nat.add_comm]
      using
        (profiledRawJointHybridForeverCommonCodePriorities_succ A strategy
          hwin inputs n).symm
  rw [A.accepts_iff_natSeqMinEvenParity]
  exact (natSeqMinEvenParity_shift physicalPriorities 1).mp hphysicalTail

end

end DetParityAutomaton

end DistributedSynthesis
