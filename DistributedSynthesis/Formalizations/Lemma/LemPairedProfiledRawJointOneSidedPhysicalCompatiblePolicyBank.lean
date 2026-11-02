/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointOneSidedPhysicalCompatiblePolicy

/-!
# The finite recurrent one-sided physical-policy bank

The recurrent policy needed after post-resolution is not determined by the
bare target incidence code alone.  Its root must also contain the physical
table installed at that target.  This file therefore indexes the bank by the
finite pair consisting of that code and that table, restricted to pairs
jointly realized by one exact one-sided semantic source.

The semantic source and its compatibility proof occur only in the subtype
predicate used to establish that a root is admissible.  They are erased from
runtime data.  For each admissible finite root, one accepting rational policy
is selected once.  A bank successor retains the same root index and invokes
the successor function of that same selected policy; in particular, no new
policy is selected at recurrent targets.
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
variable [DecidableEq In₁] [DecidableEq In₂]

variable
  (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
  (hwin : ∀ env : EnvironmentSequence In₁ In₂,
    A.Accepts (execution strategy env))

private abbrev OneSidedState :=
  ProfiledRawJointOneSidedSemanticState A strategy (I := Unit)

private abbrev PhysicalAnnotation :=
  ProfiledRawJointHybridPhysicalEdgeAnnotation A

private abbrev LinkedCode :=
  SourceFreeBeliefParentLinkedCode
    (BeliefCode := ProfiledRawJointIncidenceCode A (I := Unit))
    (Annotation := PhysicalAnnotation A)

private abbrev ActualDirection :=
  ProfiledRawJointActualDirection (I := Unit) (In₁ := In₁) (In₂ := In₂)

private abbrev LinkedMove :=
  SourceFreeBeliefParentLinkedMove
    (Direction := ActualDirection (In₁ := In₁) (In₂ := In₂))
    (Move := ProfiledRawJointLambdaFamilyMove A (I := Unit))
    (Annotation := PhysicalAnnotation A)

/-! ## Finite admissible roots -/

/-- Public finite data at a recurrent entry. -/
abbrev ProfiledRawJointOneSidedPhysicalCompatibleRootData :=
  ProfiledRawJointIncidenceCode A (I := Unit) × PhysicalAnnotation A

/-- One exact source jointly realizes the advertised code and installed
physical table.  This is a proof-only admissibility condition. -/
def ProfiledRawJointOneSidedPhysicalCompatibleRootRealizable
    (root : ProfiledRawJointOneSidedPhysicalCompatibleRootData A) : Prop :=
  ∃ source : OneSidedState A strategy,
    source.code A = root.1 ∧
      ProfiledRawJointOneSidedPhysicalAnnotationCompatible A strategy source
        root.2

/-- Finite bank index.  Its value is only `(code, table)`; realizability is a
proposition and contributes no runtime state. -/
abbrev ProfiledRawJointOneSidedPhysicalCompatibleRootKey :=
  { root : ProfiledRawJointOneSidedPhysicalCompatibleRootData A //
    ProfiledRawJointOneSidedPhysicalCompatibleRootRealizable A strategy root }

noncomputable instance
    profiledRawJointOneSidedPhysicalCompatibleRootKeyFintype :
    Fintype
      (ProfiledRawJointOneSidedPhysicalCompatibleRootKey A strategy) := by
  classical
  infer_instance

/-! ## Finite readback of an admissible root -/

/-- Search the finite bank index for the key whose public data are `root`.

This readback does not branch on the semantic realizability proposition.
Instead it compares `root` with the public data of every key in the finite
bank.  The definition remains noncomputable because the present `Fintype`
instance for the realizability subtype is obtained classically; effectivizing
that enumeration is a separate issue. -/
noncomputable def
    profiledRawJointOneSidedPhysicalCompatibleRootKey?
    (root : ProfiledRawJointOneSidedPhysicalCompatibleRootData A) :
    Option (ProfiledRawJointOneSidedPhysicalCompatibleRootKey A strategy) := by
  classical
  exact List.find? (fun key ↦ decide (key.1 = root)) Finset.univ.toList

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- A successful finite readback returns a key with exactly the requested
public data. -/
theorem profiledRawJointOneSidedPhysicalCompatibleRootKey?_some_data
    (root : ProfiledRawJointOneSidedPhysicalCompatibleRootData A)
    (key : ProfiledRawJointOneSidedPhysicalCompatibleRootKey A strategy)
    (hread :
      profiledRawJointOneSidedPhysicalCompatibleRootKey? A strategy root =
        some key) :
    key.1 = root := by
  classical
  unfold profiledRawJointOneSidedPhysicalCompatibleRootKey? at hread
  have htest := List.find?_some hread
  simpa using htest

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- If an admissible key with public data `root` exists, finite readback
succeeds and returns that same subtype key.  Equality of the proof fields is
irrelevant by subtype extensionality. -/
theorem profiledRawJointOneSidedPhysicalCompatibleRootKey?_complete
    (root : ProfiledRawJointOneSidedPhysicalCompatibleRootData A)
    (key : ProfiledRawJointOneSidedPhysicalCompatibleRootKey A strategy)
    (hkey : key.1 = root) :
    ∃ found,
      profiledRawJointOneSidedPhysicalCompatibleRootKey? A strategy root =
          some found ∧
        found = key := by
  classical
  let keys :=
    (Finset.univ : Finset
      (ProfiledRawJointOneSidedPhysicalCompatibleRootKey A strategy)).toList
  have hmem : key ∈ keys := by
    simp [keys]
  have htest : decide (key.1 = root) = true := by
    simp [hkey]
  have hexists : ∃ candidate ∈ keys,
      decide (candidate.1 = root) = true :=
    ⟨key, hmem, htest⟩
  have hsome :
      (List.find? (fun candidate :
          ProfiledRawJointOneSidedPhysicalCompatibleRootKey A strategy ↦
        decide (candidate.1 = root)) keys).isSome = true :=
    List.find?_isSome.mpr hexists
  rw [Option.isSome_iff_exists] at hsome
  obtain ⟨found, hfound⟩ := hsome
  have hfoundData : found.1 = root := by
    have hdecide : decide (found.1 = root) = true :=
      @List.find?_some _
        (fun candidate :
          ProfiledRawJointOneSidedPhysicalCompatibleRootKey A strategy ↦
          decide (candidate.1 = root)) found keys hfound
    exact of_decide_eq_true hdecide
  have hfoundKey : found = key := by
    apply Subtype.ext
    exact hfoundData.trans hkey.symm
  exact ⟨found, by
    simpa [profiledRawJointOneSidedPhysicalCompatibleRootKey?, keys] using
      hfound, hfoundKey⟩

/-- Package a compatible exact source into its finite bank index. -/
def profiledRawJointOneSidedPhysicalCompatibleRootKeyOf
    (source : OneSidedState A strategy)
    (annotation : PhysicalAnnotation A)
    (hcompatible : ProfiledRawJointOneSidedPhysicalAnnotationCompatible A
      strategy source annotation) :
    ProfiledRawJointOneSidedPhysicalCompatibleRootKey A strategy :=
  ⟨(source.code A, annotation), source, rfl, hcompatible⟩

omit [Inhabited Out₁] [Inhabited Out₂] in
@[simp] theorem
    profiledRawJointOneSidedPhysicalCompatibleRootKeyOf_code
    (source : OneSidedState A strategy)
    (annotation : PhysicalAnnotation A)
    (hcompatible : ProfiledRawJointOneSidedPhysicalAnnotationCompatible A
      strategy source annotation) :
    (profiledRawJointOneSidedPhysicalCompatibleRootKeyOf A strategy source
      annotation hcompatible).1.1 = source.code A :=
  rfl

omit [Inhabited Out₁] [Inhabited Out₂] in
@[simp] theorem
    profiledRawJointOneSidedPhysicalCompatibleRootKeyOf_annotation
    (source : OneSidedState A strategy)
    (annotation : PhysicalAnnotation A)
    (hcompatible : ProfiledRawJointOneSidedPhysicalAnnotationCompatible A
      strategy source annotation) :
    (profiledRawJointOneSidedPhysicalCompatibleRootKeyOf A strategy source
      annotation hcompatible).1.2 = annotation :=
  rfl

/-! ## One policy selected once for every finite root -/

/-- A proof witness used only to construct the selected policy. -/
noncomputable def profiledRawJointOneSidedPhysicalCompatibleBankSource
    (key : ProfiledRawJointOneSidedPhysicalCompatibleRootKey A strategy) :
    OneSidedState A strategy :=
  Classical.choose key.2

omit [Inhabited Out₁] [Inhabited Out₂] in
theorem profiledRawJointOneSidedPhysicalCompatibleBankSource_code
    (key : ProfiledRawJointOneSidedPhysicalCompatibleRootKey A strategy) :
    (profiledRawJointOneSidedPhysicalCompatibleBankSource A strategy key).code
        A = key.1.1 :=
  (Classical.choose_spec key.2).1

omit [Inhabited Out₁] [Inhabited Out₂] in
theorem profiledRawJointOneSidedPhysicalCompatibleBankSource_compatible
    (key : ProfiledRawJointOneSidedPhysicalCompatibleRootKey A strategy) :
    ProfiledRawJointOneSidedPhysicalAnnotationCompatible A strategy
      (profiledRawJointOneSidedPhysicalCompatibleBankSource A strategy key)
      key.1.2 :=
  (Classical.choose_spec key.2).2

/-- The recurrent accepting policy selected globally at an admissible finite
root. -/
noncomputable def profiledRawJointOneSidedPhysicalCompatiblePolicyBank
    (key : ProfiledRawJointOneSidedPhysicalCompatibleRootKey A strategy) :
    ProfiledRawJointOneSidedPhysicalCompatibleRationalPolicy A strategy hwin
      key.1.1 key.1.2 := by
  let source :=
    profiledRawJointOneSidedPhysicalCompatibleBankSource A strategy key
  have hpolicy :=
    nonempty_profiledRawJointOneSidedPhysicalCompatibleRationalPolicy A
      strategy hwin source key.1.2
        (profiledRawJointOneSidedPhysicalCompatibleBankSource_compatible A
          strategy key)
  have hcode : source.code A = key.1.1 :=
    profiledRawJointOneSidedPhysicalCompatibleBankSource_code A strategy key
  rw [hcode] at hpolicy
  exact Classical.choice hpolicy

/-! ## Finite runtime and its invariant -/

/-- Runtime state: an admissible finite root index paired with one finite
state of the policy selected at that index. -/
abbrev ProfiledRawJointOneSidedPhysicalCompatibleBankControl :=
  Σ key : ProfiledRawJointOneSidedPhysicalCompatibleRootKey A strategy,
    ProfiledRawJointOneSidedPhysicalCompatiblePolicyState A strategy hwin
      key.1.1 key.1.2

noncomputable instance
    profiledRawJointOneSidedPhysicalCompatibleBankControlFintype :
    Fintype
      (ProfiledRawJointOneSidedPhysicalCompatibleBankControl A strategy
        hwin) := by
  classical
  infer_instance

/-- Enter the already selected bank policy at its rational root. -/
noncomputable def profiledRawJointOneSidedPhysicalCompatibleBankRoot
    (key : ProfiledRawJointOneSidedPhysicalCompatibleRootKey A strategy) :
    ProfiledRawJointOneSidedPhysicalCompatibleBankControl A strategy hwin :=
  ⟨key,
    (profiledRawJointOneSidedPhysicalCompatiblePolicyBank A strategy hwin
      key).run []⟩

/-- The rational root exposes exactly the finite code and physical table in
the bank index. -/
theorem profiledRawJointOneSidedPhysicalCompatibleBankRoot_data
    (key : ProfiledRawJointOneSidedPhysicalCompatibleRootKey A strategy) :
    (profiledRawJointOneSidedPhysicalCompatibleBankRoot A strategy hwin
      key).2.1 = key.1 := by
  exact congrArg Prod.fst
    (profiledRawJointOneSidedPhysicalCompatiblePolicyBank A strategy hwin
      key).accepts.1.1

/-- Advance inside the selected policy without changing the bank index. -/
noncomputable def profiledRawJointOneSidedPhysicalCompatibleBankSuccessor
    (state : ProfiledRawJointOneSidedPhysicalCompatibleBankControl A strategy
      hwin)
    (childCode : LinkedCode A) :
    ProfiledRawJointOneSidedPhysicalCompatibleBankControl A strategy hwin :=
  ⟨state.1,
    (profiledRawJointOneSidedPhysicalCompatiblePolicyBank A strategy hwin
      state.1).successor state.2 childCode⟩

@[simp] theorem
    profiledRawJointOneSidedPhysicalCompatibleBankRoot_index
    (key : ProfiledRawJointOneSidedPhysicalCompatibleRootKey A strategy) :
    (profiledRawJointOneSidedPhysicalCompatibleBankRoot A strategy hwin
      key).1 = key :=
  rfl

@[simp] theorem
    profiledRawJointOneSidedPhysicalCompatibleBankSuccessor_index
    (state : ProfiledRawJointOneSidedPhysicalCompatibleBankControl A strategy
      hwin)
    (childCode : LinkedCode A) :
    (profiledRawJointOneSidedPhysicalCompatibleBankSuccessor A strategy hwin
      state childCode).1 = state.1 :=
  rfl

/-- A linked child is a genuine lift of a bare physical target when one
actual direction of the semantic source witnessing the current selected
policy move produces that linked code and the selected policy takes its
successor on the same code. -/
def ProfiledRawJointOneSidedPhysicalCompatibleBankChildRealizes
    (state : ProfiledRawJointOneSidedPhysicalCompatibleBankControl A strategy
      hwin)
    (target : ProfiledRawJointIncidenceCode A (I := Unit))
    (childCode : LinkedCode A) : Prop :=
  ∃ move : LinkedMove A (In₁ := In₁) (In₂ := In₂),
    ∃ source : OneSidedState A strategy,
      ∃ actual : ActualDirection (In₁ := In₁) (In₂ := In₂),
        source.code A = state.2.1.1 ∧
          source.move A = move.1 ∧
          ProfiledRawJointOneSidedPhysicalAnnotationCompatible A strategy
            source state.2.1.2 ∧
          (∀ direction,
            profiledRawJointOneSidedPhysicalAnnotationAdvance A strategy hwin
                source state.2.1.2 direction =
              move.2 direction) ∧
          childCode = sourceFreeBeliefParentLinkedNext
            (profiledRawJointOneSidedNext A) state.2.1 move actual ∧
          childCode.1 = target ∧
          (profiledRawJointOneSidedPhysicalCompatiblePolicyBank A strategy
              hwin state.1).successor state.2 childCode =
            (childCode,
              (sourceFreeBeliefParentLinkedCodeParityDPA
                (Annotation := PhysicalAnnotation A)
                (profiledRawJointOneSidedCodeParityDPA A
                  state.1.1.1)).step state.2.2 childCode)

/-- A realizing linked child carries the table installed by the very same
literal semantic step that produces its bare target.  This rules out a
post-hoc code-equal representative with an unrelated table. -/
theorem
    ProfiledRawJointOneSidedPhysicalCompatibleBankChildRealizes.exists_child
    (state : ProfiledRawJointOneSidedPhysicalCompatibleBankControl A strategy
      hwin)
    (target : ProfiledRawJointIncidenceCode A (I := Unit))
    (childCode : LinkedCode A)
    (hrealizes :
      ProfiledRawJointOneSidedPhysicalCompatibleBankChildRealizes A strategy
        hwin state target childCode) :
    ∃ source : OneSidedState A strategy,
      ∃ actual : ActualDirection (In₁ := In₁) (In₂ := In₂),
        (source.step A actual).code A = target ∧
          childCode.2 =
            profiledRawJointOneSidedPhysicalAnnotationAdvance A strategy hwin
              source state.2.1.2 actual ∧
          ProfiledRawJointOneSidedPhysicalAnnotationCompatible A strategy
            (source.step A actual) childCode.2 := by
  rcases hrealizes with
    ⟨move, source, actual, hcode, hmove, _hcompatible, hchildren,
      hchildCode, hbare, _hsuccessor⟩
  have hstepCode : (source.step A actual).code A = childCode.1 := by
    rw [ProfiledRawJointOneSidedSemanticState.step_code]
    rw [hcode, hmove, hchildCode]
    rfl
  have hannotation :
      childCode.2 =
        profiledRawJointOneSidedPhysicalAnnotationAdvance A strategy hwin
          source state.2.1.2 actual := by
    rw [hchildCode]
    exact (hchildren actual).symm
  refine ⟨source, actual, hstepCode.trans hbare, hannotation, ?_⟩
  rw [hannotation]
  exact
    profiledRawJointOneSidedPhysicalAnnotationAdvance_compatible A strategy
      hwin source state.2.1.2 actual

/-- Total finite lifting of a bare target to a linked child.  On realizable
targets it chooses a realizing child; outside the invariant it uses an
arbitrary finite fallback. -/
noncomputable def
    profiledRawJointOneSidedPhysicalCompatibleBankResolveTarget
    (state : ProfiledRawJointOneSidedPhysicalCompatibleBankControl A strategy
      hwin)
    (target : ProfiledRawJointIncidenceCode A (I := Unit)) : LinkedCode A := by
  classical
  exact if h : ∃ childCode,
      ProfiledRawJointOneSidedPhysicalCompatibleBankChildRealizes A strategy
        hwin state target childCode then
    Classical.choose h
  else
    state.2.1

/-- On every realizable target, the total lifting returns a genuine linked
child of the current selected policy move. -/
theorem
    profiledRawJointOneSidedPhysicalCompatibleBankResolveTarget_realizes
    (state : ProfiledRawJointOneSidedPhysicalCompatibleBankControl A strategy
      hwin)
    (target : ProfiledRawJointIncidenceCode A (I := Unit))
    (hexists : ∃ childCode,
      ProfiledRawJointOneSidedPhysicalCompatibleBankChildRealizes A strategy
        hwin state target childCode) :
    ProfiledRawJointOneSidedPhysicalCompatibleBankChildRealizes A strategy
      hwin state target
        (profiledRawJointOneSidedPhysicalCompatibleBankResolveTarget A
          strategy hwin state target) := by
  classical
  simp only [profiledRawJointOneSidedPhysicalCompatibleBankResolveTarget]
  split
  next h => exact Classical.choose_spec h
  next h => exact (h hexists).elim

/-- Reachability is measured inside the one policy selected at the stored
root index. -/
abbrev ProfiledRawJointOneSidedPhysicalCompatibleBankReachable
    (state : ProfiledRawJointOneSidedPhysicalCompatibleBankControl A strategy
      hwin) : Prop :=
  ProfiledRawJointOneSidedPhysicalCompatibleReachable A strategy hwin
    state.1.1.1 state.1.1.2
    (profiledRawJointOneSidedPhysicalCompatiblePolicyBank A strategy hwin
      state.1)
    state.2

theorem profiledRawJointOneSidedPhysicalCompatibleBankRoot_reachable
    (key : ProfiledRawJointOneSidedPhysicalCompatibleRootKey A strategy) :
    ProfiledRawJointOneSidedPhysicalCompatibleBankReachable A strategy hwin
      (profiledRawJointOneSidedPhysicalCompatibleBankRoot A strategy hwin
        key) :=
  ⟨[], rfl⟩

theorem profiledRawJointOneSidedPhysicalCompatibleBankSuccessor_reachable
    (state : ProfiledRawJointOneSidedPhysicalCompatibleBankControl A strategy
      hwin)
    (hreachable :
      ProfiledRawJointOneSidedPhysicalCompatibleBankReachable A strategy hwin
        state)
    (childCode : LinkedCode A) :
    ProfiledRawJointOneSidedPhysicalCompatibleBankReachable A strategy hwin
      (profiledRawJointOneSidedPhysicalCompatibleBankSuccessor A strategy hwin
        state childCode) :=
  profiledRawJointOneSidedPhysicalCompatible_successor_reachable A strategy
    hwin state.1.1.1 state.1.1.2
      (profiledRawJointOneSidedPhysicalCompatiblePolicyBank A strategy hwin
        state.1)
      state.2 hreachable childCode

/-- The deterministic finite lifting is an invariant-preserving transition
whenever a realizing linked child exists. -/
theorem profiledRawJointOneSidedPhysicalCompatibleBankResolveTarget_spec
    (state : ProfiledRawJointOneSidedPhysicalCompatibleBankControl A strategy
      hwin)
    (hreachable :
      ProfiledRawJointOneSidedPhysicalCompatibleBankReachable A strategy hwin
        state)
    (target : ProfiledRawJointIncidenceCode A (I := Unit))
    (hexists : ∃ childCode,
      ProfiledRawJointOneSidedPhysicalCompatibleBankChildRealizes A strategy
        hwin state target childCode) :
    let childCode :=
      profiledRawJointOneSidedPhysicalCompatibleBankResolveTarget A strategy
        hwin state target
    childCode.1 = target ∧
      ProfiledRawJointOneSidedPhysicalCompatibleBankChildRealizes A strategy
        hwin state target childCode ∧
      (profiledRawJointOneSidedPhysicalCompatibleBankSuccessor A strategy hwin
        state childCode).1 = state.1 ∧
      ProfiledRawJointOneSidedPhysicalCompatibleBankReachable A strategy hwin
        (profiledRawJointOneSidedPhysicalCompatibleBankSuccessor A strategy
          hwin state childCode) := by
  dsimp only
  have hrealizes :=
    profiledRawJointOneSidedPhysicalCompatibleBankResolveTarget_realizes A
      strategy hwin state target hexists
  rcases hrealizes with
    ⟨move, source, actual, hcode, hmove, hcompatible, hchildren,
      hchildCode, hbare, hsuccessor⟩
  have hrealizes' :
      ProfiledRawJointOneSidedPhysicalCompatibleBankChildRealizes A strategy
        hwin state target
          (profiledRawJointOneSidedPhysicalCompatibleBankResolveTarget A
            strategy hwin state target) :=
    ⟨move, source, actual, hcode, hmove, hcompatible, hchildren,
      hchildCode, hbare, hsuccessor⟩
  refine ⟨hbare, hrealizes', rfl, ?_⟩
  exact
    profiledRawJointOneSidedPhysicalCompatibleBankSuccessor_reachable A
      strategy hwin state hreachable _

/-! ## Installed-table target closure in one fixed bank component -/

/-- Every target allowed by the installed right table is realized by a
linked child code.  Advancing on that child retains the bank index and is
reachable inside the policy selected once at that index. -/
theorem
    exists_profiledRawJointOneSidedPhysicalCompatibleBankRightTargetSuccessor
    (state : ProfiledRawJointOneSidedPhysicalCompatibleBankControl A strategy
      hwin)
    (hreachable :
      ProfiledRawJointOneSidedPhysicalCompatibleBankReachable A strategy hwin
        state)
    (currentCode : ProfiledRawJointIncidenceCode A (I := Unit))
    (hcurrentCode : state.2.1.1 = currentCode)
    (root : ProfiledRawJointThreadRoot A)
    (hroot : profiledRawJointOneSidedCurrentSlots A .right currentCode () =
      some root)
    (phaseMove : ProfiledRawJointRightPhysicalSiblingMove A)
    (hphaseMove : state.2.1.2.1 = some phaseMove)
    (target : ProfiledRawJointIncidenceCode A (I := Unit))
    (htarget : profiledRawJointRightPhysicalSiblingAllowed A phaseMove.1
      target) :
    ∃ childCode : LinkedCode A,
      childCode.1 = target ∧
        ProfiledRawJointOneSidedPhysicalCompatibleBankChildRealizes A strategy
          hwin state target childCode ∧
        (profiledRawJointOneSidedPhysicalCompatibleBankSuccessor A strategy
          hwin state childCode).1 = state.1 ∧
        ProfiledRawJointOneSidedPhysicalCompatibleBankReachable A strategy
          hwin
          (profiledRawJointOneSidedPhysicalCompatibleBankSuccessor A strategy
            hwin state childCode) := by
  rcases
      exists_profiledRawJointOneSidedPhysicalCompatibleRightTargetSuccessor A
        strategy hwin state.1.1.1 state.1.1.2
        (profiledRawJointOneSidedPhysicalCompatiblePolicyBank A strategy hwin
          state.1)
        state.2 hreachable currentCode hcurrentCode root hroot phaseMove
          hphaseMove target htarget with
    ⟨move, source, actual, hcode, hmove, hcompatible, hchildren, _hside,
      _hactualTarget, _hchildAnnotation, hchildBare, hsuccessor⟩
  let childCode := sourceFreeBeliefParentLinkedNext
    (profiledRawJointOneSidedNext A) state.2.1 move actual
  have hrealizes :
      ProfiledRawJointOneSidedPhysicalCompatibleBankChildRealizes A strategy
        hwin state target childCode := by
    exact ⟨move, source, actual, hcode, hmove, hcompatible, hchildren, rfl,
      hchildBare, hsuccessor⟩
  refine ⟨childCode, hchildBare, hrealizes, rfl, ?_⟩
  exact
    profiledRawJointOneSidedPhysicalCompatibleBankSuccessor_reachable A
      strategy hwin state hreachable childCode

/-- Deterministic right-target form used by an executable carrier. -/
theorem
    profiledRawJointOneSidedPhysicalCompatibleBankResolveRightTarget_spec
    (state : ProfiledRawJointOneSidedPhysicalCompatibleBankControl A strategy
      hwin)
    (hreachable :
      ProfiledRawJointOneSidedPhysicalCompatibleBankReachable A strategy hwin
        state)
    (currentCode : ProfiledRawJointIncidenceCode A (I := Unit))
    (hcurrentCode : state.2.1.1 = currentCode)
    (root : ProfiledRawJointThreadRoot A)
    (hroot : profiledRawJointOneSidedCurrentSlots A .right currentCode () =
      some root)
    (phaseMove : ProfiledRawJointRightPhysicalSiblingMove A)
    (hphaseMove : state.2.1.2.1 = some phaseMove)
    (target : ProfiledRawJointIncidenceCode A (I := Unit))
    (htarget : profiledRawJointRightPhysicalSiblingAllowed A phaseMove.1
      target) :
    let childCode :=
      profiledRawJointOneSidedPhysicalCompatibleBankResolveTarget A strategy
        hwin state target
    childCode.1 = target ∧
      ProfiledRawJointOneSidedPhysicalCompatibleBankChildRealizes A strategy
        hwin state target childCode ∧
      (profiledRawJointOneSidedPhysicalCompatibleBankSuccessor A strategy hwin
        state childCode).1 = state.1 ∧
      ProfiledRawJointOneSidedPhysicalCompatibleBankReachable A strategy hwin
        (profiledRawJointOneSidedPhysicalCompatibleBankSuccessor A strategy
          hwin state childCode) := by
  obtain ⟨childCode, _hbare, hrealizes, _hindex, _hnext⟩ :=
    exists_profiledRawJointOneSidedPhysicalCompatibleBankRightTargetSuccessor
      A strategy hwin state hreachable currentCode hcurrentCode root hroot
        phaseMove hphaseMove target htarget
  exact
    profiledRawJointOneSidedPhysicalCompatibleBankResolveTarget_spec A
      strategy hwin state hreachable target ⟨childCode, hrealizes⟩

/-- Left-orientation mirror of bank-local installed-table target closure. -/
theorem
    exists_profiledRawJointOneSidedPhysicalCompatibleBankLeftTargetSuccessor
    (state : ProfiledRawJointOneSidedPhysicalCompatibleBankControl A strategy
      hwin)
    (hreachable :
      ProfiledRawJointOneSidedPhysicalCompatibleBankReachable A strategy hwin
        state)
    (currentCode : ProfiledRawJointIncidenceCode A (I := Unit))
    (hcurrentCode : state.2.1.1 = currentCode)
    (root : ProfiledRawJointThreadRoot A)
    (hroot : profiledRawJointOneSidedCurrentSlots A .left currentCode () =
      some root)
    (phaseMove : ProfiledRawJointLeftPhysicalSiblingMove A)
    (hphaseMove : state.2.1.2.2 = some phaseMove)
    (target : ProfiledRawJointIncidenceCode A (I := Unit))
    (htarget : profiledRawJointLeftPhysicalSiblingAllowed A phaseMove.1
      target) :
    ∃ childCode : LinkedCode A,
      childCode.1 = target ∧
        ProfiledRawJointOneSidedPhysicalCompatibleBankChildRealizes A strategy
          hwin state target childCode ∧
        (profiledRawJointOneSidedPhysicalCompatibleBankSuccessor A strategy
          hwin state childCode).1 = state.1 ∧
        ProfiledRawJointOneSidedPhysicalCompatibleBankReachable A strategy
          hwin
          (profiledRawJointOneSidedPhysicalCompatibleBankSuccessor A strategy
            hwin state childCode) := by
  rcases
      exists_profiledRawJointOneSidedPhysicalCompatibleLeftTargetSuccessor A
        strategy hwin state.1.1.1 state.1.1.2
        (profiledRawJointOneSidedPhysicalCompatiblePolicyBank A strategy hwin
          state.1)
        state.2 hreachable currentCode hcurrentCode root hroot phaseMove
          hphaseMove target htarget with
    ⟨move, source, actual, hcode, hmove, hcompatible, hchildren, _hside,
      _hactualTarget, _hchildAnnotation, hchildBare, hsuccessor⟩
  let childCode := sourceFreeBeliefParentLinkedNext
    (profiledRawJointOneSidedNext A) state.2.1 move actual
  have hrealizes :
      ProfiledRawJointOneSidedPhysicalCompatibleBankChildRealizes A strategy
        hwin state target childCode := by
    exact ⟨move, source, actual, hcode, hmove, hcompatible, hchildren, rfl,
      hchildBare, hsuccessor⟩
  refine ⟨childCode, hchildBare, hrealizes, rfl, ?_⟩
  exact
    profiledRawJointOneSidedPhysicalCompatibleBankSuccessor_reachable A
      strategy hwin state hreachable childCode

/-- Deterministic left-target mirror used by an executable carrier. -/
theorem
    profiledRawJointOneSidedPhysicalCompatibleBankResolveLeftTarget_spec
    (state : ProfiledRawJointOneSidedPhysicalCompatibleBankControl A strategy
      hwin)
    (hreachable :
      ProfiledRawJointOneSidedPhysicalCompatibleBankReachable A strategy hwin
        state)
    (currentCode : ProfiledRawJointIncidenceCode A (I := Unit))
    (hcurrentCode : state.2.1.1 = currentCode)
    (root : ProfiledRawJointThreadRoot A)
    (hroot : profiledRawJointOneSidedCurrentSlots A .left currentCode () =
      some root)
    (phaseMove : ProfiledRawJointLeftPhysicalSiblingMove A)
    (hphaseMove : state.2.1.2.2 = some phaseMove)
    (target : ProfiledRawJointIncidenceCode A (I := Unit))
    (htarget : profiledRawJointLeftPhysicalSiblingAllowed A phaseMove.1
      target) :
    let childCode :=
      profiledRawJointOneSidedPhysicalCompatibleBankResolveTarget A strategy
        hwin state target
    childCode.1 = target ∧
      ProfiledRawJointOneSidedPhysicalCompatibleBankChildRealizes A strategy
        hwin state target childCode ∧
      (profiledRawJointOneSidedPhysicalCompatibleBankSuccessor A strategy hwin
        state childCode).1 = state.1 ∧
      ProfiledRawJointOneSidedPhysicalCompatibleBankReachable A strategy hwin
        (profiledRawJointOneSidedPhysicalCompatibleBankSuccessor A strategy
          hwin state childCode) := by
  obtain ⟨childCode, _hbare, hrealizes, _hindex, _hnext⟩ :=
    exists_profiledRawJointOneSidedPhysicalCompatibleBankLeftTargetSuccessor A
      strategy hwin state hreachable currentCode hcurrentCode root hroot
        phaseMove hphaseMove target htarget
  exact
    profiledRawJointOneSidedPhysicalCompatibleBankResolveTarget_spec A
      strategy hwin state hreachable target ⟨childCode, hrealizes⟩

end

end DetParityAutomaton

end DistributedSynthesis
