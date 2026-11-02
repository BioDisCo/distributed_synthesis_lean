/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledOpenReanchoredSidewiseSuccessor

/-!
# Operational queries belong to the reachable sidewise alphabet

The re-anchored successor uses the finite subtype of fixed sidewise queries
whose rational-controller coordinates are reachable by blind-sender words.
This file supplies the operational constructor for that subtype.

At a real block prefix, the usual finite-state implementation stores the
rational control reached at `senderWord past` together with the corresponding
monitor state.  The first coordinate is therefore reachable by construction.
Only one fixed value is selected at an oriented proof step; every unused
coordinate of the finite query bank is filled by the already proved
empty-word query.

The side and finite direction tag below are arbitrary parameters.  They are
not inspected when constructing either local controller coordinate, and no
process is given an orientation, graph, strict-leader flag, or hidden bit.
-/

namespace DistributedSynthesis

universe i u v x y s

namespace DetParityAutomaton

variable {I : Type i}
variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable
  (A : DetParityAutomaton.{max u v x y, s}
    (RoundRecord In₁ In₂ Graph Out₁ Out₂))

noncomputable section

variable [Fintype I]
variable [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁]
  [Inhabited Out₂]
variable [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
variable [DecidableEq In₁] [DecidableEq In₂]

variable (initialCode : ProfiledOpenIndexedBiBeliefCode A (I := I))

/-! ## One literal controller coordinate -/

/-- A right query whose controller coordinate is reached by the supplied
blind-sender word.  The monitor coordinate is independent of the reachability
proof and may be the actual monitor state carried by the local execution. -/
noncomputable def profiledOpenFixedRightQueryAtWord
    (value : ProfiledOpenFixedRightPinnedValue A initialCode)
    (word : List In₁)
    (monitorState :
      (ProfiledOpenHiddenDescriptorRightPinnedUnionMonitor A value.1
        value.2.1).State) :
    ProfiledOpenFixedRightPinnedBlockQuery A initialCode value :=
  (value.2.2.1.toTransitionRationalTree.controlAt word, monitorState)

/-- Left mirror. -/
noncomputable def profiledOpenFixedLeftQueryAtWord
    (value : ProfiledOpenFixedLeftPinnedValue A initialCode)
    (word : List In₂)
    (monitorState :
      (ProfiledOpenHiddenDescriptorLeftPinnedUnionMonitor A value.1
        value.2.1).State) :
    ProfiledOpenFixedLeftPinnedBlockQuery A initialCode value :=
  (value.2.2.1.toTransitionRationalTree.controlAt word, monitorState)

section
omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]

@[simp] theorem profiledOpenFixedRightQueryAtWord_control
    (value : ProfiledOpenFixedRightPinnedValue A initialCode)
    (word : List In₁)
    (monitorState :
      (ProfiledOpenHiddenDescriptorRightPinnedUnionMonitor A value.1
        value.2.1).State) :
    (profiledOpenFixedRightQueryAtWord A initialCode value word
      monitorState).1 =
      value.2.2.1.toTransitionRationalTree.controlAt word :=
  rfl

@[simp] theorem profiledOpenFixedLeftQueryAtWord_control
    (value : ProfiledOpenFixedLeftPinnedValue A initialCode)
    (word : List In₂)
    (monitorState :
      (ProfiledOpenHiddenDescriptorLeftPinnedUnionMonitor A value.1
        value.2.1).State) :
    (profiledOpenFixedLeftQueryAtWord A initialCode value word
      monitorState).1 =
      value.2.2.1.toTransitionRationalTree.controlAt word :=
  rfl

theorem profiledOpenFixedRightQueryAtWord_reachable
    (value : ProfiledOpenFixedRightPinnedValue A initialCode)
    (word : List In₁)
    (monitorState :
      (ProfiledOpenHiddenDescriptorRightPinnedUnionMonitor A value.1
        value.2.1).State) :
    ProfiledOpenFixedRightQueryReachable A initialCode value
      (profiledOpenFixedRightQueryAtWord A initialCode value word
        monitorState) :=
  ⟨word, rfl⟩

theorem profiledOpenFixedLeftQueryAtWord_reachable
    (value : ProfiledOpenFixedLeftPinnedValue A initialCode)
    (word : List In₂)
    (monitorState :
      (ProfiledOpenHiddenDescriptorLeftPinnedUnionMonitor A value.1
        value.2.1).State) :
    ProfiledOpenFixedLeftQueryReachable A initialCode value
      (profiledOpenFixedLeftQueryAtWord A initialCode value word
        monitorState) :=
  ⟨word, rfl⟩

end

/-! ## Reachability is an invariant, not stored history -/

/-- Advance the right rational control by one locally observed sender input;
the union-monitor state is the independently computed next finite monitor
state. -/
noncomputable def profiledOpenFixedRightQueryStep
    (value : ProfiledOpenFixedRightPinnedValue A initialCode)
    (query : ProfiledOpenFixedRightPinnedBlockQuery A initialCode value)
    (input : In₁)
    (nextMonitor :
      (ProfiledOpenHiddenDescriptorRightPinnedUnionMonitor A value.1
        value.2.1).State) :
    ProfiledOpenFixedRightPinnedBlockQuery A initialCode value :=
  (value.2.2.1.toTransitionRationalTree.step query.1 input, nextMonitor)

/-- Left step. -/
noncomputable def profiledOpenFixedLeftQueryStep
    (value : ProfiledOpenFixedLeftPinnedValue A initialCode)
    (query : ProfiledOpenFixedLeftPinnedBlockQuery A initialCode value)
    (input : In₂)
    (nextMonitor :
      (ProfiledOpenHiddenDescriptorLeftPinnedUnionMonitor A value.1
        value.2.1).State) :
    ProfiledOpenFixedLeftPinnedBlockQuery A initialCode value :=
  (value.2.2.1.toTransitionRationalTree.step query.1 input, nextMonitor)

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
/-- A reachable right query remains reachable after the executable finite
controller step.  The longer word occurs only inside this proof; it is not a
field of the finite query state. -/
theorem profiledOpenFixedRightQueryStep_reachable
    (value : ProfiledOpenFixedRightPinnedValue A initialCode)
    (query : ProfiledOpenFixedRightPinnedBlockQuery A initialCode value)
    (hreachable : ProfiledOpenFixedRightQueryReachable A initialCode value
      query)
    (input : In₁)
    (nextMonitor :
      (ProfiledOpenHiddenDescriptorRightPinnedUnionMonitor A value.1
        value.2.1).State) :
    ProfiledOpenFixedRightQueryReachable A initialCode value
      (profiledOpenFixedRightQueryStep A initialCode value query input
        nextMonitor) := by
  rcases hreachable with ⟨word, hword⟩
  refine ⟨word ++ [input], ?_⟩
  simp only [TransitionRationalTree.controlAt_append, List.foldl_cons,
    List.foldl_nil]
  simp only [profiledOpenFixedRightQueryStep, hword]

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
/-- Left invariant step. -/
theorem profiledOpenFixedLeftQueryStep_reachable
    (value : ProfiledOpenFixedLeftPinnedValue A initialCode)
    (query : ProfiledOpenFixedLeftPinnedBlockQuery A initialCode value)
    (hreachable : ProfiledOpenFixedLeftQueryReachable A initialCode value
      query)
    (input : In₂)
    (nextMonitor :
      (ProfiledOpenHiddenDescriptorLeftPinnedUnionMonitor A value.1
        value.2.1).State) :
    ProfiledOpenFixedLeftQueryReachable A initialCode value
      (profiledOpenFixedLeftQueryStep A initialCode value query input
        nextMonitor) := by
  rcases hreachable with ⟨word, hword⟩
  refine ⟨word ++ [input], ?_⟩
  simp only [TransitionRationalTree.controlAt_append, List.foldl_cons,
    List.foldl_nil]
  simp only [profiledOpenFixedLeftQueryStep, hword]

/-! ## Sparse finite query banks -/

/-- Put an already-carried literal right query at one selected value and use
the empty-word query elsewhere.  This is the adapter used when an operational
carrier stores `(control, monitorState)` but not its witnessing word. -/
noncomputable def profiledOpenFixedRightQueryBankWithSelected
    (selected : ProfiledOpenFixedRightPinnedValue A initialCode)
    (query : ProfiledOpenFixedRightPinnedBlockQuery A initialCode selected) :
    ProfiledOpenFixedRightPinnedBlockQueryBank A initialCode := by
  classical
  exact fun value =>
    if h : value = selected then h ▸ query
    else profiledOpenFixedRightInitialReachableQuery A initialCode value

/-- Left mirror. -/
noncomputable def profiledOpenFixedLeftQueryBankWithSelected
    (selected : ProfiledOpenFixedLeftPinnedValue A initialCode)
    (query : ProfiledOpenFixedLeftPinnedBlockQuery A initialCode selected) :
    ProfiledOpenFixedLeftPinnedBlockQueryBank A initialCode := by
  classical
  exact fun value =>
    if h : value = selected then h ▸ query
    else profiledOpenFixedLeftInitialReachableQuery A initialCode value

section
omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]

@[simp] theorem profiledOpenFixedRightQueryBankWithSelected_selected
    (selected : ProfiledOpenFixedRightPinnedValue A initialCode)
    (query : ProfiledOpenFixedRightPinnedBlockQuery A initialCode selected) :
    profiledOpenFixedRightQueryBankWithSelected A initialCode selected query
        selected = query := by
  classical
  simp [profiledOpenFixedRightQueryBankWithSelected]

@[simp] theorem profiledOpenFixedLeftQueryBankWithSelected_selected
    (selected : ProfiledOpenFixedLeftPinnedValue A initialCode)
    (query : ProfiledOpenFixedLeftPinnedBlockQuery A initialCode selected) :
    profiledOpenFixedLeftQueryBankWithSelected A initialCode selected query
        selected = query := by
  classical
  simp [profiledOpenFixedLeftQueryBankWithSelected]

/-- Exact fail-fast boundary for a carried right query: the completed finite
bank is reachable precisely when its one non-default coordinate is.  Thus no
literal word must be stored at runtime; a proof-only reachability invariant is
both necessary and sufficient. -/
theorem profiledOpenFixedRightQueryBankWithSelected_reachable_iff
    (selected : ProfiledOpenFixedRightPinnedValue A initialCode)
    (query : ProfiledOpenFixedRightPinnedBlockQuery A initialCode selected) :
    (∀ value,
        ProfiledOpenFixedRightQueryReachable A initialCode value
          (profiledOpenFixedRightQueryBankWithSelected A initialCode selected
            query value)) ↔
      ProfiledOpenFixedRightQueryReachable A initialCode selected query := by
  classical
  constructor
  · intro hall
    simpa using hall selected
  · intro hselected value
    by_cases h : value = selected
    · subst selected
      simpa using hselected
    · simp only [profiledOpenFixedRightQueryBankWithSelected, dif_neg h]
      exact profiledOpenFixedRightInitialReachableQuery_reachable A initialCode
        value

/-- Left exact boundary. -/
theorem profiledOpenFixedLeftQueryBankWithSelected_reachable_iff
    (selected : ProfiledOpenFixedLeftPinnedValue A initialCode)
    (query : ProfiledOpenFixedLeftPinnedBlockQuery A initialCode selected) :
    (∀ value,
        ProfiledOpenFixedLeftQueryReachable A initialCode value
          (profiledOpenFixedLeftQueryBankWithSelected A initialCode selected
            query value)) ↔
      ProfiledOpenFixedLeftQueryReachable A initialCode selected query := by
  classical
  constructor
  · intro hall
    simpa using hall selected
  · intro hselected value
    by_cases h : value = selected
    · subst selected
      simpa using hselected
    · simp only [profiledOpenFixedLeftQueryBankWithSelected, dif_neg h]
      exact profiledOpenFixedLeftInitialReachableQuery_reachable A initialCode
        value

end

/-- Lift one already-carried right query into the raw sidewise alphabet. -/
noncomputable def profiledOpenFixedSidewiseRightRawQueryOfSelected
    (selected : ProfiledOpenFixedRightPinnedValue A initialCode)
    (query : ProfiledOpenFixedRightPinnedBlockQuery A initialCode selected)
    (direction : ProfiledOpenIndexedFiniteDirectionTag A (I := I)) :
    ProfiledOpenFixedSidewisePointedQuery A initialCode :=
  ((.right,
      (profiledOpenFixedRightQueryBankWithSelected A initialCode selected query,
        profiledOpenFixedLeftInitialReachableQuery A initialCode)),
    direction)

/-- Left raw lift. -/
noncomputable def profiledOpenFixedSidewiseLeftRawQueryOfSelected
    (selected : ProfiledOpenFixedLeftPinnedValue A initialCode)
    (query : ProfiledOpenFixedLeftPinnedBlockQuery A initialCode selected)
    (direction : ProfiledOpenIndexedFiniteDirectionTag A (I := I)) :
    ProfiledOpenFixedSidewisePointedQuery A initialCode :=
  ((.left,
      (profiledOpenFixedRightInitialReachableQuery A initialCode,
        profiledOpenFixedLeftQueryBankWithSelected A initialCode selected
          query)),
    direction)

/-- A carried right query lifts to the reachable alphabet exactly from its
ordinary control-reachability invariant. -/
noncomputable def profiledOpenFixedSidewiseRightQueryOfSelected
    (selected : ProfiledOpenFixedRightPinnedValue A initialCode)
    (query : ProfiledOpenFixedRightPinnedBlockQuery A initialCode selected)
    (hreachable : ProfiledOpenFixedRightQueryReachable A initialCode selected
      query)
    (direction : ProfiledOpenIndexedFiniteDirectionTag A (I := I)) :
    ProfiledOpenFixedSidewiseReachablePointedQuery A initialCode := by
  refine ⟨profiledOpenFixedSidewiseRightRawQueryOfSelected A initialCode
      selected query direction, ?_⟩
  constructor
  · exact
      (profiledOpenFixedRightQueryBankWithSelected_reachable_iff A initialCode
        selected query).2 hreachable
  · intro value
    exact profiledOpenFixedLeftInitialReachableQuery_reachable A initialCode
      value

/-- Left carried-query lift. -/
noncomputable def profiledOpenFixedSidewiseLeftQueryOfSelected
    (selected : ProfiledOpenFixedLeftPinnedValue A initialCode)
    (query : ProfiledOpenFixedLeftPinnedBlockQuery A initialCode selected)
    (hreachable : ProfiledOpenFixedLeftQueryReachable A initialCode selected
      query)
    (direction : ProfiledOpenIndexedFiniteDirectionTag A (I := I)) :
    ProfiledOpenFixedSidewiseReachablePointedQuery A initialCode := by
  refine ⟨profiledOpenFixedSidewiseLeftRawQueryOfSelected A initialCode
      selected query direction, ?_⟩
  constructor
  · intro value
    exact profiledOpenFixedRightInitialReachableQuery_reachable A initialCode
      value
  · exact
      (profiledOpenFixedLeftQueryBankWithSelected_reachable_iff A initialCode
        selected query).2 hreachable

/-- Install one actual right coordinate and use the empty-word query at every
other fixed value.  The dependent equality branch merely transports the
selected literal query; it reveals no runtime class. -/
noncomputable def profiledOpenFixedRightQueryBankWithActual
    (selected : ProfiledOpenFixedRightPinnedValue A initialCode)
    (word : List In₁)
    (monitorState :
      (ProfiledOpenHiddenDescriptorRightPinnedUnionMonitor A selected.1
        selected.2.1).State) :
    ProfiledOpenFixedRightPinnedBlockQueryBank A initialCode := by
  classical
  exact fun value =>
    if h : value = selected then
      h ▸ profiledOpenFixedRightQueryAtWord A initialCode selected word
        monitorState
    else
      profiledOpenFixedRightInitialReachableQuery A initialCode value

/-- Left sparse bank. -/
noncomputable def profiledOpenFixedLeftQueryBankWithActual
    (selected : ProfiledOpenFixedLeftPinnedValue A initialCode)
    (word : List In₂)
    (monitorState :
      (ProfiledOpenHiddenDescriptorLeftPinnedUnionMonitor A selected.1
        selected.2.1).State) :
    ProfiledOpenFixedLeftPinnedBlockQueryBank A initialCode := by
  classical
  exact fun value =>
    if h : value = selected then
      h ▸ profiledOpenFixedLeftQueryAtWord A initialCode selected word
        monitorState
    else
      profiledOpenFixedLeftInitialReachableQuery A initialCode value

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
theorem profiledOpenFixedRightQueryBankWithActual_reachable
    (selected : ProfiledOpenFixedRightPinnedValue A initialCode)
    (word : List In₁)
    (monitorState :
      (ProfiledOpenHiddenDescriptorRightPinnedUnionMonitor A selected.1
        selected.2.1).State) :
    ∀ value,
      ProfiledOpenFixedRightQueryReachable A initialCode value
        (profiledOpenFixedRightQueryBankWithActual A initialCode selected word
          monitorState value) := by
  classical
  intro value
  by_cases h : value = selected
  · subst selected
    simpa [profiledOpenFixedRightQueryBankWithActual] using
      profiledOpenFixedRightQueryAtWord_reachable A initialCode value word
        monitorState
  · simp only [profiledOpenFixedRightQueryBankWithActual, dif_neg h]
    exact profiledOpenFixedRightInitialReachableQuery_reachable A initialCode
      value

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
theorem profiledOpenFixedLeftQueryBankWithActual_reachable
    (selected : ProfiledOpenFixedLeftPinnedValue A initialCode)
    (word : List In₂)
    (monitorState :
      (ProfiledOpenHiddenDescriptorLeftPinnedUnionMonitor A selected.1
        selected.2.1).State) :
    ∀ value,
      ProfiledOpenFixedLeftQueryReachable A initialCode value
        (profiledOpenFixedLeftQueryBankWithActual A initialCode selected word
          monitorState value) := by
  classical
  intro value
  by_cases h : value = selected
  · subst selected
    simpa [profiledOpenFixedLeftQueryBankWithActual] using
      profiledOpenFixedLeftQueryAtWord_reachable A initialCode value word
        monitorState
  · simp only [profiledOpenFixedLeftQueryBankWithActual, dif_neg h]
    exact profiledOpenFixedLeftInitialReachableQuery_reachable A initialCode
      value

/-! ## Full reachable queries used by an actual sidewise step -/

/-- Operational right-step query.  Only the selected right value is read at
the actual prefix.  Every left coordinate and every other right coordinate is
the canonical empty-word query.  `side` is fixed to the proof-side right row,
but it is not supplied to a process-local transition. -/
noncomputable def profiledOpenFixedSidewiseRightActualRawQueryAfter
    (selected : ProfiledOpenFixedRightPinnedValue A initialCode)
    (word : List In₁)
    (monitorState :
      (ProfiledOpenHiddenDescriptorRightPinnedUnionMonitor A selected.1
        selected.2.1).State)
    (direction : ProfiledOpenIndexedFiniteDirectionTag A (I := I)) :
    ProfiledOpenFixedSidewisePointedQuery A initialCode :=
  ((.right,
      (profiledOpenFixedRightQueryBankWithActual A initialCode selected word
          monitorState,
        profiledOpenFixedLeftInitialReachableQuery A initialCode)),
    direction)

/-- Operational left-step query. -/
noncomputable def profiledOpenFixedSidewiseLeftActualRawQueryAfter
    (selected : ProfiledOpenFixedLeftPinnedValue A initialCode)
    (word : List In₂)
    (monitorState :
      (ProfiledOpenHiddenDescriptorLeftPinnedUnionMonitor A selected.1
        selected.2.1).State)
    (direction : ProfiledOpenIndexedFiniteDirectionTag A (I := I)) :
    ProfiledOpenFixedSidewisePointedQuery A initialCode :=
  ((.left,
      (profiledOpenFixedRightInitialReachableQuery A initialCode,
        profiledOpenFixedLeftQueryBankWithActual A initialCode selected word
          monitorState)),
    direction)

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
theorem profiledOpenFixedSidewiseRightActualRawQueryAfter_reachable
    (selected : ProfiledOpenFixedRightPinnedValue A initialCode)
    (word : List In₁)
    (monitorState :
      (ProfiledOpenHiddenDescriptorRightPinnedUnionMonitor A selected.1
        selected.2.1).State)
    (direction : ProfiledOpenIndexedFiniteDirectionTag A (I := I)) :
    ProfiledOpenFixedSidewisePointedQueryReachable A initialCode
      (profiledOpenFixedSidewiseRightActualRawQueryAfter A initialCode selected
        word monitorState direction) := by
  constructor
  · exact profiledOpenFixedRightQueryBankWithActual_reachable A initialCode
      selected word monitorState
  · intro value
    exact profiledOpenFixedLeftInitialReachableQuery_reachable A initialCode
      value

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
theorem profiledOpenFixedSidewiseLeftActualRawQueryAfter_reachable
    (selected : ProfiledOpenFixedLeftPinnedValue A initialCode)
    (word : List In₂)
    (monitorState :
      (ProfiledOpenHiddenDescriptorLeftPinnedUnionMonitor A selected.1
        selected.2.1).State)
    (direction : ProfiledOpenIndexedFiniteDirectionTag A (I := I)) :
    ProfiledOpenFixedSidewisePointedQueryReachable A initialCode
      (profiledOpenFixedSidewiseLeftActualRawQueryAfter A initialCode selected
        word monitorState direction) := by
  constructor
  · intro value
    exact profiledOpenFixedRightInitialReachableQuery_reachable A initialCode
      value
  · exact profiledOpenFixedLeftQueryBankWithActual_reachable A initialCode
      selected word monitorState

/-- The right operational constructor already lands in the honest finite
query alphabet consumed by the re-anchored successor. -/
noncomputable def profiledOpenFixedSidewiseRightActualQueryAfter
    (selected : ProfiledOpenFixedRightPinnedValue A initialCode)
    (word : List In₁)
    (monitorState :
      (ProfiledOpenHiddenDescriptorRightPinnedUnionMonitor A selected.1
        selected.2.1).State)
    (direction : ProfiledOpenIndexedFiniteDirectionTag A (I := I)) :
    ProfiledOpenFixedSidewiseReachablePointedQuery A initialCode :=
  ⟨profiledOpenFixedSidewiseRightActualRawQueryAfter A initialCode selected
      word monitorState direction,
    profiledOpenFixedSidewiseRightActualRawQueryAfter_reachable A initialCode
      selected word monitorState direction⟩

/-- Left operational constructor. -/
noncomputable def profiledOpenFixedSidewiseLeftActualQueryAfter
    (selected : ProfiledOpenFixedLeftPinnedValue A initialCode)
    (word : List In₂)
    (monitorState :
      (ProfiledOpenHiddenDescriptorLeftPinnedUnionMonitor A selected.1
        selected.2.1).State)
    (direction : ProfiledOpenIndexedFiniteDirectionTag A (I := I)) :
    ProfiledOpenFixedSidewiseReachablePointedQuery A initialCode :=
  ⟨profiledOpenFixedSidewiseLeftActualRawQueryAfter A initialCode selected
      word monitorState direction,
    profiledOpenFixedSidewiseLeftActualRawQueryAfter_reachable A initialCode
      selected word monitorState direction⟩

end

end DetParityAutomaton

end DistributedSynthesis
