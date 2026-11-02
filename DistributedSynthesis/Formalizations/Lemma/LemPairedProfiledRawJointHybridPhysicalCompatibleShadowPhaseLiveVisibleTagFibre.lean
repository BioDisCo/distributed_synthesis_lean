/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemFiniteDependentHeterogeneousPinnedPreselection
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleShadowPhaseLiveHandoff

/-!
# Visible fibres of delayed strict tags

A delayed strict tag contains the common origin and both fresh inputs, but the
non-receiving endpoint cannot use the partner input when the tag is created.
The correct simultaneous-preselection index is therefore not the whole tag.
It is one *visible anchor* together with a finite hidden-input fibre:

* at a strict-right creation, process one sees `(origin, inputOne)` and the
  hidden key is `inputTwo`;
* at a strict-left creation, process two sees `(origin, inputTwo)` and the
  hidden key is `inputOne`.

This file makes those two decompositions literal.  It also proves the semantic
fact needed to put all members of either fibre under one sender controller:
changing only the hidden partner input in a non-receiving round leaves the
blind endpoint's complete subsequent block sender unchanged.  The proof is
the local-view equation followed by `blockSenderOne_eq_of_view_eq` (and its
mirror); no process is told a graph, hierarchy side, leader bit, tag, hidden
input, history, or semantic view.
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

private abbrev CommonControl :=
  ProfiledRawJointHybridCommonControl A strategy hwin

private abbrev Tag :=
  ProfiledRawJointHybridShadowPhaseLiveTag A strategy hwin

/-! ## Exact visible-anchor / hidden-key decompositions -/

/-- Everything available to process one when a strict-right tag is created.
The partner's `In₂` value is deliberately absent. -/
structure ProfiledRawJointHybridShadowPhaseLiveRightVisibleAnchor where
  origin : CommonControl A strategy hwin
  inputOne : In₁
deriving Fintype

/-- Everything available to process two at the strict-left mirror. -/
structure ProfiledRawJointHybridShadowPhaseLiveLeftVisibleAnchor where
  origin : CommonControl A strategy hwin
  inputTwo : In₂
deriving Fintype

/-- Reconstruct the complete strict-right proof tag from its visible anchor
and the finite hidden-input key. -/
def ProfiledRawJointHybridShadowPhaseLiveRightVisibleAnchor.tag
    (anchor :
      ProfiledRawJointHybridShadowPhaseLiveRightVisibleAnchor A strategy hwin)
    (hidden : In₂) : Tag A strategy hwin :=
  profiledRawJointHybridShadowPhaseLiveRightTag A strategy hwin anchor.origin
    (anchor.inputOne, hidden)

/-- Strict-left reconstruction. -/
def ProfiledRawJointHybridShadowPhaseLiveLeftVisibleAnchor.tag
    (anchor :
      ProfiledRawJointHybridShadowPhaseLiveLeftVisibleAnchor A strategy hwin)
    (hidden : In₁) : Tag A strategy hwin :=
  profiledRawJointHybridShadowPhaseLiveLeftTag A strategy hwin anchor.origin
    (hidden, anchor.inputTwo)

section
omit [DecidableEq In₁] [DecidableEq In₂]

section
omit [Inhabited Out₁] [Inhabited Out₂]

@[simp] theorem
    ProfiledRawJointHybridShadowPhaseLiveRightVisibleAnchor.tag_origin
    (anchor :
      ProfiledRawJointHybridShadowPhaseLiveRightVisibleAnchor A strategy hwin)
    (hidden : In₂) :
    (anchor.tag A strategy hwin hidden).origin = anchor.origin :=
  rfl

@[simp] theorem
    ProfiledRawJointHybridShadowPhaseLiveRightVisibleAnchor.tag_input
    (anchor :
      ProfiledRawJointHybridShadowPhaseLiveRightVisibleAnchor A strategy hwin)
    (hidden : In₂) :
    (anchor.tag A strategy hwin hidden).input = (anchor.inputOne, hidden) :=
  rfl

@[simp] theorem
    ProfiledRawJointHybridShadowPhaseLiveRightVisibleAnchor.tag_side
    (anchor :
      ProfiledRawJointHybridShadowPhaseLiveRightVisibleAnchor A strategy hwin)
    (hidden : In₂) :
    (anchor.tag A strategy hwin hidden).side =
      ProfiledRawJointHybridShadowStrictSide.right :=
  rfl

@[simp] theorem
    ProfiledRawJointHybridShadowPhaseLiveLeftVisibleAnchor.tag_origin
    (anchor :
      ProfiledRawJointHybridShadowPhaseLiveLeftVisibleAnchor A strategy hwin)
    (hidden : In₁) :
    (anchor.tag A strategy hwin hidden).origin = anchor.origin :=
  rfl

@[simp] theorem
    ProfiledRawJointHybridShadowPhaseLiveLeftVisibleAnchor.tag_input
    (anchor :
      ProfiledRawJointHybridShadowPhaseLiveLeftVisibleAnchor A strategy hwin)
    (hidden : In₁) :
    (anchor.tag A strategy hwin hidden).input = (hidden, anchor.inputTwo) :=
  rfl

@[simp] theorem
    ProfiledRawJointHybridShadowPhaseLiveLeftVisibleAnchor.tag_side
    (anchor :
      ProfiledRawJointHybridShadowPhaseLiveLeftVisibleAnchor A strategy hwin)
    (hidden : In₁) :
    (anchor.tag A strategy hwin hidden).side =
      ProfiledRawJointHybridShadowStrictSide.left :=
  rfl

end

end

/-! ## Generic hidden-input invariance of a blind strict round -/

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁]
    [Fintype In₂] [Fintype Out₁] [Fintype Out₂] [DecidableEq In₁] [DecidableEq In₂] in
/-- At a right round, process one's next view contains its own input but not
the process-two input. -/
theorem strictRight_currentView_one_eq_of_same_visible
    (base : History In₁ In₂ Graph Out₁ Out₂)
    (inputOne : In₁) (hidden hidden' : In₂) :
    currentView Proc.one
        (History.append base
          (nextRound strategy base ⟨inputOne, hidden, Graph.right⟩)) =
      currentView Proc.one
        (History.append base
          (nextRound strategy base ⟨inputOne, hidden', Graph.right⟩)) := by
  simp [currentView_one_append, nextRound]

omit [Inhabited In₁] [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁] [Fintype In₂]
    [Fintype Out₁] [Fintype Out₂] [DecidableEq In₁] [DecidableEq In₂] in
/-- Consequently all strict-right candidates in one visible fibre use the
same complete process-one sender strategy, not merely the same first output. -/
theorem blockSenderOne_strictRight_eq_of_same_visible
    (base : History In₁ In₂ Graph Out₁ Out₂)
    (inputOne : In₁) (hidden hidden' : In₂) :
    blockSenderOne strategy
        (History.append base
          (nextRound strategy base ⟨inputOne, hidden, Graph.right⟩)) =
      blockSenderOne strategy
        (History.append base
          (nextRound strategy base ⟨inputOne, hidden', Graph.right⟩)) :=
  blockSenderOne_eq_of_view_eq strategy
    (strictRight_currentView_one_eq_of_same_visible strategy base inputOne
      hidden hidden')

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁]
    [Fintype In₂] [Fintype Out₁] [Fintype Out₂] [DecidableEq In₁] [DecidableEq In₂] in
/-- Mirror: at a left round process two cannot see process one's input. -/
theorem strictLeft_currentView_two_eq_of_same_visible
    (base : History In₁ In₂ Graph Out₁ Out₂)
    (hidden hidden' : In₁) (inputTwo : In₂) :
    currentView Proc.two
        (History.append base
          (nextRound strategy base ⟨hidden, inputTwo, Graph.left⟩)) =
      currentView Proc.two
        (History.append base
          (nextRound strategy base ⟨hidden', inputTwo, Graph.left⟩)) := by
  simp [currentView_two_append, nextRound]

omit [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁] [Fintype In₂]
    [Fintype Out₁] [Fintype Out₂] [DecidableEq In₁] [DecidableEq In₂] in
/-- Complete process-two sender equality throughout one strict-left fibre. -/
theorem blockSenderTwo_strictLeft_eq_of_same_visible
    (base : History In₁ In₂ Graph Out₁ Out₂)
    (hidden hidden' : In₁) (inputTwo : In₂) :
    blockSenderTwo strategy
        (History.append base
          (nextRound strategy base ⟨hidden, inputTwo, Graph.left⟩)) =
      blockSenderTwo strategy
        (History.append base
          (nextRound strategy base ⟨hidden', inputTwo, Graph.left⟩)) :=
  blockSenderTwo_eq_of_view_eq strategy
    (strictLeft_currentView_two_eq_of_same_visible strategy base hidden hidden'
      inputTwo)

/-! ## The semantic sender attached to a concrete tag fibre -/

/-- The literal strict-right history named by one visible anchor and hidden
key, rooted at the common world's shared `.both` history. -/
noncomputable def
    ProfiledRawJointHybridShadowPhaseLiveRightVisibleAnchor.history
    (anchor :
      ProfiledRawJointHybridShadowPhaseLiveRightVisibleAnchor A strategy hwin)
    (hidden : In₂) : History In₁ In₂ Graph Out₁ Out₂ :=
  let installed :=
    profiledRawJointHybridShadowPhaseLiveInstalled A strategy hwin anchor.origin
  let base := (installed.world.procOne A).bothHistory
  History.append base
    (nextRound strategy base ⟨anchor.inputOne, hidden, Graph.right⟩)

/-- Strict-left mirror, using the definitionally identical common `.both`
history from the process-two projection. -/
noncomputable def
    ProfiledRawJointHybridShadowPhaseLiveLeftVisibleAnchor.history
    (anchor :
      ProfiledRawJointHybridShadowPhaseLiveLeftVisibleAnchor A strategy hwin)
    (hidden : In₁) : History In₁ In₂ Graph Out₁ Out₂ :=
  let installed :=
    profiledRawJointHybridShadowPhaseLiveInstalled A strategy hwin anchor.origin
  let base := (installed.world.procTwo A).bothHistory
  History.append base
    (nextRound strategy base ⟨hidden, anchor.inputTwo, Graph.left⟩)

omit [Inhabited Out₁] [Inhabited Out₂] [DecidableEq In₁] [DecidableEq In₂] in
/-- Tag-fibre specialization of the generic sender equality.  This is the
common-sender premise used when building one pinned heterogeneous table over
`Key := In₂`. -/
theorem
    ProfiledRawJointHybridShadowPhaseLiveRightVisibleAnchor.blockSender_eq
    (anchor :
      ProfiledRawJointHybridShadowPhaseLiveRightVisibleAnchor A strategy hwin)
    (hidden hidden' : In₂) :
    blockSenderOne strategy (anchor.history A strategy hwin hidden) =
      blockSenderOne strategy (anchor.history A strategy hwin hidden') := by
  unfold ProfiledRawJointHybridShadowPhaseLiveRightVisibleAnchor.history
  apply blockSenderOne_strictRight_eq_of_same_visible

omit [Inhabited Out₁] [Inhabited Out₂] [DecidableEq In₁] [DecidableEq In₂] in
/-- Left-fibre specialization, for `Key := In₁`. -/
theorem
    ProfiledRawJointHybridShadowPhaseLiveLeftVisibleAnchor.blockSender_eq
    (anchor :
      ProfiledRawJointHybridShadowPhaseLiveLeftVisibleAnchor A strategy hwin)
    (hidden hidden' : In₁) :
    blockSenderTwo strategy (anchor.history A strategy hwin hidden) =
      blockSenderTwo strategy (anchor.history A strategy hwin hidden') := by
  unfold ProfiledRawJointHybridShadowPhaseLiveLeftVisibleAnchor.history
  apply blockSenderTwo_strictLeft_eq_of_same_visible

/-! ## Which tail lane is rooted at the actual strict history

The post-tag physical annotation is built from the common semantic child.
Only its live, informed-side lane is rooted at the actual strict history.
This typing fact prevents a tempting but invalid use of the fibre equality
above: the opposite hypothetical lane starts at a receiving history and its
sender need not be constant over the hidden-input fibre.
-/

/-- The common semantic child named by a strict-right fibre member. -/
noncomputable def
    ProfiledRawJointHybridShadowPhaseLiveRightVisibleAnchor.childWorld
    (anchor :
      ProfiledRawJointHybridShadowPhaseLiveRightVisibleAnchor A strategy hwin)
    (hidden : In₂) : ProfiledRawJointCommonBaseWorld A strategy :=
  let installed :=
    profiledRawJointHybridShadowPhaseLiveInstalled A strategy hwin anchor.origin
  profiledRawJointCommonWorldAfterBoth A installed.world
    (anchor.inputOne, hidden)

/-- Strict-left mirror. -/
noncomputable def
    ProfiledRawJointHybridShadowPhaseLiveLeftVisibleAnchor.childWorld
    (anchor :
      ProfiledRawJointHybridShadowPhaseLiveLeftVisibleAnchor A strategy hwin)
    (hidden : In₁) : ProfiledRawJointCommonBaseWorld A strategy :=
  let installed :=
    profiledRawJointHybridShadowPhaseLiveInstalled A strategy hwin anchor.origin
  profiledRawJointCommonWorldAfterBoth A installed.world
    (hidden, anchor.inputTwo)

omit [DecidableEq In₁] [DecidableEq In₂] [Inhabited Out₁] [Inhabited Out₂] in
/-- After a strict-right creation the live left-lane sender is literally
process two's sender at the actual strict-right history.  Process two is the
receiver of that round and may therefore depend on the alleged hidden key. -/
theorem
    ProfiledRawJointHybridShadowPhaseLiveRightVisibleAnchor.liveLeftSender_eq
    (anchor :
      ProfiledRawJointHybridShadowPhaseLiveRightVisibleAnchor A strategy hwin)
    (hidden : In₂) :
    profiledRawJointLeftSiblingSender A
        ((anchor.childWorld A strategy hwin hidden).procTwoMember A) =
      blockSenderTwo strategy (anchor.history A strategy hwin hidden) := by
  rfl

omit [DecidableEq In₁] [DecidableEq In₂] [Inhabited Out₁] [Inhabited Out₂] in
/-- At a strict-left creation the live right-lane sender is process one's
sender at the actual strict-left history. -/
theorem
    ProfiledRawJointHybridShadowPhaseLiveLeftVisibleAnchor.liveRightSender_eq
    (anchor :
      ProfiledRawJointHybridShadowPhaseLiveLeftVisibleAnchor A strategy hwin)
    (hidden : In₁) :
    profiledRawJointRightSiblingSender A
        ((anchor.childWorld A strategy hwin hidden).procOneMember A) =
      blockSenderOne strategy (anchor.history A strategy hwin hidden) := by
  rfl

end

end DetParityAutomaton

end DistributedSynthesis
