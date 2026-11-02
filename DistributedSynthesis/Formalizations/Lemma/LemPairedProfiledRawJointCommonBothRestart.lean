/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointSemanticChild
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointCommonBaseWorld
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointIncidence

/-!
# Re-rooting the raw joint family after one simultaneous round

The two independently rationalized exceptional controllers cannot be joined
after extraction.  Before extraction, however, the two pending orientations
are the two projections of one literal common-base world.  This file records
the exact delay-one fact needed by a joint initial narrowing:

* the common world gives one two-sided raw semantic family;
* the direction with empty strict pasts and two `.both` rows is an exact
  fibre; and
* its two pivots name the literal same generated history.

Thus a simultaneous round can be rationalized once and then re-rooted at one
common semantic child.  No process is given the current graph, an orientation,
or the identity of a strict leader.
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

/-! ## The two projections before rationalization -/

/-- Both one-sided projections of one literal generated world, retained in a
single raw family before any rational policy is selected. -/
def profiledRawJointCommonWorldFamily
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (world : ProfiledRawJointCommonBaseWorld A strategy) :
    ProfiledRawJointSemanticFamily A strategy (I := Unit) where
  right := fun _ => some (world.procOneMember A)
  left := fun _ => some (world.procTwoMember A)
  right_view_shared := by
    intro _ _ leftMember rightMember hleft hright
    have hleft' : world.procOneMember A = leftMember :=
      Option.some.inj hleft
    have hright' : world.procOneMember A = rightMember :=
      Option.some.inj hright
    subst leftMember
    subst rightMember
    rfl
  left_view_shared := by
    intro _ _ leftMember rightMember hleft hright
    have hleft' : world.procTwoMember A = leftMember :=
      Option.some.inj hleft
    have hright' : world.procTwoMember A = rightMember :=
      Option.some.inj hright
    subst leftMember
    subst rightMember
    rfl

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁]
    [Fintype In₂] [Fintype Out₁] [Fintype Out₂] in
@[simp] theorem profiledRawJointCommonWorldFamily_right
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (world : ProfiledRawJointCommonBaseWorld A strategy) :
    (profiledRawJointCommonWorldFamily A world).right () =
      some (world.procOneMember A) :=
  rfl

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁]
    [Fintype In₂] [Fintype Out₁] [Fintype Out₂] in
@[simp] theorem profiledRawJointCommonWorldFamily_left
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (world : ProfiledRawJointCommonBaseWorld A strategy) :
    (profiledRawJointCommonWorldFamily A world).left () =
      some (world.procTwoMember A) :=
  rfl

/-! ## The fresh one-bit direction -/

/-- The source-free direction representing a single current simultaneous
round.  Both strict-block pasts are empty and both latent rows are `.both`.
The input order is swapped only on the right-oriented block, as required by
the existing raw direction type. -/
def profiledRawJointBothRestartDirection
    (move : In₁ × In₂) :
    ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂) where
  rightPivot := ((), .both)
  rightTaggedPast := []
  rightInput := (move.2, move.1)
  leftPivot := ((), .both)
  leftTaggedPast := []
  leftInput := move

omit [Inhabited In₁] [Inhabited In₂] [Fintype In₁] [Fintype In₂] in
@[simp] theorem profiledRawJointBothRestartDirection_rightPhysicalPast
    (move : In₁ × In₂) :
    (profiledRawJointBothRestartDirection move).rightPhysicalPast = [] :=
  rfl

omit [Inhabited In₁] [Inhabited In₂] [Fintype In₁] [Fintype In₂] in
@[simp] theorem profiledRawJointBothRestartDirection_leftPhysicalPast
    (move : In₁ × In₂) :
    (profiledRawJointBothRestartDirection move).leftPhysicalPast = [] :=
  rfl

/-! ## Exact common-source restart -/

section
omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁]
    [Fintype In₂] [Fintype Out₁] [Fintype Out₂]

/-- The two pending projections form an exact fibre at the fresh simultaneous
direction.  This is the delay-one restart fact: the only retained row on each
side is the common `both` history of the same world. -/
theorem profiledRawJointCommonWorldFamily_exactFibreAt_bothRestart
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (world : ProfiledRawJointCommonBaseWorld A strategy)
    (move : In₁ × In₂) :
    (profiledRawJointCommonWorldFamily A world).ExactFibreAt A
      (profiledRawJointBothRestartDirection move) := by
  constructor
  · intro _ rightMember leftMember hright hleft
    have hright' : world.procOneMember A = rightMember :=
      Option.some.inj hright
    have hleft' : world.procTwoMember A = leftMember :=
      Option.some.inj hleft
    subst rightMember
    subst leftMember
    change
      currentView Proc.one (world.procOne A).leftHistory =
        currentView Proc.one (world.procTwo A).bothHistory
    calc
      currentView Proc.one (world.procOne A).leftHistory =
          currentView Proc.one (world.procOne A).bothHistory :=
        (world.procOne A).view_eq
      _ = currentView Proc.one (world.procTwo A).bothHistory := by
        rw [world.procOne_bothHistory_eq_procTwo A]
  · intro _ leftMember rightMember hleft hright
    have hleft' : world.procTwoMember A = leftMember :=
      Option.some.inj hleft
    have hright' : world.procOneMember A = rightMember :=
      Option.some.inj hright
    subst leftMember
    subst rightMember
    change
      currentView Proc.two (world.procTwo A).rightHistory =
        currentView Proc.two (world.procOne A).bothHistory
    calc
      currentView Proc.two (world.procTwo A).rightHistory =
          currentView Proc.two (world.procTwo A).bothHistory :=
        (world.procTwo A).view_eq
      _ = currentView Proc.two (world.procOne A).bothHistory := by
        rw [world.procOne_bothHistory_eq_procTwo A]

/-- The empty-past restart above is only one convenient direction.  At a
common world, exactness in fact depends solely on both pivots naming the
shared `.both` row; the tagged strict scans and closing inputs may be
arbitrary.  This is the form needed when a proof-side physical direction
records the first strict exit.  The pivot equations are semantic witnesses,
not observations available to either process. -/
theorem profiledRawJointCommonWorldFamily_exactFibreAt_of_bothPivots
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (world : ProfiledRawJointCommonBaseWorld A strategy)
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂))
    (hrightPivot : direction.rightPivot.2 = .both)
    (hleftPivot : direction.leftPivot.2 = .both) :
    (profiledRawJointCommonWorldFamily A world).ExactFibreAt A direction := by
  constructor
  · intro _ rightMember leftPivotMember hright hleft
    have hright' : world.procOneMember A = rightMember :=
      Option.some.inj hright
    have hleft' : world.procTwoMember A = leftPivotMember :=
      Option.some.inj hleft
    subst rightMember
    subst leftPivotMember
    rw [hleftPivot]
    change
      currentView Proc.one (world.procOne A).leftHistory =
        currentView Proc.one (world.procTwo A).bothHistory
    calc
      currentView Proc.one (world.procOne A).leftHistory =
          currentView Proc.one (world.procOne A).bothHistory :=
        (world.procOne A).view_eq
      _ = currentView Proc.one (world.procTwo A).bothHistory := by
        rw [world.procOne_bothHistory_eq_procTwo A]
  · intro _ leftMember rightPivotMember hleft hright
    have hleft' : world.procTwoMember A = leftMember :=
      Option.some.inj hleft
    have hright' : world.procOneMember A = rightPivotMember :=
      Option.some.inj hright
    subst leftMember
    subst rightPivotMember
    rw [hrightPivot]
    change
      currentView Proc.two (world.procTwo A).rightHistory =
        currentView Proc.two (world.procOne A).bothHistory
    calc
      currentView Proc.two (world.procTwo A).rightHistory =
          currentView Proc.two (world.procTwo A).bothHistory :=
        (world.procTwo A).view_eq
      _ = currentView Proc.two (world.procOne A).bothHistory := by
        rw [world.procOne_bothHistory_eq_procTwo A]

/-- Consequently the existing common-source construction produces one
literal generated source for the simultaneous restart. -/
theorem nonempty_profiledRawJointCommonWorldBothRestartSource
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (world : ProfiledRawJointCommonBaseWorld A strategy)
    (move : In₁ × In₂) :
    Nonempty
      (ProfiledRawJointCommonSourceAt A
        (profiledRawJointCommonWorldFamily A world)
        (profiledRawJointBothRestartDirection move)) :=
  (profiledRawJointCommonWorldFamily A world).exists_commonSourceAt A
    (profiledRawJointBothRestartDirection move)
    (profiledRawJointCommonWorldFamily_exactFibreAt_bothRestart A world move)

/-- Common-source package for any proof-side direction whose pivots both name
the shared row.  This is the strict-exit adapter used by the hybrid tree. -/
theorem nonempty_profiledRawJointCommonWorldSource_of_bothPivots
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (world : ProfiledRawJointCommonBaseWorld A strategy)
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂))
    (hrightPivot : direction.rightPivot.2 = .both)
    (hleftPivot : direction.leftPivot.2 = .both) :
    Nonempty
      (ProfiledRawJointCommonSourceAt A
        (profiledRawJointCommonWorldFamily A world) direction) :=
  (profiledRawJointCommonWorldFamily A world).exists_commonSourceAt A direction
    (profiledRawJointCommonWorldFamily_exactFibreAt_of_bothPivots A world
      direction hrightPivot hleftPivot)

/-- The two pivot rows of the restart are definitionally the same concrete
generated history. -/
theorem profiledRawJointCommonWorld_bothPivotHistories_eq
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (world : ProfiledRawJointCommonBaseWorld A strategy) :
    profiledRawProcOneRowHistory (world.procOne A) .both =
      profiledRawProcTwoRowHistory (world.procTwo A) .both := by
  exact world.procOne_bothHistory_eq_procTwo A

end

/-! ## Literal re-rooting after the simultaneous round -/

/-- The next common world after a simultaneous round.  We define it through
the process-one projection; the mirror construction through process two is
definitionally equal because both projections contain the same literal
`.both` history and the same automaton state. -/
def profiledRawJointCommonWorldAfterBoth
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (world : ProfiledRawJointCommonBaseWorld A strategy)
    (move : In₁ × In₂) :
    ProfiledRawJointCommonBaseWorld A strategy :=
  profiledRawRightCommonBaseWorld A (world.procOneMember A) .both []
    (move.2, move.1)

section
omit [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁] [Fintype In₂] [Fintype Out₁]
    [Fintype Out₂]

/-- The left and right descriptions of the post-`.both` world coincide
before any rational representative is chosen. -/
theorem profiledRawJointCommonWorldAfterBoth_eq_left
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (world : ProfiledRawJointCommonBaseWorld A strategy)
    (move : In₁ × In₂) :
    profiledRawJointCommonWorldAfterBoth A world move =
      profiledRawLeftCommonBaseWorld A (world.procTwoMember A) .both [] move := by
  rfl

/-- The selected right-family child is exactly the process-one projection of
the new common world. -/
theorem profiledRawJointCommonWorld_semanticChild_right_bothRestart
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (world : ProfiledRawJointCommonBaseWorld A strategy)
    (move : In₁ × In₂) :
    ((profiledRawJointCommonWorldFamily A world).semanticChild A
        (profiledRawJointBothRestartDirection move)).right () =
      some ((profiledRawJointCommonWorldAfterBoth A world move).procOneMember A) := by
  classical
  let family := profiledRawJointCommonWorldFamily A world
  let direction := profiledRawJointBothRestartDirection move
  have hpattern :
      family.leftPattern A ((), .both) direction.leftPivot = true := by
    change decide
      (currentView Proc.one (world.procTwo A).bothHistory =
        currentView Proc.one (world.procTwo A).bothHistory) = true
    simp
  have hselected := family.leftSelectedChild_eq_some_of_pattern A direction ()
    (world.procTwoMember A) (by rfl) .both hpattern
  rw [ProfiledRawJointSemanticFamily.semanticChild_right]
  rw [hselected]
  congr 1

/-- Process-two mirror of the literal post-`.both` re-rooting. -/
theorem profiledRawJointCommonWorld_semanticChild_left_bothRestart
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (world : ProfiledRawJointCommonBaseWorld A strategy)
    (move : In₁ × In₂) :
    ((profiledRawJointCommonWorldFamily A world).semanticChild A
        (profiledRawJointBothRestartDirection move)).left () =
      some ((profiledRawJointCommonWorldAfterBoth A world move).procTwoMember A) := by
  classical
  let family := profiledRawJointCommonWorldFamily A world
  let direction := profiledRawJointBothRestartDirection move
  have hpattern :
      family.rightPattern A ((), .both) direction.rightPivot = true := by
    change decide
      (currentView Proc.two (world.procOne A).bothHistory =
        currentView Proc.two (world.procOne A).bothHistory) = true
    simp
  have hselected := family.rightSelectedChild_eq_some_of_pattern A direction ()
    (world.procOneMember A) (by rfl) .both hpattern
  rw [ProfiledRawJointSemanticFamily.semanticChild_left]
  rw [hselected]
  congr 1

end

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁]
    [Fintype In₂] [Fintype Out₁] [Fintype Out₂] in
/-- Semantic-family equality is determined by its two optional member
families; the shared-view fields are propositions. -/
theorem ProfiledRawJointSemanticFamily.eq_of_right_left
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (left right : ProfiledRawJointSemanticFamily A strategy (I := Unit))
    (hright : left.right = right.right)
    (hleft : left.left = right.left) :
    left = right := by
  cases left
  cases right
  simp_all

section
omit [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁] [Fintype In₂] [Fintype Out₁]
    [Fintype Out₂]

/-- A simultaneous step preserves the literal common-world form.  Hence any
finite or infinite prefix consisting only of `.both` rounds can be re-rooted
without merging independently selected policies. -/
theorem profiledRawJointCommonWorld_semanticChild_eq_bothRestart
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (world : ProfiledRawJointCommonBaseWorld A strategy)
    (move : In₁ × In₂) :
    (profiledRawJointCommonWorldFamily A world).semanticChild A
        (profiledRawJointBothRestartDirection move) =
      profiledRawJointCommonWorldFamily A
        (profiledRawJointCommonWorldAfterBoth A world move) := by
  apply ProfiledRawJointSemanticFamily.eq_of_right_left A
  · funext index
    cases index
    exact profiledRawJointCommonWorld_semanticChild_right_bothRestart A world
      move
  · funext index
    cases index
    exact profiledRawJointCommonWorld_semanticChild_left_bothRestart A world
      move

/-- The exact cross-incidence coordinate also survives the simultaneous
restart.  This is the finite T1 equation consumed by a hybrid common/strict
semantic tree; retaining only the two marginal family codes would lose the
shared-source information again. -/
theorem profiledRawJointCommonWorld_semanticChild_incidenceCode_eq_bothRestart
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (world : ProfiledRawJointCommonBaseWorld A strategy)
    (move : In₁ × In₂) :
    let family := profiledRawJointCommonWorldFamily A world
    let direction := profiledRawJointBothRestartDirection move
    (family.semanticChild A direction).incidenceCode A =
      profiledRawJointIncidenceNext A (family.code A) (family.move A)
        direction := by
  dsimp only
  let common := Classical.choice
    (nonempty_profiledRawJointCommonWorldBothRestartSource A world move)
  exact (profiledRawJointCommonWorldFamily A world
    ).semanticChild_incidenceCode_eq_of_commonSource A
      (profiledRawJointBothRestartDirection move) common

/-- Equivalent re-rooted form of the incidence T1 law. -/
theorem profiledRawJointCommonWorldAfterBoth_incidenceCode
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (world : ProfiledRawJointCommonBaseWorld A strategy)
    (move : In₁ × In₂) :
    (profiledRawJointCommonWorldFamily A
        (profiledRawJointCommonWorldAfterBoth A world move)).incidenceCode A =
      profiledRawJointIncidenceNext A
        ((profiledRawJointCommonWorldFamily A world).code A)
        ((profiledRawJointCommonWorldFamily A world).move A)
        (profiledRawJointBothRestartDirection move) := by
  rw [← profiledRawJointCommonWorld_semanticChild_eq_bothRestart A world
    move]
  exact
    profiledRawJointCommonWorld_semanticChild_incidenceCode_eq_bothRestart A
      world move

/-- The complete finite code of the jointly constructed simultaneous child
is the source-free successor of the one common raw move. -/
theorem profiledRawJointCommonWorld_semanticChild_code_eq_bothRestart
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (world : ProfiledRawJointCommonBaseWorld A strategy)
    (move : In₁ × In₂) :
    let family := profiledRawJointCommonWorldFamily A world
    let direction := profiledRawJointBothRestartDirection move
    (family.semanticChild A direction).code A =
      profiledRawJointFamilyNext A (family.code A) (family.move A)
        direction := by
  dsimp only
  let common := Classical.choice
    (nonempty_profiledRawJointCommonWorldBothRestartSource A world move)
  exact (profiledRawJointCommonWorldFamily A world).semanticChild_code_eq_of_commonSource
    A (profiledRawJointBothRestartDirection move) common

end

end

end DetParityAutomaton

end DistributedSynthesis
