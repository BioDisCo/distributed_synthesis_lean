/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledOpenIndexedRawSemantic

/-!
# Reifying normalized literal survivors as semantic lanes

This is the model-independent half of a correlated handoff.  Given literal
semantic entries/minima indexed by the normalized survivors of a child code,
with the expected finite roots and one common receiver view, it constructs
the corresponding semantic lane.  Its slots are exactly the normalized
public root slots, and injectivity of survivor roots forces the canonical
realization to retain each literal entry and minimum.
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

variable (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
variable (hwin : ∀ env : EnvironmentSequence In₁ In₂,
  A.Accepts (execution strategy env))
variable (basis : ∀ state : PairedProfiledTreeState A,
  (pairedProfiledEntryRunAutomaton A state).RationalRunBasis)

/-- A left semantic lane built from the literal survivors, together with the
two equations that exclude representative splicing. -/
structure ProfiledOpenIndexedLeftSurvivorLanePackage
    (raw : IndexedLineageChildCode I (ProfiledOpenClassifiedAnchor A))
    (entry : raw.RootSurvivor → ProcTwoPairedEntryRep strategy)
    (minimum : raw.RootSurvivor → A.State) where
  lane : ProfiledOpenIndexedLeftSemanticLane A strategy hwin basis (I := I)
  slots_eq :
    ProfiledOpenIndexedLeftSemanticShadow.slots A strategy hwin basis
        (some lane) = raw.deduplicateRoots.rootSlots
  literal : ∀ survivor : raw.RootSurvivor,
    ∃ member : {root // root ∈ lane.source.1},
      lane.memberAt survivor.lineage = some member ∧
        lane.realization.entry member = entry survivor ∧
        lane.realization.minimum member = minimum survivor

/-- Reify a nonempty normalized survivor family as a left semantic lane.
The classified-root equation is what connects the source-free public code
to the unclassified semantic root family. -/
noncomputable def profiledOpenIndexedLeftSurvivorLanePackage
    (raw : IndexedLineageChildCode I (ProfiledOpenClassifiedAnchor A))
    (hsurvivor : Nonempty raw.RootSurvivor)
    (entry : raw.RootSurvivor → ProcTwoPairedEntryRep strategy)
    (minimum : raw.RootSurvivor → A.State)
    (semanticRoot : raw.RootSurvivor → ProfiledOpenLeftRoot A)
    (hclassified : ∀ survivor : raw.RootSurvivor,
      IndexedLineageChildCode.RootSurvivor.root survivor =
        ProfiledOpenClassifiedAnchor.left (semanticRoot survivor))
    (hroot : ∀ survivor,
      profiledOpenLeftRootOfWinning A strategy hwin (entry survivor)
        (minimum survivor) basis = semanticRoot survivor)
    (pivot : raw.RootSurvivor)
    (hview : ∀ survivor,
      currentView Proc.two (entry survivor).rightHistory =
        currentView Proc.two (entry pivot).rightHistory) :
    ProfiledOpenIndexedLeftSurvivorLanePackage A strategy hwin basis raw
      entry minimum := by
  classical
  letI : Inhabited raw.RootSurvivor := ⟨Classical.choice hsurvivor⟩
  have hrootInjective : Function.Injective semanticRoot := by
    intro left right heq
    apply IndexedLineageChildCode.RootSurvivor.root_injective
    rw [hclassified left, hclassified right, heq]
  let source := profiledOpenLeftSemanticSourceClass A strategy hwin entry
    minimum pivot hview basis
  have root_mem (survivor : raw.RootSurvivor) :
      semanticRoot survivor ∈ source.1 := by
    change semanticRoot survivor ∈ profiledOpenLeftRootImage A
      (fun index => profiledOpenLeftRootOfWinning A strategy hwin
        (entry index) (minimum index) basis)
    rw [← hroot survivor]
    simp [profiledOpenLeftRootImage]
  let realization := profiledOpenLeftSemanticSourceRealization A strategy
    hwin entry minimum pivot hview basis
  let survives : I → Prop := fun lineage =>
    ∃ survivor : raw.RootSurvivor, survivor.lineage = lineage
  let survivorAt (lineage : I) (hlive : survives lineage) :
      raw.RootSurvivor := Classical.choose hlive
  have survivorAt_lineage (lineage : I) (hlive : survives lineage) :
      (survivorAt lineage hlive).lineage = lineage :=
    Classical.choose_spec hlive
  have survivorAt_eq (lineage : I) (hlive : survives lineage)
      (survivor : raw.RootSurvivor) (hsurvivorLineage :
        survivor.lineage = lineage) :
      survivorAt lineage hlive = survivor := by
    apply IndexedLineageChildCode.RootSurvivor.lineage_injective
    exact (survivorAt_lineage lineage hlive).trans hsurvivorLineage.symm
  let memberAt : I → Option {root // root ∈ source.1} := fun lineage =>
    if hlive : survives lineage then
      some ⟨semanticRoot (survivorAt lineage hlive),
        root_mem (survivorAt lineage hlive)⟩
    else none
  have covers : ∀ member : {root // root ∈ source.1},
      ∃ lineage : I, memberAt lineage = some member := by
    intro member
    have hmember := member.property
    change member.1 ∈ profiledOpenLeftRootImage A
      (fun index => profiledOpenLeftRootOfWinning A strategy hwin
        (entry index) (minimum index) basis) at hmember
    rcases Finset.mem_image.mp hmember with
      ⟨survivor, _, hmemberRoot⟩
    have hsemanticRoot : semanticRoot survivor = member.1 := by
      rw [← hroot survivor]
      exact hmemberRoot
    let hlive : survives survivor.lineage := ⟨survivor, rfl⟩
    refine ⟨survivor.lineage, ?_⟩
    unfold memberAt
    rw [dif_pos hlive]
    apply congrArg some
    apply Subtype.ext
    rw [survivorAt_eq survivor.lineage _ survivor rfl]
    exact hsemanticRoot
  let lane : ProfiledOpenIndexedLeftSemanticLane A strategy hwin basis
      (I := I) :=
    { source := source
      realization := realization
      memberAt := memberAt
      covers := covers }
  refine ⟨lane, ?_, ?_⟩
  · funext lineage
    by_cases hlive : survives lineage
    · let survivor := survivorAt lineage hlive
      have hlineage : survivor.lineage = lineage :=
        survivorAt_lineage lineage hlive
      have hslot : raw.deduplicateRoots lineage =
          some (survivor.row, survivor.root) := by
        rw [← hlineage]
        exact survivor.slot
      simp only [lane, ProfiledOpenIndexedLeftSemanticShadow.slots,
        memberAt, dif_pos hlive, Option.map_some,
        IndexedLineageChildCode.rootSlots]
      rw [hslot]
      exact congrArg some (hclassified survivor).symm
    · have hslot : raw.deduplicateRoots lineage = none := by
        cases hcode : raw.deduplicateRoots lineage with
        | none => rfl
        | some value =>
            exfalso
            apply hlive
            exact ⟨⟨(lineage, value), hcode⟩, rfl⟩
      simp [lane, ProfiledOpenIndexedLeftSemanticShadow.slots, memberAt,
        hlive, IndexedLineageChildCode.rootSlots, hslot]
  · intro survivor
    let member : {root // root ∈ source.1} :=
      ⟨semanticRoot survivor, root_mem survivor⟩
    let hlive : survives survivor.lineage := ⟨survivor, rfl⟩
    have hmemberAt : memberAt survivor.lineage = some member := by
      unfold memberAt
      rw [dif_pos hlive]
      apply congrArg some
      apply Subtype.ext
      rw [survivorAt_eq survivor.lineage _ survivor rfl]
    refine ⟨member, hmemberAt, ?_, ?_⟩
    · change profiledOpenLeftSemanticSourceEntry A strategy hwin entry
          minimum pivot hview basis member = entry survivor
      have hactualMem :
          profiledOpenLeftRootOfWinning A strategy hwin (entry survivor)
              (minimum survivor) basis ∈ source.1 := by
        rw [hroot survivor]
        exact root_mem survivor
      have hentry := profiledOpenLeftSemanticSourceEntry_eq_of_root_injective A
        strategy hwin entry minimum pivot hview basis
        (fun left right heq => hrootInjective
          ((hroot left).symm.trans (heq.trans (hroot right))))
        survivor hactualMem
      have hmemberEq :
          (⟨profiledOpenLeftRootOfWinning A strategy hwin (entry survivor)
              (minimum survivor) basis, hactualMem⟩ :
            {root // root ∈ source.1}) = member := by
        apply Subtype.ext
        exact hroot survivor
      simpa [hmemberEq] using hentry
    · change profiledOpenLeftSemanticSourceMinimum A strategy hwin entry
          minimum pivot hview basis member = minimum survivor
      have hactualMem :
          profiledOpenLeftRootOfWinning A strategy hwin (entry survivor)
              (minimum survivor) basis ∈ source.1 := by
        rw [hroot survivor]
        exact root_mem survivor
      have hminimum :=
        profiledOpenLeftSemanticSourceMinimum_eq_of_root_injective A
        strategy hwin entry minimum pivot hview basis
        (fun left right heq => hrootInjective
          ((hroot left).symm.trans (heq.trans (hroot right))))
        survivor hactualMem
      have hmemberEq :
          (⟨profiledOpenLeftRootOfWinning A strategy hwin (entry survivor)
              (minimum survivor) basis, hactualMem⟩ :
            {root // root ∈ source.1}) = member := by
        apply Subtype.ext
        exact hroot survivor
      simpa [hmemberEq] using hminimum

omit [Fintype I] [Inhabited Out₁] [Inhabited Out₂] in
/-- If the literal survivor family has the post-handoff row diagonal, then
the reified lane exposes exactly the active-gated canonical public pattern.
The proof recovers the unique survivor behind each active lineage; no
equal-root representative can be substituted. -/
theorem ProfiledOpenIndexedLeftSurvivorLanePackage.pattern_eq_canonical
    (raw : IndexedLineageChildCode I (ProfiledOpenClassifiedAnchor A))
    (entry : raw.RootSurvivor → ProcTwoPairedEntryRep strategy)
    (minimum : raw.RootSurvivor → A.State)
    (package : ProfiledOpenIndexedLeftSurvivorLanePackage A strategy hwin
      basis raw entry minimum)
    (hliteralPattern :
      procTwoEntryOppositeViewPattern strategy entry =
        indexedLineageCanonicalRowPattern raw.RootSurvivor) :
    ProfiledOpenIndexedLeftSemanticShadow.pattern A strategy hwin basis
        (some package.lane) =
      profiledOpenIndexedActiveCanonicalRowPattern A
        raw.deduplicateRoots.rootSlots := by
  classical
  funext left right
  rcases left with ⟨leftLineage, leftRow⟩
  rcases right with ⟨rightLineage, rightRow⟩
  cases hleft : package.lane.memberAt leftLineage with
  | none =>
      have hleftRoot : raw.deduplicateRoots.rootSlots leftLineage = none := by
        have hslots := congrFun package.slots_eq leftLineage
        simpa [ProfiledOpenIndexedLeftSemanticShadow.slots, hleft] using
          hslots.symm
      simp [ProfiledOpenIndexedLeftSemanticShadow.pattern,
        profiledOpenIndexedActiveCanonicalRowPattern, hleft, hleftRoot]
  | some leftMember =>
      cases hright : package.lane.memberAt rightLineage with
      | none =>
          have hrightRoot :
              raw.deduplicateRoots.rootSlots rightLineage = none := by
            have hslots := congrFun package.slots_eq rightLineage
            simpa [ProfiledOpenIndexedLeftSemanticShadow.slots, hright] using
              hslots.symm
          simp [ProfiledOpenIndexedLeftSemanticShadow.pattern,
            profiledOpenIndexedActiveCanonicalRowPattern, hleft, hright,
            hrightRoot]
      | some rightMember =>
          have hleftRoot : raw.deduplicateRoots.rootSlots leftLineage =
              some (.left leftMember.1) := by
            have hslots := congrFun package.slots_eq leftLineage
            simpa [ProfiledOpenIndexedLeftSemanticShadow.slots, hleft] using
              hslots.symm
          have hrightRoot : raw.deduplicateRoots.rootSlots rightLineage =
              some (.left rightMember.1) := by
            have hslots := congrFun package.slots_eq rightLineage
            simpa [ProfiledOpenIndexedLeftSemanticShadow.slots, hright] using
              hslots.symm
          rcases (raw.deduplicateRoots.rootSlots_eq_some_iff leftLineage
            (.left leftMember.1)).mp hleftRoot with ⟨leftOldRow, hleftCode⟩
          rcases (raw.deduplicateRoots.rootSlots_eq_some_iff rightLineage
            (.left rightMember.1)).mp hrightRoot with
            ⟨rightOldRow, hrightCode⟩
          let leftSurvivor : raw.RootSurvivor :=
            ⟨(leftLineage, (leftOldRow, .left leftMember.1)), hleftCode⟩
          let rightSurvivor : raw.RootSurvivor :=
            ⟨(rightLineage, (rightOldRow, .left rightMember.1)), hrightCode⟩
          rcases package.literal leftSurvivor with
            ⟨leftSemanticMember, hleftAt, hleftEntry, _⟩
          rcases package.literal rightSurvivor with
            ⟨rightSemanticMember, hrightAt, hrightEntry, _⟩
          have hleftMemberEq : leftSemanticMember = leftMember := by
            exact Option.some.inj (hleftAt.symm.trans hleft)
          have hrightMemberEq : rightSemanticMember = rightMember := by
            exact Option.some.inj (hrightAt.symm.trans hright)
          have hleftEntry' : package.lane.realization.entry leftMember =
              entry leftSurvivor := by
            rw [← hleftMemberEq]
            exact hleftEntry
          have hrightEntry' : package.lane.realization.entry rightMember =
              entry rightSurvivor := by
            rw [← hrightMemberEq]
            exact hrightEntry
          have hleftHistory :
              procTwoViewClassRowHistory package.lane.realization.entry
                  (leftMember, leftRow) =
                procTwoViewClassRowHistory entry
                  (leftSurvivor, leftRow) := by
            cases leftRow <;>
              simp [procTwoViewClassRowHistory, hleftEntry']
          have hrightHistory :
              procTwoViewClassRowHistory package.lane.realization.entry
                  (rightMember, rightRow) =
                procTwoViewClassRowHistory entry
                  (rightSurvivor, rightRow) := by
            cases rightRow <;>
              simp [procTwoViewClassRowHistory, hrightEntry']
          have hpattern := congrFun
            (congrFun hliteralPattern (leftSurvivor, leftRow))
            (rightSurvivor, rightRow)
          simp only [ProfiledOpenIndexedLeftSemanticShadow.pattern, hleft,
            hright, profiledOpenIndexedActiveCanonicalRowPattern, hleftRoot,
            hrightRoot]
          change decide (currentView Proc.one
              (procTwoViewClassRowHistory package.lane.realization.entry
                (leftMember, leftRow)) =
            currentView Proc.one
              (procTwoViewClassRowHistory package.lane.realization.entry
                (rightMember, rightRow))) =
              decide (leftRow = rightRow)
          rw [hleftHistory, hrightHistory]
          simpa only [procTwoEntryOppositeViewPattern,
            indexedLineageCanonicalRowPattern] using hpattern

end

end DetParityAutomaton

end DistributedSynthesis
