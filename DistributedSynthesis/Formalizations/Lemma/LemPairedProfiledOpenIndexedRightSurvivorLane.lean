/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledOpenIndexedSurvivorLane

/-!
# Reifying normalized process-one survivors as a right semantic lane

This is the exact right-oriented mirror of
`profiledOpenIndexedLeftSurvivorLanePackage`.  It keeps the literal
process-one entry and minimum attached to every normalized survivor, exposes
exactly the normalized `.right` root slots, and prevents canonical source
realization from switching to another history with the same finite root.
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

/-- A right semantic lane built from literal process-one survivors, together
with the exact slot and literal-realization equations. -/
structure ProfiledOpenIndexedRightSurvivorLanePackage
    (raw : IndexedLineageChildCode I (ProfiledOpenClassifiedAnchor A))
    (entry : raw.RootSurvivor → ProcOnePairedEntryRep strategy)
    (minimum : raw.RootSurvivor → A.State) where
  lane : ProfiledOpenIndexedRightSemanticLane A strategy hwin basis (I := I)
  slots_eq :
    ProfiledOpenIndexedRightSemanticShadow.slots A strategy hwin basis
        (some lane) = raw.deduplicateRoots.rootSlots
  literal : ∀ survivor : raw.RootSurvivor,
    ∃ member : {root // root ∈ lane.source.1},
      lane.memberAt survivor.lineage = some member ∧
        lane.realization.entry member = entry survivor ∧
        lane.realization.minimum member = minimum survivor

/-- Reify a nonempty normalized survivor family as a right semantic lane.
Root injectivity of the normalized family makes the canonical semantic-source
representative equal to the literal survivor. -/
noncomputable def profiledOpenIndexedRightSurvivorLanePackage
    (raw : IndexedLineageChildCode I (ProfiledOpenClassifiedAnchor A))
    (hsurvivor : Nonempty raw.RootSurvivor)
    (entry : raw.RootSurvivor → ProcOnePairedEntryRep strategy)
    (minimum : raw.RootSurvivor → A.State)
    (semanticRoot : raw.RootSurvivor → ProfiledOpenRightRoot A)
    (hclassified : ∀ survivor : raw.RootSurvivor,
      IndexedLineageChildCode.RootSurvivor.root survivor =
        ProfiledOpenClassifiedAnchor.right (semanticRoot survivor))
    (hroot : ∀ survivor,
      profiledOpenRightRootOfWinning A strategy hwin (entry survivor)
        (minimum survivor) basis = semanticRoot survivor)
    (pivot : raw.RootSurvivor)
    (hview : ∀ survivor,
      currentView Proc.one (entry survivor).leftHistory =
        currentView Proc.one (entry pivot).leftHistory) :
    ProfiledOpenIndexedRightSurvivorLanePackage A strategy hwin basis raw
      entry minimum := by
  classical
  letI : Inhabited raw.RootSurvivor := ⟨Classical.choice hsurvivor⟩
  have hrootInjective : Function.Injective semanticRoot := by
    intro left right heq
    apply IndexedLineageChildCode.RootSurvivor.root_injective
    rw [hclassified left, hclassified right, heq]
  let source := profiledOpenRightSemanticSourceClass A strategy hwin entry
    minimum pivot hview basis
  have root_mem (survivor : raw.RootSurvivor) :
      semanticRoot survivor ∈ source.1 := by
    change semanticRoot survivor ∈ profiledOpenRightRootImage A
      (fun index => profiledOpenRightRootOfWinning A strategy hwin
        (entry index) (minimum index) basis)
    rw [← hroot survivor]
    simp [profiledOpenRightRootImage]
  let realization := profiledOpenRightSemanticSourceRealization A strategy
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
    change member.1 ∈ profiledOpenRightRootImage A
      (fun index => profiledOpenRightRootOfWinning A strategy hwin
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
  let lane : ProfiledOpenIndexedRightSemanticLane A strategy hwin basis
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
      simp only [lane, ProfiledOpenIndexedRightSemanticShadow.slots,
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
      simp [lane, ProfiledOpenIndexedRightSemanticShadow.slots, memberAt,
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
    · change profiledOpenRightSemanticSourceEntry A strategy hwin entry
          minimum pivot hview basis member = entry survivor
      have hactualMem :
          profiledOpenRightRootOfWinning A strategy hwin (entry survivor)
              (minimum survivor) basis ∈ source.1 := by
        rw [hroot survivor]
        exact root_mem survivor
      have hentry := profiledOpenRightSemanticSourceEntry_eq_of_root_injective A
        strategy hwin entry minimum pivot hview basis
        (fun left right heq => hrootInjective
          ((hroot left).symm.trans (heq.trans (hroot right))))
        survivor hactualMem
      have hmemberEq :
          (⟨profiledOpenRightRootOfWinning A strategy hwin (entry survivor)
              (minimum survivor) basis, hactualMem⟩ :
            {root // root ∈ source.1}) = member := by
        apply Subtype.ext
        exact hroot survivor
      simpa [hmemberEq] using hentry
    · change profiledOpenRightSemanticSourceMinimum A strategy hwin entry
          minimum pivot hview basis member = minimum survivor
      have hactualMem :
          profiledOpenRightRootOfWinning A strategy hwin (entry survivor)
              (minimum survivor) basis ∈ source.1 := by
        rw [hroot survivor]
        exact root_mem survivor
      have hminimum :=
        profiledOpenRightSemanticSourceMinimum_eq_of_root_injective A
        strategy hwin entry minimum pivot hview basis
        (fun left right heq => hrootInjective
          ((hroot left).symm.trans (heq.trans (hroot right))))
        survivor hactualMem
      have hmemberEq :
          (⟨profiledOpenRightRootOfWinning A strategy hwin (entry survivor)
              (minimum survivor) basis, hactualMem⟩ :
            {root // root ∈ source.1}) = member := by
        apply Subtype.ext
        exact hroot survivor
      simpa [hmemberEq] using hminimum

omit [Fintype I] [Inhabited Out₁] [Inhabited Out₂] in
/-- Right-oriented mirror: a literal process-one row diagonal becomes the
active-gated canonical public pattern of the reified semantic lane. -/
theorem ProfiledOpenIndexedRightSurvivorLanePackage.pattern_eq_canonical
    (raw : IndexedLineageChildCode I (ProfiledOpenClassifiedAnchor A))
    (entry : raw.RootSurvivor → ProcOnePairedEntryRep strategy)
    (minimum : raw.RootSurvivor → A.State)
    (package : ProfiledOpenIndexedRightSurvivorLanePackage A strategy hwin
      basis raw entry minimum)
    (hliteralPattern :
      procOneEntryOppositeViewPattern strategy entry =
        indexedLineageCanonicalRowPattern raw.RootSurvivor) :
    ProfiledOpenIndexedRightSemanticShadow.pattern A strategy hwin basis
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
        simpa [ProfiledOpenIndexedRightSemanticShadow.slots, hleft] using
          hslots.symm
      simp [ProfiledOpenIndexedRightSemanticShadow.pattern,
        profiledOpenIndexedActiveCanonicalRowPattern, hleft, hleftRoot]
  | some leftMember =>
      cases hright : package.lane.memberAt rightLineage with
      | none =>
          have hrightRoot :
              raw.deduplicateRoots.rootSlots rightLineage = none := by
            have hslots := congrFun package.slots_eq rightLineage
            simpa [ProfiledOpenIndexedRightSemanticShadow.slots, hright] using
              hslots.symm
          simp [ProfiledOpenIndexedRightSemanticShadow.pattern,
            profiledOpenIndexedActiveCanonicalRowPattern, hleft, hright,
            hrightRoot]
      | some rightMember =>
          have hleftRoot : raw.deduplicateRoots.rootSlots leftLineage =
              some (.right leftMember.1) := by
            have hslots := congrFun package.slots_eq leftLineage
            simpa [ProfiledOpenIndexedRightSemanticShadow.slots, hleft] using
              hslots.symm
          have hrightRoot : raw.deduplicateRoots.rootSlots rightLineage =
              some (.right rightMember.1) := by
            have hslots := congrFun package.slots_eq rightLineage
            simpa [ProfiledOpenIndexedRightSemanticShadow.slots, hright] using
              hslots.symm
          rcases (raw.deduplicateRoots.rootSlots_eq_some_iff leftLineage
            (.right leftMember.1)).mp hleftRoot with ⟨leftOldRow, hleftCode⟩
          rcases (raw.deduplicateRoots.rootSlots_eq_some_iff rightLineage
            (.right rightMember.1)).mp hrightRoot with
            ⟨rightOldRow, hrightCode⟩
          let leftSurvivor : raw.RootSurvivor :=
            ⟨(leftLineage, (leftOldRow, .right leftMember.1)), hleftCode⟩
          let rightSurvivor : raw.RootSurvivor :=
            ⟨(rightLineage, (rightOldRow, .right rightMember.1)), hrightCode⟩
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
              procOneViewClassRowHistory package.lane.realization.entry
                  (leftMember, leftRow) =
                procOneViewClassRowHistory entry
                  (leftSurvivor, leftRow) := by
            cases leftRow <;>
              simp [procOneViewClassRowHistory, hleftEntry']
          have hrightHistory :
              procOneViewClassRowHistory package.lane.realization.entry
                  (rightMember, rightRow) =
                procOneViewClassRowHistory entry
                  (rightSurvivor, rightRow) := by
            cases rightRow <;>
              simp [procOneViewClassRowHistory, hrightEntry']
          have hpattern := congrFun
            (congrFun hliteralPattern (leftSurvivor, leftRow))
            (rightSurvivor, rightRow)
          simp only [ProfiledOpenIndexedRightSemanticShadow.pattern, hleft,
            hright, profiledOpenIndexedActiveCanonicalRowPattern, hleftRoot,
            hrightRoot]
          change decide (currentView Proc.two
              (procOneViewClassRowHistory package.lane.realization.entry
                (leftMember, leftRow)) =
            currentView Proc.two
              (procOneViewClassRowHistory package.lane.realization.entry
                (rightMember, rightRow))) =
              decide (leftRow = rightRow)
          rw [hleftHistory, hrightHistory]
          simpa only [procOneEntryOppositeViewPattern,
            indexedLineageCanonicalRowPattern] using hpattern

end

end DetParityAutomaton

end DistributedSynthesis
