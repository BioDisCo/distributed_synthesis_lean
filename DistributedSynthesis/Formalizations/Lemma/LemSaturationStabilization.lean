/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemConcreteReversalInstantiation
import DistributedSynthesis.Formalizations.Lemma.LemSummaryWindowSetClosure

/-!
# The refinement tower and the stabilization closure

The final generic layer of the set route.  The candidate-set closure
certificate needs the set pullback bound with ONE summary family on both
sides, while each refinement round proves it from the refined old side to
the unrefined new side.  This file builds the full refinement tower and
reduces the same-family bound to a single named stabilization predicate
-- the Lean form of the paper's stabilized partition `Q_d*`.

* The **lawfulness tower**: the window monoid is lawful over a lawful
  summary (`windowMul_assoc`, `windowOne_mul`, `windowMul_one`), the
  label-profile matrices are lawful over a lawful carrier
  (`profileSummarySemigroup_lawful`), and products preserve lawfulness
  (`PathSummaryLawful.prod`).  Hence every level of the tower is lawful.
* The **tower** (`saturationLevel`): level `0` is the base family; level
  `k+1` on side `d` is the base refined by the window profile valued in
  level-`k` windows of the other side.
* **Stabilization** (`SaturationStabilizesAt k`): level-`k` windows
  determine level-`k+1` windows.  This is the model-specific content of
  `prop:journalatomsreversalclosure`'s `Q_d*`.  It is obtained from the
  generic pigeonhole `exists_saturationStabilizesAt_of_finite_quotient`
  once every level factors through one fixed finite quotient; the master
  quotient is `E_d` (`enrichedCode`, `LemSaturationFactorization.lean`),
  not the run-relative `M_A × Q_d`.
* **The closure** (`saturatedSetClosureCertificate`): under
  stabilization, the same-family set pullback bound holds at level `k`
  (`setPullbackBound_of_stabilization`), and the candidate-set reversal
  closure certificate follows verbatim.
-/

namespace DistributedSynthesis

universe u v w x y z v' r

/-! ### Window monoid laws -/

section WindowLaws

variable {EdgeType : Type u}
  (S : PathSummarySemigroup.{u, v} EdgeType) (c : Nat)

theorem prefixAtMost_idem {α : Type u} (w : List α) :
    prefixAtMost c (prefixAtMost c w) = prefixAtMost c w := by
  simp [prefixAtMost, List.take_take]

theorem prefixAtMost_take_left {α : Type u} (w z : List α) :
    prefixAtMost c (prefixAtMost c w ++ z) = prefixAtMost c (w ++ z) := by
  rw [prefixAtMost_append c (prefixAtMost c w) z, prefixAtMost_idem,
    <- prefixAtMost_append c w z]

theorem prefixAtMost_take_right {α : Type u} (x w : List α) :
    prefixAtMost c (x ++ prefixAtMost c w) = prefixAtMost c (x ++ w) := by
  rw [prefixAtMost_append c x (prefixAtMost c w), prefixAtMost_idem,
    <- prefixAtMost_append c x w]

theorem suffixAtMost_idem {α : Type u} (w : List α) :
    suffixAtMost c (suffixAtMost c w) = suffixAtMost c w := by
  have h : (suffixAtMost c w).length ≤ c := by
    rw [suffixAtMost_length]
    omega
  simp only [suffixAtMost, List.length_drop]
  rw [show w.length - (w.length - c) - c = 0 by
    simp only [suffixAtMost, List.length_drop] at h
    omega]
  simp

theorem suffixAtMost_drop_left {α : Type u} (w z : List α) :
    suffixAtMost c (suffixAtMost c w ++ z) = suffixAtMost c (w ++ z) := by
  rw [suffixAtMost_append c (suffixAtMost c w) z, suffixAtMost_idem,
    <- suffixAtMost_append c w z]

theorem suffixAtMost_drop_right {α : Type u} (x w : List α) :
    suffixAtMost c (x ++ suffixAtMost c w) = suffixAtMost c (x ++ w) := by
  rw [suffixAtMost_append c x (suffixAtMost c w), suffixAtMost_idem,
    <- suffixAtMost_append c x w]

/-- Repackaging a bounded window from its own list is the identity. -/
theorem boundedEndpointWindowOfList_toList_eq {α : Type u}
    (w : BoundedEndpointWindow α c) (h : w.toList.length ≤ c) :
    boundedEndpointWindowOfList c w.toList h = w := by
  apply BoundedEndpointWindow.toList_injective
  simp

theorem windowMul_assoc (hlaw : PathSummaryLawful S)
    (a b d : FiniteSummaryWindowValue S.Summary EdgeType c) :
    windowMul S c (windowMul S c a b) d =
      windowMul S c a (windowMul S c b d) := by
  unfold windowMul
  refine Prod.ext (hlaw.assoc _ _ _) (Prod.ext ?_ ?_)
  · apply BoundedEndpointWindow.toList_injective
    simp only [boundedEndpointWindowOfList_toList]
    rw [prefixAtMost_take_left, prefixAtMost_take_right, List.append_assoc]
  · apply BoundedEndpointWindow.toList_injective
    simp only [boundedEndpointWindowOfList_toList]
    rw [suffixAtMost_drop_left, suffixAtMost_drop_right, List.append_assoc]

theorem windowOne_mul (hlaw : PathSummaryLawful S)
    (a : FiniteSummaryWindowValue S.Summary EdgeType c) :
    windowMul S c (windowOne S c) a = a := by
  unfold windowMul windowOne finiteSummaryWindowAbstraction
  refine Prod.ext (hlaw.one_mul _) (Prod.ext ?_ ?_)
  · apply BoundedEndpointWindow.toList_injective
    simp only [boundedEndpointWindowOfList_toList, boundedPrefixAtMost_toList]
    have h : a.2.1.toList.length ≤ c := by
      rw [BoundedEndpointWindow.length_toList]
      omega
    simp [prefixAtMost, List.take_of_length_le h]
  · apply BoundedEndpointWindow.toList_injective
    simp only [boundedEndpointWindowOfList_toList, boundedSuffixAtMost_toList]
    have h : a.2.2.toList.length ≤ c := by
      rw [BoundedEndpointWindow.length_toList]
      omega
    have hnil : suffixAtMost c ([] : List EdgeType) = [] := by
      simp [suffixAtMost]
    rw [hnil, List.nil_append]
    have h0 : (a.2.2.1.val - c : Nat) = 0 := by
      have := a.2.2.1.isLt
      omega
    simp [suffixAtMost, BoundedEndpointWindow.length_toList, h0]

theorem windowMul_one (hlaw : PathSummaryLawful S)
    (a : FiniteSummaryWindowValue S.Summary EdgeType c) :
    windowMul S c a (windowOne S c) = a := by
  unfold windowMul windowOne finiteSummaryWindowAbstraction
  refine Prod.ext (hlaw.mul_one _) (Prod.ext ?_ ?_)
  · apply BoundedEndpointWindow.toList_injective
    simp only [boundedEndpointWindowOfList_toList, boundedPrefixAtMost_toList]
    have h : a.2.1.toList.length ≤ c := by
      rw [BoundedEndpointWindow.length_toList]
      omega
    simp [prefixAtMost, List.take_of_length_le h]
  · apply BoundedEndpointWindow.toList_injective
    simp only [boundedEndpointWindowOfList_toList, boundedSuffixAtMost_toList]
    have h : a.2.2.toList.length ≤ c := by
      rw [BoundedEndpointWindow.length_toList]
      omega
    have hnil : suffixAtMost c ([] : List EdgeType) = [] := by
      simp [suffixAtMost]
    rw [hnil, List.append_nil]
    have h0 : (a.2.2.1.val - c : Nat) = 0 := by
      have := a.2.2.1.isLt
      omega
    simp [suffixAtMost, BoundedEndpointWindow.length_toList, h0]

end WindowLaws

/-! ### Profile matrix laws -/

section ProfileLaws

variable {Label : Type w} {M : Type x}
variable [DecidableEq Label] [DecidableEq M] [Fintype Label]

omit [DecidableEq Label] in
theorem profileComp_assoc (mmul : M -> M -> M)
    (massoc : ∀ a b d : M, mmul (mmul a b) d = mmul a (mmul b d))
    (P Q R : LabelProfile Label M) :
    profileComp mmul (profileComp mmul P Q) R =
      profileComp mmul P (profileComp mmul Q R) := by
  funext left right
  ext m
  rw [mem_profileComp, mem_profileComp]
  constructor
  · rintro ⟨mid₂, m₁₂, m₃, hm₁₂, hm₃, rfl⟩
    rcases (mem_profileComp mmul P Q left mid₂ m₁₂).mp hm₁₂ with
      ⟨mid₁, m₁, m₂, hm₁, hm₂, rfl⟩
    exact ⟨mid₁, m₁, mmul m₂ m₃, hm₁,
      (mem_profileComp mmul Q R mid₁ right _).mpr
        ⟨mid₂, m₂, m₃, hm₂, hm₃, rfl⟩,
      massoc m₁ m₂ m₃⟩
  · rintro ⟨mid₁, m₁, m₂₃, hm₁, hm₂₃, rfl⟩
    rcases (mem_profileComp mmul Q R mid₁ right m₂₃).mp hm₂₃ with
      ⟨mid₂, m₂, m₃, hm₂, hm₃, rfl⟩
    exact ⟨mid₂, mmul m₁ m₂, m₃,
      (mem_profileComp mmul P Q left mid₂ _).mpr
        ⟨mid₁, m₁, m₂, hm₁, hm₂, rfl⟩,
      hm₃, (massoc m₁ m₂ m₃).symm⟩

theorem profileComp_id_left (mone : M) (mmul : M -> M -> M)
    (hone : ∀ m : M, mmul mone m = m) (P : LabelProfile Label M) :
    profileComp mmul (identityProfile mone) P = P := by
  funext left right
  ext m
  rw [mem_profileComp]
  constructor
  · rintro ⟨mid, m₁, m₂, hm₁, hm₂, rfl⟩
    unfold identityProfile at hm₁
    by_cases hmid : left = mid
    · rw [if_pos hmid, Finset.mem_singleton] at hm₁
      subst hmid
      rw [hm₁, hone]
      exact hm₂
    · rw [if_neg hmid] at hm₁
      exact absurd hm₁ (Finset.notMem_empty m₁)
  · intro hm
    exact ⟨left, mone, m, by simp [identityProfile], hm, (hone m).symm⟩

theorem profileComp_id_right (mone : M) (mmul : M -> M -> M)
    (hone : ∀ m : M, mmul m mone = m) (P : LabelProfile Label M) :
    profileComp mmul P (identityProfile mone) = P := by
  funext left right
  ext m
  rw [mem_profileComp]
  constructor
  · rintro ⟨mid, m₁, m₂, hm₁, hm₂, rfl⟩
    unfold identityProfile at hm₂
    by_cases hmid : mid = right
    · rw [if_pos hmid, Finset.mem_singleton] at hm₂
      subst hmid
      rw [hm₂, hone]
      exact hm₁
    · rw [if_neg hmid] at hm₂
      exact absurd hm₂ (Finset.notMem_empty m₂)
  · intro hm
    exact ⟨right, m, mone, hm, by simp [identityProfile], (hone m).symm⟩

end ProfileLaws

/-! ### Lawfulness of profiles and products -/

section LawfulnessTower

variable {OldEdge : Type u} {NewEdge : Type v} {Label : Type w}

/-- The window-valued profile semigroup over a lawful new-side summary is
lawful. -/
theorem windowProfileSemigroup_lawful
    [Fintype Label] [DecidableEq Label]
    (scheme : FiniteSubstitutionScheme OldEdge NewEdge Label)
    (Snew : PathSummarySemigroup.{v, x} NewEdge)
    [Fintype NewEdge] [DecidableEq NewEdge] [DecidableEq Snew.Summary]
    (radius : Nat) (hlaw : PathSummaryLawful Snew) :
    PathSummaryLawful (windowProfileSemigroup scheme Snew radius) where
  assoc a b d :=
    profileComp_assoc (windowMul Snew radius)
      (windowMul_assoc Snew radius hlaw) a b d
  one_mul a :=
    profileComp_id_left (windowOne Snew radius) (windowMul Snew radius)
      (windowOne_mul Snew radius hlaw) a
  mul_one a :=
    profileComp_id_right (windowOne Snew radius) (windowMul Snew radius)
      (windowMul_one Snew radius hlaw) a

/-- Products of lawful summaries are lawful. -/
theorem PathSummaryLawful.prod {EdgeType : Type u}
    {S : PathSummarySemigroup.{u, v} EdgeType}
    {T : PathSummarySemigroup.{u, w} EdgeType}
    (hS : PathSummaryLawful S) (hT : PathSummaryLawful T) :
    PathSummaryLawful (S.prod T) where
  assoc a b d := Prod.ext (hS.assoc _ _ _) (hT.assoc _ _ _)
  one_mul a := Prod.ext (hS.one_mul _) (hT.one_mul _)
  mul_one a := Prod.ext (hS.mul_one _) (hT.mul_one _)

end LawfulnessTower

/-! ### Pointwise families of summaries -/

section PiSemigroup

variable {EdgeType : Type u}

/-- The pointwise product of a finite family of path-summary semigroups
over one edge type. -/
def PathSummarySemigroup.pi {iota : Type y} [Fintype iota] [DecidableEq iota]
    (T : iota -> PathSummarySemigroup.{u, v} EdgeType) :
    PathSummarySemigroup.{u, max v y} EdgeType where
  Summary := ∀ i, (T i).Summary
  summaryFinite := by infer_instance
  empty := fun i => (T i).empty
  ofEdge edge := fun i => (T i).ofEdge edge
  multiply a b := fun i => (T i).multiply (a i) (b i)

theorem PathSummarySemigroup.pathSummaryValue_pi {iota : Type y}
    [Fintype iota] [DecidableEq iota]
    (T : iota -> PathSummarySemigroup.{u, v} EdgeType)
    (path : TypedPath EdgeType) (i : iota) :
    pathSummaryValue (PathSummarySemigroup.pi T) path i =
      pathSummaryValue (T i) path := by
  induction path using List.reverseRecOn with
  | nil => rfl
  | append_singleton path edge ih =>
      simp only [pathSummaryValue, List.foldl_append, List.foldl_cons,
        List.foldl_nil] at ih ⊢
      show (T i).multiply
          ((path.foldl (fun acc e => (PathSummarySemigroup.pi T).multiply acc
            ((PathSummarySemigroup.pi T).ofEdge e))
            (PathSummarySemigroup.pi T).empty) i) ((T i).ofEdge edge) = _
      rw [ih]

theorem PathSummaryLawful.pi {iota : Type y} [Fintype iota] [DecidableEq iota]
    {T : iota -> PathSummarySemigroup.{u, v} EdgeType}
    (h : ∀ i, PathSummaryLawful (T i)) :
    PathSummaryLawful (PathSummarySemigroup.pi T) where
  assoc a b d := funext fun i => (h i).assoc _ _ _
  one_mul a := funext fun i => (h i).one_mul _
  mul_one a := funext fun i => (h i).mul_one _

end PiSemigroup

/-! ### The parameterized refinement tower and stabilization -/

section Tower

variable {EdgeType : Proc -> Type u} {Label : Type w}
variable [Fintype Label] [DecidableEq Label]
variable [∀ d, Fintype (EdgeType d)] [∀ d, DecidableEq (EdgeType d)]
variable {Param : Proc -> Type w}
variable [∀ d, Fintype (Param d)] [∀ d, DecidableEq (Param d)]
variable (schemeAt : (d : Proc) -> Param d ->
  FiniteSubstitutionScheme (EdgeType d) (EdgeType (d.other)) Label)
variable (base : (d : Proc) -> PathSummarySemigroup.{u, max u w} (EdgeType d))
variable (radius : Nat)

/-- The parameterized refinement tower: level `k+1` on side `d` refines
the base with, for EVERY closing parameter, the window profile of that
parameter's scheme, valued in level-`k` windows of the other side.  The
concrete substitution is tuple-dependent, so the whole finite parameter
family is refined simultaneously. -/
noncomputable def saturationLevel :
    Nat -> (d : Proc) -> PathSummarySemigroup.{u, max u w} (EdgeType d)
  | 0, d => base d
  | k + 1, d =>
      letI : DecidableEq (saturationLevel k d.other).Summary :=
        Classical.decEq _
      (base d).prod
        (PathSummarySemigroup.pi fun param : Param d =>
          windowProfileSemigroup (schemeAt d param)
            (saturationLevel k d.other) radius)

/-- Every level of the tower is lawful. -/
theorem saturationLevel_lawful
    (hbase : ∀ d, PathSummaryLawful (base d)) :
    ∀ (k : Nat) (d : Proc),
      PathSummaryLawful (saturationLevel schemeAt base radius k d) := by
  intro k
  induction k with
  | zero => exact hbase
  | succ k ih =>
      intro d
      letI : DecidableEq
          (saturationLevel schemeAt base radius k d.other).Summary :=
        Classical.decEq _
      show PathSummaryLawful ((base d).prod _)
      exact (hbase d).prod
        (PathSummaryLawful.pi fun param =>
          windowProfileSemigroup_lawful (schemeAt d param)
            (saturationLevel schemeAt base radius k d.other) radius
            (ih d.other))

/-- **The parameterwise one-round bound along the tower**: level-`k+1`
windows of the old side determine, for every closing parameter, the
images of level-`k` output windows of that parameter's scheme. -/
theorem saturationLevel_round_bound
    (hbase : ∀ d, PathSummaryLawful (base d))
    (k : Nat) (d : Proc) (param : Param d) (bound : Nat)
    {old₁ old₂ : TypedPath (EdgeType d)}
    (hwindow :
      summaryWindowAbstraction (saturationLevel schemeAt base radius (k + 1) d)
          bound old₁ =
        summaryWindowAbstraction (saturationLevel schemeAt base radius (k + 1) d)
          bound old₂) :
    (summaryWindowAbstraction (saturationLevel schemeAt base radius k d.other)
        radius) '' (schemeAt d param).SuccessorWords old₁ =
      (summaryWindowAbstraction (saturationLevel schemeAt base radius k d.other)
        radius) '' (schemeAt d param).SuccessorWords old₂ := by
  letI : DecidableEq
      (saturationLevel schemeAt base radius k d.other).Summary :=
    Classical.decEq _
  apply substitution_windowImage_eq_of_profile_eq (schemeAt d param)
    (saturationLevel schemeAt base radius k d.other) radius
    (saturationLevel_lawful schemeAt base radius hbase k d.other)
  have hsummary := congrArg SummaryWindowValue.summary hwindow
  simp only [summaryWindowAbstraction] at hsummary
  have hlevel : saturationLevel schemeAt base radius (k + 1) d =
      (base d).prod
        (PathSummarySemigroup.pi fun param : Param d =>
          windowProfileSemigroup (schemeAt d param)
            (saturationLevel schemeAt base radius k d.other) radius) := rfl
  rw [hlevel, PathSummarySemigroup.pathSummaryValue_prod,
    PathSummarySemigroup.pathSummaryValue_prod] at hsummary
  have hparam := congrFun (congrArg Prod.snd hsummary) param
  dsimp only at hparam
  rw [PathSummarySemigroup.pathSummaryValue_pi,
    PathSummarySemigroup.pathSummaryValue_pi] at hparam
  exact hparam

/--
**The stabilization predicate** -- the Lean form of the stabilized
partition `Q_d*` of `prop:journalatomsreversalclosure`: at level `k`, the
windows already determine the next level's windows.
-/
def SaturationStabilizesAt (k : Nat) : Prop :=
  ∀ (d : Proc) (bound : Nat) (old new : TypedPath (EdgeType d)),
    summaryWindowAbstraction (saturationLevel schemeAt base radius k d)
        bound old =
      summaryWindowAbstraction (saturationLevel schemeAt base radius k d)
        bound new ->
    summaryWindowAbstraction (saturationLevel schemeAt base radius (k + 1) d)
        bound old =
      summaryWindowAbstraction (saturationLevel schemeAt base radius (k + 1) d)
        bound new

/-- Level-`k` summaries determine level-`k+1` summaries. -/
def SummaryDetermines (k : Nat) : Prop :=
  ∀ (d : Proc) (old new : TypedPath (EdgeType d)),
    pathSummaryValue (saturationLevel schemeAt base radius k d) old =
        pathSummaryValue (saturationLevel schemeAt base radius k d) new ->
      pathSummaryValue (saturationLevel schemeAt base radius (k + 1) d) old =
        pathSummaryValue (saturationLevel schemeAt base radius (k + 1) d) new

/-- Windows differ across levels only in the summary component, so
summary determination is stabilization. -/
theorem saturationStabilizesAt_of_summaryDetermines
    {k : Nat} (h : SummaryDetermines schemeAt base radius k) :
    SaturationStabilizesAt schemeAt base radius k := by
  intro d bound old new hwindow
  have hsummary := congrArg SummaryWindowValue.summary hwindow
  have hpref : prefixAtMost bound old = prefixAtMost bound new :=
    congrArg SummaryWindowValue.pref hwindow
  have hsuff : suffixAtMost bound old = suffixAtMost bound new :=
    congrArg SummaryWindowValue.suff hwindow
  simp only [summaryWindowAbstraction] at hsummary ⊢
  simp only [SummaryWindowValue.mk.injEq]
  exact ⟨h d old new hsummary, hpref, hsuff⟩

/--
**Generic finite stabilization** (`exists_saturationStabilizesAt_of_finite_quotient`):
if every level's summary factors through one fixed finite quotient and
levels refine monotonically, then some level stabilizes.  The proof is
the pigeonhole on identified code pairs: the identified-pair sets are
antitone along the tower and live in a fixed finite type, so two
consecutive levels agree, and factorization turns pair agreement into
summary determination.
-/
theorem exists_saturationStabilizesAt_of_finite_quotient
    {Q : Proc -> Type x} [∀ d, Fintype (Q d)]
    (code : (d : Proc) -> TypedPath (EdgeType d) -> Q d)
    (hfactor : ∀ (k : Nat) (d : Proc) (old new : TypedPath (EdgeType d)),
      code d old = code d new ->
        pathSummaryValue (saturationLevel schemeAt base radius k d) old =
          pathSummaryValue (saturationLevel schemeAt base radius k d) new)
    (hrefine : ∀ (k : Nat) (d : Proc) (old new : TypedPath (EdgeType d)),
      pathSummaryValue (saturationLevel schemeAt base radius (k + 1) d) old =
          pathSummaryValue (saturationLevel schemeAt base radius (k + 1) d)
            new ->
        pathSummaryValue (saturationLevel schemeAt base radius k d) old =
          pathSummaryValue (saturationLevel schemeAt base radius k d) new) :
    ∃ k : Nat, SaturationStabilizesAt schemeAt base radius k := by
  classical
  -- identified code pairs at each level
  let R : Nat -> (d : Proc) -> Q d -> Q d -> Prop := fun k d a b =>
    ∀ old new : TypedPath (EdgeType d),
      code d old = a -> code d new = b ->
        pathSummaryValue (saturationLevel schemeAt base radius k d) old =
          pathSummaryValue (saturationLevel schemeAt base radius k d) new
  let F : Nat -> Finset ((d : Proc) × (Q d × Q d)) := fun k =>
    Finset.univ.filter fun t => R k t.1 t.2.1 t.2.2
  have hFmono : ∀ k, F (k + 1) ⊆ F k := by
    intro k t ht
    rw [Finset.mem_filter] at ht ⊢
    exact ⟨Finset.mem_univ t, fun old new hold hnew =>
      hrefine k t.1 old new (ht.2 old new hold hnew)⟩
  have hstep : ∃ k, F (k + 1) = F k := by
    by_contra hne
    push Not at hne
    have hlt : ∀ k, (F (k + 1)).card < (F k).card := by
      intro k
      exact Finset.card_lt_card
        (lt_of_le_of_ne (hFmono k) (hne k))
    have hbound : ∀ k, (F k).card + k ≤ (F 0).card := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
          have := hlt k
          omega
    have := hbound ((F 0).card + 1)
    omega
  obtain ⟨k, hk⟩ := hstep
  refine ⟨k, saturationStabilizesAt_of_summaryDetermines schemeAt base radius
    ?_⟩
  intro d old new hvalue
  have hmem : (⟨d, (code d old, code d new)⟩ : (d : Proc) × (Q d × Q d)) ∈
      F k := by
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, fun old' new' hold' hnew' => ?_⟩
    calc
      pathSummaryValue (saturationLevel schemeAt base radius k d) old' =
          pathSummaryValue (saturationLevel schemeAt base radius k d) old :=
        hfactor k d old' old hold'
      _ = pathSummaryValue (saturationLevel schemeAt base radius k d) new :=
        hvalue
      _ = pathSummaryValue (saturationLevel schemeAt base radius k d) new' :=
        (hfactor k d new' new hnew').symm
  rw [<- hk, Finset.mem_filter] at hmem
  exact hmem.2 old new rfl rfl

/-- **Under stabilization, the same-family set pullback bound holds at
the stable level, per closing parameter.** -/
theorem setPullbackBoundAt_of_stabilization
    (hbase : ∀ d, PathSummaryLawful (base d))
    {k : Nat} (hstab : SaturationStabilizesAt schemeAt base radius k)
    (d : Proc) (param : Param d) :
    SummaryWindowRelSetPullbackBoundAt radius
      (saturationLevel schemeAt base radius k d)
      (saturationLevel schemeAt base radius k d.other)
      (fun old => (schemeAt d param).SuccessorWords old) := by
  intro old₁ old₂ hwindow
  exact saturationLevel_round_bound schemeAt base radius hbase k d param
    (endpointPullbackBound radius)
    (hstab d (endpointPullbackBound radius) old₁ old₂ hwindow)

variable {In₁ : Type v} {In₂ : Type x} {Out₁ : Type y} {Out₂ : Type z}

/--
**The saturated candidate-set reversal-closure certificate, tuple
dependent.**  `paramOf` extracts each closing tuple's parameter (its bits
and letter); the substitution relation consults the parameter's scheme,
so the concrete tuple dependence is preserved.  Stabilization is the sole
remaining model-specific input, obtainable from
`exists_saturationStabilizesAt_of_finite_quotient` once the fixed-quotient
congruence is proved for the concrete schemes.
-/
noncomputable def saturatedSetClosureCertificate
    {BaseAtom : Proc -> Type v'} {Continuation : Proc -> Type r}
    (hbase : ∀ d, PathSummaryLawful (base d))
    {k : Nat} (hstab : SaturationStabilizesAt schemeAt base radius k)
    (paramOf : (d : Proc) ->
      DirectReversalTuple
        (SummaryWindowAtom (saturationLevel schemeAt base radius k) radius)
        In₁ In₂ Out₁ Out₂ d -> Param d)
    (baseAtomOf : (d : Proc) -> TypedPath (EdgeType d) -> BaseAtom d)
    (continuationOf : (d : Proc) -> TypedPath (EdgeType d) -> Continuation d)
    (baseSound : ∀ d, OneDirectionalSound (baseAtomOf d) (continuationOf d))
    (compatible : ∀ d,
      SummaryWindowCompatible (saturationLevel schemeAt base radius k d)
        radius (baseAtomOf d))
    (hradius : endpointPullbackBound radius ≤ radius) :
    JournalAtomsReversalClosureCertificate EdgeType BaseAtom
      In₁ In₂ Out₁ Out₂ Continuation :=
  summaryWindowSetClosureCertificate
    (saturationLevel schemeAt base radius k) radius
    (fun d tuple old =>
      (schemeAt d (paramOf d tuple)).SuccessorWords old)
    baseAtomOf continuationOf baseSound compatible
    (fun d tuple =>
      setPullbackBoundAt_of_stabilization schemeAt base radius hbase hstab d
        (paramOf d tuple))
    hradius

end Tower

end DistributedSynthesis
