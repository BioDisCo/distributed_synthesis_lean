/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemSubstitutionLabelProfile
import DistributedSynthesis.Formalizations.Lemma.LemSummaryWindowRelationalClosure

/-!
# The window-valued label profile and the concrete set pullback bound

Step 1 of the set route.  The decisive simplification: instantiate the
boundary-label profile of `LemSubstitutionLabelProfile` with the finite
summary-window value itself as the carrier.  The profile of an old path
then lists, per boundary-label pair, exactly the achievable output
*windows* -- so the image of output windows over all locally uniform
substitutions is a function of the profile alone
(`substitution_windowImage_eq_of_profile_eq`), and the set-level
pullback bound follows with no mirroring geometry
(`substitution_setPullbackBound`).

The only algebraic input is that finite summary-window values compose
over concatenation (`finiteSummaryWindowAbstraction_append`), which
requires the new-side summary semigroup to be lawful (associative with
neutral empty) -- the explicit lawfulness requirement of the set route.
-/

namespace DistributedSynthesis

universe u v w x

/-! ### List window arithmetic -/

section ListWindows

variable {α : Type u}

theorem prefixAtMost_append (c : Nat) (xs ys : List α) :
    prefixAtMost c (xs ++ ys) =
      prefixAtMost c (prefixAtMost c xs ++ prefixAtMost c ys) := by
  simp only [prefixAtMost, List.take_append, List.take_take, List.length_take,
    Nat.min_self]
  congr 2
  omega

theorem suffixAtMost_length (c : Nat) (xs : List α) :
    (suffixAtMost c xs).length = min c xs.length := by
  simp only [suffixAtMost, List.length_drop]
  omega

theorem prefixAtMost_reverse (c : Nat) (l : List α) :
    prefixAtMost c l.reverse = (suffixAtMost c l).reverse := by
  simp [prefixAtMost, suffixAtMost, List.take_reverse]

theorem suffixAtMost_append (c : Nat) (xs ys : List α) :
    suffixAtMost c (xs ++ ys) =
      suffixAtMost c (suffixAtMost c xs ++ suffixAtMost c ys) := by
  have h : ∀ l : List α,
      suffixAtMost c l = (prefixAtMost c l.reverse).reverse := by
    intro l
    rw [prefixAtMost_reverse, List.reverse_reverse]
  rw [h (xs ++ ys), h (suffixAtMost c xs ++ suffixAtMost c ys),
    List.reverse_append, List.reverse_append,
    prefixAtMost_append c ys.reverse xs.reverse,
    prefixAtMost_reverse c ys, prefixAtMost_reverse c xs]

end ListWindows

/-! ### The finite window monoid -/

section WindowMonoid

variable {EdgeType : Type u}
  (S : PathSummarySemigroup.{u, v} EdgeType) (c : Nat)

/-- The window of the empty path. -/
def windowOne : FiniteSummaryWindowValue S.Summary EdgeType c :=
  finiteSummaryWindowAbstraction S c []

/-- Composition of finite summary-window values: multiply the summaries
and re-window the concatenated endpoint windows. -/
def windowMul (a b : FiniteSummaryWindowValue S.Summary EdgeType c) :
    FiniteSummaryWindowValue S.Summary EdgeType c :=
  (S.multiply a.1 b.1,
    boundedEndpointWindowOfList c
      (prefixAtMost c (a.2.1.toList ++ b.2.1.toList)) (by simp [prefixAtMost]),
    boundedEndpointWindowOfList c
      (suffixAtMost c (a.2.2.toList ++ b.2.2.toList)) (by
        rw [suffixAtMost_length]
        omega))

/-- Lawfulness of the underlying summary semigroup. -/
structure PathSummaryLawful : Prop where
  assoc : ∀ a b d : S.Summary,
    S.multiply (S.multiply a b) d = S.multiply a (S.multiply b d)
  one_mul : ∀ a : S.Summary, S.multiply S.empty a = a
  mul_one : ∀ a : S.Summary, S.multiply a S.empty = a

/-- The path summary of a lawful semigroup is multiplicative over
concatenation. -/
theorem pathSummaryValue_append (hlaw : PathSummaryLawful S)
    (xs ys : TypedPath EdgeType) :
    pathSummaryValue S (xs ++ ys) =
      S.multiply (pathSummaryValue S xs) (pathSummaryValue S ys) := by
  have hgen : ∀ (ys : List EdgeType) (a : S.Summary),
      ys.foldl (fun acc edge => S.multiply acc (S.ofEdge edge)) a =
        S.multiply a (pathSummaryValue S ys) := by
    intro ys
    induction ys with
    | nil => intro a; exact (hlaw.mul_one a).symm
    | cons y ys ih =>
        intro a
        show (ys.foldl _ (S.multiply a (S.ofEdge y))) = _
        rw [ih (S.multiply a (S.ofEdge y))]
        have hy : pathSummaryValue S (y :: ys) =
            S.multiply (S.ofEdge y) (pathSummaryValue S ys) := by
          show (ys.foldl _ (S.multiply S.empty (S.ofEdge y))) = _
          rw [hlaw.one_mul, ih (S.ofEdge y)]
        rw [hy, hlaw.assoc]
  rw [pathSummaryValue, List.foldl_append]
  exact hgen ys (pathSummaryValue S xs)

/-- The finite window abstraction is multiplicative over concatenation. -/
theorem finiteSummaryWindowAbstraction_append (hlaw : PathSummaryLawful S)
    (xs ys : TypedPath EdgeType) :
    finiteSummaryWindowAbstraction S c (xs ++ ys) =
      windowMul S c (finiteSummaryWindowAbstraction S c xs)
        (finiteSummaryWindowAbstraction S c ys) := by
  unfold finiteSummaryWindowAbstraction windowMul
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · exact pathSummaryValue_append S hlaw xs ys
  · apply BoundedEndpointWindow.toList_injective
    simp only [boundedPrefixAtMost_toList, boundedEndpointWindowOfList_toList]
    exact prefixAtMost_append c xs ys
  · apply BoundedEndpointWindow.toList_injective
    simp only [boundedSuffixAtMost_toList, boundedEndpointWindowOfList_toList]
    exact suffixAtMost_append c xs ys

@[simp]
theorem finiteSummaryWindowAbstraction_nil :
    finiteSummaryWindowAbstraction S c [] = windowOne S c :=
  rfl

end WindowMonoid

/-! ### The concrete set pullback bound -/

section SetBound

variable {OldEdge : Type u} {NewEdge : Type v} {Label : Type w}
variable [Fintype Label] [DecidableEq Label]
variable (scheme : FiniteSubstitutionScheme OldEdge NewEdge Label)
variable (Snew : PathSummarySemigroup.{v, x} NewEdge)
variable [Fintype NewEdge] [DecidableEq NewEdge] [DecidableEq Snew.Summary]
variable (radius : Nat)

/-- The window-valued profile semigroup of the scheme: per boundary-label
pair, the achievable output windows at the given radius. -/
noncomputable def windowProfileSemigroup :
    PathSummarySemigroup.{u, max w v x} OldEdge :=
  scheme.profileSummarySemigroup
    (finiteSummaryWindowAbstraction Snew radius)
    (windowOne Snew radius) (windowMul Snew radius)

omit [Fintype NewEdge] [DecidableEq NewEdge] [DecidableEq Snew.Summary] in
/-- The raw summary window of an output path is recovered from its finite
window value. -/
theorem summaryWindowAbstraction_eq_ofFinite (out : TypedPath NewEdge) :
    summaryWindowAbstraction Snew radius out =
      { summary := (finiteSummaryWindowAbstraction Snew radius out).1
        pref := (finiteSummaryWindowAbstraction Snew radius out).2.1.toList
        suff := (finiteSummaryWindowAbstraction Snew radius out).2.2.toList } := by
  simp [summaryWindowAbstraction, finiteSummaryWindowAbstraction]

/-- **The output-window image is a function of the window profile**: two
old paths with equal window-profile summaries have equal images of raw
output windows over all locally uniform substitutions. -/
theorem substitution_windowImage_eq_of_profile_eq
    (hlaw : PathSummaryLawful Snew)
    {old₁ old₂ : TypedPath OldEdge}
    (hprofile :
      pathSummaryValue (windowProfileSemigroup scheme Snew radius) old₁ =
        pathSummaryValue (windowProfileSemigroup scheme Snew radius) old₂) :
    (summaryWindowAbstraction Snew radius) '' scheme.SuccessorWords old₁ =
      (summaryWindowAbstraction Snew radius) '' scheme.SuccessorWords old₂ := by
  have hfinite :
      ∀ old : TypedPath OldEdge,
        (finiteSummaryWindowAbstraction Snew radius) ''
            scheme.SuccessorWords old =
          { value |
            ∃ left right,
              value ∈
                pathSummaryValue (windowProfileSemigroup scheme Snew radius)
                  old left right } := by
    intro old
    ext value
    constructor
    · rintro ⟨out, ⟨left, right, hlocal⟩, rfl⟩
      exact ⟨left, right,
        (scheme.mem_profileSummaryValue_iff _ _ _
            (finiteSummaryWindowAbstraction_nil Snew radius)
            (finiteSummaryWindowAbstraction_append Snew radius hlaw)
            old left right _).mpr ⟨out, hlocal, rfl⟩⟩
    · rintro ⟨left, right, hmem⟩
      rcases (scheme.mem_profileSummaryValue_iff _ _ _
          (finiteSummaryWindowAbstraction_nil Snew radius)
          (finiteSummaryWindowAbstraction_append Snew radius hlaw)
          old left right value).mp hmem with ⟨out, hlocal, rfl⟩
      exact ⟨out, ⟨left, right, hlocal⟩, rfl⟩
  have hraw :
      ∀ old : TypedPath OldEdge,
        (summaryWindowAbstraction Snew radius) '' scheme.SuccessorWords old =
          (fun value : FiniteSummaryWindowValue Snew.Summary NewEdge radius =>
              SummaryWindowValue.mk value.1 value.2.1.toList
                value.2.2.toList) ''
            ((finiteSummaryWindowAbstraction Snew radius) ''
              scheme.SuccessorWords old) := by
    intro old
    rw [<- Set.image_comp]
    apply Set.image_congr
    intro out _
    exact summaryWindowAbstraction_eq_ofFinite Snew radius out
  rw [hraw, hraw, hfinite, hfinite, hprofile]

/-- **Step 1, concrete form**: with the old-side summary refined by the
window profile, the substitution relation satisfies the set-level
pullback bound at the profile's radius -- for every pullback stability
margin, since the profile is read off the summary component alone. -/
theorem substitution_setPullbackBound (hlaw : PathSummaryLawful Snew)
    (bound : Nat)
    {old₁ old₂ : TypedPath OldEdge}
    (hwindow :
      summaryWindowAbstraction (windowProfileSemigroup scheme Snew radius)
          bound old₁ =
        summaryWindowAbstraction (windowProfileSemigroup scheme Snew radius)
          bound old₂) :
    (summaryWindowAbstraction Snew radius) '' scheme.SuccessorWords old₁ =
      (summaryWindowAbstraction Snew radius) '' scheme.SuccessorWords old₂ :=
  substitution_windowImage_eq_of_profile_eq scheme Snew radius hlaw
    (congrArg SummaryWindowValue.summary hwindow)

end SetBound

end DistributedSynthesis
