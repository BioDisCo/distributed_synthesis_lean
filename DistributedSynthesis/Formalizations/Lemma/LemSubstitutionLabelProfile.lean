/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import Mathlib.Data.Finset.NAry
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import DistributedSynthesis.Formalizations.Lemma.LemSubstitutiontransducer

/-!
# The boundary-label transition profile of a substitution scheme

Step 2 of the set route for the concrete reversal transduction: enrich
the old-side path summary with the finite boundary-label transition
relation of the substitution transducer.

For a `FiniteSubstitutionScheme` and any evaluation `valueOf` of output
words into a finite carrier `M` that is multiplicative over concatenation,
the **label profile** of an old path assigns to every pair of boundary
labels the finite set of achievable output values of locally uniform
substitutions threading those labels.  The profile is computed by an
ordinary `PathSummarySemigroup` (`profileSummarySemigroup`), and its
value is exact (`mem_profileSummaryValue_iff`): membership is precisely
`LocalFrom`-achievability.  Consequently two old paths with equal profile
summaries admit exactly the same interior label threads with the same
output values (`localFrom_value_iff_of_profile_eq`) -- the mirroring
input needed by the set-level pullback bound
(`SummaryWindowRelSetPullbackBound`).
-/

namespace DistributedSynthesis

universe u v w x

variable {OldEdge : Type u} {NewEdge : Type v} {Label : Type w} {M : Type x}

/-- A finite boundary-label transition profile: for each pair of boundary
labels, the achievable output values. -/
abbrev LabelProfile (Label : Type w) (M : Type x) :=
  Label -> Label -> Finset M

variable [DecidableEq Label] [DecidableEq M]

/-- The profile of the empty path: the diagonal at the empty value. -/
def identityProfile (mone : M) : LabelProfile Label M :=
  fun left right => if left = right then {mone} else ∅

/-- Composition of profiles: thread every intermediate label and multiply
the achievable values. -/
def profileComp [Fintype Label] (mmul : M -> M -> M)
    (P Q : LabelProfile Label M) : LabelProfile Label M :=
  fun left right =>
    (Finset.univ : Finset Label).biUnion fun mid =>
      Finset.image₂ mmul (P left mid) (Q mid right)

omit [DecidableEq Label] in
theorem mem_profileComp [Fintype Label] (mmul : M -> M -> M)
    (P Q : LabelProfile Label M) (left right : Label) (m : M) :
    m ∈ profileComp mmul P Q left right ↔
      ∃ mid m₁ m₂,
        m₁ ∈ P left mid ∧ m₂ ∈ Q mid right ∧ m = mmul m₁ m₂ := by
  simp only [profileComp, Finset.mem_biUnion, Finset.mem_univ, true_and,
    Finset.mem_image₂]
  constructor
  · rintro ⟨mid, m₁, hm₁, m₂, hm₂, rfl⟩
    exact ⟨mid, m₁, m₂, hm₁, hm₂, rfl⟩
  · rintro ⟨mid, m₁, m₂, hm₁, hm₂, rfl⟩
    exact ⟨mid, m₁, hm₁, m₂, hm₂, rfl⟩

namespace FiniteSubstitutionScheme

variable (scheme : FiniteSubstitutionScheme OldEdge NewEdge Label)

/-- The one-edge profile: the achievable output values of the scheme's
choices with the given boundary labels. -/
def edgeProfile (valueOf : List NewEdge -> M) (old : OldEdge) :
    LabelProfile Label M :=
  fun left right =>
    ((Finset.univ : Finset (scheme.Choice old)).filter fun choice =>
        scheme.left old choice = left ∧ scheme.right old choice = right).image
      fun choice => valueOf (scheme.block old choice).toList

theorem mem_edgeProfile (valueOf : List NewEdge -> M) (old : OldEdge)
    (left right : Label) (m : M) :
    m ∈ scheme.edgeProfile valueOf old left right ↔
      ∃ choice : scheme.Choice old,
        scheme.left old choice = left ∧
          scheme.right old choice = right ∧
          valueOf (scheme.block old choice).toList = m := by
  simp only [edgeProfile, Finset.mem_image, Finset.mem_filter,
    Finset.mem_univ, true_and]
  constructor
  · rintro ⟨choice, ⟨hleft, hright⟩, hvalue⟩
    exact ⟨choice, hleft, hright, hvalue⟩
  · rintro ⟨choice, hleft, hright, hvalue⟩
    exact ⟨choice, ⟨hleft, hright⟩, hvalue⟩

omit [DecidableEq Label] [DecidableEq M] in
/-- Locally uniform substitutions decompose at the last old edge. -/
theorem localFrom_snoc (left : Label) (path : List OldEdge) (old : OldEdge)
    (output : List NewEdge) (right : Label) :
    scheme.LocalFrom left (path ++ [old]) output right ↔
      ∃ (mid : Label) (front : List NewEdge) (choice : scheme.Choice old),
        scheme.LocalFrom left path front mid ∧
          scheme.left old choice = mid ∧
          scheme.right old choice = right ∧
          output = front ++ (scheme.block old choice).toList := by
  induction path generalizing left output with
  | nil =>
      constructor
      · rintro ⟨emitted, restOutput, mid, choice, hleft, hemitted, hright,
          ⟨rfl, rfl⟩, rfl⟩
        exact ⟨left, [], choice, ⟨rfl, rfl⟩, hleft, hright, by simp [hemitted]⟩
      · rintro ⟨mid, front, choice, ⟨rfl, rfl⟩, hleft, hright, rfl⟩
        exact ⟨(scheme.block old choice).toList, [], right, choice, hleft,
          rfl, hright, ⟨rfl, rfl⟩, by simp⟩
  | cons head tail ih =>
      constructor
      · rintro ⟨emitted, restOutput, mid, choice, hleft, hemitted, hright,
          hrest, rfl⟩
        rcases (ih mid restOutput).mp hrest with
          ⟨mid', front, choice', hfront, hleft', hright', rfl⟩
        exact ⟨mid', emitted ++ front, choice',
          ⟨emitted, front, mid, choice, hleft, hemitted, hright, hfront, rfl⟩,
          hleft', hright', by simp⟩
      · rintro ⟨mid', front, choice', hfront, hleft', hright', rfl⟩
        rcases hfront with
          ⟨emitted, frontRest, mid, choice, hleft, hemitted, hright, hrest,
            rfl⟩
        exact ⟨emitted, frontRest ++ (scheme.block old choice').toList, mid,
          choice, hleft, hemitted, hright,
          (ih mid (frontRest ++ (scheme.block old choice').toList)).mpr
            ⟨mid', frontRest, choice', hrest, hleft', hright', rfl⟩,
          by simp⟩

variable [Fintype Label] [Fintype M]

/-- The boundary-label transition profile as an ordinary path-summary
semigroup over old edges. -/
def profileSummarySemigroup (valueOf : List NewEdge -> M) (mone : M)
    (mmul : M -> M -> M) :
    PathSummarySemigroup.{u, max w x} OldEdge where
  Summary := LabelProfile Label M
  summaryFinite := inferInstance
  empty := identityProfile mone
  ofEdge := scheme.edgeProfile valueOf
  multiply := profileComp mmul

@[simp]
theorem profileSummaryValue_nil (valueOf : List NewEdge -> M) (mone : M)
    (mmul : M -> M -> M) :
    pathSummaryValue (scheme.profileSummarySemigroup valueOf mone mmul) [] =
      identityProfile mone :=
  rfl

theorem profileSummaryValue_snoc (valueOf : List NewEdge -> M) (mone : M)
    (mmul : M -> M -> M) (path : List OldEdge) (old : OldEdge) :
    pathSummaryValue (scheme.profileSummarySemigroup valueOf mone mmul)
        (path ++ [old]) =
      profileComp mmul
        (pathSummaryValue (scheme.profileSummarySemigroup valueOf mone mmul)
          path)
        (scheme.edgeProfile valueOf old) := by
  simp [pathSummaryValue, List.foldl_append, profileSummarySemigroup]

/-- **Exactness of the label profile**: membership in the profile summary
of an old path is precisely `LocalFrom`-achievability of the value. -/
theorem mem_profileSummaryValue_iff (valueOf : List NewEdge -> M) (mone : M)
    (mmul : M -> M -> M)
    (hnil : valueOf [] = mone)
    (happend : ∀ xs ys, valueOf (xs ++ ys) = mmul (valueOf xs) (valueOf ys))
    (path : List OldEdge) (left right : Label) (m : M) :
    m ∈ pathSummaryValue (scheme.profileSummarySemigroup valueOf mone mmul)
        path left right ↔
      ∃ output : List NewEdge,
        scheme.LocalFrom left path output right ∧ valueOf output = m := by
  induction path using List.reverseRecOn generalizing right m with
  | nil =>
      constructor
      · intro hm
        rw [profileSummaryValue_nil] at hm
        unfold identityProfile at hm
        by_cases hlr : left = right
        · rw [if_pos hlr, Finset.mem_singleton] at hm
          subst hlr
          exact ⟨[], ⟨rfl, rfl⟩, hnil.trans hm.symm⟩
        · rw [if_neg hlr] at hm
          exact absurd hm (Finset.notMem_empty m)
      · rintro ⟨output, ⟨rfl, rfl⟩, rfl⟩
        rw [profileSummaryValue_nil]
        unfold identityProfile
        rw [if_pos rfl, Finset.mem_singleton, hnil]
  | append_singleton path old ih =>
      rw [profileSummaryValue_snoc]
      rw [mem_profileComp]
      constructor
      · rintro ⟨mid, m₁, m₂, hm₁, hm₂, rfl⟩
        rcases (ih mid m₁).mp hm₁ with ⟨front, hfront, rfl⟩
        rcases (scheme.mem_edgeProfile valueOf old mid right m₂).mp hm₂ with
          ⟨choice, hleft, hright, rfl⟩
        exact ⟨front ++ (scheme.block old choice).toList,
          (scheme.localFrom_snoc left path old _ right).mpr
            ⟨mid, front, choice, hfront, hleft, hright, rfl⟩,
          happend _ _⟩
      · rintro ⟨output, hlocal, rfl⟩
        rcases (scheme.localFrom_snoc left path old output right).mp hlocal
          with ⟨mid, front, choice, hfront, hleft, hright, rfl⟩
        exact ⟨mid, valueOf front,
          valueOf (scheme.block old choice).toList,
          (ih mid (valueOf front)).mpr ⟨front, hfront, rfl⟩,
          (scheme.mem_edgeProfile valueOf old mid right _).mpr
            ⟨choice, hleft, hright, rfl⟩,
          happend _ _⟩

/-- **The mirroring interface**: two old paths with equal profile
summaries admit exactly the same locally uniform substitution outcomes,
label pair and output value alike. -/
theorem localFrom_value_iff_of_profile_eq (valueOf : List NewEdge -> M)
    (mone : M) (mmul : M -> M -> M)
    (hnil : valueOf [] = mone)
    (happend : ∀ xs ys, valueOf (xs ++ ys) = mmul (valueOf xs) (valueOf ys))
    {path₁ path₂ : List OldEdge}
    (hprofile :
      pathSummaryValue (scheme.profileSummarySemigroup valueOf mone mmul)
          path₁ =
        pathSummaryValue (scheme.profileSummarySemigroup valueOf mone mmul)
          path₂)
    (left right : Label) (m : M) :
    (∃ output, scheme.LocalFrom left path₁ output right ∧
        valueOf output = m) ↔
      ∃ output, scheme.LocalFrom left path₂ output right ∧
        valueOf output = m := by
  rw [<- scheme.mem_profileSummaryValue_iff valueOf mone mmul hnil happend,
    <- scheme.mem_profileSummaryValue_iff valueOf mone mmul hnil happend,
    hprofile]

end FiniteSubstitutionScheme

end DistributedSynthesis
