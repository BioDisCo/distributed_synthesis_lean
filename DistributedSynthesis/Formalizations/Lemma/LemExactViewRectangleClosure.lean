/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledExactViewTree

/-!
# One-step rectangle closure of exact view pairs

This file isolates the constructor-level fact behind the rectangle-free
analysis of the delay-one model.  Starting from an arbitrary relation on old
view pairs, one exact environment step cannot create a non-degenerate
`2 × 2` rectangle.  No finiteness, strategy, or automaton assumption is used.

The module is deliberately standalone: it is a substantive closure lemma for
the exact operational transition, not an additional uniformization interface.
-/

namespace DistributedSynthesis

universe u v w z

open DetParityAutomaton

/-- A binary relation has no `2 × 2` rectangle with distinct rows and columns. -/
def RectangleFree {Left : Type w} {Right : Type z}
    (relation : Left → Right → Prop) : Prop :=
  ∀ {left₀ left₁ right₀ right₁},
    relation left₀ right₀ →
      relation left₀ right₁ →
      relation left₁ right₀ →
      relation left₁ right₁ →
      left₀ = left₁ ∨ right₀ = right₁

/--
The relation obtained by applying one exact environment step to every pair in
an arbitrary old relation.
-/
def ViewPairOneStepImage
    {In₁ : Type u} {In₂ : Type v}
    (oldRelation :
      View In₁ In₂ Proc.one → View In₁ In₂ Proc.two → Prop) :
    View In₁ In₂ Proc.one → View In₁ In₂ Proc.two → Prop :=
  fun nextOne nextTwo ↦
    ∃ oldOne oldTwo env,
      oldRelation oldOne oldTwo ∧
        advanceViewsWithEnvironment (oldOne, oldTwo) env = (nextOne, nextTwo)

/--
One delay-one view update maps every old relation to a rectangle-free relation.

The result is independent of the old relation.  It follows solely from the
disjointness and injectivity of `View.recv` and `View.noRecv` in the three graph
cases.
-/
theorem viewPairOneStepImage_rectangleFree
    {In₁ : Type u} {In₂ : Type v}
    (oldRelation :
      View In₁ In₂ Proc.one → View In₁ In₂ Proc.two → Prop) :
    RectangleFree (ViewPairOneStepImage oldRelation) := by
  intro left₀ left₁ right₀ right₁ h₀₀ h₀₁ h₁₀ h₁₁
  rcases h₀₀ with ⟨oldOne₀₀, oldTwo₀₀, ⟨inputOne₀₀, inputTwo₀₀, graph₀₀⟩,
    _, h₀₀⟩
  rcases h₀₁ with ⟨oldOne₀₁, oldTwo₀₁, ⟨inputOne₀₁, inputTwo₀₁, graph₀₁⟩,
    _, h₀₁⟩
  rcases h₁₀ with ⟨oldOne₁₀, oldTwo₁₀, ⟨inputOne₁₀, inputTwo₁₀, graph₁₀⟩,
    _, h₁₀⟩
  rcases h₁₁ with ⟨oldOne₁₁, oldTwo₁₁, ⟨inputOne₁₁, inputTwo₁₁, graph₁₁⟩,
    _, h₁₁⟩
  cases graph₀₀ <;>
    cases graph₀₁ <;>
    cases graph₁₀ <;>
    cases graph₁₁ <;>
    simp only [advanceViewsWithEnvironment, Prod.mk.injEq] at h₀₀ h₀₁ h₁₀ h₁₁ <;>
    aesop

/-! ## The actual reachable relation at a fixed depth -/

/-- The exact-view prefix fold extends by one round, without typeclass assumptions. -/
theorem exactViewsAfterEnvironmentPrefix_snoc_unconditional
    {In₁ : Type u} {In₂ : Type v}
    (envs : List (EnvironmentRound In₁ In₂))
    (env : EnvironmentRound In₁ In₂) :
    exactViewsAfterEnvironmentPrefix (envs ++ [env]) =
      advanceViewsWithEnvironment
        (exactViewsAfterEnvironmentPrefix envs) env := by
  simp [exactViewsAfterEnvironmentPrefix, List.foldl_append]

/--
The exact pairs of local views reachable after exactly `depth` environment
rounds.  The successor clause is intentionally the genuine one-step image,
so it retains all old pairs rather than presupposing any finite abstraction.
-/
def ExactViewPairReachableAt
    {In₁ : Type u} {In₂ : Type v} :
    Nat → View In₁ In₂ Proc.one → View In₁ In₂ Proc.two → Prop
  | 0, viewOne, viewTwo =>
      viewOne = .empty Proc.one ∧ viewTwo = .empty Proc.two
  | depth + 1, viewOne, viewTwo =>
      ViewPairOneStepImage (ExactViewPairReachableAt depth) viewOne viewTwo

/-- Unfold the successor layer of exact reachability. -/
theorem exactViewPairReachableAt_succ
    {In₁ : Type u} {In₂ : Type v}
    (depth : Nat) :
    ExactViewPairReachableAt (In₁ := In₁) (In₂ := In₂) (depth + 1) =
      ViewPairOneStepImage (ExactViewPairReachableAt depth) :=
  rfl

/--
Recursive exact reachability is precisely reachability by an environment
prefix of the indicated length.
-/
theorem exactViewPairReachableAt_iff_exists_environmentPrefix
    {In₁ : Type u} {In₂ : Type v}
    (depth : Nat)
    (viewOne : View In₁ In₂ Proc.one)
    (viewTwo : View In₁ In₂ Proc.two) :
    ExactViewPairReachableAt depth viewOne viewTwo ↔
      ∃ envs : List (EnvironmentRound In₁ In₂),
        envs.length = depth ∧
          exactViewsAfterEnvironmentPrefix envs = (viewOne, viewTwo) := by
  induction depth generalizing viewOne viewTwo with
  | zero =>
      simp [ExactViewPairReachableAt, exactViewsAfterEnvironmentPrefix, eq_comm]
  | succ depth ih =>
      constructor
      · intro hreach
        change
          ViewPairOneStepImage (ExactViewPairReachableAt depth)
            viewOne viewTwo at hreach
        rcases hreach with ⟨oldOne, oldTwo, env, hOld, hStep⟩
        rcases (ih oldOne oldTwo).mp hOld with ⟨envs, hLength, hViews⟩
        refine ⟨envs ++ [env], ?_, ?_⟩
        · simp [hLength]
        · rw [exactViewsAfterEnvironmentPrefix_snoc_unconditional, hViews]
          exact hStep
      · rintro ⟨envs, hLength, hViews⟩
        rcases List.eq_nil_or_concat envs with rfl | ⟨envPrefix, env, hConcat⟩
        · simp at hLength
        · rw [List.concat_eq_append] at hConcat
          subst envs
          have hPrefixLength : envPrefix.length = depth := by
            simpa using hLength
          change
            ViewPairOneStepImage (ExactViewPairReachableAt depth)
              viewOne viewTwo
          refine
            ⟨ (exactViewsAfterEnvironmentPrefix envPrefix).1,
              (exactViewsAfterEnvironmentPrefix envPrefix).2, env, ?_, ?_ ⟩
          · apply (ih _ _).mpr
            exact ⟨envPrefix, hPrefixLength, rfl⟩
          · rw [exactViewsAfterEnvironmentPrefix_snoc_unconditional] at hViews
            simpa using hViews

/-- Every positive-depth exact reachable view-pair relation is rectangle-free. -/
theorem exactViewPairReachableAt_succ_rectangleFree
    {In₁ : Type u} {In₂ : Type v}
    (depth : Nat) :
    RectangleFree
      (ExactViewPairReachableAt
        (In₁ := In₁) (In₂ := In₂) (depth + 1)) := by
  rw [exactViewPairReachableAt_succ]
  exact viewPairOneStepImage_rectangleFree _

end DistributedSynthesis
