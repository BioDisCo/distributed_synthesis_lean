/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderPhases.CoordinatorResponses

/-! Exact finite observation updates with private inputs. The representation
stores two equality relations, not the full local histories. Its size is
bounded only when the number of represented environment histories is bounded. -/
namespace Characterisation
open DistributedSynthesis

abbrev InputShape (H : Type*) := Proc → H → H → Bool

instance inputShape_finite {H : Type*} [Finite H] : Finite (InputShape H) := by
  unfold InputShape
  infer_instance

def RepresentsInputShape {H I₁ I₂ : Type*}
    (past : H → EnvHistory I₁ I₂) (shape : InputShape H) : Prop :=
  ∀ p h k, shape p h k = true ↔ currentView p (past h) = currentView p (past k)

/-- The update uses only equality of old views and fresh input values.
The current graph is used by the compiler to enumerate scenarios; it is not
provided to a process as an observation. -/
def advanceInputShape {H I₁ I₂ : Type*} [DecidableEq I₁] [DecidableEq I₂]
    (shape : InputShape H) : InputShape (NextScenario H I₁ I₂)
  | .one, (h,x,y,g), (k,x',y',z) =>
    match g,z with
    | .right,.right => shape .one h k && decide (x=x')
    | .left,.left | .left,.both | .both,.left | .both,.both =>
        shape .one h k && decide (x=x') && shape .two h k && decide (y=y')
    | _,_ => false
  | .two, (h,x,y,g), (k,x',y',z) =>
    match g,z with
    | .left,.left => shape .two h k && decide (y=y')
    | .right,.right | .right,.both | .both,.right | .both,.both =>
        shape .two h k && decide (y=y') && shape .one h k && decide (x=x')
    | _,_ => false

/-- Exactness holds for all pairs of scenarios, including different graph
slots and different private inputs. -/
theorem advanceInputShape_exact {H I₁ I₂ : Type*} [DecidableEq I₁] [DecidableEq I₂]
    (past : H → EnvHistory I₁ I₂) (shape : InputShape H)
    (represents : RepresentsInputShape past shape) :
    RepresentsInputShape (scenarioHistory past) (advanceInputShape (I₁:=I₁) (I₂:=I₂) shape) := by
  intro p ⟨h,x,y,g⟩ ⟨k,x',y',z⟩
  have one := represents .one h k
  have two := represents .two h k
  change advanceInputShape shape p (h,x,y,g) (k,x',y',z) = true ↔
    currentView p (History.append (past h) ⟨x,y,g,(),()⟩) =
      currentView p (History.append (past k) ⟨x',y',z,(),()⟩)
  cases p
  · rw [currentView_one_append, currentView_one_append]
    cases g <;> cases z <;> simp [advanceInputShape, Proc.other, one, two, and_assoc]
  · rw [currentView_two_append, currentView_two_append]
    cases g <;> cases z <;> simp [advanceInputShape, Proc.other, one, two, and_assoc]

/-- A finite representation exists for every finite family of histories.
Choice is used only to extract semantic equality; the update above is an
explicit Boolean operation. -/
noncomputable def extractInputShape {H I₁ I₂ : Type*}
    (past : H → EnvHistory I₁ I₂) : InputShape H := by
  classical
  exact fun p h k => decide (currentView p (past h) = currentView p (past k))

theorem extractInputShape_exact {H I₁ I₂ : Type*} (past : H → EnvHistory I₁ I₂) :
    RepresentsInputShape past (extractInputShape past) := by
  classical
  intro p h k
  simp [extractInputShape]

def ShapeCoherent {S O₁ O₂ : Type*} (shape : InputShape S)
    (out : S → O₁ × O₂) : Prop :=
  (∀ s t, shape .one s t = true → (out s).1 = (out t).1) ∧
  (∀ s t, shape .two s t = true → (out s).2 = (out t).2)

instance shapeCoherent_decidable {S O₁ O₂ : Type*} [Fintype S]
    [DecidableEq O₁] [DecidableEq O₂] (shape : InputShape S) (out : S → O₁ × O₂) :
    Decidable (ShapeCoherent shape out) := by
  unfold ShapeCoherent
  infer_instance

/-- Executable enumeration of all implementable response assignments from
an observation matrix. No actual histories occur in this enumeration. -/
def admissibleResponses {S O₁ O₂ : Type*} [Fintype S] [DecidableEq S]
    [Fintype O₁] [Fintype O₂] [DecidableEq O₁] [DecidableEq O₂]
    (shape : InputShape S) : Finset (S → O₁ × O₂) :=
  Finset.univ.filter (ShapeCoherent shape)

theorem shapeCoherent_iff_local {S I₁ I₂ O₁ O₂ : Type*}
    [Nonempty O₁] [Nonempty O₂]
    (past : S → EnvHistory I₁ I₂) (shape : InputShape S)
    (represents : RepresentsInputShape past shape) (out : S → O₁ × O₂) :
    ShapeCoherent shape out ↔ ∃ σ : StrategyPair I₁ I₂ O₁ O₂, ∀ s,
      σ.one (currentView .one (past s)) = (out s).1 ∧
      σ.two (currentView .two (past s)) = (out s).2 := by
  constructor
  · intro h
    obtain ⟨one,hOne⟩ := factor_local_response (fun s => currentView .one (past s))
      (fun s => (out s).1) (fun s t eq => h.1 s t ((represents .one s t).mpr eq))
    obtain ⟨two,hTwo⟩ := factor_local_response (fun s => currentView .two (past s))
      (fun s => (out s).2) (fun s t eq => h.2 s t ((represents .two s t).mpr eq))
    exact ⟨⟨one,two⟩,fun s => ⟨hOne s,hTwo s⟩⟩
  · rintro ⟨σ,h⟩
    constructor
    · intro s t eq
      rw [← (h s).1, ← (h t).1, (represents .one s t).mp eq]
    · intro s t eq
      rw [← (h s).2, ← (h t).2, (represents .two s t).mp eq]

theorem admissibleResponses_exact {S I₁ I₂ O₁ O₂ : Type*}
    [Fintype S] [DecidableEq S] [Fintype O₁] [Fintype O₂]
    [DecidableEq O₁] [DecidableEq O₂] [Nonempty O₁] [Nonempty O₂]
    (past : S → EnvHistory I₁ I₂) (shape : InputShape S)
    (represents : RepresentsInputShape past shape) (out : S → O₁ × O₂) :
    out ∈ admissibleResponses shape ↔ ∃ σ : StrategyPair I₁ I₂ O₁ O₂, ∀ s,
      σ.one (currentView .one (past s)) = (out s).1 ∧
      σ.two (currentView .two (past s)) = (out s).2 := by
  simpa only [admissibleResponses, Finset.mem_filter, Finset.mem_univ, true_and]
    using shapeCoherent_iff_local past shape represents out

/-- Restricting to admissible scenarios or renumbering slots preserves exact
observation information. The map need not be injective. -/
def restrictInputShape {H S : Type*} (shape : InputShape H) (f : S → H) : InputShape S :=
  fun p s t => shape p (f s) (f t)

theorem restrictInputShape_exact {H S I₁ I₂ : Type*}
    (past : H → EnvHistory I₁ I₂) (shape : InputShape H)
    (represents : RepresentsInputShape past shape) (f : S → H) :
    RepresentsInputShape (past ∘ f) (restrictInputShape shape f) :=
  fun p s t => represents p (f s) (f t)

end Characterisation
