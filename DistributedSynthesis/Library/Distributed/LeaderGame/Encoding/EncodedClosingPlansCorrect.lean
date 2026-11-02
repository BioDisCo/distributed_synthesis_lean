/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderGame.Encoding.EncodedClosingPlans
import DistributedSynthesis.Library.Distributed.LeaderPhases.RollingClosingPlans

/-! The numeric closing-plan table has exactly the existing semantic
scenarios and entries. Its overlap test is the original rolling promise
condition, including every intermediate output position. -/
namespace Characterisation.EncodedClosingPlans
open DistributedSynthesis

variable {I₁ I₂ O₁ O₂ : Type} {E V D : Nat}
  (env : (I₁ × I₂ × Graph) ≃ Fin E)

def scenarioEncode (s : ClosingScenario I₁ I₂ D) : List Nat :=
  List.ofFn (fun i => (env (s.2.2 i)).val)

theorem scenarioEncode_injective : Function.Injective (scenarioEncode (D:=D) env) := by
  rintro ⟨⟨⟩,n,word⟩ ⟨⟨⟩,m,word'⟩ equal
  have lengths := congrArg List.length equal
  simp only [scenarioEncode,List.length_ofFn] at lengths
  have time : n=m := Fin.ext (by omega)
  subst m
  have words : word=word' := by
    funext i
    apply env.injective
    apply Fin.ext
    have entries := congrArg (fun xs : List Nat => xs[i.val]?) equal
    simpa only [scenarioEncode,List.getElem?_ofFn,i.isLt,↓reduceDIte,Option.some.injEq] using entries
  subst word'
  rfl

theorem scenarioEncode_mem (s : ClosingScenario I₁ I₂ D) :
    scenarioEncode env s ∈ rawScenarios (E,D) := by
  apply List.mem_flatMap.mpr
  exact ⟨s.2.1.val,List.mem_range.mpr s.2.1.isLt,FiniteSearch.ofFn_mem_tables _⟩

theorem scenarioEncode_sound (word : List Nat) (member : word ∈ rawScenarios (E,D)) :
    ∃ s : ClosingScenario I₁ I₂ D, scenarioEncode env s = word := by
  obtain ⟨n,hn,hw⟩ := List.mem_flatMap.mp member
  obtain ⟨policy,equal⟩ := (FiniteSearch.mem_tables_iff_policy word).mp hw
  refine ⟨((),⟨⟨n,List.mem_range.mp hn⟩,fun i => env.symm (policy i)⟩),?_⟩
  simpa only [scenarioEncode,Equiv.apply_symm_apply] using equal

noncomputable def scenarioNumber : ClosingScenario I₁ I₂ D ≃ Fin (scenarios (E,D)).length := by
  letI : Fintype (ClosingScenario I₁ I₂ D) :=
    @Fintype.ofEquiv _ _ (inferInstance : Fintype (Unit × Σ n : Fin D, Fin (n.val+1) → Fin E))
      ((Equiv.refl Unit).prodCongr (Equiv.sigmaCongrRight (fun _ => Equiv.arrowCongr (Equiv.refl _) env.symm)))
  exact (FiniteCodeNumbering.equiv (rawScenarios (E,D)) (scenarioEncode env)
    (scenarioEncode_injective env) (scenarioEncode_mem env) (scenarioEncode_sound env)).trans
      (finCongr (by rw [scenarios]))

theorem scenarioNumber_val (s : ClosingScenario I₁ I₂ D) :
    (scenarioNumber env s).val = scenarioName (E,D) (scenarioEncode env s) := rfl

variable (output : (O₁ × O₂) ≃ Fin V)

noncomputable def planEncode (plan : LeaderClosingPlan I₁ I₂ O₁ O₂ D) : Plan :=
  FiniteFunctionCodes.encode (scenarioNumber env) (output ∘ plan)

theorem planEncode_mem (plan : LeaderClosingPlan I₁ I₂ O₁ O₂ D) :
    planEncode env output plan ∈ plans (E,D) V := FiniteFunctionCodes.encode_mem _ _

theorem entry_encode (plan : LeaderClosingPlan I₁ I₂ O₁ O₂ D)
    (s : ClosingScenario I₁ I₂ D) :
    entry (E,D) (planEncode env output plan) (scenarioEncode env s) = (output (plan s)).val :=
  FiniteFunctionCodes.eval_encode (scenarioNumber env) (output ∘ plan) s

theorem planEncode_injective : Function.Injective (planEncode (D:=D) env output) := by
  intro left right equal
  funext s
  apply output.injective
  apply Fin.ext
  have entries := congrArg (fun plan => entry (E,D) plan (scenarioEncode env s)) equal
  simpa only [entry_encode] using entries

theorem planEncode_sound (code : Plan) (member : code ∈ plans (E,D) V) :
    ∃ plan : LeaderClosingPlan I₁ I₂ O₁ O₂ D, planEncode env output plan = code := by
  obtain ⟨policy,equal⟩ := (FiniteSearch.mem_tables_iff_policy code).mp member
  refine ⟨fun s => output.symm (policy (scenarioNumber env s)),?_⟩
  simpa only [planEncode,FiniteFunctionCodes.encode,Function.comp_apply,
    Equiv.apply_symm_apply] using equal

theorem scenarioEncode_prepend (round : I₁ × I₂ × Graph)
    (s : ClosingScenario I₁ I₂ D) :
    scenarioEncode env (prependClosingScenario round s) =
      (env round).val :: scenarioEncode env s := by
  simp [scenarioEncode,prependClosingScenario,List.ofFn_succ]

theorem scenarioEncode_restrict {F : Nat} (bound : D ≤ F)
    (s : ClosingScenario I₁ I₂ D) :
    scenarioEncode env (restrictClosingScenario bound s) = scenarioEncode env s := rfl

/-- No output is moved to a different round: word length remains the
physical distance from the current boundary. -/
theorem overlap_encode (old new : LeaderClosingPlan I₁ I₂ O₁ O₂ (D+1))
    (round : I₁ × I₂ × Graph) :
    overlap ((E,D),planEncode env output old,planEncode env output new,(env round).val) = true ↔
      RollingClosingOverlap old new round := by
  rw [overlap,decide_eq_true_eq]
  constructor
  · intro test
    funext s
    apply output.injective
    apply Fin.ext
    have h := test (scenarioEncode env s)
      (by rw [scenarios,FiniteCodeNumbering.mem_unique]; exact scenarioEncode_mem env s)
    change entry (E,D+1) (planEncode env output old) ((env round).val :: scenarioEncode env s) =
      entry (E,D+1) (planEncode env output new) (scenarioEncode env s) at h
    rw [← scenarioEncode_prepend env round s,entry_encode] at h
    rw [← scenarioEncode_restrict env (Nat.le_succ D) s,entry_encode] at h
    exact h
  · intro equal word member
    rw [scenarios,FiniteCodeNumbering.mem_unique] at member
    obtain ⟨s,rfl⟩ := scenarioEncode_sound (D:=D) env word member
    change entry (E,D+1) (planEncode env output old) ((env round).val :: scenarioEncode env s) =
      entry (E,D+1) (planEncode env output new) (scenarioEncode env s)
    rw [← scenarioEncode_prepend env round s,entry_encode]
    rw [← scenarioEncode_restrict env (Nat.le_succ D) s,entry_encode]
    exact congrArg (fun value => (output value).val) (congrFun equal s)

/-- Consecutive successful numeric tests preserve every originally promised
output, even when arbitrarily many tables are replenished. -/
theorem overlap_preserves_promises
    (plans : Nat → LeaderClosingPlan I₁ I₂ O₁ O₂ (D+1))
    (rounds : Nat → I₁ × I₂ × Graph)
    (tested : ∀ a, overlap ((E,D),planEncode env output (plans a),
      planEncode env output (plans (a+1)),(env (rounds a)).val) = true)
    (a t : Nat) (within : t < D+1) :
    closingPlanEntry (plans a) (fun n => rounds (a+n)) ⟨t,within⟩ =
      closingPlanEntry (plans (a+t)) (fun n => rounds (a+t+n)) ⟨0,by omega⟩ :=
  rollingClosingPlans_preserve_promises plans rounds
    (fun n => (overlap_encode env output _ _ _).mp (tested n)) a t within

end Characterisation.EncodedClosingPlans
