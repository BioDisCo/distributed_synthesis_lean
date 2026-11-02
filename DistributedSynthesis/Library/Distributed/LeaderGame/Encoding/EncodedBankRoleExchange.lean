/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderGame.Encoding.EncodedClosingBanksCorrect
import DistributedSynthesis.Library.Distributed.LeaderGame.RoleExchange

/-! Exchange the local interpretation of a closing bank while retaining
its numeric scenario and output indices. This lets a left leader use the
original recognizer's graph memory and complete closing collector. -/
namespace Characterisation.EncodedBankRoleExchange
open DistributedSynthesis
attribute [local irreducible] Primrec

def graph (g : Nat) := if g=0 then 2 else if g=2 then 0 else g
def round (r : EncodedClosingObservations.Round) : EncodedClosingObservations.Round := (r.2.1,r.1,graph r.2.2)
def bankData (b : EncodedClosingBanks.Data) : EncodedClosingBanks.Data :=
  (b.1,b.2.1,(EncodedClosingBanks.roundTable b).map round,
    (EncodedClosingBanks.outputTable b).map Prod.swap,(EncodedClosingBanks.matrix b).map Prod.swap)

theorem graph_primrec : Primrec graph :=
  Primrec.ite (Primrec.eq.comp Primrec.id (Primrec.const 0)) (Primrec.const 2)
    (Primrec.ite (Primrec.eq.comp Primrec.id (Primrec.const 2)) (Primrec.const 0) Primrec.id)
theorem round_primrec : Primrec round := (Primrec.fst.comp Primrec.snd).pair
  (Primrec.fst.pair (graph_primrec.comp (Primrec.snd.comp Primrec.snd)))
theorem bankData_primrec : Primrec bankData := Primrec.fst.pair ((Primrec.fst.comp Primrec.snd).pair
  ((Primrec.list_map EncodedClosingBanks.roundTable_primrec (round_primrec.comp Primrec.snd).to₂).pair
    ((Primrec.list_map EncodedClosingBanks.outputTable_primrec ((Primrec.snd.pair Primrec.fst).comp Primrec.snd).to₂).pair
      (Primrec.list_map EncodedClosingBanks.matrix_primrec ((Primrec.snd.pair Primrec.fst).comp Primrec.snd).to₂))))

theorem graph_twice (g : Nat) : graph (graph g) = g := by
  by_cases h : g=0
  · subst g; rfl
  by_cases h2 : g=2
  · subst g; rfl
  simp [graph,h,h2]
theorem round_twice (r : EncodedClosingObservations.Round) : round (round r) = r := by
  simp [round,graph_twice]
theorem bankData_twice (b : EncodedClosingBanks.Data) : bankData (bankData b) = b := by
  simp [bankData,EncodedClosingBanks.roundTable,EncodedClosingBanks.outputTable,EncodedClosingBanks.matrix,
    List.map_map,Function.comp_def,round_twice]

variable {H I₁ I₂ O₁ O₂ : Type} {R E V N₁ N₂ P₁ P₂ D : Nat}

def inputEquiv : (I₂ × I₁ × Graph) ≃ (I₁ × I₂ × Graph) where
  toFun := exchangeInput
  invFun := exchangeInput
  left_inv := exchangeInput_twice
  right_inv := exchangeInput_twice

def environment (env : (I₁ × I₂ × Graph) ≃ Fin E) : (I₂ × I₁ × Graph) ≃ Fin E := inputEquiv.trans env
def output (out : (O₁ × O₂) ≃ Fin V) : (O₂ × O₁) ≃ Fin V := (Equiv.prodComm _ _).trans out

variable (root : H ≃ Fin R) (env : (I₁ × I₂ × Graph) ≃ Fin E)
variable (one : I₁ ≃ Fin N₁) (two : I₂ ≃ Fin N₂)
variable (out : (O₁ × O₂) ≃ Fin V) (outOne : O₁ ≃ Fin P₁) (outTwo : O₂ ≃ Fin P₂)

@[simp] theorem environment_apply (r : I₂ × I₁ × Graph) : environment env r = env (exchangeInput r) := rfl
@[simp] theorem output_apply (a : O₂ × O₁) : output out a = out a.swap := rfl

theorem environment_twice : environment (environment env) = env := by
  ext r
  simp only [environment_apply,exchangeInput_twice]

theorem output_twice : output (output out) = out := by
  ext a
  rfl

theorem round_encode (r : I₁ × I₂ × Graph) : round (EncodedClosingObservations.roundEncode one two r) =
    EncodedClosingObservations.roundEncode two one (exchangeInput r) := by
  rcases r with ⟨i,j,g⟩
  cases g <;> rfl

theorem bankData_encode (shape : InputShape H) :
    bankData (EncodedClosingBanks.dataEncode root env one two out outOne outTwo shape D) =
      EncodedClosingBanks.dataEncode root (environment env) two one (output out) outTwo outOne (exchangeShape shape) D := by
  simp only [bankData,EncodedClosingBanks.dataEncode,EncodedClosingBanks.roundTable,EncodedClosingBanks.outputTable,
    EncodedClosingBanks.matrix,List.map_ofFn]
  apply Prod.ext
  · rfl
  apply Prod.ext
  · rfl
  apply Prod.ext
  · apply congrArg List.ofFn
    funext i
    exact round_encode one two (env.symm i)
  · rfl

theorem scenarioEncode_exchange (s : ClosingScenario I₁ I₂ D) :
    EncodedClosingPlans.scenarioEncode (environment env) (exchangeScenario s) =
      EncodedClosingPlans.scenarioEncode env s := by
  simp only [EncodedClosingPlans.scenarioEncode,exchangeScenario,environment_apply,exchangeInput_twice]

theorem scenarioNumber_exchange (s : ClosingScenario I₁ I₂ D) :
    EncodedClosingPlans.scenarioNumber (environment env) (exchangeScenario s) =
      EncodedClosingPlans.scenarioNumber env s := by
  apply Fin.ext
  simp only [EncodedClosingPlans.scenarioNumber_val,scenarioEncode_exchange]

theorem planEncode_exchange (plan : LeaderClosingPlan I₁ I₂ O₁ O₂ D) :
    EncodedClosingPlans.planEncode (environment env) (output out) (exchangePlan plan) =
      EncodedClosingPlans.planEncode env out plan := by
  unfold EncodedClosingPlans.planEncode FiniteFunctionCodes.encode
  apply congrArg List.ofFn
  funext i
  have inverse : (EncodedClosingPlans.scenarioNumber (environment env)).symm i =
      exchangeScenario ((EncodedClosingPlans.scenarioNumber env).symm i) := by
    apply (EncodedClosingPlans.scenarioNumber (environment env)).injective
    rw [Equiv.apply_symm_apply,scenarioNumber_exchange,Equiv.apply_symm_apply]
  rw [inverse]
  simp only [Function.comp_apply,exchangePlan,exchangeScenario_twice,output_apply,Prod.swap_swap]

theorem bankEncode_exchange (bank : H → LeaderClosingPlan I₁ I₂ O₁ O₂ D) :
    EncodedClosingBanks.bankEncode root (environment env) (output out) (fun h => exchangePlan (bank h)) =
      EncodedClosingBanks.bankEncode root env out bank := by
  unfold EncodedClosingBanks.bankEncode
  simp only [planEncode_exchange]

theorem bankEncode_unexchange (bank : H → LeaderClosingPlan I₂ I₁ O₂ O₁ D) :
    EncodedClosingBanks.bankEncode root env out (fun h => exchangePlan (bank h)) =
      EncodedClosingBanks.bankEncode root (environment env) (output out) bank := by
  have h := bankEncode_exchange root env out (fun h => exchangePlan (bank h))
  simpa only [exchangePlan_twice] using h.symm

end Characterisation.EncodedBankRoleExchange
