/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderGame.Encoding.EncodedLeftGraphMemoryNumbering

/-! Exact execution of the generated left memory and checks at every
physical round. The transition tables and state enumeration are the shared
ones; only the complete left-closing restriction is different. -/
namespace Characterisation.EncodedLeftGraphMemory
open DistributedSynthesis
local instance leftRunStateBEq : BEq State := instBEqOfDecidableEq
local instance leftRunLetterBEq : BEq Letter := instBEqOfDecidableEq

variable {H G GQ Q I₁ I₂ O₁ O₂ : Type} {R E V N₁ N₂ P₁ P₂ J S B C d K : Nat}
variable [Fintype H] [Fintype GQ] [Fintype Q]
variable [Fintype I₁] [Fintype I₂] [Fintype O₁] [Fintype O₂]
variable [DecidableEq H] [DecidableEq GQ] [DecidableEq Q]
variable [DecidableEq I₁] [DecidableEq I₂] [DecidableEq O₁] [DecidableEq O₂]
variable (root : H ≃ Fin R) (env : (I₁ × I₂ × Graph) ≃ Fin E)
variable (one : I₁ ≃ Fin N₁) (two : I₂ ≃ Fin N₂)
variable (out : (O₁ × O₂) ≃ Fin V) (outOne : O₁ ≃ Fin P₁) (outTwo : O₂ ≃ Fin P₂)
variable (number : Q ≃ Fin J) (shape : InputShape H)
variable (recognizer : Recognizer Graph GQ) [DecidablePred (· ∈ recognizer.accept)]
variable (graphs : GraphRootState GQ d K ≃ Fin S)
variable (advance : GraphRootState GQ d K → GraphRootState GQ d K)
variable (source : H → GraphRootState GQ d K) (start : H → Q)
variable (bank : ClosingPlanBank H I₂ I₁ O₂ O₁ d) (transitions : EncodedParityTables.Data)
variable (slot : H → Fin (B+1)) (minimum : Q → Fin (C+1))

local notation "swappedEnv" => EncodedBankRoleExchange.environment env
local notation "swappedOut" => EncodedBankRoleExchange.output out
local notation "Memory" => GraphLeaderMemory H GQ Q I₂ I₁ O₂ O₁ d K
local notation "encode" => EncodedGraphMemory.stateEncode root swappedEnv swappedOut number graphs


local notation "input" => dataEncode root env one two out outOne outTwo number shape recognizer graphs advance source start bank transitions slot minimum
local notation "letterCode" => EncodedGraphMemory.letterEncode root swappedEnv swappedOut
variable (size : EncodedParityTables.size transitions = J)
variable (step : Q → (I₁ × I₂ × Graph) → (O₁ × O₂) → Q)
variable (transition : ∀ q r o, EncodedParityTables.next transitions (number q).val
  ((env r).val*V+(out o).val) = (number (step q r o)).val)

include size transition in
theorem restricted_encode (allowed : Finset (LeaderHandover Q B C)) (q : Memory) :
    Restricted input (EncodedGraphMemory.allowedEncode number allowed) (encode q) ↔
      graphClosingOffers recognizer q.1.1 q.1.2.1
        (exchangeShape (jointLeaderShape (exchangeShape shape) q.2.2)) q.2.2
        step q.1.2.2 (closingPolicyOfBank (fun h => exchangePlan (q.2.1 h))) slot minimum ⊆ allowed := by
  have ctx : EncodedGraphMemory.outcomeContext input = (B,J,C) := by
    change (B,EncodedParityTables.size transitions,C) = _
    rw [size]
  have member := collect_member_encode root env one two out outOne outTwo number shape recognizer graphs advance source start bank transitions slot minimum step transition q
  unfold Restricted
  rw [ctx]
  constructor
  · intro checked o ho
    rcases checked (EncodedLeaderAlphabet.outcomeEncode number o) (EncodedLeaderAlphabet.outcomeEncode_mem number o) with absent | present
    · exact False.elim (absent ((member o).mpr ho))
    · exact (EncodedGraphMemory.mem_allowedEncode number allowed o).mp present
  · intro restricted code hc
    obtain ⟨o,rfl⟩ := EncodedLeaderAlphabet.outcomeEncode_sound number code hc
    by_cases offered : EncodedLeaderAlphabet.outcomeEncode number o ∈ EncodedGraphCollector.collect (collector input (encode q))
    · exact Or.inr ((EncodedGraphMemory.mem_allowedEncode number allowed o).mpr (restricted ((member o).mp offered)))
    · exact Or.inl offered

include size transition in
theorem valid_encode (group : H → G) (allowed : Finset (LeaderHandover Q B C)) (q : Memory)
    (a : RealizedBlockRound I₁ I₂ (RollingReceiverOutput H I₂ I₁ O₂ O₁ d) (G → O₂)) :
    valid input (EncodedGraphMemory.allowedEncode number allowed) (encode q) (letterCode group a) = true ↔
      jointLeaderCheck group (exchangeShape shape) q.2 a = true ∧
      leftGraphLeaderCollect shape recognizer step slot minimum q a ⊆ allowed := by
  rw [valid,rolling_encode,Bool.and_eq_true,decide_eq_true_eq,
    restricted_encode root env one two out outOne outTwo number shape recognizer graphs advance source start bank transitions slot minimum size step transition]
  rfl

private theorem map_lookup {X Y : Type} [BEq X] [LawfulBEq X]
    (xs : List X) (f : X → Y) (fallback : Y) (x : X) (member : x ∈ xs) :
    (xs.map f).getD (xs.idxOf x) fallback = f x := by
  have bound := List.idxOf_lt_length_iff.mpr member
  rw [List.getD_eq_getElem _ _ (by simpa only [List.length_map] using bound),List.getElem_map,
    List.getElem_idxOf bound]

include size transition in
omit [Fintype H] [Fintype Q] [Fintype I₁] [Fintype I₂] [Fintype O₁] [Fintype O₂]
    [DecidableEq H] [DecidableEq Q] [DecidableEq I₁] [DecidableEq I₂] [DecidableEq O₁]
    [DecidableEq O₂] in
theorem readNext_encode (group : H → G) (q : Memory)
    (a : RealizedBlockRound I₁ I₂ (RollingReceiverOutput H I₂ I₁ O₂ O₁ d) (G → O₂)) :
    EncodedGraphMemory.readNext input (EncodedGraphMemory.name input (encode q)) (letterCode group a) =
      EncodedGraphMemory.name input (encode (leftGraphLeaderNext group recognizer step advance q a)) := by
  have row := map_lookup (EncodedGraphMemory.letters input)
    (fun a => (EncodedGraphMemory.states input).map (fun q => EncodedGraphMemory.name input (EncodedGraphMemory.next input q a))) []
    (letterCode group a)
    (letterEncode_mem root env one two out outOne outTwo number shape recognizer graphs advance source start bank transitions slot minimum group a)
  have entry := map_lookup (EncodedGraphMemory.states input)
    (fun q => EncodedGraphMemory.name input (EncodedGraphMemory.next input q (letterCode group a))) 0 (encode q)
    ((FiniteCodeNumbering.mem_unique _ _).mpr
      (stateEncode_mem root env one two out outOne outTwo number shape recognizer graphs advance source start bank transitions slot minimum size q))
  unfold EncodedGraphMemory.readNext
  rw [show (EncodedGraphMemory.updates input).getD
    ((EncodedGraphMemory.letters input).idxOf (letterCode group a)) [] = _ from row]
  change (((EncodedGraphMemory.states input).map _).getD ((EncodedGraphMemory.states input).idxOf (encode q)) 0) % _ = _
  rw [entry]
  dsimp only
  rw [next_encode root env one two out outOne outTwo number shape recognizer graphs advance source start bank transitions slot minimum step transition]
  have bound := (stateNumber root env one two out outOne outTwo number shape recognizer graphs advance source start bank transitions slot minimum size
    (leftGraphLeaderNext group recognizer step advance q a)).isLt
  rw [stateNumber_val] at bound
  exact Nat.mod_eq_of_lt bound

include size transition in
theorem readCheck_encode (group : H → G) (allowed : Finset (LeaderHandover Q B C)) (q : Memory)
    (a : RealizedBlockRound I₁ I₂ (RollingReceiverOutput H I₂ I₁ O₂ O₁ d) (G → O₂)) :
    readCheck input (EncodedGraphMemory.allowedEncode number allowed) (EncodedGraphMemory.name input (encode q)) (letterCode group a) = true ↔
      jointLeaderCheck group (exchangeShape shape) q.2 a = true ∧
      leftGraphLeaderCollect shape recognizer step slot minimum q a ⊆ allowed := by
  have row := map_lookup (EncodedGraphMemory.letters input)
    (fun a => (EncodedGraphMemory.states input).map (fun q => valid input (EncodedGraphMemory.allowedEncode number allowed) q a)) []
    (letterCode group a)
    (letterEncode_mem root env one two out outOne outTwo number shape recognizer graphs advance source start bank transitions slot minimum group a)
  have entry := map_lookup (EncodedGraphMemory.states input)
    (fun q => valid input (EncodedGraphMemory.allowedEncode number allowed) q (letterCode group a)) false (encode q)
    ((FiniteCodeNumbering.mem_unique _ _).mpr
      (stateEncode_mem root env one two out outOne outTwo number shape recognizer graphs advance source start bank transitions slot minimum size q))
  unfold readCheck
  rw [show (checks input (EncodedGraphMemory.allowedEncode number allowed)).getD
    ((EncodedGraphMemory.letters input).idxOf (letterCode group a)) [] = _ from row]
  change (((EncodedGraphMemory.states input).map _).getD ((EncodedGraphMemory.states input).idxOf (encode q)) false = true) ↔ _
  rw [entry]
  exact valid_encode root env one two out outOne outTwo number shape recognizer graphs advance source start bank transitions slot minimum size step transition group allowed q a

variable (group : H → G)
include size transition in
omit [Fintype H] [Fintype Q] [Fintype I₁] [Fintype I₂] [Fintype O₁] [Fintype O₂]
    [DecidableEq H] [DecidableEq Q] [DecidableEq I₁] [DecidableEq I₂] [DecidableEq O₁]
    [DecidableEq O₂] in
theorem run_encode (play : Nat → RealizedBlockRound I₁ I₂ (RollingReceiverOutput H I₂ I₁ O₂ O₁ d) (G → O₂)) (n : Nat) :
    phaseMemoryRun (EncodedGraphMemory.start input) (EncodedGraphMemory.readNext input)
      (fun n => letterCode group (play n)) n =
      EncodedGraphMemory.name input (encode (phaseMemoryRun ((source,(fun _ => true),start),bank,true)
        (leftGraphLeaderNext group recognizer step advance) play n)) := by
  induction n with
  | zero =>
    change EncodedGraphMemory.name input (EncodedGraphMemory.initial input) = _
    rw [initial_encode]
    rfl
  | succ n ih =>
    change EncodedGraphMemory.readNext input
      (phaseMemoryRun (EncodedGraphMemory.start input) (EncodedGraphMemory.readNext input)
        (fun n => letterCode group (play n)) n) (letterCode group (play n)) = _
    rw [ih,readNext_encode root env one two out outOne outTwo number shape recognizer graphs advance source start bank transitions slot minimum size step transition]
    rfl

include size transition in
theorem guard_wins_iff (allowed : Finset (LeaderHandover Q B C))
    (phase : BlockRecordMonitor.{0,0,0,0,0} I₁ I₂ (H → O₁) (G → O₂))
    (play : Nat → RealizedBlockRound I₁ I₂ (RollingReceiverOutput H I₂ I₁ O₂ O₁ d) (G → O₂)) :
    (leftGraphGuard group shape recognizer step advance source start bank slot minimum allowed phase).WinsPlay play ↔
      phase.WinsPlay (phasePhysicalPlay Prod.fst play) ∧
      ∀ n, readCheck input (EncodedGraphMemory.allowedEncode number allowed)
        (phaseMemoryRun (EncodedGraphMemory.start input) (EncodedGraphMemory.readNext input)
          (fun n => letterCode group (play n)) n) (letterCode group (play n)) = true := by
  simp only [run_encode root env one two out outOne outTwo number shape recognizer graphs advance source start bank transitions slot minimum size step transition,
    readCheck_encode root env one two out outOne outTwo number shape recognizer graphs advance source start bank transitions slot minimum size step transition]
  simp only [leftGraphGuard,leaderMemoryMonitor_wins_iff,Bool.and_eq_true,decide_eq_true_eq]

end Characterisation.EncodedLeftGraphMemory
