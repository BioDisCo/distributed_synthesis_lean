/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderGame.Encoding.EncodedGraphMemoryNumbering

/-! Exact complete closing restrictions and correctness of every generated
memory-table entry. The tested outcomes range over the full numbered
outcome alphabet, not independently chosen target-root entries. -/
namespace Characterisation.EncodedGraphMemory
open DistributedSynthesis
local instance checkStateBEq : BEq State := instBEqOfDecidableEq
local instance checkLetterBEq : BEq Letter := instBEqOfDecidableEq

variable {H G GQ Q I₁ I₂ O₁ O₂ : Type} {R E V N₁ N₂ P₁ P₂ J S B C d K : Nat}
variable [Fintype H] [Fintype GQ] [Fintype Q]
variable [Fintype I₁] [Fintype I₂] [Fintype O₁] [Fintype O₂]
variable [DecidableEq H] [DecidableEq GQ] [DecidableEq Q]
variable [DecidableEq I₁] [DecidableEq I₂] [DecidableEq O₁] [DecidableEq O₂]
variable (root : H ≃ Fin R) (env : (I₁ × I₂ × Graph) ≃ Fin E)
variable (one : I₁ ≃ Fin N₁) (two : I₂ ≃ Fin N₂)
variable (output : (O₁ × O₂) ≃ Fin V) (outOne : O₁ ≃ Fin P₁) (outTwo : O₂ ≃ Fin P₂)
variable (number : Q ≃ Fin J) (shape : InputShape H)
variable (recognizer : Recognizer Graph GQ) [DecidablePred (· ∈ recognizer.accept)]
variable (graphs : GraphRootState GQ d K ≃ Fin S)
variable (advance : GraphRootState GQ d K → GraphRootState GQ d K)
variable (source : H → GraphRootState GQ d K) (start : H → Q)
variable (bank : ClosingPlanBank H I₁ I₂ O₁ O₂ d) (transitions : EncodedParityTables.Data)
variable (slot : H → Fin (B+1)) (minimum : Q → Fin (C+1))


local notation "input" => dataEncode root env one two output outOne outTwo number shape recognizer graphs advance source start bank transitions slot minimum
local notation "encode" => stateEncode root env output number graphs
local notation "Memory" => GraphLeaderMemory H GQ Q I₁ I₂ O₁ O₂ d K

noncomputable def allowedEncode (allowed : Finset (LeaderHandover Q B C)) : List EncodedLeaderAlphabet.Outcome :=
  allowed.toList.map (EncodedLeaderAlphabet.outcomeEncode number)

omit [Fintype Q] [DecidableEq Q] in
theorem mem_allowedEncode (allowed : Finset (LeaderHandover Q B C)) (o : LeaderHandover Q B C) :
    EncodedLeaderAlphabet.outcomeEncode number o ∈ allowedEncode number allowed ↔ o ∈ allowed := by
  simp only [allowedEncode,List.mem_map,Finset.mem_toList]
  constructor
  · rintro ⟨q,hq,equal⟩
    exact EncodedLeaderAlphabet.outcomeEncode_injective number equal ▸ hq
  · intro ho
    exact ⟨o,ho,rfl⟩

omit [Fintype H] [Fintype Q] [Fintype I₁] [Fintype I₂] [Fintype O₁] [Fintype O₂]
    [DecidableEq H] [DecidableEq Q] [DecidableEq I₁] [DecidableEq I₂] [DecidableEq O₁]
    [DecidableEq O₂] in
theorem letterEncode_mem (group : H → G)
    (a : RealizedBlockRound I₂ I₁ (RollingReceiverOutput H I₁ I₂ O₁ O₂ d) (G → O₁)) :
    letterEncode root env output group a ∈ letters input :=
  List.mem_product.mpr ⟨List.mem_range.mpr (env _).isLt,
    List.mem_product.mpr ⟨FiniteFunctionCodes.encode_mem _ _,
      EncodedClosingBanks.bankEncode_mem root env one two output outOne outTwo shape _⟩⟩

variable (size : EncodedParityTables.size transitions = J)
variable (step : Q → (I₁ × I₂ × Graph) → (O₁ × O₂) → Q)
variable (transition : ∀ q r o, EncodedParityTables.next transitions (number q).val
  ((env r).val*V+(output o).val) = (number (step q r o)).val)

include size transition in
theorem restricted_encode (allowed : Finset (LeaderHandover Q B C)) (q : Memory) :
    Restricted input (allowedEncode number allowed) (encode q) ↔
      graphClosingOffers recognizer q.1.1 q.1.2.1 (jointLeaderShape shape q.2.2) q.2.2
        step q.1.2.2 (closingPolicyOfBank q.2.1) slot minimum ⊆ allowed := by
  have ctx : outcomeContext input = (B,J,C) := by
    change (B,EncodedParityTables.size transitions,C) = _
    rw [size]
  have member := collect_member_encode root env one two output outOne outTwo number shape recognizer graphs advance source start bank transitions slot minimum step transition q
  unfold Restricted
  rw [ctx]
  constructor
  · intro checked o ho
    rcases checked (EncodedLeaderAlphabet.outcomeEncode number o) (EncodedLeaderAlphabet.outcomeEncode_mem number o) with absent | present
    · exact False.elim (absent ((member o).mpr ho))
    · exact (mem_allowedEncode number allowed o).mp present
  · intro restricted code hc
    obtain ⟨o,rfl⟩ := EncodedLeaderAlphabet.outcomeEncode_sound number code hc
    by_cases offered : EncodedLeaderAlphabet.outcomeEncode number o ∈ EncodedGraphCollector.collect (collector input (encode q))
    · exact Or.inr ((mem_allowedEncode number allowed o).mpr (restricted ((member o).mp offered)))
    · exact Or.inl offered

include size transition in
theorem valid_encode (group : H → G) (allowed : Finset (LeaderHandover Q B C)) (q : Memory)
    (a : RealizedBlockRound I₂ I₁ (RollingReceiverOutput H I₁ I₂ O₁ O₂ d) (G → O₁)) :
    valid input (allowedEncode number allowed) (encode q) (letterEncode root env output group a) = true ↔
      jointLeaderCheck group shape q.2 a = true ∧
      jointGraphLeaderCollect recognizer step shape slot minimum q a ⊆ allowed := by
  rw [valid,rolling_encode,Bool.and_eq_true,decide_eq_true_eq,
    restricted_encode root env one two output outOne outTwo number shape recognizer graphs advance source start bank transitions slot minimum size step transition]
  rfl

private theorem map_lookup {X Y : Type} [BEq X] [LawfulBEq X]
    (xs : List X) (f : X → Y) (fallback : Y) (x : X) (member : x ∈ xs) :
    (xs.map f).getD (xs.idxOf x) fallback = f x := by
  have bound := List.idxOf_lt_length_iff.mpr member
  rw [List.getD_eq_getElem _ _ (by simpa only [List.length_map] using bound),List.getElem_map,
    List.getElem_idxOf bound]

include size in
omit [Fintype H] [Fintype Q] [Fintype I₁] [Fintype I₂] [Fintype O₁] [Fintype O₂]
    [DecidableEq H] [DecidableEq Q] [DecidableEq I₁] [DecidableEq I₂] [DecidableEq O₁]
    [DecidableEq O₂] in
theorem map_state_lookup (f : State → Nat) (q : Memory) :
    ((states input).map f).getD (name input (encode q)) 0 = f (encode q) := by
  apply map_lookup
  exact (FiniteCodeNumbering.mem_unique _ _).mpr
    (stateEncode_mem root env one two output outOne outTwo number shape recognizer graphs advance source start bank transitions slot minimum size q)

include size transition in
omit [Fintype H] [Fintype Q] [Fintype I₁] [Fintype I₂] [Fintype O₁] [Fintype O₂]
    [DecidableEq H] [DecidableEq Q] [DecidableEq I₁] [DecidableEq I₂] [DecidableEq O₁]
    [DecidableEq O₂] in
theorem updates_entry (group : H → G) (q : Memory)
    (a : RealizedBlockRound I₂ I₁ (RollingReceiverOutput H I₁ I₂ O₁ O₂ d) (G → O₁)) :
    ((updates input).getD ((letters input).idxOf (letterEncode root env output group a)) []).getD
      (name input (encode q)) 0 =
      name input (encode (jointGraphLeaderNext group recognizer step advance q a)) := by
  have row := map_lookup (letters input) (fun a => (states input).map (fun q => name input (next input q a))) []
    (letterEncode root env output group a)
    (letterEncode_mem root env one two output outOne outTwo number shape recognizer graphs advance source start bank transitions slot minimum group a)
  change ((updates input).getD _ []).getD _ 0 = _
  rw [show (updates input).getD ((letters input).idxOf (letterEncode root env output group a)) [] = _ from row,
    map_state_lookup root env one two output outOne outTwo number shape recognizer graphs advance source start bank transitions slot minimum size,
    next_encode root env one two output outOne outTwo number shape recognizer graphs advance source start bank transitions slot minimum step transition]

include size transition in
theorem checks_entry (group : H → G) (allowed : Finset (LeaderHandover Q B C)) (q : Memory)
    (a : RealizedBlockRound I₂ I₁ (RollingReceiverOutput H I₁ I₂ O₁ O₂ d) (G → O₁)) :
    ((checks input (allowedEncode number allowed)).getD
      ((letters input).idxOf (letterEncode root env output group a)) []).getD (name input (encode q)) false = true ↔
      jointLeaderCheck group shape q.2 a = true ∧
      jointGraphLeaderCollect recognizer step shape slot minimum q a ⊆ allowed := by
  have row := map_lookup (letters input)
    (fun a => (states input).map (fun q => valid input (allowedEncode number allowed) q a)) []
    (letterEncode root env output group a)
    (letterEncode_mem root env one two output outOne outTwo number shape recognizer graphs advance source start bank transitions slot minimum group a)
  rw [show (checks input (allowedEncode number allowed)).getD
    ((letters input).idxOf (letterEncode root env output group a)) [] = _ from row]
  have entry := map_lookup (states input)
    (fun q => valid input (allowedEncode number allowed) q (letterEncode root env output group a)) false (encode q)
    ((FiniteCodeNumbering.mem_unique _ _).mpr
      (stateEncode_mem root env one two output outOne outTwo number shape recognizer graphs advance source start bank transitions slot minimum size q))
  change (((states input).map _).getD ((states input).idxOf (encode q)) false = true) ↔ _
  rw [entry]
  exact valid_encode root env one two output outOne outTwo number shape recognizer graphs advance source start bank transitions slot minimum size step transition group allowed q a

end Characterisation.EncodedGraphMemory
