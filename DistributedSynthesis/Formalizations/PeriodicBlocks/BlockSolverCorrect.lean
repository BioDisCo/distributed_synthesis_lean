/- Project authors: see AUTHORS.md at the repository root. -/
import DistributedSynthesis.Formalizations.PeriodicBlocks.BlockGameEncoding

namespace Characterisation.PeriodicBlocks
open DistributedSynthesis
noncomputable section
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096
set_option synthInstance.maxSize 2048
attribute [local instance] Classical.propDecidable

section
variable {I₁ I₂ O₁ O₂ G Q : Type} {B D E V S N N₁ N₂ P₁ P₂ K : Nat}
variable [Fintype I₁] [Fintype I₂] [Fintype O₁] [Fintype O₂] [Fintype G] [Fintype Q]
variable [DecidableEq I₁] [DecidableEq I₂] [DecidableEq O₁] [DecidableEq O₂] [DecidableEq G] [DecidableEq Q]
variable (env : (I₁ × I₂ × Graph) ≃ Fin E) (output : (O₁ × O₂) ≃ Fin V)
variable (one : I₁ ≃ Fin N₁) (two : I₂ ≃ Fin N₂)
variable (outOne : O₁ ≃ Fin P₁) (outTwo : O₂ ≃ Fin P₂)
variable (graph : G ≃ Fin S) (objective : Q ≃ Fin N)
variable (M : Recognizer Graph G) [DecidablePred (· ∈ M.accept)]
variable (physical : EncodedParityTables.Data)
variable (step : Q → (I₁ × I₂ × Graph) → (O₁ × O₂) → Q) (χ : Q → Nat)
variable (transition : ∀ q e y, EncodedParityTables.next physical (objective q).val
  ((env e).val*V+(output y).val) = (objective (step q e y)).val)
variable (ranks : ∀ q, EncodedParityTables.priority physical (objective q).val = χ q)
variable (positive : 0 < D)
variable (first : BlockOutcome I₁ I₂ G Q B D) (code : HandoverCode B K)

local notation "Move" => BlockMove I₁ I₂ O₁ O₂ G Q B D
local notation "Outcome" => BlockOutcome I₁ I₂ G Q B D
local notation "ctx" => blockContext (B:=B) (D:=D) (S:=S) (N:=N) env output one two outOne outTwo
local notation "data" => blockData (B:=B) (D:=D) (N:=N) env output one two outOne outTwo graph M physical
local notation "movP" => movePresentation (B:=B) (D:=D) env output one two outOne outTwo graph objective
local notation "obsP" => outcomePresentation (B:=B) (D:=D) env graph objective
local notation "encM" => FinitePresentation.encode movP
local notation "encO" => FinitePresentation.encode obsP
local notation "system" => hiddenCodeContinuitySystem (handoverPriorityDPA B K) code (BlockEdge (B:=B) (D:=D) (K:=K) M step χ)

local notation "input" => blockInput env output one two outOne outTwo graph objective M physical first code
local notation "numM" => moveNumber env output one two outOne outTwo graph objective
local notation "numO" => outcomeNumber (B:=B) (D:=D) env output one two outOne outTwo graph objective
local notation "numRow" => rowNumber env output one two outOne outTwo graph objective M physical first code
local notation "compiled" => EncodedBlock.compile input
local notation "numeric" => EncodedSupportedGame.semantic compiled

omit [Fintype I₁] [Fintype I₂] [Fintype O₁] [Fintype O₂] [Fintype G] [Fintype Q]
  [DecidableEq I₁] [DecidableEq I₂] [DecidableEq O₁] [DecidableEq O₂] [DecidableEq G] [DecidableEq Q] in
theorem block_observations_eq : EncodedSupportedGame.observations compiled =
    (EncodedBlock.outcomes ctx).length := by
  apply Nat.sub_add_cancel
  exact lt_of_le_of_lt (Nat.zero_le _) (numO first).isLt

def blockObservationNumber : Outcome ≃ Fin (EncodedSupportedGame.observations compiled) :=
  (numO).trans (finCongr (block_observations_eq env output one two outOne outTwo graph objective M physical first code).symm)
local notation "obsNum" => blockObservationNumber env output one two outOne outTwo graph objective M physical first code

def numericBlockProgress : DetParityAutomaton (Move × Outcome) :=
  (EncodedSupportedGame.wordAutomaton compiled).comap (fun a => (numM a.1,obsNum a.2))

omit [Fintype I₁] [Fintype I₂] [Fintype O₁] [Fintype O₂] [Fintype G] [Fintype Q]
  [DecidableEq I₁] [DecidableEq I₂] [DecidableEq O₁] [DecidableEq O₂] [DecidableEq G] [DecidableEq Q] in
theorem numericBlockProgress_eq :
    numericBlockProgress env output one two outOne outTwo graph objective M physical first code =
      blockProgress env output one two outOne outTwo graph objective M physical first code := by
  rw [blockProgress,EncodedThreadCompiler.automaton_eq]
  unfold numericBlockProgress EncodedSupportedGame.wordAutomaton DetParityAutomaton.comap EncodedParityTables.automaton
  congr 1
  funext q a
  apply Fin.ext
  change EncodedParityTables.next (EncodedThreadCompiler.compile (EncodedBlock.threadData input)) q.val
      ((numM a.1).val*EncodedSupportedGame.observations compiled+(numO a.2).val) =
    EncodedParityTables.next (EncodedThreadCompiler.compile (EncodedBlock.threadData input)) q.val (numRow a).val
  rw [block_observations_eq,rowNumber_val]

include transition positive in
omit [Fintype O₁] [Fintype O₂] [Fintype G] [Fintype Q] [DecidableEq O₁] [DecidableEq O₂] in
theorem block_offered_table (m : Move) (b : Outcome) :
    EncodedSupportedGame.offered compiled (numM m).val (obsNum b).val = blockOffers M step m b := by
  unfold EncodedSupportedGame.offered
  change (EncodedBlock.offersTable input).getD
    ((numM m).val*EncodedSupportedGame.observations compiled+(numO b).val) false = _
  rw [block_observations_eq]
  have h := FinitePresentation.lookup2 (EncodedBlock.moves ctx) (EncodedBlock.outcomes ctx)
    (EncodedBlock.offered data) (numM m) (numO b) false
  rw [moveNumber_get,outcomeNumber_get] at h
  exact h.trans (encoded_offered env output one two outOne outTwo graph objective M physical step transition positive m b)

include transition positive in
omit [Fintype O₁] [Fintype O₂] [Fintype G] [Fintype Q] in
theorem block_legal_table (b : Outcome) (m : Move) :
    EncodedSupportedGame.allowed compiled (obsNum b).val (numM m).val = decide (BlockMoveValid M step b.target m) := by
  change (EncodedBlock.legalTable input).getD
    ((numO b).val*(EncodedBlock.moves ctx).length+(numM m).val) false = _
  have h := FinitePresentation.lookup2 (EncodedBlock.outcomes ctx) (EncodedBlock.moves ctx)
    (fun b m => EncodedBlock.legal data b.2 m) (numO b) (numM m) false
  rw [moveNumber_get,outcomeNumber_get] at h
  apply h.trans
  apply Bool.eq_iff_iff.mpr
  rw [decide_eq_true_eq]
  exact encoded_legal env output one two outOne outTwo graph objective M physical step transition positive b.target m

def compiledBlockGame := supportedPublicTreeMonitor
  (numericBlockProgress env output one two outOne outTwo graph objective M physical first code)
  (blockOffers M step) first (fun b m => BlockMoveValid M step b.target m)
local notation "typed" => compiledBlockGame env output one two outOne outTwo graph objective M physical step first code

def blockStateDecode (q : (numeric).State) : (typed).State := ((obsNum).symm q.1,q.2)

omit [Fintype I₁] [Fintype I₂] [Fintype O₁] [Fintype O₂] [Fintype G] [Fintype Q]
  [DecidableEq I₁] [DecidableEq I₂] [DecidableEq O₁] [DecidableEq O₂] [DecidableEq G] [DecidableEq Q] in
theorem block_initial_number : (numeric).initial.1 = obsNum first := by
  apply Fin.ext
  change (@List.idxOf EncodedBlock.Outcome instBEqOfDecidableEq (encO first) (EncodedBlock.outcomes ctx)) %
    EncodedSupportedGame.observations compiled = (obsNum first).val
  change (numO first).val % EncodedSupportedGame.observations compiled = (obsNum first).val
  exact Nat.mod_eq_of_lt (obsNum first).isLt

theorem blockStateDecode_initial :
    blockStateDecode env output one two outOne outTwo graph objective M physical step first code (numeric).initial =
      (typed).initial := by
  apply Prod.ext
  · exact (congrArg (obsNum).symm
      (block_initial_number env output one two outOne outTwo graph objective M physical first code)).trans
        ((obsNum).symm_apply_apply first)
  · rfl

include transition positive in
theorem blockStateDecode_step (q : (numeric).State)
    (m : Fin (EncodedSupportedGame.moves compiled)) (b : Fin (EncodedSupportedGame.observations compiled)) :
    blockStateDecode env output one two outOne outTwo graph objective M physical step first code ((numeric).step q m b) =
      (typed).step (blockStateDecode env output one two outOne outTwo graph objective M physical step first code q)
        ((numM).symm m) ((obsNum).symm b) := by
  have offers := block_offered_table env output one two outOne outTwo graph objective M physical step transition positive
    first code ((numM).symm m) ((obsNum).symm b)
  have legal := block_legal_table env output one two outOne outTwo graph objective M physical step transition positive
    first code ((obsNum).symm q.1) ((numM).symm m)
  simp only [Equiv.apply_symm_apply] at offers legal
  simp only [blockStateDecode,EncodedSupportedGame.semantic,supportedPublicTreeMonitor,
    compiledBlockGame,numericBlockProgress,DetParityAutomaton.comap,Equiv.apply_symm_apply,offers,legal,decide_eq_true_eq]

include transition ranks positive in
theorem compiledBlockGame_winning_iff (tree : LabeledTree Outcome Move) :
    (typed).WinningTree tree ↔ (blockGame M step χ first code).WinningTree tree := by
  letI : Inhabited Outcome := ⟨first⟩
  unfold compiledBlockGame blockGame
  conv_lhs => rw [supportedPublicTreeMonitor_winning_iff]
  conv_rhs => rw [supportedPublicTreeMonitor_winning_iff]
  apply and_congr_right
  intro _
  apply forall_congr'
  intro branch
  apply imp_congr_right
  intro _
  rw [numericBlockProgress_eq]
  exact blockProgress_accepts env output one two outOne outTwo graph objective M physical step χ
    transition ranks positive first code _

include transition ranks positive in
/-- The primitive-recursive numeric solver decides exactly the new block game. -/
theorem encoded_block_solve_correct : EncodedBlock.solve input = true ↔
    ∃ tree, (blockGame M step χ first code).WinningTree tree := by
  rw [EncodedBlock.solve,EncodedSupportedGame.solve,EncodedTreeNonemptiness.solve_correct,
    EncodedSupportedGame.nonempty_iff]
  have retraction : (∃ tree, (numeric).toRunAutomaton.acceptsTree tree) ↔
      ∃ tree, (typed).toRunAutomaton.acceptsTree tree := by
    apply TreeMonitorRetraction.nonempty_iff numeric typed
      (blockStateDecode env output one two outOne outTwo graph objective M physical step first code)
      (obsNum).symm (numM).symm
    · exact blockStateDecode_initial env output one two outOne outTwo graph objective M physical step first code
    · exact blockStateDecode_step env output one two outOne outTwo graph objective M physical step transition positive first code
    · intro q; rfl
    · exact (obsNum).symm.surjective
    · exact (numM).symm.surjective
  apply retraction.trans
  apply exists_congr
  intro tree
  exact ((typed).acceptsTree_iff_winningTree tree).trans
    (compiledBlockGame_winning_iff env output one two outOne outTwo graph objective M physical step χ
      transition ranks positive first code tree)

end
end
end Characterisation.PeriodicBlocks
