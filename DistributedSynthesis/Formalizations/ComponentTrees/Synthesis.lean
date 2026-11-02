/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Formalizations.ComponentTrees.Decision
import DistributedSynthesis.Formalizations.ComponentTrees.FiniteModels

/-! Extract a finite MSO model generator, decode concrete component trees,
and reconstruct the realizing local output functions on demand. -/
namespace Characterisation.ComponentTrees.Effective
open DistributedSynthesis Characterisation Characterisation.PeriodicBlocks
open ComponentGames
open scoped DistributedSynthesis.FiniteOrders Characterisation.ComponentGames.FiniteEnumeration
set_option maxHeartbeats 2400000
set_option maxRecDepth 4000
set_option linter.unusedSectionVars false

abbrev Code (d : EncodedGuardedObjective.Data) (D : Nat) :=
  LabeledTree (Fin (computedCapacity (automaton d D)))
    (GeneratingAlphabet.Letter (automaton d D) (live d D)
      (computedReductionBound (automaton d D)) (computedCapacity_positive (automaton d D)))

def extractCode (d : EncodedGuardedObjective.Data) (D : Nat) : Option (Code d D) :=
  FiniteRunMSO.Star.model
    (GeneratingAlphabet.tables (automaton d D) (live d D) (computedReductionBound (automaton d D))
      (computedCapacity_positive (automaton d D)))
    (GeneratingAlphabet.starTest (automaton d D) (live d D) (computedReductionBound (automaton d D))
      (computedCapacity_positive (automaton d D)))
    (computedCapacity_positive (automaton d D)) (GeneratingAlphabet.edgeIndex (automaton d D))

theorem extractCode_sound (d : EncodedGuardedObjective.Data) (D : Nat) (code : Code d D)
    (found : extractCode d D = some code) :
    GeneratingAlphabet.Accepting (automaton d D) (live d D) (computedReductionBound (automaton d D))
      (computedCapacity_positive (automaton d D)) code :=
  FiniteRunMSO.Star.model_sound _ _ _ _ code found

theorem extractCode_complete (d : EncodedGuardedObjective.Data) (D : Nat) :
    (∃ code, extractCode d D = some code) ↔
      GeneratingAlphabet.satisfiable (automaton d D) (live d D) (computedReductionBound (automaton d D))
        (computedCapacity_positive (automaton d D)) = true :=
  (FiniteRunMSO.Star.model_complete _ _ _ _).trans (GeneratingAlphabet.satisfiable_accepting_iff _ _ _ _).symm

variable (d : EncodedGuardedObjective.Data) (D : Nat)
variable (initialLive : (prefixRecognizer (graphInput d.1)).eval [] ∈ (prefixRecognizer (graphInput d.1)).accept)
variable (code : Code d D) (found : extractCode d D = some code)

def compressed :=
  GeneratingAlphabet.decode (automaton d D) (live d D) (computedReductionBound (automaton d D))
    (computedCapacity_positive (automaton d D))
    (prefixRecognizer (graphInput d.1)) (live_correct d D) initialLive code (extractCode_sound d D code found).1

theorem compressed_accepting : (compressed d D initialLive code found).Accepting :=
  GeneratingAlphabet.decode_accepting (automaton d D) (live d D) (computedReductionBound (automaton d D))
    (computedCapacity_positive (automaton d D))
    (prefixRecognizer (graphInput d.1)) (live_correct d D) initialLive code (extractCode_sound d D code found)

def uncompressed := ExecutableReverse.tree (automaton d D) (prefixRecognizer (graphInput d.1))
  (blockAutomaton_stateLiveness (prefixRecognizer (graphInput d.1)) (objective d))
  (compressed d D initialLive code found) (compressed_accepting d D initialLive code found).1

theorem uncompressed_accepting : (uncompressed d D initialLive code found).Accepting :=
  ExecutableReverse.tree_accepting (automaton d D) (prefixRecognizer (graphInput d.1))
    (blockAutomaton_stateLiveness (prefixRecognizer (graphInput d.1)) (objective d))
    (compressed d D initialLive code found) (compressed_accepting d D initialLive code found).1
    (compressed_accepting d D initialLive code found)

def strategy : WithInputs.Strategies d.2 :=
  ExecutableReadback.strategy (automaton d D) (prefixRecognizer (graphInput d.1))
    (uncompressed d D initialLive code found) (0,0)

theorem strategy_correct (alphabet : (EncodedParityTables.rows d.1).length = 3) (positive : 0 < D) :
    ∀ env, (graphInput d.1).Accepts (fun n => (env n).graph) →
      LTL.Satisfies (EncodedNoDirect.interp d.2) (execution (strategy d D initialLive code found) env)
        (EncodedFiniteLTL.decode d.2.formula) := by
  apply CompiledObjective.implementing_strategy_realizes {word | (graphInput d.1).Accepts word} (graphInput d.1)
    (fun _ => Iff.rfl) d.2 (objective d) (objective_language d alphabet) positive
    (uncompressed d D initialLive code found) (uncompressed_accepting d D initialLive code found)
    (strategy d D initialLive code found)
  exact ExecutableReadback.strategy_implements (automaton d D) (prefixRecognizer (graphInput d.1))
    (uncompressed d D initialLive code found) (uncompressed_accepting d D initialLive code found).1 (0,0)

/-- Returns actual computable local functions. A finite generator for the
MSO model is not a finite-state restriction on these distributed functions. -/
def synthesize
    (promise : IsNowhereDense (geometricMap '' {word | (graphInput d.1).Accepts word})) :
    Option (WithInputs.Strategies d.2) :=
  if initialLive : (prefixRecognizer (graphInput d.1)).eval [] ∈ (prefixRecognizer (graphInput d.1)).accept then
    let D := Consensus.encodedConsensusBound d.1 promise
    match found : extractCode d D with
    | none => none
    | some code => some (strategy d D initialLive code found)
  else some ⟨fun _ => 0,fun _ => 0⟩

theorem synthesize_complete (alphabet : (EncodedParityTables.rows d.1).length = 3)
    (promise : IsNowhereDense (geometricMap '' {word | (graphInput d.1).Accepts word})) :
    (∃ σ, synthesize d promise = some σ) ↔ WithInputs.Realizable {word | (graphInput d.1).Accepts word} d.2 := by
  rw [← solve_correct d alphabet promise]
  unfold synthesize solve
  split
  · rename_i initialLive
    have eq := extractCode_complete d (Consensus.encodedConsensusBound d.1 promise)
    rw [← eq]
    dsimp only
    split <;> simp_all
  · simp

theorem synthesize_sound (alphabet : (EncodedParityTables.rows d.1).length = 3)
    (promise : IsNowhereDense (geometricMap '' {word | (graphInput d.1).Accepts word}))
    (σ : WithInputs.Strategies d.2) (found : synthesize d promise = some σ) :
    ∀ env, (graphInput d.1).Accepts (fun n => (env n).graph) →
      LTL.Satisfies (EncodedNoDirect.interp d.2) (execution σ env) (EncodedFiniteLTL.decode d.2.formula) := by
  unfold synthesize at found
  split at found
  · rename_i initialLive
    dsimp only at found
    split at found
    · cases found
    · rename_i code extracted
      cases Option.some.inj found
      exact strategy_correct d _ initialLive code extracted alphabet (Consensus.encodedConsensusBound_correct (V:=Bool) d.1 promise).1
  · rename_i empty
    intro env admitted
    have prefixExact := prefixRecognizer_correct (graphInput d.1) {word | (graphInput d.1).Accepts word} (fun _ => Iff.rfl)
    exact False.elim (empty ((prefixExact []).mp ⟨fun n => (env n).graph,admitted,rfl⟩))

end Characterisation.ComponentTrees.Effective
