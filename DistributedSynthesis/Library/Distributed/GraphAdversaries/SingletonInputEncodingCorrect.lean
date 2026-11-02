/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.GraphAdversaries.SingletonInputEncoding
import DistributedSynthesis.Library.Distributed.InputAlphabetRelabeling

/-! Exact realizability preservation for the singleton-input embedding.
Input names are renamed bijectively, and the physical time index is unchanged. -/
namespace Characterisation.SingletonInputEncoding
open DistributedSynthesis

def unitNumber : Unit ≃ Fin 1 where
  toFun _ := 0
  invFun _ := ()
  left_inv _ := rfl
  right_inv _ := Subsingleton.elim _ _

theorem environment_eq (env : EnvironmentSequence (Fin 1) (Fin 1)) :
    env = fun t => InputAlphabetRelabeling.environment unitNumber unitNumber
      (GraphExecutions.ofGraphs (fun n => (env n).graph) t) := by
  funext t
  apply EnvironmentRound.equivProd.injective
  exact Prod.ext (Subsingleton.elim _ _) (Prod.ext (Subsingleton.elim _ _) rfl)

theorem atom (d : SynthesisInstance) (a : Nat) (r : Characterisation.Letter d) :
    EncodedNoDirect.interp (embed d) a (InputAlphabetRelabeling.record unitNumber unitNumber r) ↔
      atomInterpretation d a r := by
  change (a,(0,0,EncodedNoDirect.graphCode r.graph,r.outputOne.val,r.outputTwo.val)) ∈ d.2.2.1.map entry ↔ _
  rw [← graph_code r.graph]
  change entry (a,(Characterisation.graphCode r.graph,r.outputOne.val,r.outputTwo.val)) ∈ d.2.2.1.map entry ↔
    (a,(Characterisation.graphCode r.graph,r.outputOne.val,r.outputTwo.val)) ∈ d.2.2.1
  rw [List.mem_map]
  constructor
  · rintro ⟨old,member,equal⟩
    exact entry_injective equal ▸ member
  · intro member
    exact ⟨_,member,rfl⟩

theorem satisfies (d : SynthesisInstance) (word : Nat → Characterisation.Letter d) :
    LTL.Satisfies (EncodedNoDirect.interp (embed d))
      (OmegaWord.map (InputAlphabetRelabeling.record unitNumber unitNumber) word)
      (EncodedFiniteLTL.decode (embed d).formula) ↔
      LTL.Satisfies (atomInterpretation d) word (EncodedFiniteLTL.decode d.2.2.2) := by
  rw [LTL.satisfies_word_map]
  have interpretation : (fun a r => EncodedNoDirect.interp (embed d) a
      (InputAlphabetRelabeling.record unitNumber unitNumber r)) = atomInterpretation d := by
    funext a r
    exact propext (atom d a r)
  rw [interpretation]
  rfl

/-- An exact computable embedding, for every graph adversary, without any
regularity assumption or change of rounds. -/
theorem realizable (A : Set (Nat → Graph)) (d : SynthesisInstance) :
    WithInputs.Realizable A (embed d) ↔ Characterisation.Realizable A d := by
  constructor
  · rintro ⟨τ,winning⟩
    let σ := InputAlphabetRelabeling.strategy unitNumber.symm unitNumber.symm τ
    have recover : InputAlphabetRelabeling.strategy unitNumber unitNumber σ = τ :=
      InputAlphabetRelabeling.strategy_inverse unitNumber.symm unitNumber.symm τ
    refine ⟨σ,?_⟩
    intro x admitted
    have run := funext (InputAlphabetRelabeling.execution_map unitNumber unitNumber σ (GraphExecutions.ofGraphs x))
    rw [recover] at run
    have accepted := winning (fun t => InputAlphabetRelabeling.environment unitNumber unitNumber
      (GraphExecutions.ofGraphs x t)) admitted
    have transported := congrArg (fun word => LTL.Satisfies (EncodedNoDirect.interp (embed d))
      word (EncodedFiniteLTL.decode (embed d).formula)) run
    exact (satisfies d _).mp (transported.mp accepted)
  · rintro ⟨σ,winning⟩
    let τ := InputAlphabetRelabeling.strategy unitNumber unitNumber σ
    refine ⟨τ,?_⟩
    intro env admitted
    have run := (congrArg (execution τ) (environment_eq env)).trans
      (funext (InputAlphabetRelabeling.execution_map unitNumber unitNumber σ
        (GraphExecutions.ofGraphs (fun n => (env n).graph))))
    have transported := congrArg (fun word => LTL.Satisfies (EncodedNoDirect.interp (embed d))
      word (EncodedFiniteLTL.decode (embed d).formula)) run
    exact transported.mpr ((satisfies d _).mpr (winning (fun n => (env n).graph) admitted))

/-- A decision procedure for the finite-input model would decide the earlier
singleton-input model through this primitive-recursive embedding. -/
theorem computable_preimage (A : Set (Nat → Graph))
    (decidable : ComputablePred (WithInputs.Realizable A)) :
    ComputablePred (Characterisation.Realizable A) := by
  obtain ⟨inst,effective⟩ := decidable
  letI := inst
  have composed : ComputablePred (fun d => WithInputs.Realizable A (embed d)) :=
    ⟨inferInstance,effective.comp embed_primrec.to_comp⟩
  exact composed.of_eq (realizable A)

end Characterisation.SingletonInputEncoding
