/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemScalingLTL

/-! # Realizable LTL without a finite physical implementation -/

namespace DistributedSynthesis.ScalingSafety.ResidueLTL

def views (env : EnvironmentSequence Unit Unit) : Nat → View Unit Unit .one × View Unit Unit .two
  | 0 => (.empty .one,.empty .two)
  | n+1 => advanceViewsWithEnvironment (views env n) (env n)

/-- Output labels do not affect the full-view update. -/
theorem execution_views {A B : Type*} (σ : StrategyPair Unit Unit A B)
    (env : EnvironmentSequence Unit Unit) (n : Nat) :
    (currentView .one (executionPrefix σ env n),currentView .two (executionPrefix σ env n)) =
      views env n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [currentView_executionPrefix_succ,currentView_executionPrefix_succ]
    change advanceViewsWithEnvironment
      (currentView .one (executionPrefix σ env n),currentView .two (executionPrefix σ env n))
        (env n) = _
    rw [ih]
    rfl

def liftedStrategy : StrategyPair Unit Unit Output Output where
  one := fun v ↦ ⟨Source.strategy.one v,mod3 (coordinate v)⟩
  two := fun v ↦ ⟨Source.strategy.two v,mod3 (coordinate v)⟩

theorem execution_record {A B : Type*} (σ : StrategyPair Unit Unit A B)
    (env : EnvironmentSequence Unit Unit) (n : Nat) :
    execution σ env n = ⟨(),(),(env n).graph,
      σ.one (views env (n+1)).1,σ.two (views env (n+1)).2⟩ := by
  have hv := congrArg Prod.fst (execution_views σ env (n+1))
  have hu := congrArg Prod.snd (execution_views σ env (n+1))
  dsimp only at hv hu
  simp only [currentView_executionPrefix_succ] at hv hu
  simp only [execution_apply,nextRound,hv,hu]

theorem lifted_forget (env : EnvironmentSequence Unit Unit) :
    (fun n ↦ forget (execution liftedStrategy env n)) = execution Source.strategy env := by
  funext n
  simp only [execution_record,forget,liftedStrategy]

def viewResidues (env : EnvironmentSequence Unit Unit) (n : Nat) : Residues :=
  (mod3 (coordinate (views env n).1),mod3 (coordinate (views env n).2))

theorem viewResidues_succ (env : EnvironmentSequence Unit Unit) (n : Nat) :
    viewResidues env (n+1) = update (viewResidues env n) (env n).graph := by
  cases hg : (env n).graph <;>
    simp [viewResidues,views,advanceViewsWithEnvironment,hg,coordinate,update,mod3,
      Nat.add_mod,Nat.mul_mod] <;> first | rfl | exact ⟨rfl,rfl⟩

theorem lifted_residues (env : EnvironmentSequence Unit Unit) (n : Nat) :
    residues (execution liftedStrategy env n) = viewResidues env (n+1) := by
  rw [execution_record]
  rfl

theorem lifted_residue_valid (env : EnvironmentSequence Unit Unit) :
    ResidueValid (execution liftedStrategy env) := by
  constructor
  · change residues (execution liftedStrategy env 0) = _
    rw [lifted_residues,viewResidues_succ]
    rfl
  · intro n
    rw [lifted_residues,lifted_residues,viewResidues_succ]
    rw [execution_record]

/-- The augmented labels are emitted by genuinely local perfect-recall
strategies; no process receives the global orientation as an input. -/
theorem lifted_wins (env : EnvironmentSequence Unit Unit) :
    LTL.Satisfies FiniteLetterLTL.interp (execution liftedStrategy env) formula := by
  apply (formula_iff_accepts _).mpr
  refine ⟨lifted_residue_valid env,?_⟩
  rw [lifted_forget]
  exact Source.wins env

universe u v

/-- Forgetting the residue changes only Moore output maps, not local
control types, physical transitions, or information available to a process. -/
def projectController
    (C : FinitePairedPhysicalController.{0,0,0,0,u,v} Unit Unit Output Output) :
    FinitePairedPhysicalController.{0,0,0,0,u,v} Unit Unit Label Label where
  OneControl := C.OneControl
  TwoControl := C.TwoControl
  oneFinite := C.oneFinite
  twoFinite := C.twoFinite
  initialOne := C.initialOne
  initialTwo := C.initialTwo
  noRecvOne := C.noRecvOne
  noRecvTwo := C.noRecvTwo
  recvOne := C.recvOne
  recvTwo := C.recvTwo
  outputOne := fun c ↦ (C.outputOne c).base
  outputTwo := fun c ↦ (C.outputTwo c).base

theorem project_word
    (C : FinitePairedPhysicalController.{0,0,0,0,u,v} Unit Unit Output Output)
    (env : EnvironmentSequence Unit Unit) :
    (projectController C).globalMachine.globalMachineTraceWord
      (projectController C).globalOutputOne (projectController C).globalOutputTwo env =
      fun n ↦ forget (C.globalMachine.globalMachineTraceWord C.globalOutputOne C.globalOutputTwo env n) := by
  rfl

theorem no_finite_ltl_winner
    (C : FinitePairedPhysicalController.{0,0,0,0,u,v} Unit Unit Output Output) :
    ¬ (∀ env, LTL.Satisfies FiniteLetterLTL.interp
      (C.globalMachine.globalMachineTraceWord C.globalOutputOne C.globalOutputTwo env) formula) := by
  intro h
  apply no_finite_winner (projectController C)
  intro env
  rw [project_word]
  exact ((formula_iff_accepts _).mp (h env)).2

/-- A finite LTL specification over finite output and graph letters has a
perfect-recall distributed winner and no finite paired physical winner. -/
theorem ltl_realizable_not_finite :
    (∃ σ : StrategyPair Unit Unit Output Output,
      ∀ env, LTL.Satisfies FiniteLetterLTL.interp (execution σ env) formula) ∧
    ¬ (∃ C : FinitePairedPhysicalController.{0,0,0,0,u,v} Unit Unit Output Output,
      ∀ env, LTL.Satisfies FiniteLetterLTL.interp
        (C.globalMachine.globalMachineTraceWord C.globalOutputOne C.globalOutputTwo env) formula) := by
  refine ⟨⟨liftedStrategy,lifted_wins⟩,?_⟩
  rintro ⟨C,hC⟩
  exact no_finite_ltl_winner C hC

end DistributedSynthesis.ScalingSafety.ResidueLTL
