/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderGame.Encoding.LocalLeaderLanguage

/-! Numbering the two output alphabets preserves local synthesis. The
receiver and leader retain exactly their original input histories, including
the history length; the translation changes only their output values. -/
namespace Characterisation
open DistributedSynthesis

variable {RIn SIn ROut SOut ROut' SOut' : Type}

def mapBlockOutputs (receiver : ROut → ROut') (leader : SOut → SOut')
    (a : RealizedBlockRound RIn SIn ROut SOut) : RealizedBlockRound RIn SIn ROut' SOut' :=
  (a.1,receiver a.2.1,leader a.2.2)

theorem pairPlay_mapOutputs (r : ROut → ROut') (s : SOut → SOut')
    (receiver : ReceiverBlockStrategy RIn SIn ROut) (leader : SenderBlockStrategy SIn SOut)
    (env : Nat → RIn × SIn) :
    pairPlay (fun history input => r (receiver history input))
      (fun history input => s (leader history input)) env =
      fun n => mapBlockOutputs r s (pairPlay receiver leader env n) := rfl

/-- Strategy translation is by postcomposition, so it grants no extra
observations and preserves the physical round number. -/
theorem blockStrategies_output_equiv (r : ROut ≃ ROut') (s : SOut ≃ SOut')
    (P : (Nat → RealizedBlockRound RIn SIn ROut SOut) → Prop)
    (Q : (Nat → RealizedBlockRound RIn SIn ROut' SOut') → Prop)
    (language : ∀ play, P play ↔ Q (fun n => mapBlockOutputs r s (play n))) :
    (∃ receiver : ReceiverBlockStrategy RIn SIn ROut,
      ∃ leader : SenderBlockStrategy SIn SOut, ∀ env, P (pairPlay receiver leader env)) ↔
    (∃ receiver : ReceiverBlockStrategy RIn SIn ROut',
      ∃ leader : SenderBlockStrategy SIn SOut', ∀ env, Q (pairPlay receiver leader env)) := by
  constructor
  · rintro ⟨receiver,leader,winning⟩
    refine ⟨fun history input => r (receiver history input),
      fun history input => s (leader history input),?_⟩
    intro env
    rw [pairPlay_mapOutputs]
    exact (language _).mp (winning env)
  · rintro ⟨receiver,leader,winning⟩
    refine ⟨fun history input => r.symm (receiver history input),
      fun history input => s.symm (leader history input),?_⟩
    intro env
    apply (language _).mpr
    have undo : (fun n => mapBlockOutputs r s
        (pairPlay (fun history input => r.symm (receiver history input))
          (fun history input => s.symm (leader history input)) env n)) =
        pairPlay receiver leader env := by
      funext n
      simp only [pairPlay_mapOutputs,mapBlockOutputs,Equiv.apply_symm_apply]
    rw [undo]
    exact winning env

variable [Fintype RIn] [Fintype SIn] [Fintype ROut] [Fintype SOut] [Fintype ROut'] [Fintype SOut']
variable [DecidableEq RIn] [DecidableEq SIn]
variable [Inhabited RIn] [Inhabited SIn] [Inhabited ROut] [Inhabited ROut']
variable (M : BlockRecordMonitor.{0,0,0,0,0} RIn SIn ROut SOut) [DecidableEq M.State]
variable (N : BlockRecordMonitor.{0,0,0,0,0} RIn SIn ROut' SOut') [DecidableEq N.State]

/-- Both the output numbering and the monitor's internal state space may
change. Equality of the translated physical languages suffices. -/
theorem leaderThreadTest_output_equiv (r : ROut ≃ ROut') (s : SOut ≃ SOut')
    (language : ∀ play, M.WinsPlay play ↔ N.WinsPlay (fun n => mapBlockOutputs r s (play n))) :
    leaderThreadTest M = leaderThreadTest N := by
  apply Bool.eq_iff_iff.mpr
  rw [leaderThreadTest_iff_strategies,leaderThreadTest_iff_strategies]
  exact blockStrategies_output_equiv r s M.WinsPlay N.WinsPlay language

end Characterisation
