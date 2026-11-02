/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderGame.Encoding.EncodedClosingReplay

/-! Generate the graph/objective/minimum transition table used in numbered
closing offers. Graph transitions are fixed adversary data. Every physical
letter advances the objective and updates the carried phase minimum. -/
namespace Characterisation.EncodedLeaderAnnotations
open DistributedSynthesis
attribute [local irreducible] Primrec

/-- Graph-state count, objective-state count, priority bound, chosen graph
steps, graph decoding for environment letters, output count, and objective. -/
abbrev Data := Nat × Nat × Nat × List Nat × List Nat × Nat × EncodedParityTables.Data
def graphCount (d : Data) := d.1
def objectiveCount (d : Data) := d.2.1
def bound (d : Data) := d.2.2.1
def graphSteps (d : Data) := d.2.2.2.1
def graphs (d : Data) := d.2.2.2.2.1
def outputs (d : Data) := d.2.2.2.2.2.1
def objective (d : Data) := d.2.2.2.2.2.2
def count (d : Data) := graphCount d * objectiveCount d * (bound d+1)
def graphState (d : Data) (q : Nat) := q / (bound d+1) / objectiveCount d
def objectiveState (d : Data) (q : Nat) := q / (bound d+1) % objectiveCount d
def minimum (d : Data) (q : Nat) := q % (bound d+1)
def graphNext (d : Data) (q letter : Nat) :=
  (graphSteps d).getD (graphState d q * 3 + (graphs d).getD (letter/outputs d) 0) 0
def objectiveNext (d : Data) (q letter : Nat) := EncodedParityTables.next (objective d) (objectiveState d q) letter
def step (d : Data) (q letter : Nat) :=
  min (minimum d q) (EncodedParityTables.priority (objective d) (objectiveNext d q letter)) +
    (bound d+1) * (objectiveNext d q letter + objectiveCount d * graphNext d q letter)
def reset (d : Data) (q : Nat) := bound d + (bound d+1)*(q/(bound d+1))
def minima (d : Data) := (List.range (count d)).map (minimum d)
def compile (d : Data) (alphabet : Nat) : EncodedParityTables.Data :=
  (count d-1,0,[],(List.range alphabet).map (fun a => (List.range (count d)).map (fun q => step d q a)))

theorem graphCount_primrec : Primrec graphCount := Primrec.fst
theorem objectiveCount_primrec : Primrec objectiveCount := Primrec.fst.comp Primrec.snd
theorem bound_primrec : Primrec bound := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
theorem graphSteps_primrec : Primrec graphSteps := Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
theorem graphs_primrec : Primrec graphs := Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
theorem outputs_primrec : Primrec outputs := Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))))
theorem objective_primrec : Primrec objective := Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))))
theorem count_primrec : Primrec count := Primrec.nat_mul.comp
  (Primrec.nat_mul.comp graphCount_primrec objectiveCount_primrec) (Primrec.succ.comp bound_primrec)
theorem graphState_primrec : Primrec₂ graphState := Primrec.nat_div.comp
  (Primrec.nat_div.comp Primrec.snd (Primrec.succ.comp (bound_primrec.comp Primrec.fst))) (objectiveCount_primrec.comp Primrec.fst)
theorem objectiveState_primrec : Primrec₂ objectiveState := Primrec.nat_mod.comp
  (Primrec.nat_div.comp Primrec.snd (Primrec.succ.comp (bound_primrec.comp Primrec.fst))) (objectiveCount_primrec.comp Primrec.fst)
theorem minimum_primrec : Primrec₂ minimum := Primrec.nat_mod.comp Primrec.snd (Primrec.succ.comp (bound_primrec.comp Primrec.fst))
theorem graphNext_primrec : Primrec (fun x : Data × Nat × Nat => graphNext x.1 x.2.1 x.2.2) :=
  (Primrec.list_getD 0).comp (graphSteps_primrec.comp Primrec.fst)
    (Primrec.nat_add.comp (Primrec.nat_mul.comp
      (graphState_primrec.comp Primrec.fst (Primrec.fst.comp Primrec.snd)) (Primrec.const 3))
      ((Primrec.list_getD 0).comp (graphs_primrec.comp Primrec.fst)
        (Primrec.nat_div.comp (Primrec.snd.comp Primrec.snd) (outputs_primrec.comp Primrec.fst))))
theorem objectiveNext_primrec : Primrec (fun x : Data × Nat × Nat => objectiveNext x.1 x.2.1 x.2.2) :=
  EncodedParityTables.next_primrec.comp ((objective_primrec.comp Primrec.fst).pair
    ((objectiveState_primrec.comp Primrec.fst (Primrec.fst.comp Primrec.snd)).pair (Primrec.snd.comp Primrec.snd)))
theorem step_primrec : Primrec (fun x : Data × Nat × Nat => step x.1 x.2.1 x.2.2) :=
  Primrec.nat_add.comp
    (Primrec.nat_min.comp (minimum_primrec.comp Primrec.fst (Primrec.fst.comp Primrec.snd))
      (EncodedParityTables.priority_primrec.comp (objective_primrec.comp Primrec.fst) objectiveNext_primrec))
    (Primrec.nat_mul.comp (Primrec.succ.comp (bound_primrec.comp Primrec.fst))
      (Primrec.nat_add.comp objectiveNext_primrec
        (Primrec.nat_mul.comp (objectiveCount_primrec.comp Primrec.fst) graphNext_primrec)))
theorem reset_primrec : Primrec₂ reset := Primrec.nat_add.comp (bound_primrec.comp Primrec.fst)
  (Primrec.nat_mul.comp (Primrec.succ.comp (bound_primrec.comp Primrec.fst))
    (Primrec.nat_div.comp Primrec.snd (Primrec.succ.comp (bound_primrec.comp Primrec.fst))))
theorem minima_primrec : Primrec minima := Primrec.list_map (Primrec.list_range.comp count_primrec) minimum_primrec.to₂
theorem compile_primrec : Primrec₂ compile :=
  (Primrec.nat_sub.comp (count_primrec.comp Primrec.fst) (Primrec.const 1)).pair
    ((Primrec.const 0).pair ((Primrec.const []).pair
      (Primrec.list_map (Primrec.list_range.comp Primrec.snd)
        (Primrec.list_map (Primrec.list_range.comp (count_primrec.comp (Primrec.fst.comp Primrec.fst)))
          (step_primrec.comp ((Primrec.fst.comp (Primrec.fst.comp Primrec.fst)).pair
            (Primrec.snd.pair (Primrec.snd.comp Primrec.fst)))).to₂).to₂)))

end Characterisation.EncodedLeaderAnnotations
