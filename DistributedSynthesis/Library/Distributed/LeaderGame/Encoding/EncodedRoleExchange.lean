/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderGame.Encoding.EncodedLeaderObjective

/-! Exchange the local roles in numeric round-objective data. The underlying
objective states and priorities are retained; physical letters are translated
one for one. The instance fields here specify alphabets, not a new LTL task. -/
namespace Characterisation.EncodedRoleExchange
open DistributedSynthesis
open EncodedNoDirect
attribute [local irreducible] Primrec

def swapFields (x : InstanceFields) : InstanceFields :=
  (x.2.1,x.1,x.2.2.2.1,x.2.2.1,x.2.2.2.2)
def swapInstance (i : Instance) := instanceEquiv.symm (swapFields (instanceEquiv i))
def swapGraph (g : Fin 3) : Fin 3 := if g=0 then 1 else if g=1 then 0 else 2
def swapCode (a : LetterCode) : LetterCode := (a.2.1,a.1,swapGraph a.2.2.1,a.2.2.2.2,a.2.2.2.1)
def transitions (d : EncodedRoundObjectives.Data) :=
  (letters (swapInstance d.1)).map (fun a => (List.range (EncodedRoundObjectives.stateCount d)).map
    (fun q => EncodedRoundObjectives.objectiveStep d q (swapCode a)))
def swap (d : EncodedRoundObjectives.Data) : EncodedRoundObjectives.Data :=
  (swapInstance d.1,(d.2.1,EncodedParityTables.initial d.2,EncodedParityTables.priorities d.2,transitions d))

theorem swapFields_primrec : Primrec swapFields := (Primrec.fst.comp Primrec.snd).pair
  (Primrec.fst.pair ((Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))).pair
    ((Primrec.fst.comp (Primrec.snd.comp Primrec.snd)).pair (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))))))
theorem swapInstance_primrec : Primrec swapInstance :=
  Primrec.of_equiv_symm.comp (swapFields_primrec.comp instanceEquiv_primrec)
theorem swapGraph_primrec : Primrec swapGraph := Primrec.dom_finite _
theorem swapCode_primrec : Primrec swapCode := (Primrec.fst.comp Primrec.snd).pair
  (Primrec.fst.pair ((swapGraph_primrec.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))).pair
    ((Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))).pair
      (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))))))
theorem transitions_primrec : Primrec transitions :=
  Primrec.list_map (letters_primrec.comp (swapInstance_primrec.comp Primrec.fst))
    (Primrec.list_map (Primrec.list_range.comp (EncodedRoundObjectives.stateCount_primrec.comp Primrec.fst))
      (EncodedRoundObjectives.objectiveStep_comp (Primrec.fst.comp Primrec.fst) Primrec.snd
        (swapCode_primrec.comp (Primrec.snd.comp Primrec.fst))).to₂).to₂
theorem swap_primrec : Primrec swap := (swapInstance_primrec.comp Primrec.fst).pair
  ((Primrec.fst.comp Primrec.snd).pair ((EncodedParityTables.initial_primrec.comp Primrec.snd).pair
    ((EncodedParityTables.priorities_primrec.comp Primrec.snd).pair transitions_primrec)))

end Characterisation.EncodedRoleExchange
