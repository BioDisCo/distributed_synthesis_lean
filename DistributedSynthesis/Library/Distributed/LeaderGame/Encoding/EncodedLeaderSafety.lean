/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderGame.Encoding.EncodedLocalLeaderTest
import DistributedSynthesis.Library.Automata.EncodedParityConjunction

/-! A finite memory check with a permanent rejecting state, followed by the
existing parity conjunction compiler. The memory transitions and checks
are letter-major tables; every physical letter advances both components. -/
namespace Characterisation.EncodedLeaderSafety
open DistributedSynthesis
attribute [local irreducible] Primrec

/-- Base physical monitor, maximum memory index, initial memory index,
memory updates, and validity checks. -/
abbrev Data := EncodedLocalLeaderTest.Data × Nat × Nat × List (List Nat) × List (List Bool)
def base (d : Data) := d.1
def memorySize (d : Data) := d.2.1+1
def initialMemory (d : Data) := d.2.2.1 % memorySize d
def updates (d : Data) := d.2.2.2.1
def checks (d : Data) := d.2.2.2.2
def memoryNext (d : Data) (m a : Nat) := ((updates d).getD a []).getD m 0 % memorySize d
def valid (d : Data) (m a : Nat) := ((checks d).getD a []).getD m false
def step (d : Data) (q a : Nat) :=
  if q = 0 then 0 else if valid d (q-1) a then memoryNext d (q-1) a+1 else 0
def priority (q : Nat) := if q = 0 then 1 else 0
def safety (d : Data) : EncodedParityTables.Data :=
  (memorySize d,initialMemory d+1,(List.range (memorySize d+1)).map priority,
    (List.range (EncodedLocalLeaderTest.physicalSize (base d))).map
      (fun a => (List.range (memorySize d+1)).map (fun q => step d q a)))
def compile (d : Data) : EncodedLocalLeaderTest.Data :=
  (EncodedParityConjunction.compile
      (EncodedLocalLeaderTest.physicalSize (base d),[EncodedLocalLeaderTest.monitorData (base d),safety d]),
    (base d).2)
def solve (d : Data) := EncodedLocalLeaderTest.solve (compile d)

theorem base_primrec : Primrec base := Primrec.fst
theorem memorySize_primrec : Primrec memorySize := Primrec.succ.comp (Primrec.fst.comp Primrec.snd)
theorem initialMemory_primrec : Primrec initialMemory := Primrec.nat_mod.comp
  (Primrec.fst.comp (Primrec.snd.comp Primrec.snd)) memorySize_primrec
theorem updates_primrec : Primrec updates := Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
theorem checks_primrec : Primrec checks := Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
theorem memoryNext_primrec : Primrec (fun x : Data × Nat × Nat => memoryNext x.1 x.2.1 x.2.2) :=
  Primrec.nat_mod.comp ((Primrec.list_getD 0).comp
    ((Primrec.list_getD []).comp (updates_primrec.comp Primrec.fst) (Primrec.snd.comp Primrec.snd))
    (Primrec.fst.comp Primrec.snd)) (memorySize_primrec.comp Primrec.fst)
theorem valid_primrec : Primrec (fun x : Data × Nat × Nat => valid x.1 x.2.1 x.2.2) :=
  (Primrec.list_getD false).comp
    ((Primrec.list_getD []).comp (checks_primrec.comp Primrec.fst) (Primrec.snd.comp Primrec.snd))
    (Primrec.fst.comp Primrec.snd)
theorem step_primrec : Primrec (fun x : Data × Nat × Nat => step x.1 x.2.1 x.2.2) := by
  have args : Primrec (fun x : Data × Nat × Nat => (x.1,x.2.1-1,x.2.2)) :=
    Primrec.fst.pair ((Primrec.nat_sub.comp (Primrec.fst.comp Primrec.snd) (Primrec.const 1)).pair
      (Primrec.snd.comp Primrec.snd))
  exact Primrec.ite (Primrec.eq.comp (Primrec.fst.comp Primrec.snd) (Primrec.const 0))
    (Primrec.const 0) (Primrec.ite (Primrec.eq.comp (valid_primrec.comp args) (Primrec.const true))
      (Primrec.succ.comp (memoryNext_primrec.comp args)) (Primrec.const 0))
theorem priority_primrec : Primrec priority :=
  Primrec.ite (Primrec.eq.comp Primrec.id (Primrec.const 0)) (Primrec.const 1) (Primrec.const 0)
theorem safety_primrec : Primrec safety := memorySize_primrec.pair
  ((Primrec.succ.comp initialMemory_primrec).pair
    ((Primrec.list_map (Primrec.list_range.comp (Primrec.succ.comp memorySize_primrec))
      (priority_primrec.comp Primrec.snd).to₂).pair
    (Primrec.list_map (Primrec.list_range.comp (EncodedLocalLeaderTest.physicalSize_primrec.comp base_primrec))
      (Primrec.list_map (Primrec.list_range.comp (Primrec.succ.comp (memorySize_primrec.comp Primrec.fst)))
        (step_primrec.comp ((Primrec.fst.comp Primrec.fst).pair
          (Primrec.snd.pair (Primrec.snd.comp Primrec.fst)))).to₂).to₂)))
theorem compile_primrec : Primrec compile :=
  (EncodedParityConjunction.compile_primrec.comp
    ((EncodedLocalLeaderTest.physicalSize_primrec.comp base_primrec).pair
      (Primrec.list_cons.comp (EncodedLocalLeaderTest.monitorData_primrec.comp base_primrec)
        (Primrec.list_cons.comp safety_primrec (Primrec.const []))))).pair
    (Primrec.snd.comp base_primrec)
theorem solve_primrec : Primrec solve := EncodedLocalLeaderTest.solve_primrec.comp compile_primrec

end Characterisation.EncodedLeaderSafety
