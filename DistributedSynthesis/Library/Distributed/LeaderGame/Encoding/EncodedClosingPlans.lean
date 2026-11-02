/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Computability.FiniteFunctionCodes
import DistributedSynthesis.Library.Computability.FiniteCodeNumbering

/-! Numeric closing plans retain an entry for every nonempty input/graph
prefix up to the horizon. Replenishment compares the old prefixed entry with
the new entry at each remaining physical round. -/
namespace Characterisation.EncodedClosingPlans
open DistributedSynthesis

/-- Environment alphabet count and horizon. -/
abbrev Context := Nat × Nat
abbrev Plan := List Nat

def rawScenarios (c : Context) : List (List Nat) :=
  (List.range c.2).flatMap (fun n => FiniteSearch.tables c.1 (n+1))
@[irreducible] def scenarios (c : Context) := FiniteCodeNumbering.unique (rawScenarios c)
def scenarioName (c : Context) (word : List Nat) := FiniteCodeNumbering.name (rawScenarios c) word
def plans (c : Context) (outputs : Nat) := FiniteSearch.tables outputs (scenarios c).length
def entry (c : Context) (plan : Plan) (word : List Nat) := plan.getD (scenarioName c word) 0

abbrev OverlapInput := Context × Plan × Plan × Nat
def Overlap (x : OverlapInput) : Prop :=
  ∀ word ∈ scenarios x.1,
    entry (x.1.1,x.1.2+1) x.2.1 (x.2.2.2 :: word) =
      entry (x.1.1,x.1.2+1) x.2.2.1 word
instance (x : OverlapInput) : Decidable (Overlap x) := by
  unfold Overlap
  infer_instance
@[irreducible] def overlap (x : OverlapInput) := decide (Overlap x)

theorem rawScenarios_primrec : Primrec rawScenarios :=
  Primrec.list_flatMap (Primrec.list_range.comp Primrec.snd)
    (FiniteSearch.tables_primrec.comp (Primrec.fst.comp Primrec.fst) (Primrec.succ.comp Primrec.snd)).to₂
theorem scenarios_primrec : Primrec scenarios := by
  unfold scenarios
  exact FiniteCodeNumbering.unique_primrec.comp rawScenarios_primrec
theorem scenarioName_primrec : Primrec₂ scenarioName :=
  FiniteCodeNumbering.name_primrec.comp (rawScenarios_primrec.comp Primrec.fst) Primrec.snd
theorem plans_primrec : Primrec₂ plans := FiniteSearch.tables_primrec.comp Primrec.snd
  (Primrec.list_length.comp (scenarios_primrec.comp Primrec.fst))
theorem entry_primrec : Primrec (fun x : Context × Plan × List Nat => entry x.1 x.2.1 x.2.2) :=
  (Primrec.list_getD 0).comp (Primrec.fst.comp Primrec.snd)
    (scenarioName_primrec.comp Primrec.fst (Primrec.snd.comp Primrec.snd))

theorem overlap_primrec : Primrec overlap := by
  unfold overlap
  apply PrimrecPred.decide
  apply FiniteSearch.forall_mem (scenarios_primrec.comp Primrec.fst)
  have hc : Primrec (fun x : OverlapInput × List Nat => (x.1.1.1,x.1.1.2+1)) :=
    (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)).pair
      (Primrec.succ.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)))
  have ho : Primrec (fun x : OverlapInput × List Nat => x.1.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  have hn : Primrec (fun x : OverlapInput × List Nat => x.1.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
  have hr : Primrec (fun x : OverlapInput × List Nat => x.1.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
  exact Primrec.eq.comp
    (entry_primrec.comp (hc.pair (ho.pair (Primrec.list_cons.comp hr Primrec.snd))))
    (entry_primrec.comp (hc.pair (hn.pair Primrec.snd)))

end Characterisation.EncodedClosingPlans
