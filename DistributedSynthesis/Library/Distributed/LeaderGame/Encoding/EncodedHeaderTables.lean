/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderGame.Encoding.EncodedPhysicalObjective
import DistributedSynthesis.Library.Distributed.LeaderGame.Encoding.EncodedLeaderAlphabetCorrect
import DistributedSynthesis.Library.Distributed.LeaderGame.Encoding.EncodedClosingBanksCorrect

/-! Decode raw numbered headers and the canonical physical alphabets into
the existing bank metadata. No semantic header or finite equivalence is an
argument to the executable functions. -/
namespace Characterisation.EncodedHeaderTables
open DistributedSynthesis
attribute [local irreducible] Primrec

def graph (g : Nat) := if g=0 then 2 else if g=1 then 0 else 1
def environment (o : EncodedRoundObjectives.Data) (i : Nat) : EncodedClosingObservations.Round :=
  (i / (EncodedRoundObjectives.inputTwo o * 3),i % (EncodedRoundObjectives.inputTwo o * 3) / 3,
    graph (i % (EncodedRoundObjectives.inputTwo o * 3) % 3))
def output (o : EncodedRoundObjectives.Data) (i : Nat) :=
  (i / EncodedRoundObjectives.outputTwo o,i % EncodedRoundObjectives.outputTwo o)
def environments (o : EncodedRoundObjectives.Data) :=
  (List.range (EncodedPhysicalObjective.environments o)).map (environment o)
def outputs (o : EncodedRoundObjectives.Data) :=
  (List.range (EncodedPhysicalObjective.outputs o)).map (output o)
def matrix (h : EncodedLeaderAlphabet.Header) := (List.range (h.1*h.1)).map
  (fun i => (decide (h.2.1.getD i 0 = 1),decide (h.2.2.1.getD i 0 = 1)))
def bankData (o : EncodedRoundObjectives.Data) (h : EncodedLeaderAlphabet.Header) (horizon : Nat) : EncodedClosingBanks.Data :=
  (h.1,(EncodedPhysicalObjective.environments o,horizon),environments o,outputs o,matrix h)

theorem graph_primrec : Primrec graph :=
  Primrec.ite (Primrec.eq.comp Primrec.id (Primrec.const 0)) (Primrec.const 2)
    (Primrec.ite (Primrec.eq.comp Primrec.id (Primrec.const 1)) (Primrec.const 0) (Primrec.const 1))
theorem environment_primrec : Primrec₂ environment := by
  have tail := Primrec.nat_mul.comp (EncodedRoundObjectives.inputTwo_primrec.comp
    (Primrec.fst : Primrec (fun x : EncodedRoundObjectives.Data × Nat => x.1))) (Primrec.const 3)
  have rest := Primrec.nat_mod.comp Primrec.snd tail
  exact (Primrec.nat_div.comp Primrec.snd tail).pair
    ((Primrec.nat_div.comp rest (Primrec.const 3)).pair
      (graph_primrec.comp (Primrec.nat_mod.comp rest (Primrec.const 3))))
theorem output_primrec : Primrec₂ output :=
  (Primrec.nat_div.comp Primrec.snd (EncodedRoundObjectives.outputTwo_primrec.comp Primrec.fst)).pair
    (Primrec.nat_mod.comp Primrec.snd (EncodedRoundObjectives.outputTwo_primrec.comp Primrec.fst))
theorem environments_primrec : Primrec environments :=
  Primrec.list_map (Primrec.list_range.comp EncodedPhysicalObjective.environments_primrec) environment_primrec.to₂
theorem outputs_primrec : Primrec outputs :=
  Primrec.list_map (Primrec.list_range.comp EncodedPhysicalObjective.outputs_primrec) output_primrec.to₂
theorem matrix_primrec : Primrec matrix := by
  have size : Primrec (fun h : EncodedLeaderAlphabet.Header => h.1*h.1) :=
    Primrec.nat_mul.comp Primrec.fst Primrec.fst
  have left : Primrec (fun x : EncodedLeaderAlphabet.Header × Nat => x.1.2.1.getD x.2 0) :=
    (Primrec.list_getD 0).comp (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)) Primrec.snd
  have right : Primrec (fun x : EncodedLeaderAlphabet.Header × Nat => x.1.2.2.1.getD x.2 0) :=
    (Primrec.list_getD 0).comp (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))) Primrec.snd
  exact Primrec.list_map (Primrec.list_range.comp size)
    (((Primrec.eq.comp left (Primrec.const 1)).decide).pair
      ((Primrec.eq.comp right (Primrec.const 1)).decide)).to₂

theorem bankData_primrec : Primrec (fun x : EncodedRoundObjectives.Data × EncodedLeaderAlphabet.Header × Nat => bankData x.1 x.2.1 x.2.2) :=
  (Primrec.fst.comp (Primrec.fst.comp Primrec.snd)).pair
    (((EncodedPhysicalObjective.environments_primrec.comp Primrec.fst).pair (Primrec.snd.comp Primrec.snd)).pair
      ((environments_primrec.comp Primrec.fst).pair
        ((outputs_primrec.comp Primrec.fst).pair (matrix_primrec.comp (Primrec.fst.comp Primrec.snd)))))

theorem graph_decode (g : Fin 3) : graph g.val = (graphCode (EncodedParityPresentation.graphNumber.symm g)).val := by
  fin_cases g <;> rfl

theorem environment_decode (o : EncodedRoundObjectives.Data) (i : Fin (EncodedPhysicalObjective.environments o)) :
    environment o i.val = EncodedClosingObservations.roundEncode (Equiv.refl _) (Equiv.refl _)
      ((EncodedPhysicalObjective.environmentNumber o).symm i) := by
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · rfl
    · exact graph_decode ⟨i.val % (EncodedRoundObjectives.inputTwo o * 3) % 3,Nat.mod_lt _ (by decide)⟩

theorem environments_encode (o : EncodedRoundObjectives.Data) : environments o =
    List.ofFn (fun i => EncodedClosingObservations.roundEncode (Equiv.refl _) (Equiv.refl _)
      ((EncodedPhysicalObjective.environmentNumber o).symm i)) := by
  exact FiniteSearch.tabulate_eq_ofFn _ _ (environment_decode o)

theorem outputs_encode (o : EncodedRoundObjectives.Data) : outputs o =
    List.ofFn (fun i => let p := (EncodedPhysicalObjective.outputNumber o).symm i; (p.1.val,p.2.val)) := by
  exact FiniteSearch.tabulate_eq_ofFn _ _ (fun _ => rfl)

theorem matrix_encode {Q : Type} {N B : Nat} (number : Q ≃ Fin N) (h : SwitchInterface Q B) :
    matrix (EncodedLeaderAlphabet.headerEncode number h) =
      List.ofFn (fun i => let p := (FiniteFunctionCodes.prod (Equiv.refl (Fin h.1.val)) (Equiv.refl _)).symm i
        (h.2.1 .one p.1 p.2,h.2.1 .two p.1 p.2)) := by
  apply FiniteSearch.tabulate_eq_ofFn
  intro i
  let p := finProdFinEquiv.symm i
  have entry (proc : Proc) := FiniteFunctionCodes.eval_encode finProdFinEquiv
    (fun ij => finTwoEquiv.symm (h.2.1 proc ij.1 ij.2)) p
  have index : (finProdFinEquiv p).val = i.val := congrArg Fin.val (Equiv.apply_symm_apply finProdFinEquiv i)
  have read (proc : Proc) : (EncodedLeaderAlphabet.matrixEncode (h.2.1 proc)).getD i.val 0 =
      (finTwoEquiv.symm (h.2.1 proc p.1 p.2)).val :=
    (congrArg (fun j => (EncodedLeaderAlphabet.matrixEncode (h.2.1 proc)).getD j 0) index).symm.trans (entry proc)
  change (decide ((EncodedLeaderAlphabet.matrixEncode (h.2.1 .one)).getD i.val 0 = 1),
    decide ((EncodedLeaderAlphabet.matrixEncode (h.2.1 .two)).getD i.val 0 = 1)) = _
  rw [read .one,read .two]
  change (decide ((finTwoEquiv.symm (h.2.1 .one p.1 p.2)).val = 1),
    decide ((finTwoEquiv.symm (h.2.1 .two p.1 p.2)).val = 1)) =
    (h.2.1 .one p.1 p.2,h.2.1 .two p.1 p.2)
  cases h.2.1 .one p.1 p.2 <;> cases h.2.1 .two p.1 p.2 <;> rfl

theorem bankData_encode {Q : Type} {N B : Nat} (o : EncodedRoundObjectives.Data)
    (number : Q ≃ Fin N) (h : SwitchInterface Q B) (horizon : Nat) :
    bankData o (EncodedLeaderAlphabet.headerEncode number h) horizon =
      EncodedClosingBanks.dataEncode (Equiv.refl (Fin h.1.val))
        (EncodedPhysicalObjective.environmentNumber o) (Equiv.refl _) (Equiv.refl _)
        (EncodedPhysicalObjective.outputNumber o) (Equiv.refl _) (Equiv.refl _) h.2.1 horizon := by
  unfold bankData EncodedClosingBanks.dataEncode
  rw [environments_encode,outputs_encode,matrix_encode]
  rfl

end Characterisation.EncodedHeaderTables
