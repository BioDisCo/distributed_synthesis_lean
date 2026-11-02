/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.GraphAdversaries.Inputs

/-! A primitive-recursive embedding of the earlier singleton-input instances
into the library's finite-private-input encoding. Formula codes and output
sizes are retained; graph codes and singleton input fields are translated. -/
namespace Characterisation.SingletonInputEncoding
open DistributedSynthesis
attribute [local irreducible] Primrec

/-- Earlier right/both/left codes 0/1/2 become library codes 1/2/0. -/
def graph (g : Fin 3) : Fin 3 := g+1

theorem graph_injective : Function.Injective graph := fun _ _ h => add_right_cancel h

theorem graph_code (g : Graph) : graph (Characterisation.graphCode g) = EncodedNoDirect.graphCode g := by
  cases g <;> rfl

def entry (x : Nat × (Fin 3 × Nat × Nat)) : Nat × EncodedNoDirect.LetterCode :=
  (x.1,0,0,graph x.2.1,x.2.2.1,x.2.2.2)

def embed (d : SynthesisInstance) : WithInputs.Instance :=
  ⟨0,0,d.1,d.2.1,d.2.2.1.map entry,d.2.2.2⟩

theorem entry_primrec : Primrec entry := Primrec.fst.pair
  ((Primrec.const 0).pair ((Primrec.const 0).pair
    (((Primrec.dom_finite graph).comp (Primrec.fst.comp Primrec.snd)).pair
      ((Primrec.fst.comp (Primrec.snd.comp Primrec.snd)).pair
        (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))))))

theorem embed_primrec : Primrec embed := by
  have fields : Primrec (fun d : SynthesisInstance =>
      (0,0,d.1,d.2.1,d.2.2.1.map entry,d.2.2.2) : SynthesisInstance → EncodedNoDirect.InstanceFields) :=
    (Primrec.const 0).pair ((Primrec.const 0).pair (Primrec.fst.pair
      ((Primrec.fst.comp Primrec.snd).pair
        ((Primrec.list_map (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
          (entry_primrec.comp Primrec.snd).to₂).pair
          (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))))))
  have inverse : Primrec (EncodedNoDirect.instanceEquiv.symm : EncodedNoDirect.InstanceFields → EncodedNoDirect.Instance) :=
    Primrec.of_equiv_symm
  exact (inverse.comp fields).of_eq (fun _ => rfl)

theorem entry_injective : Function.Injective entry := by
  intro x y equal
  apply Prod.ext
  · exact congrArg (fun z : Nat × EncodedNoDirect.LetterCode => z.1) equal
  · apply Prod.ext
    · exact graph_injective (congrArg (fun z => z.2.2.2.1) equal)
    · apply Prod.ext
      · exact congrArg (fun z => z.2.2.2.2.1) equal
      · exact congrArg (fun z => z.2.2.2.2.2) equal

end Characterisation.SingletonInputEncoding
