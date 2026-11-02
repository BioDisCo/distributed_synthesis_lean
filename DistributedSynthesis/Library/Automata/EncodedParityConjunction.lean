/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Automata.EncodedParityProduct

/-! Uniform finite conjunction, reusing the checked synchronous binary
product. The empty family accepts every word. Every product consumes exactly
one physical letter in each component at each round. -/
namespace Characterisation.EncodedParityConjunction
open DistributedSynthesis
attribute [local irreducible] Primrec

abbrev Data := Nat × List EncodedParityTables.Data
def top (alphabet : Nat) : EncodedParityTables.Data :=
  (0,0,[0],(List.range alphabet).map (fun _ => [0]))
def identityLetters (alphabet : Nat) := (List.range alphabet).map (fun a => (a,a))
def product (alphabet : Nat) (left right : EncodedParityTables.Data) : EncodedParityProduct.Data :=
  (left,right,identityLetters alphabet)
def pair (alphabet : Nat) (left right : EncodedParityTables.Data) :=
  EncodedParityProduct.conjunction (product alphabet left right)
def compile (d : Data) := d.2.foldr (pair d.1) (top d.1)

theorem top_primrec : Primrec top := (Primrec.const 0).pair ((Primrec.const 0).pair
  ((Primrec.const [0]).pair (Primrec.list_map Primrec.list_range (Primrec.const [0]).to₂)))
theorem identityLetters_primrec : Primrec identityLetters :=
  Primrec.list_map Primrec.list_range (Primrec.snd.pair Primrec.snd).to₂
theorem product_primrec : Primrec (fun x : Nat × EncodedParityTables.Data × EncodedParityTables.Data =>
    product x.1 x.2.1 x.2.2) :=
  (Primrec.fst.comp Primrec.snd).pair ((Primrec.snd.comp Primrec.snd).pair
    (identityLetters_primrec.comp Primrec.fst))
theorem pair_primrec : Primrec (fun x : Nat × EncodedParityTables.Data × EncodedParityTables.Data =>
    pair x.1 x.2.1 x.2.2) := EncodedParityProduct.conjunction_primrec.comp product_primrec
theorem compile_primrec : Primrec compile :=
  Primrec.list_foldr Primrec.snd (top_primrec.comp Primrec.fst)
    (pair_primrec.comp ((Primrec.fst.comp Primrec.fst).pair Primrec.snd)).to₂

end Characterisation.EncodedParityConjunction
