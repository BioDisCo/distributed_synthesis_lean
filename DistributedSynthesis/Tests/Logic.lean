/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Logic.FiniteEncoding

/-! A client of only the public finite-encoding API. -/
open DistributedSynthesis

example {A : Type} [Fintype A] (w : OmegaWord A) (P : A → Prop) :
    LTL.Satisfies FiniteLetterLTL.interp w (FiniteLetterLTL.test P) ↔ P (w 0) :=
  FiniteLetterLTL.satisfies_test w P

example {A : Type} [Primcodable A] :
    Primrec (EncodedFiniteLTL.assemble : EncodedFiniteLTL.Tables A → EncodedFiniteLTL.Code A) :=
  EncodedFiniteLTL.assemble_primrec
