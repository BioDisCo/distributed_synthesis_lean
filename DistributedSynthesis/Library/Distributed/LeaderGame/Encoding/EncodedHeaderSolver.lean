/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderGame.Encoding.EncodedHeaderCompiler

/-! Remove the template bank from the raw input. The complete bank search
replaces it before every local test, so even an empty numeric template is
sufficient. -/
namespace Characterisation.EncodedHeaderCompiler
open DistributedSynthesis
attribute [local irreducible] Primrec
local instance headerSolverDataCode : Primcodable Data := inferInstance

def replaceBank (d : Data) (b : EncodedClosingBanks.Bank) : Data :=
  (d.1,d.2.1,d.2.2.1,b,d.2.2.2.2)
theorem replaceBank_primrec : Primrec₂ replaceBank := (Primrec.fst.comp Primrec.fst).pair
  ((Primrec.fst.comp (Primrec.snd.comp Primrec.fst)).pair
    ((Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))).pair
      (Primrec.snd.pair (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))))))

theorem banks_replaceBank (d : Data) (b : EncodedClosingBanks.Bank) (one : Bool) :
    EncodedInitialLeaderBanks.banks (compile (replaceBank d b) one) =
      EncodedInitialLeaderBanks.banks (compile d one) := by
  cases one <;> rfl

theorem withBank_replaceBank (d : Data) (b next : EncodedClosingBanks.Bank) (one : Bool) :
    EncodedInitialLeaderBanks.withBank (compile (replaceBank d b) one) next =
      EncodedInitialLeaderBanks.withBank (compile d one) next := by
  cases one <;> rfl

theorem solve_replaceBank (d : Data) (b : EncodedClosingBanks.Bank) (one : Bool) :
    solve (replaceBank d b) one = solve d one := by
  cases one with
  | false =>
    apply Bool.eq_iff_iff.mpr
    change EncodedInitialLeftLeaderBanks.solve _ = true ↔ EncodedInitialLeftLeaderBanks.solve _ = true
    rw [EncodedInitialLeftLeaderBanks.solve_iff,EncodedInitialLeftLeaderBanks.solve_iff]
    simp only [banks_replaceBank,withBank_replaceBank]
  | true =>
    apply Bool.eq_iff_iff.mpr
    change EncodedInitialLeaderBanks.solve _ = true ↔ EncodedInitialLeaderBanks.solve _ = true
    rw [EncodedInitialLeaderBanks.solve_iff,EncodedInitialLeaderBanks.solve_iff]
    simp only [banks_replaceBank,withBank_replaceBank]

/-- Raw local question: fixed graph data, physical objective, header code,
and complete advertised outcome codes. -/
abbrev Question := GraphData × EncodedRoundObjectives.Data × EncodedLeaderAlphabet.Header × List EncodedLeaderAlphabet.Outcome
local instance headerSolverQuestionCode : Primcodable Question := inferInstance

def seed (q : Question) : Data := (q.1,q.2.1,q.2.2.1,[],q.2.2.2)
def test (q : Question) (one : Bool) := solve (seed q) one

theorem seed_primrec : Primrec seed := Primrec.fst.pair
  ((Primrec.fst.comp Primrec.snd).pair ((Primrec.fst.comp (Primrec.snd.comp Primrec.snd)).pair
    ((Primrec.const []).pair (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))))
theorem test_primrec : Primrec₂ test := solve_primrec.comp (seed_primrec.comp Primrec.fst) Primrec.snd

theorem test_eq_solve (g : GraphData) (o : EncodedRoundObjectives.Data)
    (h : EncodedLeaderAlphabet.Header) (allowed : List EncodedLeaderAlphabet.Outcome)
    (b : EncodedClosingBanks.Bank) (one : Bool) :
    test (g,o,h,allowed) one = solve (g,o,h,b,allowed) one :=
  solve_replaceBank (g,o,h,b,allowed) [] one

end Characterisation.EncodedHeaderCompiler
