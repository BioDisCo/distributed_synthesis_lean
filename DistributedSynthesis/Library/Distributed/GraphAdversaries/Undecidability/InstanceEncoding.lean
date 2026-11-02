/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.GraphAdversaries.Undecidability.GuardedEncoding

/-! Effective atom renaming and finite output numbering for the exact target. -/
namespace Characterisation
open DistributedSynthesis CounterMachine ResidueLTL Compiler EncodedFiniteLTL

/-- Rename atoms without changing postfix operators, including malformed codes. -/
def renameCode {A B : Type*} (f : A → B) (c : Code A) : Code B :=
  c.map (Sum.map f id)

private theorem evalToken_map {A B : Type*} (f : A → B) (t : Token A) (s : List (LTL A)) :
    evalToken (Sum.map f id t) (s.map (LTL.map f)) =
      (evalToken t s).map (LTL.map f) := by
  cases t with
  | inl a => rfl
  | inr k =>
    obtain ⟨k, hk⟩ := k
    interval_cases k <;> cases s with
    | nil => rfl
    | cons p s => cases s <;> rfl

theorem decode_renameCode {A B : Type*} (f : A → B) (c : Code A) :
    decode (renameCode f c) = (decode c).map f := by
  have he (s : List (LTL A)) : eval (renameCode f c) (s.map (LTL.map f)) =
      (eval c s).map (LTL.map f) := by
    induction c generalizing s with
    | nil => rfl
    | cons t c ih =>
      simp only [renameCode, List.map_cons, eval, List.foldl_cons]
      rw [evalToken_map]
      exact ih _
  unfold decode
  rw [show ([] : List (LTL B)) = ([] : List (LTL A)).map (LTL.map f) from rfl, he]
  cases eval c [] with
  | nil => rfl
  | cons p s => cases s <;> rfl

noncomputable def payloadNumber : Payload ≃ Fin (Fintype.card Payload) := Fintype.equivFin Payload

def splitOutput (n : Nat) : Output (Fin (n+1)) ≃ Payload × Fin (n+1) where
  toFun o := (eraseOutput o, o.base.control)
  invFun z := ⟨⟨z.2, z.1.base.zero, z.1.base.carry, z.1.base.right⟩, z.1.residue⟩
  left_inv o := by cases o; rfl
  right_inv z := by rcases z with ⟨⟨⟨u,a,b,c⟩,r⟩,q⟩; cases u; rfl

noncomputable def numberedOutput (n : Nat) :
    Output (Fin (n+1)) ≃ Fin (Fintype.card Payload * (n+1)) :=
  (splitOutput n).trans ((Equiv.prodCongr payloadNumber (Equiv.refl _)).trans finProdFinEquiv)

/-- Numeric output alphabet parameter, expressed as cardinality minus one. -/
def outputParameter (n : Nat) := Fintype.card Payload * (n+1) - 1

private theorem payload_positive : 0 < Fintype.card Payload := by
  apply Fintype.card_pos_iff.mpr
  exact ⟨⟨⟨(), fun _ => false, fun _ => 0,
    fun _ => ⟨0, 0⟩⟩, 0⟩⟩

theorem outputParameter_succ (n : Nat) : outputParameter n + 1 = Fintype.card Payload * (n+1) := by
  have := Nat.mul_pos payload_positive (Nat.succ_pos n)
  exact Nat.sub_add_cancel this

noncomputable def outputEquiv (n : Nat) : Output (Fin (n+1)) ≃ Fin (outputParameter n + 1) :=
  (numberedOutput n).trans (finCongr (outputParameter_succ n).symm)

noncomputable def tableEntry (n : Nat) (a : RawLetter) : Nat × (Fin 3 × Nat × Nat) :=
  (Encodable.encode a, (graphCode a.1.1,
    a.2.1 + (n+1) * (payloadNumber a.1.2.1).val,
    a.2.2 + (n+1) * (payloadNumber a.1.2.2).val))

noncomputable def encodeInstance (I : Compiler.Instance) : SynthesisInstance :=
  (outputParameter I.1, outputParameter I.1,
    (letters I.1).map (tableEntry I.1), renameCode Encodable.encode I.2)

theorem encodeInstance_computable : Computable encodeInstance := by
  have par : Primrec outputParameter :=
    Primrec.nat_sub.comp
      (Primrec.nat_mul.comp (Primrec.const _) Primrec.succ) (Primrec.const 1)
  have ent : Primrec₂ tableEntry := by
    have payload₁ : Primrec (fun z : Nat × RawLetter => (payloadNumber z.2.1.2.1).val) :=
      (Primrec.dom_finite (fun s : Shape => (payloadNumber s.2.1).val)).comp
        (Primrec.fst.comp Primrec.snd)
    have payload₂ : Primrec (fun z : Nat × RawLetter => (payloadNumber z.2.1.2.2).val) :=
      (Primrec.dom_finite (fun s : Shape => (payloadNumber s.2.2).val)).comp
        (Primrec.fst.comp Primrec.snd)
    exact Primrec.pair (Primrec.encode.comp Primrec.snd)
      (Primrec.pair
        ((Primrec.dom_finite (fun s : Shape => graphCode s.1)).comp
          (Primrec.fst.comp Primrec.snd))
        (Primrec.pair
          (Primrec.nat_add.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
            (Primrec.nat_mul.comp (Primrec.succ.comp Primrec.fst) payload₁))
          (Primrec.nat_add.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
            (Primrec.nat_mul.comp (Primrec.succ.comp Primrec.fst) payload₂))))
  have rename : Primrec (renameCode (Encodable.encode : RawLetter → Nat)) := by
    apply Primrec.list_map Primrec.id
    have tok : Primrec (Sum.map (Encodable.encode : RawLetter → Nat) (id : Fin 8 → Fin 8)) :=
      Primrec.sumCasesOn Primrec.id
        (Primrec.sumInl.comp (Primrec.encode.comp Primrec.snd)).to₂
        (Primrec.sumInr.comp Primrec.snd).to₂
    exact (tok.comp Primrec.snd).to₂
  exact (Primrec.pair (par.comp Primrec.fst)
    (Primrec.pair (par.comp Primrec.fst)
      (Primrec.pair
        ((Primrec.list_map letters_primrec ent).comp Primrec.fst)
        (rename.comp Primrec.snd)))).to_comp

/-- Renaming an output changes no local view, since views contain no outputs. -/
def mapStrategy {O₁ O₂ P₁ P₂ : Type*} (f₁ : O₁ → P₁) (f₂ : O₂ → P₂)
    (σ : StrategyPair Unit Unit O₁ O₂) : StrategyPair Unit Unit P₁ P₂ :=
  ⟨fun v => f₁ (σ.one v), fun v => f₂ (σ.two v)⟩

def mapRecord {O₁ O₂ P₁ P₂ : Type*} (f₁ : O₁ → P₁) (f₂ : O₂ → P₂)
    (r : RoundRecord Unit Unit Graph O₁ O₂) : RoundRecord Unit Unit Graph P₁ P₂ :=
  ⟨(), (), r.graph, f₁ r.outputOne, f₂ r.outputTwo⟩

theorem mapStrategy_execution {O₁ O₂ P₁ P₂ : Type*} (f₁ : O₁ → P₁) (f₂ : O₂ → P₂)
    (σ : StrategyPair Unit Unit O₁ O₂) (x : Nat → Graph) :
    execution (mapStrategy f₁ f₂ σ) (GraphExecutions.ofGraphs x) =
      OmegaWord.map (mapRecord f₁ f₂) (execution σ (GraphExecutions.ofGraphs x)) := by
  funext t
  have h := GraphExecutions.execution_outputs σ (GraphExecutions.ofGraphs x) t
  have hp := GraphExecutions.execution_outputs (mapStrategy f₁ f₂ σ) (GraphExecutions.ofGraphs x) t
  have hg := GraphExecutions.execution_graph σ (GraphExecutions.ofGraphs x) t
  have hgp := GraphExecutions.execution_graph (mapStrategy f₁ f₂ σ) (GraphExecutions.ofGraphs x) t
  change execution _ _ t = mapRecord _ _ (execution _ _ t)
  generalize execution (mapStrategy f₁ f₂ σ) (GraphExecutions.ofGraphs x) t = r at hp hgp ⊢
  generalize execution σ (GraphExecutions.ofGraphs x) t = s at h hg ⊢
  cases r with
  | mk i j g o p =>
    cases s with
    | mk i' j' g' o' p' =>
      cases i; cases j; cases i'; cases j'
      congr 1
      · exact hgp.trans hg.symm
      · exact hp.1.trans (congrArg f₁ h.1).symm
      · exact hp.2.trans (congrArg f₂ h.2).symm

theorem outputEquiv_val (n : Nat) (o : Output (Fin (n+1))) :
    (outputEquiv n o).val = o.base.control.val + (n+1) * (payloadNumber (eraseOutput o)).val := rfl

theorem numbered_atom (I : Compiler.Instance) (a : RawLetter)
    (r : ResidueLTL.Letter (Fin (I.1+1))) :
    atomInterpretation (encodeInstance I) (Encodable.encode a)
      (mapRecord (outputEquiv I.1) (outputEquiv I.1) r) ↔ raw r = a := by
  change (Encodable.encode a, (graphCode r.graph,
    (outputEquiv I.1 r.outputOne).val, (outputEquiv I.1 r.outputTwo).val)) ∈
      (letters I.1).map (tableEntry I.1) ↔ raw r = a
  rw [List.mem_map]
  constructor
  · rintro ⟨b, hb, eq⟩
    have eb : b = a := Encodable.encode_injective (congrArg Prod.fst eq)
    subst b
    have eg : a.1.1 = r.graph := by
      have eqg := congrArg (fun z => z.2.1) eq
      change graphCode a.1.1 = graphCode r.graph at eqg
      have inj : Function.Injective graphCode := by
        intro g k eq
        cases g <;> cases k <;> simp only [graphCode] at eq <;>
          first | rfl | contradiction
      exact inj eqg
    have eo₁ := congrArg (fun z => z.2.2.1) eq
    have eo₂ := congrArg (fun z => z.2.2.2) eq
    have bounds := (mem_letters _ _).mp hb
    have decodeOutput (p : Payload) (k : Nat) (hk : k ≤ I.1)
        (o : Output (Fin (I.1+1)))
        (e : k + (I.1+1) * (payloadNumber p).val = (outputEquiv I.1 o).val) :
        p = eraseOutput o ∧ k = o.base.control.val := by
      let o' := (splitOutput I.1).symm (p, ⟨k, Nat.lt_succ_of_le hk⟩)
      have ee : outputEquiv I.1 o' = outputEquiv I.1 o := Fin.ext e
      have oo := (outputEquiv I.1).injective ee
      have pairEq := congrArg (splitOutput I.1) oo
      change (p, (⟨k, _⟩ : Fin (I.1+1))) = (eraseOutput o, o.base.control) at pairEq
      exact ⟨congrArg Prod.fst pairEq, congrArg (fun z => z.2.val) pairEq⟩
    obtain ⟨ep₁, ek₁⟩ := decodeOutput _ _ bounds.1 r.outputOne eo₁
    obtain ⟨ep₂, ek₂⟩ := decodeOutput _ _ bounds.2 r.outputTwo eo₂
    rcases a with ⟨⟨g,p,q⟩,i,j⟩
    exact Prod.ext (Prod.ext eg.symm (Prod.ext ep₁.symm ep₂.symm))
      (Prod.ext ek₁.symm ek₂.symm)
  · rintro rfl
    exact ⟨raw r, raw_mem r, rfl⟩

theorem numbered_satisfies (I : Compiler.Instance)
    (w : Nat → ResidueLTL.Letter (Fin (I.1+1))) :
    LTL.Satisfies (atomInterpretation (encodeInstance I))
      (OmegaWord.map (mapRecord (outputEquiv I.1) (outputEquiv I.1)) w)
      (decode (encodeInstance I).2.2.2) ↔
    LTL.Satisfies FiniteLetterLTL.interp (fun k => raw (w k)) (decode I.2) := by
  change LTL.Satisfies _ _ (decode (renameCode Encodable.encode I.2)) ↔ _
  rw [decode_renameCode, LTL.satisfies_map, LTL.satisfies_word_map]
  have interpEq : (fun a r => atomInterpretation (encodeInstance I) (Encodable.encode a)
      (mapRecord (outputEquiv I.1) (outputEquiv I.1) r)) =
      (fun a r => FiniteLetterLTL.interp a (raw r)) := by
    funext a r
    exact propext (numbered_atom I a r)
  rw [interpEq]
  exact (LTL.satisfies_word_map FiniteLetterLTL.interp raw w (decode I.2)).symm

theorem encodeInstance_realizable (A : Set (Nat → Graph)) (I : Compiler.Instance) :
    Realizable A (encodeInstance I) ↔ RestrictedEncodedRealizable A I := by
  change (∃ τ : StrategyPair Unit Unit (Fin (outputParameter I.1+1))
    (Fin (outputParameter I.1+1)), _) ↔ _
  constructor
  · rintro ⟨τ, ht⟩
    let σ := mapStrategy (outputEquiv I.1).symm (outputEquiv I.1).symm τ
    have recover : mapStrategy (outputEquiv I.1) (outputEquiv I.1) σ = τ := by
      cases τ
      simp only [σ, mapStrategy, Equiv.apply_symm_apply]
    refine ⟨σ, ?_⟩
    intro x hx
    apply (numbered_satisfies I _).mp
    erw [← mapStrategy_execution, recover]
    exact ht x hx
  · rintro ⟨σ, hs⟩
    refine ⟨mapStrategy (outputEquiv I.1) (outputEquiv I.1) σ, ?_⟩
    intro x hx
    erw [mapStrategy_execution]
    exact (numbered_satisfies I _).mpr (hs x hx)

/-- The negative direction in exactly the instance representation of the conjecture. -/
theorem no_geometric_holes_undecidable (A : Set (Nat → Graph))
    (noHoles : ¬ GeometricHoles A) : ¬ ComputablePred (Realizable A) := by
  intro dec
  apply no_geometric_holes_encoded_undecidable A noHoles
  obtain ⟨inst, hc⟩ := dec
  letI := inst
  have comp : ComputablePred (fun I => Realizable A (encodeInstance I)) :=
    ⟨inferInstance, hc.comp encodeInstance_computable⟩
  exact comp.of_eq (encodeInstance_realizable A)

theorem decidable_implies_geometric_holes (A : Set (Nat → Graph))
    (dec : ComputablePred (Realizable A)) : GeometricHoles A := by
  by_contra noHoles
  exact no_geometric_holes_undecidable A noHoles dec

end Characterisation
