/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledOpenProvenanceDistinguishedStream

/-!
# Acceptance of the finite distinguished provenance stream

The actual descriptor coordinate of the finite distinguished recurrence is a
literal path of the selected source-free belief-code policy.  Consequently,
its positive-time descriptor-code word is accepted by the belief-code DPA.

The root equation is stated explicitly.  An arbitrary package type does not
record that its semantic point was installed at `codePolicy.run []`; merely
being policy-live only gives reachability.  The root-specialized constructor
at the end of the file returns a package together with precisely this missing
equation and therefore discharges the hypothesis without strengthening the
runtime state.
-/

namespace DistributedSynthesis

universe i u v x y s

namespace DetParityAutomaton

variable {I : Type i}
variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable
  (A : DetParityAutomaton.{max u v x y, s}
    (RoundRecord In₁ In₂ Graph Out₁ Out₂))

noncomputable section

variable [Fintype I] [Inhabited I]
variable [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁]
  [Inhabited Out₂]
variable [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
variable [DecidableEq In₁] [DecidableEq In₂]

variable (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
variable (hwin : ∀ env : EnvironmentSequence In₁ In₂,
  A.Accepts (execution strategy env))
variable (basis : ∀ state : PairedProfiledTreeState A,
  (pairedProfiledEntryRunAutomaton A state).RationalRunBasis)
variable (initialCode : ProfiledOpenIndexedBiBeliefCode A (I := I))
variable (codePolicy : ProfiledOpenIndexedProvenanceCodeRationalPolicy A
  strategy hwin basis initialCode)

variable {initialState : PairedProfiledTreeState A}
variable (fixedPolicy :
  (pairedProfiledEntryRunAutomaton A initialState).RationalTransitionPolicy)
variable
  (point : ProfiledOpenIndexedOptionalControlledSemanticState A strategy hwin
    basis initialCode)
variable (initialRoot : ProfiledFixedPolicyRoot A fixedPolicy)
variable
  (package : ProfiledOpenProvenancePolicyFixedTablePackage A strategy hwin
    basis initialCode codePolicy fixedPolicy point initialRoot)

private abbrev AcceptanceQuery :=
  ProfiledOpenWitnessedTableQuery A initialCode

/-! ## The finite stream is one code-policy path -/

/-- The finite recurrence's initial base descriptor is exactly the descriptor
of the semantic point used to seed the table. -/
theorem profiledOpenProvenancePolicyDistinguishedInitial_descriptor :
    profiledOpenProvenancePolicyDistinguishedDescriptor A strategy hwin basis
        initialCode codePolicy fixedPolicy point initialRoot package
        (profiledOpenProvenancePolicyDistinguishedInitial A strategy hwin basis
          initialCode codePolicy fixedPolicy point initialRoot package) =
      profiledOpenIndexedOptionalControlledSemanticDescriptor A strategy hwin
        basis initialCode point := by
  rfl

/-- Descriptor states of the canonical finite stream, viewed as a coherent
path through the selected source-free belief-code rational policy. -/
noncomputable def profiledOpenProvenancePolicyDistinguishedStreamPath
    (hroot :
      (profiledOpenIndexedOptionalControlledSemanticDescriptor A strategy hwin
        basis initialCode point).1 = codePolicy.run [])
    (query : Nat → AcceptanceQuery A initialCode) :
    SourceFreeBeliefCodeParityPolicyPath
      (profiledOpenIndexedBiBeliefCodeParityDPA A initialCode)
      initialCode
      (ProfiledOpenIndexedProvenanceValid A strategy hwin basis)
      (profiledOpenIndexedBiBeliefNextFiniteTag A) codePolicy where
  state := fun n ↦
    (profiledOpenProvenancePolicyDistinguishedDescriptor A strategy hwin basis
      initialCode codePolicy fixedPolicy point initialRoot package
      (profiledOpenProvenancePolicyDistinguishedStateAt A strategy hwin basis
        initialCode codePolicy fixedPolicy point initialRoot package query n)).1
  direction := fun n ↦ (query n).1.2
  initial := by
    rw [profiledOpenProvenancePolicyDistinguishedStateAt_zero,
      profiledOpenProvenancePolicyDistinguishedInitial_descriptor]
    exact hroot
  successor := fun n ↦
    profiledOpenProvenancePolicyDistinguishedStateAt_policySuccessor A strategy
      hwin basis initialCode codePolicy fixedPolicy point initialRoot package
      query n

/-- Its generic path child word is definitionally the positive-time word of
actual descriptor codes. -/
theorem profiledOpenProvenancePolicyDistinguishedStreamPath_childCodeWord
    (hroot :
      (profiledOpenIndexedOptionalControlledSemanticDescriptor A strategy hwin
        basis initialCode point).1 = codePolicy.run [])
    (query : Nat → AcceptanceQuery A initialCode) :
    (profiledOpenProvenancePolicyDistinguishedStreamPath A strategy hwin basis
      initialCode codePolicy fixedPolicy point initialRoot package hroot query
      ).childCodeWord
        (profiledOpenIndexedBiBeliefCodeParityDPA A initialCode)
        initialCode
        (ProfiledOpenIndexedProvenanceValid A strategy hwin basis)
        (profiledOpenIndexedBiBeliefNextFiniteTag A) codePolicy =
      (fun n ↦
        (profiledOpenProvenancePolicyDistinguishedDescriptor A strategy hwin
          basis initialCode codePolicy fixedPolicy point initialRoot package
          (profiledOpenProvenancePolicyDistinguishedStateAt A strategy hwin
            basis initialCode codePolicy fixedPolicy point initialRoot package
            query (n + 1))).code) := by
  rfl

/-- The exact positive-time descriptor-code word of the finite recurrence is
accepted.  This is acceptance of its one distinguished retagged path, not of
an independently pasted sequence of candidates. -/
theorem profiledOpenProvenancePolicyDistinguishedStream_accepts
    (hroot :
      (profiledOpenIndexedOptionalControlledSemanticDescriptor A strategy hwin
        basis initialCode point).1 = codePolicy.run [])
    (query : Nat → AcceptanceQuery A initialCode) :
    (profiledOpenIndexedBiBeliefCodeParityDPA A initialCode).Accepts
      (fun n ↦
        (profiledOpenProvenancePolicyDistinguishedDescriptor A strategy hwin
          basis initialCode codePolicy fixedPolicy point initialRoot package
          (profiledOpenProvenancePolicyDistinguishedStateAt A strategy hwin
            basis initialCode codePolicy fixedPolicy point initialRoot package
            query (n + 1))).code) := by
  let path := profiledOpenProvenancePolicyDistinguishedStreamPath A strategy
    hwin basis initialCode codePolicy fixedPolicy point initialRoot package
    hroot query
  have haccepts := path.accepts
    (profiledOpenIndexedBiBeliefCodeParityDPA A initialCode)
    initialCode
    (ProfiledOpenIndexedProvenanceValid A strategy hwin basis)
    (profiledOpenIndexedBiBeliefNextFiniteTag A) codePolicy
  simpa only [path,
    profiledOpenProvenancePolicyDistinguishedStreamPath_childCodeWord] using
      haccepts

/-! ## Root-specialized extraction -/

/-- The root installation theorem with the descriptor equation retained in
its result.  This is the precise strengthening unavailable from the bare
package type. -/
theorem exists_profiledOpenProvenancePolicyDistinguishedRootPackage
    (initialRoot : ProfiledFixedPolicyRoot A fixedPolicy)
    (hinitialRoot : initialRoot.state A fixedPolicy = fixedPolicy.run []) :
    ∃ point : ProfiledOpenIndexedOptionalControlledSemanticState A strategy
        hwin basis initialCode,
      (profiledOpenIndexedOptionalControlledSemanticDescriptor A strategy hwin
        basis initialCode point).1 = codePolicy.run [] ∧
      Nonempty
        (ProfiledOpenProvenancePolicyFixedTablePackage A strategy hwin basis
          initialCode codePolicy fixedPolicy point initialRoot) := by
  obtain ⟨move, point, hmove, hdescriptor, _hcandidate, _hlive⟩ :=
    exists_profiledOpenIndexedProvenanceCodePolicyInitialCandidate A strategy
      hwin basis initialCode codePolicy
  have hrun := profiledOpenIndexedProvenanceCodePolicy_run_nil A strategy hwin
    basis initialCode codePolicy
  have hdescriptor' :
      profiledOpenIndexedOptionalControlledSemanticDescriptor A strategy hwin
          basis initialCode point = (codePolicy.run [], move) := by
    simpa only [hrun] using hdescriptor
  obtain ⟨package, _hthreads⟩ :=
    exists_profiledOpenProvenancePolicyFixedTable A strategy hwin basis
      initialCode codePolicy fixedPolicy (codePolicy.run []) move point
      hdescriptor' ⟨[], rfl⟩ hmove initialRoot hinitialRoot
  exact ⟨point, congrArg Prod.fst hdescriptor', ⟨package⟩⟩

/-- One root-created finite package carries an accepted distinguished stream
for every query word. -/
theorem exists_profiledOpenProvenancePolicyDistinguishedAcceptedStream
    (initialRoot : ProfiledFixedPolicyRoot A fixedPolicy)
    (hinitialRoot : initialRoot.state A fixedPolicy = fixedPolicy.run []) :
    ∃ point : ProfiledOpenIndexedOptionalControlledSemanticState A strategy
        hwin basis initialCode,
      ∃ package : ProfiledOpenProvenancePolicyFixedTablePackage A strategy hwin
          basis initialCode codePolicy fixedPolicy point initialRoot,
        ∀ query : Nat → AcceptanceQuery A initialCode,
          (profiledOpenIndexedBiBeliefCodeParityDPA A initialCode).Accepts
            (fun n ↦
              (profiledOpenProvenancePolicyDistinguishedDescriptor A strategy
                hwin basis initialCode codePolicy fixedPolicy point initialRoot
                package
                (profiledOpenProvenancePolicyDistinguishedStateAt A strategy
                  hwin basis initialCode codePolicy fixedPolicy point
                  initialRoot package query (n + 1))).code) := by
  obtain ⟨point, hroot, ⟨package⟩⟩ :=
    exists_profiledOpenProvenancePolicyDistinguishedRootPackage A strategy hwin
      basis initialCode codePolicy fixedPolicy initialRoot hinitialRoot
  exact ⟨point, package, fun query ↦
    profiledOpenProvenancePolicyDistinguishedStream_accepts A strategy hwin
      basis initialCode codePolicy fixedPolicy point initialRoot package hroot
      query⟩

end

end DetParityAutomaton

end DistributedSynthesis
