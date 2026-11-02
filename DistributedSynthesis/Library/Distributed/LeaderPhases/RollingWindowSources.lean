/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderPhases.RollingWindowReadback

/-! Recovering the earlier source of two closing windows from a shared
observation. Perfect recall retains the absolute round; a reception reveals
the complete history strictly before that reception. -/
namespace Characterisation
open DistributedSynthesis

theorem equal_currentView_length {I₁ I₂ : Type*} (p : Proc)
    (h k : EnvHistory I₁ I₂) (same : currentView p h = currentView p k) :
    List.length h = List.length k := by
  have len := congrArg (fun v => (ownInputs v).length) same
  simpa only [ownInputs_current,inputWord,List.length_map] using len

/-- Perfect recall projects equal observations to the same absolute
round, not the same relative offset in two independently started windows. -/
theorem equal_currentView_take {I₁ I₂ : Type*} (p : Proc)
    (h k : EnvHistory I₁ I₂) (same : currentView p h = currentView p k)
    (n : Nat) (within : n ≤ List.length h) :
    currentView p (h.take n) = currentView p (k.take n) := by
  have len := equal_currentView_length p h k same
  have one := lagView_take p h (List.length h-n) (Nat.sub_le _ _)
  have two := lagView_take p k (List.length h-n) (by omega)
  have indexH : List.length h - (List.length h-n) = n := by omega
  have indexK : List.length k - (List.length h-n) = n := by omega
  rw [indexH] at one
  rw [indexK] at two
  exact one.symm.trans ((congrArg (lagView (List.length h-n)) same).trans two)

/-- If the shared view includes a reception strictly after round `n`, it
identifies the entire environment history through round `n`. The strict
inequality is necessary: reception does not reveal the current graph. -/
theorem equal_view_recent_prefix {I₁ I₂ : Type*} (p : Proc)
    (h k : EnvHistory I₁ I₂) (same : currentView p h = currentView p k)
    (n : Nat) (recent : silentAge (currentView p h) < List.length h-n) :
    h.take n = k.take n := by
  have len := equal_currentView_length p h k same
  have within : n ≤ List.length h := by omega
  have both : ∀ q, currentView q (h.take n) = currentView q (k.take n) := by
    intro q
    have shared := shared_recent_lag (List.length h-n) h k q p same recent
    rw [lagView_take q h _ (Nat.sub_le _ _),lagView_take q k _ (by omega)] at shared
    have indexH : List.length h - (List.length h-n) = n := by omega
    have indexK : List.length k - (List.length h-n) = n := by omega
    simpa only [indexH,indexK] using shared
  exact joint_env_history _ _ (both .one) (both .two)

/-- A sufficiently long silent age forces every graph in the specified
suffix to be outgoing from the process. -/
theorem silent_suffix_outgoing {I₁ I₂ : Type*} (p : Proc)
    (h u : EnvHistory I₁ I₂)
    (silent : List.length u ≤ silentAge (currentView p (h++u))) :
    ∀ r ∈ u, r.graph = leaderOutgoingGraph p := by
  induction u using List.reverseRecOn with
  | nil => simp
  | append_singleton u r ih =>
    have last : r.graph = leaderOutgoingGraph p := by
      apply nonzero_age_outgoing p (h++u) r
      have len : List.length u + 1 ≤ silentAge (currentView p ((h++u)++[r])) := by
        simpa only [List.length_append,List.length_singleton,List.append_assoc] using silent
      omega
    have age : silentAge (currentView p ((h++u)++[r])) =
        silentAge (currentView p (h++u)) + 1 := by
      rw [leader_view_append_outgoing p (h++u) r last]
      rfl
    have previous : List.length u ≤ silentAge (currentView p (h++u)) := by
      simp only [List.length_append,List.length_singleton,← List.append_assoc,age] at silent
      omega
    intro s member
    rcases List.mem_append.mp member with earlier | final
    · exact ih previous s earlier
    · have eq : s = r := List.mem_singleton.mp final
      simpa only [eq] using last

/-- For any earlier window source, an equal final observation either
identifies that source exactly, or the entire intervening suffix sends only
outwards. In the second case leader outputs must be supplied by the shared
own-input strategy, rather than identified by their window offsets. -/
theorem equal_view_source_or_outgoing {I₁ I₂ : Type*} (p : Proc)
    (h u k : EnvHistory I₁ I₂)
    (same : currentView p (h++u) = currentView p k) :
    h = k.take (List.length h) ∨ ∀ r ∈ u, r.graph = leaderOutgoingGraph p := by
  by_cases recent : silentAge (currentView p (h++u)) < List.length u
  · left
    have identified := equal_view_recent_prefix p (h++u) k same (List.length h)
      (by simpa only [List.length_append,Nat.add_sub_cancel_left] using recent)
    simpa only [List.take_left] using identified
  · right
    exact silent_suffix_outgoing p h u (by omega)

/-- At a rightward source, equal receiver views identify the source
history. Empty extensions use the common initial leader view; nonempty
extensions use the last reception and the known outgoing graph. -/
theorem rollingSourceHistory_two_identifies {H I₁ I₂ : Type}
    (past : H → EnvHistory I₁ I₂) (L : Nat) (depth : ∀ h, List.length (past h) = L)
    (leaders : ∀ h k, currentView .one (past h) = currentView .one (past k))
    (node word : List (I₂ × I₁)) (h k : H)
    (same : currentView .two (rollingSourceHistory past node h) =
      currentView .two (rollingSourceHistory past word k)) :
    rollingSourceHistory past node h = rollingSourceHistory past word k := by
  have len := equal_currentView_length .two _ _ same
  simp only [rollingSourceHistory,rightInputHistory,List.length_append,List.length_map,depth] at len
  cases node using List.reverseRecOn with
  | nil =>
    have empty : word = [] := List.length_eq_zero_iff.mp (by simpa using len.symm)
    subst word
    simp only [rollingSourceHistory,rightInputHistory,List.map_nil,List.append_nil] at same ⊢
    exact joint_env_history _ _ (leaders h k) same
  | append_singleton node r =>
    cases word using List.reverseRecOn with
    | nil => simp only [List.length_append,List.length_singleton,List.length_nil] at len; omega
    | append_singleton word s =>
      rw [rollingSourceHistory_snoc,rollingSourceHistory_snoc] at same ⊢
      have identified := receiving_two_identifies_past _ _
        ⟨r.2,r.1,.right,(),()⟩ ⟨s.2,s.1,.right,(),()⟩ (Or.inl rfl) (Or.inl rfl) same
      obtain ⟨old,one,two⟩ := identified
      dsimp only at one two
      rw [old,one,two]

/-- Silence can increase by at most the number of elapsed physical rounds. -/
theorem silentAge_suffix_le {I₁ I₂ : Type*} (p : Proc)
    (h u : EnvHistory I₁ I₂) :
    silentAge (currentView p (h++u)) ≤ silentAge (currentView p h) + List.length u := by
  induction u using List.reverseRecOn with
  | nil => simp
  | append_singleton u r ih =>
    rw [← List.append_assoc,List.length_append,List.length_singleton]
    change silentAge (currentView p (History.append (h++u) r)) ≤ _
    cases p
    · rw [currentView_one_append]
      cases r.graph <;> simp only [silentAge] <;> omega
    · rw [currentView_two_append]
      cases r.graph <;> simp only [silentAge] <;> omega

/-- When the later source ends in a reception, equal final receiver views
identify the earlier source exactly. The current delivering graph can be
rightward or bidirectional; it is not inferred from the reception. -/
theorem receiving_later_source_identifies_earlier {I₁ I₂ : Type*}
    (h k u v : EnvHistory I₁ I₂) (r : RoundRecord I₁ I₂ Graph Unit Unit)
    (receives : r.graph = .right ∨ r.graph = .both)
    (later : List.length h < List.length (k++[r]))
    (same : currentView .two (h++u) = currentView .two ((k++[r])++v)) :
    h = (k++[r]).take (List.length h) := by
  have zero : silentAge (currentView .two (k++[r])) = 0 := by
    change silentAge (currentView .two (History.append k r)) = 0
    rw [currentView_two_append]
    rcases receives with graph | graph <;> simp only [graph,silentAge]
  have age := silentAge_suffix_le .two (k++[r]) v
  rw [zero,Nat.zero_add] at age
  have identified := equal_view_recent_prefix .two ((k++[r])++v) (h++u) same.symm
    (List.length h) (by simp only [List.length_append] at later ⊢; omega)
  rw [List.take_left,List.take_append_of_le_length (Nat.le_of_lt later)] at identified
  exact identified.symm

end Characterisation
