/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.PaddingProjection

/-! # Embedding histories into communication blocks

A block consists of one original graph followed by bidirectional padding.
The first round is active. Each padding round swaps the two projected local
views; an even number of padding rounds restores their original owners.
All statements use the existing full-view evaluation and local projection.
-/

namespace DistributedSynthesis.BlockEmbedding
open FullViewPath PaddingProjection

def active (L : Nat) (t : Nat) : Bool := decide (t % L = 0)

def embed (L : Nat) (h : List Graph) : List Graph :=
  h.flatMap fun g ↦ g :: List.replicate (L-1) .both

/-- The original next graph has occurred, followed by `d` padding rounds.
Thus `d` is also the zero-based output offset within the current block. -/
def phase (L : Nat) (h : List Graph) (g : Graph) (d : Nat) : List Graph :=
  embed L h ++ [g] ++ List.replicate d .both

def pairProject (schedule : Nat → Bool) (h : List Graph) : Nat × Nat :=
  (project schedule (evaluate h).one, project schedule (evaluate h).two)

def swap (v : Nat × Nat) : Nat × Nat := (v.2, v.1)

def swapped (d : Nat) (v : Nat × Nat) : Nat × Nat :=
  if d % 2 = 0 then v else swap v

def graphStep (g : Graph) (v : Nat × Nat) : Nat × Nat :=
  match g with
  | .left => (v.1 + 2*v.2, 3*v.2)
  | .right => (3*v.1, v.2 + 2*v.1)
  | .both => (v.1 + 2*v.2, v.2 + 2*v.1)

theorem swapped_succ (d : Nat) (v : Nat × Nat) :
    swapped (d+1) v = swap (swapped d v) := by
  have := Nat.mod_lt d (by omega : 0 < 2)
  by_cases hd : d % 2 = 0
  · have he : (d+1) % 2 ≠ 0 := by omega
    simp [swapped, hd, he]
  · have he : (d+1) % 2 = 0 := by omega
    simp [swapped, hd, he, swap]

theorem pairProject_active (schedule : Nat → Bool) (h : List Graph) (g : Graph)
    (ha : schedule h.length = true) :
    pairProject schedule (h ++ [g]) = graphStep g (pairProject schedule h) := by
  have hd := at_depth h
  cases g <;> simp [pairProject, at_append, advance, advanceViews, project,
    Proc.other, hd.1, hd.2, ha, graphStep]

theorem pairProject_padding (schedule : Nat → Bool) (h : List Graph)
    (ha : schedule h.length = false) :
    pairProject schedule (h ++ [.both]) = swap (pairProject schedule h) := by
  have hd := at_depth h
  simp [pairProject, at_append, advance, advanceViews, project,
    Proc.other, hd.1, hd.2, ha, swap]

/-- Arbitrarily long bidirectional padding alternates the two projections.
No property of the preceding history is required. -/
theorem pairProject_padding_run (schedule : Nat → Bool) (h : List Graph) (d : Nat)
    (ha : ∀ j, j < d → schedule (h.length+j) = false) :
    pairProject schedule (h ++ List.replicate d .both) = swapped d (pairProject schedule h) := by
  induction d with
  | zero => simp [swapped]
  | succ d ih =>
    have hr : List.replicate (d+1) Graph.both = List.replicate d .both ++ [.both] := by
      rw [List.replicate_add]; rfl
    rw [hr, ← List.append_assoc, pairProject_padding schedule _ (by simpa using ha d (by omega)),
      ih (fun j hj ↦ ha j (by omega)), ← swapped_succ]

@[simp] theorem embed_nil (L : Nat) : embed L [] = [] := rfl

theorem embed_append (L : Nat) (h : List Graph) (g : Graph) :
    embed L (h ++ [g]) = phase L h g (L-1) := by
  simp [embed, phase, List.flatMap_append, List.append_assoc]

theorem embed_length (L : Nat) (hL : 0 < L) (h : List Graph) :
    (embed L h).length = L*h.length := by
  induction h using List.reverseRecOn with
  | nil => simp
  | append_singleton h g ih =>
    rw [embed_append]
    simp only [phase, List.length_append, List.length_singleton, List.length_replicate, ih]
    rw [Nat.mul_add, Nat.mul_one]
    omega

theorem phase_length (L : Nat) (hL : 0 < L) (h : List Graph) (g : Graph) (d : Nat) :
    (phase L h g d).length = L*h.length+1+d := by
  simp [phase, embed_length L hL, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem active_boundary (L n : Nat) : active L (L*n) = true := by simp [active]

theorem inactive_inside (L n j : Nat) (hj : 0 < j) (hjL : j < L) :
    active L (L*n+j) = false := by
  simp [active, Nat.add_mod, Nat.mod_eq_of_lt hjL, Nat.ne_of_gt hj]

theorem phase_projection (L : Nat) (hL : 0 < L) (h : List Graph) (g : Graph)
    (d : Nat) (hd : d < L) :
    pairProject (active L) (phase L h g d) =
      swapped d (graphStep g (pairProject (active L) (embed L h))) := by
  unfold phase
  rw [pairProject_padding_run, pairProject_active]
  · simp [embed_length L hL, active_boundary]
  · intro j hj
    simp only [List.length_append, List.length_singleton, embed_length L hL]
    simpa only [Nat.add_assoc] using inactive_inside L h.length (1+j) (by omega) (by omega)

/-- Complete odd-length blocks preserve both original process identities. -/
theorem embed_projection (L : Nat) (hL : 0 < L) (heven : (L-1) % 2 = 0)
    (h : List Graph) :
    pairProject (active L) (embed L h) = pairProject (fun _ ↦ true) h := by
  induction h using List.reverseRecOn with
  | nil => rfl
  | append_singleton h g ih =>
    rw [embed_append, phase_projection L hL h g (L-1) (by omega)]
    simp only [swapped, heven, ↓reduceIte, ih]
    exact (pairProject_active (fun _ ↦ true) h g rfl).symm

/-- At each output offset the projection is the original history's pair,
with exactly the parity-dependent exchange of owners. -/
theorem phase_projection_original (L : Nat) (hL : 0 < L) (heven : (L-1) % 2 = 0)
    (h : List Graph) (g : Graph) (d : Nat) (hd : d < L) :
    pairProject (active L) (phase L h g d) =
      swapped d (pairProject (fun _ ↦ true) (h ++ [g])) := by
  rw [phase_projection L hL h g d hd, embed_projection L hL heven,
    pairProject_active (fun _ ↦ true) h g rfl]

theorem virtualDepth_padding (schedule : Nat → Bool) (t d : Nat)
    (ha : ∀ j, j < d → schedule (t+j) = false) :
    virtualDepth schedule (t+d) = virtualDepth schedule t := by
  induction d with
  | zero => rfl
  | succ d ih =>
    rw [show t+(d+1) = (t+d)+1 by omega, virtualDepth, ha d (by omega)]
    simpa using ih (fun j hj ↦ ha j (by omega))

theorem virtualDepth_inside (L : Nat) (n d : Nat) (hd : d < L) :
    virtualDepth (active L) (L*n+1+d) = virtualDepth (active L) (L*n)+1 := by
  rw [virtualDepth_padding (active L) (L*n+1) d]
  · simp [virtualDepth, active_boundary]
  · intro j hj
    simpa only [Nat.add_assoc] using inactive_inside L n (1+j) (by omega) (by omega)

theorem virtualDepth_boundary (L : Nat) (hL : 0 < L) (n : Nat) :
    virtualDepth (active L) (L*n) = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have he : L*(n+1) = L*n+1+(L-1) := by rw [Nat.mul_succ]; omega
    rw [he, virtualDepth_inside L n (L-1) (by omega), ih]

theorem phase_virtualDepth (L : Nat) (hL : 0 < L) (h : List Graph) (g : Graph)
    (d : Nat) (hd : d < L) :
    virtualDepth (active L) (phase L h g d).length = h.length+1 := by
  rw [phase_length L hL, virtualDepth_inside L h.length d hd, virtualDepth_boundary L hL]

theorem core_padding (schedule : Nat → Bool) (h : List Graph) (d : Nat) :
    core schedule (h ++ List.replicate d .both) = core schedule h := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [List.replicate_add, ← List.append_assoc]
    change core schedule ((h ++ List.replicate d .both) ++ [.both]) = _
    rw [core_append]
    simpa only [decide_true, Bool.or_true, Bool.and_true] using ih

theorem embed_core (L : Nat) (hL : 0 < L) (h : List Graph) :
    core (active L) (embed L h) = true := by
  induction h using List.reverseRecOn with
  | nil => rfl
  | append_singleton h g ih =>
    rw [embed_append]
    unfold phase
    rw [core_padding, core_append, embed_length L hL, active_boundary]
    simp [ih]

theorem phase_core (L : Nat) (hL : 0 < L) (h : List Graph) (g : Graph) (d : Nat) :
    core (active L) (phase L h g d) = true := by
  unfold phase
  rw [core_padding, core_append, embed_length L hL, active_boundary, embed_core L hL]
  simp

/-- The actual tagged endpoint belonging to a named process. -/
def endpoint (h : List Graph) : Proc → Vertex
  | .one => .inl (evaluate h).one
  | .two => .inr (evaluate h).two

theorem endpoint_reachable (h : List Graph) (p : Proc) : Reachable h.length (endpoint h p) := by
  refine ⟨h, rfl, ?_⟩
  cases p
  · exact Or.inl rfl
  · exact Or.inr rfl

def ownerAt (d : Nat) (p : Proc) : Proc := if d % 2 = 0 then p else p.other

theorem phase_coordinate (L : Nat) (hL : 0 < L) (heven : (L-1) % 2 = 0)
    (h : List Graph) (g : Graph) (d : Nat) (hd : d < L) (p : Proc) :
    vertexProject (active L) (endpoint (phase L h g d) p) =
      coordinate (endpoint (h ++ [g]) (ownerAt d p)) := by
  have he := phase_projection_original L hL heven h g d hd
  have h₁ := congrArg Prod.fst he
  have h₂ := congrArg Prod.snd he
  cases p <;> by_cases hmod : d % 2 = 0 <;>
    simp [pairProject, swapped, swap, hmod, endpoint, ownerAt,
      coordinate, vertexProject, Proc.other] at h₁ h₂ ⊢
  all_goals first | exact h₁ | exact h₂

/-- Exact identification of the projected original view, including its owner
and its full recursive contents. No view-correspondence premise is assumed. -/
theorem phase_view_iff (L : Nat) (hL : 0 < L) (heven : (L-1) % 2 = 0)
    (h : List Graph) (g : Graph) (d : Nat) (hd : d < L) (p : Proc) (u : Vertex) :
    (Reachable (virtualDepth (active L) (phase L h g d).length) u ∧
      coordinate u = vertexProject (active L) (endpoint (phase L h g d) p)) ↔
      u = endpoint (h ++ [g]) (ownerAt d p) := by
  rw [phase_virtualDepth L hL h g d hd, phase_coordinate L hL heven h g d hd p]
  have hr : Reachable (h.length+1) (endpoint (h ++ [g]) (ownerAt d p)) := by
    simpa using endpoint_reachable (h ++ [g]) (ownerAt d p)
  constructor
  · rintro ⟨hu, hp⟩
    exact coordinate_injective hu hr hp
  · rintro rfl
    exact ⟨hr, rfl⟩

/-- Specialization to the binary frame `11 0 b₀ 0 ... b_{K-1} 0`.
At every data position physical process `p` represents original process
`p.other`; this holds for every original history and every encoded bit. -/
theorem binary_data_view_iff (K : Nat) (h : List Graph) (g : Graph)
    (j : Nat) (hj : j < K) (p : Proc) (u : Vertex) :
    (Reachable (h.length+1) u ∧ coordinate u =
      vertexProject (active (2*K+3)) (endpoint (phase (2*K+3) h g (2*j+3)) p)) ↔
      u = endpoint (h ++ [g]) p.other := by
  have hl : 0 < 2*K+3 := by omega
  have he : (2*K+3-1) % 2 = 0 := by omega
  have hd : 2*j+3 < 2*K+3 := by omega
  have hp := phase_view_iff (2*K+3) hl he h g (2*j+3) hd p u
  rw [phase_virtualDepth (2*K+3) hl h g (2*j+3) hd] at hp
  simpa [ownerAt, show (2*j+3) % 2 ≠ 0 by omega] using hp

/-- Infinite environment embedding: only block starts carry source graphs. -/
def stream (L : Nat) (source : Nat → Graph) (t : Nat) : Graph :=
  if t % L = 0 then source (t/L) else .both

def graphPrefix (source : Nat → Graph) (t : Nat) : List Graph := (List.range t).map source

@[simp] theorem prefix_length (source : Nat → Graph) (t : Nat) :
    (graphPrefix source t).length = t := by simp [graphPrefix]

theorem prefix_succ (source : Nat → Graph) (t : Nat) :
    graphPrefix source (t+1) = graphPrefix source t ++ [source t] := by
  simp [graphPrefix, List.range_succ]

theorem stream_boundary (L : Nat) (hL : 0 < L) (source : Nat → Graph) (n : Nat) :
    stream L source (L*n) = source n := by simp [stream, Nat.mul_div_cancel_left _ hL]

theorem stream_inside (L : Nat) (source : Nat → Graph) (n j : Nat)
    (hj : 0 < j) (hjL : j < L) : stream L source (L*n+j) = .both := by
  simp [stream, Nat.add_mod, Nat.mod_eq_of_lt hjL, Nat.ne_of_gt hj]

private theorem prefix_phase_of_boundary (L : Nat) (hL : 0 < L)
    (source : Nat → Graph) (n : Nat)
    (hb : graphPrefix (stream L source) (L*n) = embed L (graphPrefix source n))
    (d : Nat) (hd : d < L) :
    graphPrefix (stream L source) (L*n+1+d) = phase L (graphPrefix source n) (source n) d := by
  induction d with
  | zero => simp [phase, prefix_succ, hb, stream_boundary L hL]
  | succ d ih =>
    rw [show L*n+1+(d+1) = (L*n+1+d)+1 by omega, prefix_succ, ih (by omega)]
    rw [show L*n+1+d = L*n+(1+d) by omega,
      stream_inside L source n (1+d) (by omega) (by omega)]
    simp only [phase, List.replicate_add, List.replicate_one, List.append_assoc]

theorem stream_prefix_boundary (L : Nat) (hL : 0 < L) (source : Nat → Graph) (n : Nat) :
    graphPrefix (stream L source) (L*n) = embed L (graphPrefix source n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have he : L*(n+1) = L*n+1+(L-1) := by rw [Nat.mul_succ]; omega
    rw [he, prefix_phase_of_boundary L hL source n ih (L-1) (by omega),
      prefix_succ, embed_append]

/-- The finite block embedding really is the prefix of one infinite target
environment; it is not a separate choice of environment for every data bit. -/
theorem stream_prefix_phase (L : Nat) (hL : 0 < L) (source : Nat → Graph)
    (n d : Nat) (hd : d < L) :
    graphPrefix (stream L source) (L*n+1+d) = phase L (graphPrefix source n) (source n) d :=
  prefix_phase_of_boundary L hL source n (stream_prefix_boundary L hL source n) d hd

/-- On the single embedded infinite play, every binary data position decodes
the other process's original view after round `n+1`. -/
theorem binary_stream_data_view_iff (K : Nat) (source : Nat → Graph)
    (n j : Nat) (hj : j < K) (p : Proc) (u : Vertex) :
    (Reachable (n+1) u ∧ coordinate u = vertexProject (active (2*K+3))
      (endpoint (graphPrefix (stream (2*K+3) source) ((2*K+3)*n+1+(2*j+3))) p)) ↔
      u = endpoint (graphPrefix source (n+1)) p.other := by
  rw [stream_prefix_phase (2*K+3) (by omega) source n (2*j+3) (by omega), prefix_succ]
  simpa only [prefix_length] using binary_data_view_iff K (graphPrefix source n) (source n) j hj p u

end DistributedSynthesis.BlockEmbedding
