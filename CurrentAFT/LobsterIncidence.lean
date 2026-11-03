import CurrentAFT.PublicCharge
import AFT.Algebra

/-! # Integral basis of the actual placed body path and two-edge legs

The load is written in the manuscript's body, primary, companion order.
Its inverse reads both leg edges and then solves the remaining body path.
Only the generic integral path basis is reused from the frozen directory.
-/
namespace CurrentAFT.LobsterIncidence
open AFT PublicCharge
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

variable {Leg : Type*} [Fintype Leg] {bodyEdges : ℕ}

abbrev Edges (bodyEdges : ℕ) (Leg : Type*) :=
  (Fin bodyEdges → ℤ) × ((Leg → ℤ) × (Leg → ℤ))

def zeroSum (Index : Type*) [Fintype Index] : Submodule ℤ (Index → ℤ) where
  carrier := {word | ∑ index, word index = 0}
  zero_mem' := by simp
  add_mem' := by intro first second hf hs; simp_all [Finset.sum_add_distrib]
  smul_mem' := by
    intro scalar word hw
    change ∑ index, scalar * word index = 0
    rw [← Finset.mul_sum, hw, mul_zero]

def load (placement : Equiv.Perm (Fin (bodyEdges + 1))) (attachment : Leg → Fin (bodyEdges + 1))
    (edges : Edges bodyEdges Leg) : EndpointIndex (bodyEdges + 1) Leg → ℤ
  | .inl vertex => pathLoad bodyEdges edges.1 (placement.symm vertex) +
      attachmentIncrement attachment edges.2.2 vertex
  | .inr (.inl leg) => edges.2.1 leg
  | .inr (.inr leg) => -edges.2.1 leg - edges.2.2 leg

theorem sum_load (placement : Equiv.Perm (Fin (bodyEdges + 1)))
    (attachment : Leg → Fin (bodyEdges + 1)) (edges : Edges bodyEdges Leg) :
    ∑ index, load placement attachment edges index = 0 := by
  simp only [Fintype.sum_sum_type, load, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_neg_distrib]
  rw [placement.symm.sum_comp, sum_attachmentIncrement]
  have h := totalCharge_pathLoad bodyEdges edges.1
  unfold totalCharge at h
  rw [h]
  ring

def firstEdge (word : EndpointIndex (bodyEdges + 1) Leg → ℤ) (leg : Leg) : ℤ := word (.inr (.inl leg))
def secondEdge (word : EndpointIndex (bodyEdges + 1) Leg → ℤ) (leg : Leg) : ℤ :=
  -word (.inr (.inl leg)) - word (.inr (.inr leg))

@[simp] theorem firstEdge_load (placement : Equiv.Perm (Fin (bodyEdges + 1)))
    (attachment : Leg → Fin (bodyEdges + 1)) (edges : Edges bodyEdges Leg) :
    firstEdge (load placement attachment edges) = edges.2.1 := rfl

@[simp] theorem secondEdge_load (placement : Equiv.Perm (Fin (bodyEdges + 1)))
    (attachment : Leg → Fin (bodyEdges + 1)) (edges : Edges bodyEdges Leg) :
    secondEdge (load placement attachment edges) = edges.2.2 := by
  funext leg
  simp only [secondEdge, load]
  ring

def bodyResidual (attachment : Leg → Fin (bodyEdges + 1))
    (word : EndpointIndex (bodyEdges + 1) Leg → ℤ) (vertex : Fin (bodyEdges + 1)) : ℤ :=
  word (.inl vertex) - attachmentIncrement attachment (secondEdge word) vertex

theorem bodyResidual_charge (attachment : Leg → Fin (bodyEdges + 1))
    (word : EndpointIndex (bodyEdges + 1) Leg → ℤ) (hword : ∑ index, word index = 0) :
    ∑ vertex, bodyResidual attachment word vertex = 0 := by
  simp only [bodyResidual, Finset.sum_sub_distrib, sum_attachmentIncrement,
    secondEdge, Finset.sum_neg_distrib]
  simp only [Fintype.sum_sum_type] at hword
  linarith

theorem load_injective (placement : Equiv.Perm (Fin (bodyEdges + 1)))
    (attachment : Leg → Fin (bodyEdges + 1)) : Function.Injective (load placement attachment) := by
  intro first second hequal
  have hfirst := congrArg firstEdge hequal
  have hsecond := congrArg secondEdge hequal
  simp only [firstEdge_load, secondEdge_load] at hfirst hsecond
  have hbody : pathLoad bodyEdges first.1 = pathLoad bodyEdges second.1 := by
    funext vertex
    have h := congrFun hequal (.inl (placement vertex))
    simp only [load, Equiv.symm_apply_apply, hsecond] at h
    exact add_right_cancel h
  exact Prod.ext (pathLoad_injective bodyEdges hbody) (Prod.ext hfirst hsecond)

theorem exists_load (placement : Equiv.Perm (Fin (bodyEdges + 1)))
    (attachment : Leg → Fin (bodyEdges + 1)) (word : EndpointIndex (bodyEdges + 1) Leg → ℤ)
    (hword : ∑ index, word index = 0) : ∃ edges, load placement attachment edges = word := by
  have hroot : totalCharge (fun vertex => bodyResidual attachment word (placement vertex)) = 0 := by
    unfold totalCharge
    rw [Equiv.sum_comp placement]
    exact bodyResidual_charge attachment word hword
  obtain ⟨path, hpath⟩ := AFT.exists_pathLoad bodyEdges _ hroot
  refine ⟨(path, firstEdge word, secondEdge word), ?_⟩
  funext index
  rcases index with vertex | (leg | leg)
  · simp only [load, hpath, Equiv.apply_symm_apply, bodyResidual]
    ring
  · rfl
  · simp only [load, firstEdge, secondEdge]
    ring

def incidenceLinear (placement : Equiv.Perm (Fin (bodyEdges + 1)))
    (attachment : Leg → Fin (bodyEdges + 1)) :
    Edges bodyEdges Leg →ₗ[ℤ] (EndpointIndex (bodyEdges + 1) Leg → ℤ) where
  toFun := load placement attachment
  map_add' first second := by
    funext index
    rcases index with vertex | (leg | leg)
    · have hsplit (leg : Leg) : (if attachment leg = vertex then first.2.2 leg + second.2.2 leg else 0) =
          (if attachment leg = vertex then first.2.2 leg else 0) +
          (if attachment leg = vertex then second.2.2 leg else 0) := by split_ifs <;> simp
      simp only [load, Prod.fst_add, Prod.snd_add, pathLoad_add, Pi.add_apply,
        attachmentIncrement, hsplit, Finset.sum_add_distrib]
      ring
    · rfl
    · simp only [load, Prod.fst_add, Prod.snd_add, Pi.add_apply]
      ring
  map_smul' scalar edges := by
    funext index
    rcases index with vertex | (leg | leg)
    · have hsplit (leg : Leg) : (if attachment leg = vertex then scalar * edges.2.2 leg else 0) =
          scalar * (if attachment leg = vertex then edges.2.2 leg else 0) := by split_ifs <;> simp
      simp only [load, Prod.smul_fst, Prod.smul_snd, pathLoad_smul, Pi.smul_apply, smul_eq_mul,
        attachmentIncrement, hsplit, ← Finset.mul_sum, RingHom.id_apply]
      ring
    · rfl
    · simp only [load, Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
      ring

/-- The actual placed incidence is an integral basis, for every attachment
map and every body permutation; no graph or rank hypothesis is assumed. -/
def basis (placement : Equiv.Perm (Fin (bodyEdges + 1)))
    (attachment : Leg → Fin (bodyEdges + 1)) :
    Edges bodyEdges Leg ≃ₗ[ℤ] zeroSum (EndpointIndex (bodyEdges + 1) Leg) :=
  LinearEquiv.ofBijective
    ((incidenceLinear placement attachment).codRestrict _ (sum_load placement attachment)) (by
      constructor
      · intro first second hequal
        exact load_injective placement attachment (congrArg Subtype.val hequal)
      · rintro ⟨word, hword⟩
        obtain ⟨edges, hequal⟩ := exists_load placement attachment word hword
        exact ⟨edges, Subtype.ext hequal⟩)

@[simp] theorem basis_apply (placement : Equiv.Perm (Fin (bodyEdges + 1)))
    (attachment : Leg → Fin (bodyEdges + 1)) (edges : Edges bodyEdges Leg) :
    (basis placement attachment edges).val = load placement attachment edges := rfl

end
end CurrentAFT.LobsterIncidence
