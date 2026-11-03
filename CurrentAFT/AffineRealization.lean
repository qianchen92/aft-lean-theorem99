import CurrentAFT.AffineBaseline

/-! # Actual queue columns and integral affine realization of the lobster load -/
namespace CurrentAFT.AffineRealization
open AFT LobsterCoordinates LobsterMixerMatrix AffineBaseline
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

def queueEmbedding (bodyEdges legs modulus : ℕ)
    (queues : Fin modulus ↪ Fin (bodyEdges + 1))
    (relabeling : Equiv.Perm (Fin (bodyEdges + (legs + legs) + 1))) :
    Fin modulus ↪ Fin (bodyEdges + (legs + legs) + 1) :=
  queues.trans ((Function.Embedding.inl : Fin (bodyEdges + 1) ↪
    (Fin (bodyEdges + 1) ⊕ (Fin legs ⊕ Fin legs))).trans
      ((vertexIndex bodyEdges legs).toEmbedding.trans relabeling.toEmbedding))

def queueColumn (bodyEdges legs modulus : ℕ)
    (queues : Fin modulus ↪ Fin (bodyEdges + 1))
    (relabeling : Equiv.Perm (Fin (bodyEdges + (legs + legs) + 1))) :
    Fin (bodyEdges + (legs + legs) + 1) → ℤ :=
  fun index => if index ∈ Finset.univ.map (queueEmbedding bodyEdges legs modulus queues relabeling) then 1 else 0

theorem queueColumn_charge (bodyEdges legs modulus : ℕ)
    (queues : Fin modulus ↪ Fin (bodyEdges + 1))
    (relabeling : Equiv.Perm (Fin (bodyEdges + (legs + legs) + 1))) :
    totalCharge (queueColumn bodyEdges legs modulus queues relabeling) = (modulus : ℤ) := by
  simp [totalCharge, queueColumn]
  exact (Finset.card_image_of_injective _ (queueEmbedding bodyEdges legs modulus queues relabeling).injective).trans
    (by simp)

theorem queue_modulus_le (bodyEdges legs modulus : ℕ) (queues : Fin modulus ↪ Fin (bodyEdges + 1)) :
    modulus ≤ bodyEdges + (legs + legs) + 1 := by
  have h := Fintype.card_le_of_injective queues queues.injective
  simp only [Fintype.card_fin] at h
  omega

def extensionCorrection (bodyEdges legs modulus : ℕ)
    (queues : Fin modulus ↪ Fin (bodyEdges + 1))
    (relabeling : Equiv.Perm (Fin (bodyEdges + (legs + legs) + 1))) :
    Fin (bodyEdges + (legs + legs)) → ℤ :=
  Classical.choose (exists_extension_correction _
    (injectionColumn _ modulus) (queueColumn bodyEdges legs modulus queues relabeling)
    ((queueColumn_charge bodyEdges legs modulus queues relabeling).trans
      (totalCharge_injectionColumn _ modulus (queue_modulus_le bodyEdges legs modulus queues)).symm))

theorem extensionCorrection_load (bodyEdges legs modulus : ℕ)
    (queues : Fin modulus ↪ Fin (bodyEdges + 1))
    (relabeling : Equiv.Perm (Fin (bodyEdges + (legs + legs) + 1))) :
    pathLoad _ (extensionCorrection bodyEdges legs modulus queues relabeling) =
      queueColumn bodyEdges legs modulus queues relabeling - injectionColumn _ modulus :=
  (Classical.choose_spec (exists_extension_correction _
    (injectionColumn _ modulus) (queueColumn bodyEdges legs modulus queues relabeling)
    ((queueColumn_charge bodyEdges legs modulus queues relabeling).trans
      (totalCharge_injectionColumn _ modulus (queue_modulus_le bodyEdges legs modulus queues)).symm))).1

def linearPart (bodyEdges legs modulus : ℕ)
    (queues : Fin modulus ↪ Fin (bodyEdges + 1))
    (placement : Equiv.Perm (Fin (bodyEdges + 1))) (attachment : Fin legs → Fin (bodyEdges + 1))
    (relabeling : Equiv.Perm (Fin (bodyEdges + (legs + legs) + 1)))
    (scale shear : Fin legs → ℤ) :
    ((Fin (bodyEdges + (legs + legs)) → ℤ) × ℤ) →ₗ[ℤ]
      ((Fin (bodyEdges + (legs + legs)) → ℤ) × ℤ) :=
  blockTransport _ (edgeBasisChange _ (relabeledBasis bodyEdges legs placement attachment relabeling))
    (numberedMatrix bodyEdges legs scale shear).mulVecLin
    (extensionCorrection bodyEdges legs modulus queues relabeling)

theorem linearPart_load (bodyEdges legs modulus : ℕ)
    (queues : Fin modulus ↪ Fin (bodyEdges + 1))
    (placement : Equiv.Perm (Fin (bodyEdges + 1))) (attachment : Fin legs → Fin (bodyEdges + 1))
    (relabeling : Equiv.Perm (Fin (bodyEdges + (legs + legs) + 1)))
    (scale shear : Fin legs → ℤ) (input : (Fin (bodyEdges + (legs + legs)) → ℤ) × ℤ) :
    roundingLoad _ (injectionColumn _ modulus)
      (linearPart bodyEdges legs modulus queues placement attachment relabeling scale shear input) =
      (relabeledBasis bodyEdges legs placement attachment relabeling
        ((numberedMatrix bodyEdges legs scale shear).mulVec input.1)).val +
          input.2 • queueColumn bodyEdges legs modulus queues relabeling :=
  tree_transport_identity _ _ _ _ _ _
    (extensionCorrection_load bodyEdges legs modulus queues relabeling) input

def offsetCoordinates (bodyEdges legs modulus : ℕ) [NeZero modulus]
    (queues : Fin modulus ↪ Fin (bodyEdges + 1))
    (centers : Fin (bodyEdges + 1) → ℤ) (shift intercept : Fin legs → ℤ)
    (placement : Equiv.Perm (Fin (bodyEdges + 1))) (closureScalar : ℤ)
    (relabeling : Equiv.Perm (Fin (bodyEdges + (legs + legs) + 1)))
    (hcharge : PublicCharge.PublicChargeTest modulus centers shift) :
    (Fin (bodyEdges + (legs + legs)) → ℤ) × ℤ :=
  Classical.choose (offset_integral_preimage bodyEdges legs modulus (NeZero.ne modulus)
    (injectionColumn _ modulus) (totalCharge_injectionColumn _ modulus (queue_modulus_le bodyEdges legs modulus queues))
    centers shift intercept placement closureScalar relabeling hcharge)

theorem offsetCoordinates_load (bodyEdges legs modulus : ℕ) [NeZero modulus]
    (queues : Fin modulus ↪ Fin (bodyEdges + 1))
    (centers : Fin (bodyEdges + 1) → ℤ) (shift intercept : Fin legs → ℤ)
    (placement : Equiv.Perm (Fin (bodyEdges + 1))) (closureScalar : ℤ)
    (relabeling : Equiv.Perm (Fin (bodyEdges + (legs + legs) + 1)))
    (hcharge : PublicCharge.PublicChargeTest modulus centers shift) :
    roundingLoad _ (injectionColumn _ modulus)
      (offsetCoordinates bodyEdges legs modulus queues centers shift intercept placement closureScalar relabeling hcharge) =
        numberedOffset bodyEdges legs modulus centers shift intercept placement closureScalar relabeling :=
  (Classical.choose_spec (offset_integral_preimage bodyEdges legs modulus (NeZero.ne modulus)
    (injectionColumn _ modulus) (totalCharge_injectionColumn _ modulus (queue_modulus_le bodyEdges legs modulus queues))
    centers shift intercept placement closureScalar relabeling hcharge)).1

/-- Exact integer affine assembly for all inputs. The body cycle closure
belongs to the public offset, and the hidden queue remains one coordinate. -/
theorem affine_load (bodyEdges legs modulus : ℕ) [NeZero modulus]
    (queues : Fin modulus ↪ Fin (bodyEdges + 1))
    (placement : Equiv.Perm (Fin (bodyEdges + 1))) (attachment : Fin legs → Fin (bodyEdges + 1))
    (relabeling : Equiv.Perm (Fin (bodyEdges + (legs + legs) + 1)))
    (scale shear : Fin legs → ℤ) (centers : Fin (bodyEdges + 1) → ℤ) (shift intercept : Fin legs → ℤ)
    (closureScalar : ℤ) (hcharge : PublicCharge.PublicChargeTest modulus centers shift)
    (input : (Fin (bodyEdges + (legs + legs)) → ℤ) × ℤ) :
    roundingLoad _ (injectionColumn _ modulus)
      (linearPart bodyEdges legs modulus queues placement attachment relabeling scale shear input +
        offsetCoordinates bodyEdges legs modulus queues centers shift intercept placement closureScalar relabeling hcharge) =
      (relabeledBasis bodyEdges legs placement attachment relabeling
        ((numberedMatrix bodyEdges legs scale shear).mulVec input.1)).val +
        input.2 • queueColumn bodyEdges legs modulus queues relabeling +
        numberedOffset bodyEdges legs modulus centers shift intercept placement closureScalar relabeling := by
  have hadd (n : ℕ) (column : Fin (n + 1) → ℤ) (first second : (Fin n → ℤ) × ℤ) :
      roundingLoad n column (first + second) = roundingLoad n column first + roundingLoad n column second := by
    simp only [roundingLoad, Prod.fst_add, Prod.snd_add, pathLoad_add, add_smul]
    abel
  rw [hadd, linearPart_load, offsetCoordinates_load]

def matrix (bodyEdges legs modulus : ℕ)
    (queues : Fin modulus ↪ Fin (bodyEdges + 1))
    (placement : Equiv.Perm (Fin (bodyEdges + 1))) (attachment : Fin legs → Fin (bodyEdges + 1))
    (relabeling : Equiv.Perm (Fin (bodyEdges + (legs + legs) + 1))) (scale shear : Fin legs → ℤ) :
    Matrix (Fin (bodyEdges + (legs + legs)) ⊕ Unit) (Fin (bodyEdges + (legs + legs)) ⊕ Unit) ℤ :=
  transportBlockMatrix _ (edgeBasisChangeMatrix _ (relabeledBasis bodyEdges legs placement attachment relabeling))
    (numberedMatrix bodyEdges legs scale shear) (extensionCorrection bodyEdges legs modulus queues relabeling)

theorem basis_matrix_action (count : ℕ) (basis : (Fin count → ℤ) ≃ₗ[ℤ] zeroSumLattice count)
    (input : Fin count → ℤ) :
    (edgeBasisChangeMatrix count basis).mulVec input = edgeBasisChange count basis input := by
  simpa only [edgeBasisChangeMatrix, Pi.basisFun_repr, LinearEquiv.coe_coe] using
    LinearMap.toMatrix_mulVec_repr (Pi.basisFun ℤ (Fin count)) (Pi.basisFun ℤ (Fin count))
      (edgeBasisChange count basis).toLinearMap input

/-- The modularly invertible matrix is exactly the linear map used in the
integer load identity, rather than an unrelated determinant witness. -/
theorem matrix_action (bodyEdges legs modulus : ℕ)
    (queues : Fin modulus ↪ Fin (bodyEdges + 1))
    (placement : Equiv.Perm (Fin (bodyEdges + 1))) (attachment : Fin legs → Fin (bodyEdges + 1))
    (relabeling : Equiv.Perm (Fin (bodyEdges + (legs + legs) + 1)))
    (scale shear : Fin legs → ℤ) (input : (Fin (bodyEdges + (legs + legs)) → ℤ) × ℤ) :
    (matrix bodyEdges legs modulus queues placement attachment relabeling scale shear).mulVec
      (Sum.elim input.1 (fun _ : Unit => input.2)) =
      Sum.elim (linearPart bodyEdges legs modulus queues placement attachment relabeling scale shear input).1
        (fun _ : Unit => (linearPart bodyEdges legs modulus queues placement attachment relabeling scale shear input).2) := by
  rw [matrix, transportBlockMatrix, Matrix.fromBlocks_mulVec]
  simp only [Function.comp_def, Sum.elim_inl, Sum.elim_inr, Matrix.zero_mulVec,
    Matrix.one_mulVec, zero_add, ← Matrix.mulVec_mulVec, basis_matrix_action,
    linearPart, blockTransport, LinearMap.coe_mk, AddHom.coe_mk, Matrix.mulVecLin_apply]
  congr 1
  ext index
  simp [Matrix.mulVec, dotProduct, mul_comm]

theorem matrix_modular_invertible (bodyEdges legs modulus : ℕ) [Fact modulus.Prime]
    (queues : Fin modulus ↪ Fin (bodyEdges + 1))
    (placement : Equiv.Perm (Fin (bodyEdges + 1))) (attachment : Fin legs → Fin (bodyEdges + 1))
    (relabeling : Equiv.Perm (Fin (bodyEdges + (legs + legs) + 1)))
    (scale shear : Fin legs → ℤ) (hscale : ∀ leg, (scale leg : ZMod modulus) ≠ 0) :
    IsUnit ((matrix bodyEdges legs modulus queues placement attachment relabeling scale shear).map
      (Int.castRingHom (ZMod modulus))) :=
  relabeled_transport_modular_invertible bodyEdges legs modulus placement attachment relabeling scale shear hscale _

end
end CurrentAFT.AffineRealization
