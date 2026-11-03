import CurrentAFT.LobsterCoordinates
import CurrentAFT.LegMixer

/-! # The complete integer source mixer and its actual modular determinant -/
namespace CurrentAFT.LobsterMixerMatrix
open AFT LobsterCoordinates
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

variable {Scalar : Type*} [CommRing Scalar]

def blockMatrix (bodyEdges legs : ℕ) (scale shear : Fin legs → Scalar) :
    Matrix (Fin bodyEdges ⊕ (Fin legs ⊕ Fin legs)) (Fin bodyEdges ⊕ (Fin legs ⊕ Fin legs)) Scalar :=
  Matrix.fromBlocks 1 0 0 (Matrix.fromBlocks (Matrix.diagonal scale) (Matrix.diagonal shear) 0 1)

def numberedMatrix (bodyEdges legs : ℕ) (scale shear : Fin legs → Scalar) :
    Matrix (Fin (bodyEdges + (legs + legs))) (Fin (bodyEdges + (legs + legs))) Scalar :=
  Matrix.reindex (edgeIndex bodyEdges legs) (edgeIndex bodyEdges legs) (blockMatrix bodyEdges legs scale shear)

theorem blockMatrix_det (bodyEdges legs : ℕ) (scale shear : Fin legs → Scalar) :
    (blockMatrix bodyEdges legs scale shear).det = ∏ leg, scale leg := by
  simp [blockMatrix]

theorem numberedMatrix_det (bodyEdges legs : ℕ) (scale shear : Fin legs → Scalar) :
    (numberedMatrix bodyEdges legs scale shear).det = ∏ leg, scale leg := by
  rw [numberedMatrix, Matrix.det_reindex_self, blockMatrix_det]

theorem numberedMatrix_action (bodyEdges legs : ℕ) (scale shear : Fin legs → Scalar)
    (input : Fin (bodyEdges + (legs + legs)) → Scalar)
    (index : Fin bodyEdges ⊕ (Fin legs ⊕ Fin legs)) :
    (numberedMatrix bodyEdges legs scale shear).mulVec input (edgeIndex bodyEdges legs index) =
      (blockMatrix bodyEdges legs scale shear).mulVec (input ∘ edgeIndex bodyEdges legs) index := by
  simp only [numberedMatrix, Matrix.mulVec, dotProduct, Matrix.reindex_apply, Matrix.submatrix_apply,
    Equiv.symm_apply_apply]
  rw [← Equiv.sum_comp (edgeIndex bodyEdges legs)]
  simp only [Equiv.symm_apply_apply, Function.comp_apply]

theorem blockMatrix_action (bodyEdges legs : ℕ) (scale shear : Fin legs → Scalar)
    (input : (Fin bodyEdges ⊕ (Fin legs ⊕ Fin legs)) → Scalar) :
    (blockMatrix bodyEdges legs scale shear).mulVec input =
      Sum.elim (fun vertex => input (.inl vertex))
        (Sum.elim (fun leg => scale leg * input (.inr (.inl leg)) + shear leg * input (.inr (.inr leg)))
          (fun leg => input (.inr (.inr leg)))) := by
  ext index
  rcases index with vertex | (leg | leg) <;>
    simp [blockMatrix, Matrix.mulVec, dotProduct, Fintype.sum_sum_type,
      Matrix.one_apply, Matrix.diagonal_apply]

/-- The exact integer mixer used by the incidence construction reduces to
an invertible matrix whenever each public scale is nonzero modulo q. -/
theorem numberedMatrix_mod_det_nonzero (bodyEdges legs modulus : ℕ) [Fact modulus.Prime]
    (scale shear : Fin legs → ℤ) (hscale : ∀ leg, (scale leg : ZMod modulus) ≠ 0) :
    ((numberedMatrix bodyEdges legs scale shear).det : ZMod modulus) ≠ 0 := by
  rw [numberedMatrix_det, Int.cast_prod]
  exact Finset.prod_ne_zero_iff.mpr (fun leg _ => hscale leg)

/-- This is the full current tree-plus-queue transport, with an arbitrary
integral queue-column correction. The graph basis is the proved actual load. -/
theorem transport_modular_invertible (bodyEdges legs modulus : ℕ) [Fact modulus.Prime]
    (placement : Equiv.Perm (Fin (bodyEdges + 1)))
    (attachment : Fin legs → Fin (bodyEdges + 1))
    (scale shear : Fin legs → ℤ) (hscale : ∀ leg, (scale leg : ZMod modulus) ≠ 0)
    (correction : Fin (bodyEdges + (legs + legs)) → ℤ) :
    IsUnit ((transportBlockMatrix (bodyEdges + (legs + legs))
      (edgeBasisChangeMatrix _ (incidenceBasis bodyEdges legs placement attachment))
      (numberedMatrix bodyEdges legs scale shear) correction).map (Int.castRingHom (ZMod modulus))) :=
  tree_transport_modular_invertible _ modulus (incidenceBasis bodyEdges legs placement attachment)
    _ correction (numberedMatrix_mod_det_nonzero bodyEdges legs modulus scale shear hscale)

theorem transport_determinant (bodyEdges legs : ℕ)
    (placement : Equiv.Perm (Fin (bodyEdges + 1))) (attachment : Fin legs → Fin (bodyEdges + 1))
    (scale shear : Fin legs → ℤ) (correction : Fin (bodyEdges + (legs + legs)) → ℤ) :
    (transportBlockMatrix (bodyEdges + (legs + legs))
      (edgeBasisChangeMatrix _ (incidenceBasis bodyEdges legs placement attachment))
      (numberedMatrix bodyEdges legs scale shear) correction).det = (∏ leg, scale leg) ∨
    (transportBlockMatrix (bodyEdges + (legs + legs))
      (edgeBasisChangeMatrix _ (incidenceBasis bodyEdges legs placement attachment))
      (numberedMatrix bodyEdges legs scale shear) correction).det = -(∏ leg, scale leg) := by
  simpa only [numberedMatrix_det] using tree_transport_determinant (bodyEdges + (legs + legs))
    (incidenceBasis bodyEdges legs placement attachment) (numberedMatrix bodyEdges legs scale shear) correction

theorem relabeled_transport_modular_invertible (bodyEdges legs modulus : ℕ) [Fact modulus.Prime]
    (placement : Equiv.Perm (Fin (bodyEdges + 1))) (attachment : Fin legs → Fin (bodyEdges + 1))
    (relabeling : Equiv.Perm (Fin (bodyEdges + (legs + legs) + 1)))
    (scale shear : Fin legs → ℤ) (hscale : ∀ leg, (scale leg : ZMod modulus) ≠ 0)
    (correction : Fin (bodyEdges + (legs + legs)) → ℤ) :
    IsUnit ((transportBlockMatrix (bodyEdges + (legs + legs))
      (edgeBasisChangeMatrix _ (relabeledBasis bodyEdges legs placement attachment relabeling))
      (numberedMatrix bodyEdges legs scale shear) correction).map (Int.castRingHom (ZMod modulus))) :=
  tree_transport_modular_invertible _ modulus
    (relabeledBasis bodyEdges legs placement attachment relabeling) _ correction
    (numberedMatrix_mod_det_nonzero bodyEdges legs modulus scale shear hscale)

end
end CurrentAFT.LobsterMixerMatrix
