import AFT.PhysicalCoordinateBasis

/-! # The concrete V7 edge matrix is invertible modulo the actual prime -/
namespace AFT.V7Calibration
open GaussianSource BoundaryCalibration
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
attribute [local instance] actualModulusNeZero

variable {R : Type*} [CommRing R]

def physicalChartLinear (n : ℕ) (scale shear : Fin (Parameters.legs n) → R) :
    (Fin (Parameters.dimension n-1) → R) →ₗ[R] (Fin (Parameters.dimension n-1) → R) :=
  (physicalEdgeCoordinates n).symm.toLinearMap.comp
    ((LinearMap.prodMap (legTriangularLinear scale shear) (LinearMap.id)).comp
      (physicalEdgeCoordinates n).toLinearMap)

def physicalChartEquiv {K : Type*} [Field K] (n : ℕ)
    (scale shear : Fin (Parameters.legs n) → K) (hscale : ∀ leg,scale leg ≠ 0) :
    (Fin (Parameters.dimension n-1) → K) ≃ₗ[K] (Fin (Parameters.dimension n-1) → K) :=
  (physicalEdgeCoordinates n).trans
    ((LinearEquiv.prodCongr (legTriangularEquiv scale shear hscale) (LinearEquiv.refl _ _)).trans
      (physicalEdgeCoordinates n).symm)

theorem physicalChartEquiv_toLinearMap {K : Type*} [Field K] (n : ℕ)
    (scale shear : Fin (Parameters.legs n) → K) (hscale : ∀ leg,scale leg ≠ 0) :
    (physicalChartEquiv n scale shear hscale).toLinearMap=physicalChartLinear n scale shear := rfl

def actualPhysicalEdgeLinear (n : ℕ)
    (chart : Fin (Parameters.legs n) → Chart (ZMod (Parameters.modulus n))) :
    (Fin (Parameters.dimension n-1) → ℤ) →ₗ[ℤ] (Fin (Parameters.dimension n-1) → ℤ) :=
  physicalChartLinear n (fun leg => ((chart leg).2.1.val : ℤ)) (fun leg => ((chart leg).2.2.val : ℤ))

def actualPhysicalEdgeMatrix (n : ℕ)
    (chart : Fin (Parameters.legs n) → Chart (ZMod (Parameters.modulus n))) :
    Matrix (Fin (Parameters.dimension n-1)) (Fin (Parameters.dimension n-1)) ℤ :=
  LinearMap.toMatrix (Pi.basisFun ℤ _) (Pi.basisFun ℤ _) (actualPhysicalEdgeLinear n chart)

/-- Coordinate changes use only relabeling and pairing, so the integer
edge map reduces to the same triangular map over the residue field. -/
theorem physicalChartLinear_map {S : Type*} [CommRing S] (f : R →+* S) (n : ℕ)
    (scale shear : Fin (Parameters.legs n) → R) (input : Fin (Parameters.dimension n-1) → R) :
    (fun index => f (physicalChartLinear n scale shear input index))=
      physicalChartLinear n (fun leg => f (scale leg)) (fun leg => f (shear leg))
        (fun index => f (input index)) := by
  funext index
  obtain ⟨index,rfl⟩ := (physicalEdgeIndexEquiv n).surjective index
  rcases index with ⟨leg,slot⟩|body
  · fin_cases slot <;>
      simp [physicalChartLinear,physicalEdgeCoordinates,physicalEdgePairEquiv,
        legTriangularLinear,LinearEquiv.sumArrowLequivProdArrow,LinearEquiv.funCongrLeft,
        Equiv.sumArrowEquivProdArrow,LinearEquiv.prodCongr_symm]
  · simp [physicalChartLinear,physicalEdgeCoordinates,physicalEdgePairEquiv,
      legTriangularLinear,LinearEquiv.sumArrowLequivProdArrow,LinearEquiv.funCongrLeft,
      Equiv.sumArrowEquivProdArrow,LinearEquiv.prodCongr_symm]

/-- Every chart on the actual positive support yields an invertible edge
matrix modulo q. This uses its explicit inverse, not a determinant assumption. -/
theorem actualPhysicalEdgeMatrix_det_nonzero (n : ℕ)
    (chart : Fin (Parameters.legs n) → Chart (ZMod (Parameters.modulus n)))
    (hscale : ∀ leg,(chart leg).2.1 ≠ 0) :
    ((actualPhysicalEdgeMatrix n chart).det : ZMod (Parameters.modulus n)) ≠ 0 := by
  let e := physicalChartEquiv n (fun leg => (chart leg).2.1) (fun leg => (chart leg).2.2) hscale
  have hm : (actualPhysicalEdgeMatrix n chart).map (Int.castRingHom (ZMod (Parameters.modulus n)))=
      LinearMap.toMatrix (Pi.basisFun (ZMod (Parameters.modulus n)) _) (Pi.basisFun (ZMod (Parameters.modulus n)) _) e.toLinearMap := by
    ext i j
    change ((actualPhysicalEdgeLinear n chart (Pi.single j 1) i : ℤ) : ZMod (Parameters.modulus n))=
      e (Pi.single j 1) i
    have h := congrFun (physicalChartLinear_map (Int.castRingHom (ZMod (Parameters.modulus n))) n
      (fun leg => ((chart leg).2.1.val : ℤ)) (fun leg => ((chart leg).2.2.val : ℤ)) (Pi.single j 1)) i
    change _ = physicalChartLinear n (fun leg => (chart leg).2.1) (fun leg => (chart leg).2.2) (Pi.single j 1) i
    have hsingle : (fun index : Fin (Parameters.dimension n-1) =>
        (Int.castRingHom (ZMod (Parameters.modulus n))) ((Pi.single j (1 : ℤ) : Fin (Parameters.dimension n-1) → ℤ) index))=
        (Pi.single j 1 : Fin (Parameters.dimension n-1) → ZMod (Parameters.modulus n)) := by
      funext index
      by_cases hj : index=j <;> simp [Pi.single_apply,hj]
    rw [hsingle] at h
    simpa [actualPhysicalEdgeLinear] using h
  have hu := e.isUnit_det (Pi.basisFun (ZMod (Parameters.modulus n)) _) (Pi.basisFun (ZMod (Parameters.modulus n)) _)
  rw [← hm] at hu
  change IsUnit ((Int.castRingHom (ZMod (Parameters.modulus n))).mapMatrix (actualPhysicalEdgeMatrix n chart)).det at hu
  rw [← RingHom.map_det] at hu
  exact isUnit_iff_ne_zero.mp hu

theorem actual_physical_transport_modular_invertible (n : ℕ)
    (chart : Fin (Parameters.legs n) → Chart (ZMod (Parameters.modulus n)))
    (hscale : ∀ leg,(chart leg).2.1 ≠ 0) (correction : Fin (Parameters.dimension n-1) → ℤ) :
    IsUnit ((transportBlockMatrix (Parameters.dimension n-1)
      (edgeBasisChangeMatrix _ (actualPhysicalIncidenceBasis n)) (actualPhysicalEdgeMatrix n chart) correction).map
      (Int.castRingHom (ZMod (Parameters.modulus n)))) :=
  tree_transport_modular_invertible _ _ (actualPhysicalIncidenceBasis n) _ correction
    (actualPhysicalEdgeMatrix_det_nonzero n chart hscale)

end
end AFT.V7Calibration
