import AFT.PhysicalAffinePair

/-! # Reduction of actual integer linear equivalences -/
namespace AFT
open V7Calibration
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false

def integerCoordinateMatrix (count : ℕ)
    (linear : ((Fin count → ℤ) × ℤ) ≃ₗ[ℤ] ((Fin count → ℤ) × ℤ)) :
    Matrix (Fin count ⊕ Unit) (Fin count ⊕ Unit) ℤ :=
  LinearMap.toMatrix (Pi.basisFun _ _) (Pi.basisFun _ _)
    (((extensionCoordinates count).symm.trans linear).trans (extensionCoordinates count)).toLinearMap

theorem integerCoordinateMatrix_det_unit (count : ℕ)
    (linear : ((Fin count → ℤ) × ℤ) ≃ₗ[ℤ] ((Fin count → ℤ) × ℤ)) :
    IsUnit (integerCoordinateMatrix count linear).det :=
  (((extensionCoordinates count).symm.trans linear).trans (extensionCoordinates count)).isUnit_det _ _

def reduceIntegerLinearEquiv (count q : ℕ)
    (linear : ((Fin count → ℤ) × ℤ) ≃ₗ[ℤ] ((Fin count → ℤ) × ℤ)) :
    ((Fin count → ZMod q) × ZMod q) ≃ₗ[ZMod q] ((Fin count → ZMod q) × ZMod q) :=
  (extensionCoordinates count).trans
    ((((integerCoordinateMatrix count linear).map (Int.castRingHom (ZMod q))).toLinearEquiv
      (Pi.basisFun _ _)
      (by
        change IsUnit ((Int.castRingHom (ZMod q)).mapMatrix (integerCoordinateMatrix count linear)).det
        rw [← (Int.castRingHom (ZMod q)).map_det]
        exact (integerCoordinateMatrix_det_unit count linear).map (Int.castRingHom (ZMod q)))).trans
          (extensionCoordinates count).symm)

/-- Reducing the integer matrix agrees with reducing its integer action;
invertibility follows from the proved integral inverse. -/
theorem reduceIntegerLinearEquiv_apply (count q : ℕ)
    (linear : ((Fin count → ℤ) × ℤ) ≃ₗ[ℤ] ((Fin count → ℤ) × ℤ))
    (input : (Fin count → ℤ) × ℤ) :
    reduceIntegerLinearEquiv count q linear (reduceCoordinates count q input)=
      reduceCoordinates count q (linear input) := by
  apply (extensionCoordinates count).injective
  simp only [reduceIntegerLinearEquiv,LinearEquiv.trans_apply,LinearEquiv.apply_symm_apply,Matrix.toLinearEquiv_apply]
  change ((integerCoordinateMatrix count linear).map (Int.castRingHom (ZMod q))).mulVec
    (extensionCoordinates count (reduceCoordinates count q input))=_
  have hh := RingHom.map_mulVec (Int.castRingHom (ZMod q))
    (integerCoordinateMatrix count linear) (extensionCoordinates count input)
  have he (word : (Fin count → ℤ) × ℤ) :
      extensionCoordinates count (reduceCoordinates count q word)=
        (Int.castRingHom (ZMod q)) ∘ extensionCoordinates count word := by
    funext index
    cases index <;> rfl
  have hm : (integerCoordinateMatrix count linear).mulVec (extensionCoordinates count input)=
      extensionCoordinates count (linear input) := by
    simp only [integerCoordinateMatrix,LinearMap.toMatrix_eq_toMatrix',LinearMap.toMatrix'_mulVec,
      LinearEquiv.coe_coe,LinearEquiv.trans_apply,LinearEquiv.symm_apply_apply]
  rw [hm] at hh
  rw [he,he]
  exact (funext hh).symm

end
end AFT
