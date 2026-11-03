import AFT.PhysicalAffineLoad
import AFT.Affine
import AFT.Geometry
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-! # A legal affine pair for each actual positive physical chart -/
namespace AFT.V7Calibration
open GaussianSource BoundaryCalibration
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
attribute [local instance] actualModulusNeZero

variable {R : Type*} [CommRing R]

def extensionCoordinates (size : ℕ) : ((Fin size → R) × R) ≃ₗ[R] ((Fin size ⊕ Unit) → R) where
  toFun point := Sum.elim point.1 (fun _ => point.2)
  invFun word := (fun index => word (.inl index),word (.inr ()))
  left_inv := by intro point; rfl
  right_inv := by intro word; funext index; rcases index with index|⟨⟩ <;> rfl
  map_add' := by intro first second; funext index; cases index <;> rfl
  map_smul' := by intro scalar point; funext index; cases index <;> rfl

def actualPhysicalTransportMatrix (n : ℕ)
    (chart : Fin (Parameters.legs n) → Chart (ZMod (Parameters.modulus n)))
    (placement : Equiv.Perm (blockIndex n)) :
    Matrix (Fin (Parameters.dimension n-1) ⊕ Unit) (Fin (Parameters.dimension n-1) ⊕ Unit) ℤ :=
  transportBlockMatrix _ (edgeBasisChangeMatrix _ (actualPhysicalIncidenceBasis n))
    (actualPhysicalEdgeMatrix n chart) (actualPhysicalCorrection n placement)

theorem actualPhysicalTransportMatrix_apply (n : ℕ)
    (chart : Fin (Parameters.legs n) → Chart (ZMod (Parameters.modulus n)))
    (placement : Equiv.Perm (blockIndex n))
    (input : (Fin (Parameters.dimension n-1) → ℤ) × ℤ) :
    (actualPhysicalTransportMatrix n chart placement).mulVec (extensionCoordinates _ input)=
      extensionCoordinates _ (actualPhysicalTransport n chart placement input) := by
  unfold actualPhysicalTransportMatrix transportBlockMatrix
  rw [Matrix.fromBlocks_mulVec]
  funext index
  cases index with
  | inl index =>
    change (((edgeBasisChangeMatrix _ (actualPhysicalIncidenceBasis n))*(actualPhysicalEdgeMatrix n chart)).mulVec input.1 index+
      (∑ _ : Unit,actualPhysicalCorrection n placement index*input.2))=_
    rw [← Matrix.mulVec_mulVec]
    simp only [edgeBasisChangeMatrix,actualPhysicalEdgeMatrix,LinearMap.toMatrix_eq_toMatrix',
      LinearMap.toMatrix'_mulVec,Fintype.sum_unique]
    simp [extensionCoordinates,actualPhysicalTransport,blockTransport,mul_comm]
  | inr index =>
    simp [Matrix.zero_mulVec,Matrix.one_mulVec,extensionCoordinates,actualPhysicalTransport,blockTransport]

def actualPhysicalReducedTransport (n : ℕ)
    (chart : Fin (Parameters.legs n) → Chart (ZMod (Parameters.modulus n)))
    (hscale : ∀ leg,(chart leg).2.1 ≠ 0) (placement : Equiv.Perm (blockIndex n)) :
    ((Fin (Parameters.dimension n-1) → ZMod (Parameters.modulus n)) × ZMod (Parameters.modulus n)) ≃ₗ[ZMod (Parameters.modulus n)]
      ((Fin (Parameters.dimension n-1) → ZMod (Parameters.modulus n)) × ZMod (Parameters.modulus n)) :=
  (extensionCoordinates _).trans
    (((actualPhysicalTransportMatrix n chart placement).map (Int.castRingHom (ZMod (Parameters.modulus n)))).toLinearEquiv
      (Pi.basisFun _ _) ((Matrix.isUnit_iff_isUnit_det _).mp
        (actual_physical_transport_modular_invertible n chart hscale (actualPhysicalCorrection n placement))) |>.trans
          (extensionCoordinates _).symm)

/-- Reduction of the constructed integer transport agrees with the same
proved invertible map used in the affine output. -/
theorem actualPhysicalReducedTransport_reduce (n : ℕ)
    (chart : Fin (Parameters.legs n) → Chart (ZMod (Parameters.modulus n)))
    (hscale : ∀ leg,(chart leg).2.1 ≠ 0) (placement : Equiv.Perm (blockIndex n))
    (input : (Fin (Parameters.dimension n-1) → ℤ) × ℤ) :
    actualPhysicalReducedTransport n chart hscale placement (reduceCoordinates _ _ input)=
      reduceCoordinates _ _ (actualPhysicalTransport n chart placement input) := by
  apply (extensionCoordinates _).injective
  simp only [actualPhysicalReducedTransport,LinearEquiv.trans_apply,LinearEquiv.apply_symm_apply,
    Matrix.toLinearEquiv_apply]
  change ((actualPhysicalTransportMatrix n chart placement).map (Int.castRingHom (ZMod (Parameters.modulus n)))).mulVec
      (extensionCoordinates _ (reduceCoordinates _ _ input))=
    extensionCoordinates _ (reduceCoordinates _ _ (actualPhysicalTransport n chart placement input))
  have h := RingHom.map_mulVec (Int.castRingHom (ZMod (Parameters.modulus n)))
    (actualPhysicalTransportMatrix n chart placement) (extensionCoordinates _ input)
  rw [actualPhysicalTransportMatrix_apply] at h
  have he (word : (Fin (Parameters.dimension n-1) → ℤ) × ℤ) :
      extensionCoordinates _ (reduceCoordinates _ (Parameters.modulus n) word)=
        (Int.castRingHom (ZMod (Parameters.modulus n))) ∘ extensionCoordinates _ word := by
    funext index
    cases index <;> rfl
  rw [he,he]
  exact (funext h).symm

def actualPhysicalInitialCoordinates (C : ℝ) (n : ℕ)
    (chart : Fin (Parameters.legs n) → Chart (ZMod (Parameters.modulus n)))
    (baseline : Fin (Parameters.legs n) → ℤ) (center : blockIndex n → Fin (Parameters.modulus n))
    (hcharge : (Parameters.modulus n : ℤ) ∣
      (∑ leg,baseline leg)+(∑ index,((center index).val : ℤ))-(Parameters.legs n : ℤ)) :
    (Fin (Parameters.dimension n-1) → ℤ) × ℤ :=
  (roundingCoordinates _ (Parameters.modulus n) (by exact_mod_cast (NeZero.ne (Parameters.modulus n)))
    (injectionColumn _ (Parameters.modulus n)) (totalCharge_injectionColumn _ _ (modulus_le_actualDimension n))).symm
      ⟨actualPhysicalInitialLoad C n chart baseline center,actualPhysicalInitialLoad_charge C n chart baseline center hcharge⟩

theorem actualPhysicalInitialCoordinates_load (C : ℝ) (n : ℕ)
    (chart : Fin (Parameters.legs n) → Chart (ZMod (Parameters.modulus n)))
    (baseline : Fin (Parameters.legs n) → ℤ) (center : blockIndex n → Fin (Parameters.modulus n))
    (hcharge : (Parameters.modulus n : ℤ) ∣
      (∑ leg,baseline leg)+(∑ index,((center index).val : ℤ))-(Parameters.legs n : ℤ)) :
    roundingLoad _ (injectionColumn _ (Parameters.modulus n)) (actualPhysicalInitialCoordinates C n chart baseline center hcharge)=
      actualPhysicalInitialLoad C n chart baseline center := by
  exact congrArg Subtype.val ((roundingCoordinates _ _ _ _ _).apply_symm_apply _)

def actualPhysicalAffinePair (C : ℝ) (n : ℕ)
    (chart : Fin (Parameters.legs n) → Chart (ZMod (Parameters.modulus n)))
    (hscale : ∀ leg,(chart leg).2.1 ≠ 0) (placement : Equiv.Perm (blockIndex n))
    (baseline : Fin (Parameters.legs n) → ℤ) (center : blockIndex n → Fin (Parameters.modulus n))
    (hcharge : (Parameters.modulus n : ℤ) ∣
      (∑ leg,baseline leg)+(∑ index,((center index).val : ℤ))-(Parameters.legs n : ℤ)) :
    AffinePair (ZMod (Parameters.modulus n))
      ((Fin (Parameters.dimension n-1) → ZMod (Parameters.modulus n)) × ZMod (Parameters.modulus n)) where
  linear := actualPhysicalReducedTransport n chart hscale placement
  offset := reduceCoordinates _ _ (actualPhysicalInitialCoordinates C n chart baseline center hcharge)

/-- The legal affine evaluator is the reduction of the actual integer
construction, including its proved integral initial preimage. -/
theorem actualPhysicalAffinePair_eval (C : ℝ) (n : ℕ)
    (chart : Fin (Parameters.legs n) → Chart (ZMod (Parameters.modulus n)))
    (hscale : ∀ leg,(chart leg).2.1 ≠ 0) (placement : Equiv.Perm (blockIndex n))
    (baseline : Fin (Parameters.legs n) → ℤ) (center : blockIndex n → Fin (Parameters.modulus n))
    (hcharge : (Parameters.modulus n : ℤ) ∣
      (∑ leg,baseline leg)+(∑ index,((center index).val : ℤ))-(Parameters.legs n : ℤ))
    (input : (Fin (Parameters.dimension n-1) → ℤ) × ℤ) :
    (actualPhysicalAffinePair C n chart hscale placement baseline center hcharge).eval (reduceCoordinates _ _ input)=
      reduceCoordinates _ _ (actualPhysicalTransport n chart placement input+
        actualPhysicalInitialCoordinates C n chart baseline center hcharge) := by
  change actualPhysicalReducedTransport n chart hscale placement (reduceCoordinates _ _ input)+_=_
  rw [actualPhysicalReducedTransport_reduce]
  ext index <;> simp [reduceCoordinates,actualPhysicalAffinePair]

end
end AFT.V7Calibration
