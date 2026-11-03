import CurrentAFT.RectanglePointIndex
import CurrentAFT.PublicParameterProgram
import CurrentAFT.CalibrationMatrixApproximation

/-! # Actual checked modulus and safe palette in rectangular calibration storage -/
namespace CurrentAFT.CurrentRectangleIndex
open AFT GradedControlAlgebra
set_option maxHeartbeats 800000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

def colors (security : ℕ) : ℕ := (PublicParameterProgram.modulus security).count

def safe (security : ℕ) (color : Fin (colors security)) : Prop :=
  ((3 * (security+2)^2 : ℕ) : ℤ) ≤ color.val ∧
    (color.val : ℤ) < (colors security : ℤ) - ((3 * (security+2)^2 : ℕ) : ℤ)

instance safeDecidable (security : ℕ) : DecidablePred (safe security) := fun color => by
  unfold safe
  infer_instance

theorem colors_eq (security : ℕ) : colors security = Parameters.modulus security :=
  PublicParameterProgram.modulus_value security

theorem colors_pos (security : ℕ) : 0 < colors security := by
  rw [colors_eq]
  exact (Parameters.modulus_spec security).2.pos

def paletteEquiv (security : ℕ) : Fin (colors security) ≃ ActualControls.Palette security :=
  finCongr (colors_eq security)

theorem safe_iff (security : ℕ) (color : Fin (colors security)) :
    safe security color ↔ InwardAnchor.SafeColor security (paletteEquiv security color) := by
  simp only [safe, InwardAnchor.SafeColor, paletteEquiv, finCongr_apply, Fin.val_cast,
    colors_eq, Parameters.safeMargin, Parameters.sourceCutoff, Parameters.base]

def safeEquiv (security : ℕ) : {color : Fin (colors security) // safe security color} ≃ ActualControls.SafePalette security where
  toFun color := ⟨paletteEquiv security color.val, (safe_iff security color.val).mp color.property⟩
  invFun color := ⟨(paletteEquiv security).symm color.val, (safe_iff security _).mpr (by
    simpa only [Equiv.apply_symm_apply] using color.property)⟩
  left_inv color := by apply Subtype.ext; exact (paletteEquiv security).symm_apply_apply color.val
  right_inv color := by apply Subtype.ext; exact (paletteEquiv security).apply_symm_apply color.val

def pointEquiv (security order : ℕ) :
    RectanglePointIndex.Point (colors security) order (safe security) ≃
      CalibrationPointCoordinates.PointIndex (ActualControls.Palette security) (ActualControls.SafePalette security) order :=
  Equiv.sigmaCongrRight (fun arity : TruncatedArity order =>
    Equiv.prodCongr (Equiv.piCongrRight (fun _ : Fin arity.val.1.val => paletteEquiv security))
      (Equiv.piCongrRight (fun _ : Fin arity.val.2.val => safeEquiv security)))

abbrev Rectangle (security order : ℕ) := RectanglePointIndex.Rectangle (colors security) order
abbrev Point (security order : ℕ) :=
  CalibrationPointCoordinates.PointIndex (ActualControls.Palette security) (ActualControls.SafePalette security) order

def encode (security order : ℕ) : Point security order ↪ Rectangle security order where
  toFun point := RectanglePointIndex.encode (colors security) order (colors_pos security) (safe security)
    ((pointEquiv security order).symm point)
  inj' := (RectanglePointIndex.encode_injective _ _ _ _).comp (pointEquiv security order).symm.injective

def decode (security order : ℕ) (index : Rectangle security order) : Option (Point security order) :=
  (RectanglePointIndex.decode (colors security) order (colors_pos security) (safe security) index).map
    (pointEquiv security order)

theorem decode_eq_some (security order : ℕ) (index : Rectangle security order) (point : Point security order) :
    decode security order index = some point ↔ index = encode security order point := by
  constructor
  · intro h
    obtain ⟨raw, hr, hp⟩ := Option.map_eq_some_iff.mp h
    have he := (RectanglePointIndex.decode_eq_some _ _ _ _ index raw).mp hr
    subst point
    simpa only [encode, Function.Embedding.coeFn_mk, Equiv.symm_apply_apply] using he
  · intro h
    have hr := (RectanglePointIndex.decode_eq_some (colors security) order (colors_pos security)
      (safe security) index ((pointEquiv security order).symm point)).mpr h
    simp only [decode, hr, Option.map_some, Equiv.apply_symm_apply]

def defect (security order : ℕ) (matrix : Point security order → Point security order → ℚ) :
    Rectangle security order → Rectangle security order → ℚ :=
  CalibrationRectanglePadding.defect (decode security order) matrix

def rhs (security order : ℕ) : Rectangle security order → ℚ :=
  CalibrationRectanglePadding.extend (decode security order)
    (fun point => if point.1.val.1.val + point.1.val.2.val = 0 then 1 else 0)

noncomputable section
open scoped Classical
local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _

theorem rhs_eq (security order : ℕ) : rhs security order =
    CalibrationRectanglePadding.extend (decode security order) (CalibrationMatrixApproximation.rhs security order) := by
  unfold rhs
  congr 1
  funext point
  have he : point.1.val.1.val + point.1.val.2.val = 0 ↔ point.1 = zeroArity order := by
    constructor
    · intro h
      apply Subtype.ext
      apply Prod.ext <;> apply Fin.ext <;> change _ = 0 <;> omega
    · intro h
      rw [h]
      rfl
  simp only [CalibrationMatrixApproximation.rhs, he]

theorem iteration_at (security order : ℕ) (matrix : Point security order → Point security order → ℚ)
    (steps : ℕ) (point : Point security order) :
    RationalNumerics.linearIteration (defect security order matrix) (rhs security order) steps
      (encode security order point) =
        RationalNumerics.linearIteration matrix (CalibrationMatrixApproximation.rhs security order) steps point := by
  rw [rhs_eq]
  exact CalibrationRectanglePadding.linearIteration_at (encode security order) (decode security order)
    (decode_eq_some security order) matrix _ steps point

theorem iteration_unused (security order : ℕ) (matrix : Point security order → Point security order → ℚ)
    (steps : ℕ) (index : Rectangle security order) (hindex : decode security order index = none) :
    RationalNumerics.linearIteration (defect security order matrix) (rhs security order) steps index = 0 := by
  rw [rhs_eq]
  exact CalibrationRectanglePadding.linearIteration_unused (encode security order) (decode security order)
    (decode_eq_some security order) matrix _ steps index hindex

theorem size_bound (security order : ℕ) : Fintype.card (Rectangle security order) ≤
    (order+1)^2 * 131072^order * Parameters.base security^(64*order) := by
  simp only [Rectangle, RectanglePointIndex.Rectangle, Fintype.card_prod, Fintype.card_fin, colors_eq]
  have h := Nat.pow_le_pow_left (Parameters.modulus_bounds security).2 order
  rw [mul_pow, ← pow_mul] at h
  exact (Nat.mul_le_mul_left ((order+1)^2) h).trans_eq (by ring)

end
end CurrentAFT.CurrentRectangleIndex
