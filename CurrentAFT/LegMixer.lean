import Mathlib

/-!
# The current leg incidence map and its invertible coordinate mixer

This file verifies the concrete matrices in `sec:affine-realization-matrix`
and `sec:leg-edge-injection` of the current manuscript. The integer load
identity and its zero charge are derived from their actual matrix product.
Over a field, the inverse mixer is explicitly `(u - shear * v) / scale, v`.

These results cover local leg mixers and their block product. They do not
assert the full spanning-tree basis theorem, integrality of the affine
offset, carry safety, or polynomial-time implementation of the sampler.
-/

namespace CurrentAFT

namespace LegMixer

open scoped BigOperators Matrix

variable {Scalar : Type*} [CommRing Scalar]

/-- The actual two-edge, three-vertex incidence matrix, with vertex
order primary, companion, attachment. -/
def legIncidence : Matrix (Fin 3) (Fin 2) Scalar :=
  !![1, 0; -1, -1; 0, 1]

/-- Only the first tree-edge coordinate is mixed. The second coordinate
is precisely the load transferred from companion to attachment. -/
def coordinateMixer (scale shear : Scalar) : Matrix (Fin 2) (Fin 2) Scalar :=
  !![scale, shear; 0, 1]

/-- The vertex-load matrix is the derived incidence-times-mixer product. -/
def legInjectionMatrix (scale shear : Scalar) : Matrix (Fin 3) (Fin 2) Scalar :=
  (legIncidence : Matrix (Fin 3) (Fin 2) Scalar) * coordinateMixer scale shear

theorem coordinateMixer_action (scale shear : Scalar) (input : Fin 2 → Scalar) :
    (coordinateMixer scale shear).mulVec input =
      ![scale * input 0 + shear * input 1, input 1] := by
  ext index
  fin_cases index <;> simp [coordinateMixer, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem legInjectionMatrix_entries (scale shear : Scalar) :
    legInjectionMatrix scale shear = !![scale, shear; -scale, -(shear + 1); 0, 1] := by
  ext row column
  change (∑ index : Fin 2, (legIncidence : Matrix (Fin 3) (Fin 2) Scalar) row index *
    coordinateMixer scale shear index column) = _
  fin_cases row <;> fin_cases column <;>
    simp [legIncidence, coordinateMixer, Fin.sum_univ_two]
  ring

/-- This is the manuscript's complete three-coordinate source action.
The attachment receives exactly the original second input. -/
theorem legInjection_action (scale shear : Scalar) (input : Fin 2 → Scalar) :
    (legInjectionMatrix scale shear).mulVec input =
      ![scale * input 0 + shear * input 1,
        -scale * input 0 - (shear + 1) * input 1, input 1] := by
  rw [legInjectionMatrix_entries]
  ext index
  fin_cases index <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  ring

/-- The two off-body increments lose exactly the attachment increment.
This equality holds over the integers without modular reduction. -/
theorem legInjection_zero_charge (scale shear : Scalar) (input : Fin 2 → Scalar) :
    ∑ vertex, (legInjectionMatrix scale shear).mulVec input vertex = 0 := by
  rw [legInjection_action]
  simp [Fin.sum_univ_succ]
  ring

theorem coordinateMixer_determinant (scale shear : Scalar) :
    (coordinateMixer scale shear).det = scale := by
  simp [coordinateMixer, Matrix.det_fin_two]

/-- All leg mixers have determinant equal to the product of their
actual scales. No general-linear-group membership is assumed. -/
def blockCoordinateMixer {Leg : Type*} [Fintype Leg] [DecidableEq Leg]
    (scale shear : Leg → Scalar) : Matrix (Fin 2 × Leg) (Fin 2 × Leg) Scalar :=
  Matrix.blockDiagonal (fun leg => coordinateMixer (scale leg) (shear leg))

theorem blockCoordinateMixer_determinant {Leg : Type*} [Fintype Leg] [DecidableEq Leg]
    (scale shear : Leg → Scalar) :
    (blockCoordinateMixer scale shear).det = ∏ leg, scale leg := by
  simp [blockCoordinateMixer, coordinateMixer_determinant]

section Field

variable {FieldScalar : Type*} [Field FieldScalar]

/-- The explicit inverse of the actual mixer. -/
def inverseMixer (scale shear : FieldScalar) (output : Fin 2 → FieldScalar) :
    Fin 2 → FieldScalar :=
  ![(output 0 - shear * output 1) / scale, output 1]

theorem inverseMixer_left (scale shear : FieldScalar) (hscale : scale ≠ 0)
    (input : Fin 2 → FieldScalar) :
    inverseMixer scale shear ((coordinateMixer scale shear).mulVec input) = input := by
  ext index
  fin_cases index <;> simp [inverseMixer, coordinateMixer_action]
  field_simp [hscale]

theorem inverseMixer_right (scale shear : FieldScalar) (hscale : scale ≠ 0)
    (output : Fin 2 → FieldScalar) :
    (coordinateMixer scale shear).mulVec (inverseMixer scale shear output) = output := by
  ext index
  fin_cases index <;> simp [inverseMixer, coordinateMixer_action]
  field_simp [hscale]
  ring

/-- A nonzero scale constructs an actual linear equivalence whose
forward map is multiplication by the specified coordinate mixer. -/
def mixerLinearEquiv (scale shear : FieldScalar) (hscale : scale ≠ 0) :
    (Fin 2 → FieldScalar) ≃ₗ[FieldScalar] (Fin 2 → FieldScalar) :=
  { (coordinateMixer scale shear).mulVecLin with
    invFun := inverseMixer scale shear
    left_inv := inverseMixer_left scale shear hscale
    right_inv := inverseMixer_right scale shear hscale }

theorem mixerLinearEquiv_action (scale shear : FieldScalar) (hscale : scale ≠ 0)
    (input : Fin 2 → FieldScalar) :
    mixerLinearEquiv scale shear hscale input = (coordinateMixer scale shear).mulVec input := rfl

theorem mixerLinearEquiv_inverse (scale shear : FieldScalar) (hscale : scale ≠ 0)
    (output : Fin 2 → FieldScalar) :
    (mixerLinearEquiv scale shear hscale).symm output =
      ![(output 0 - shear * output 1) / scale, output 1] := rfl

theorem blockCoordinateMixer_determinant_ne_zero {Leg : Type*} [Fintype Leg] [DecidableEq Leg]
    (scale shear : Leg → FieldScalar) (hscale : ∀ leg, scale leg ≠ 0) :
    (blockCoordinateMixer scale shear).det ≠ 0 := by
  rw [blockCoordinateMixer_determinant]
  exact Finset.prod_ne_zero_iff.mpr (fun leg _ => hscale leg)

/-- The corresponding product equivalence acts on each source leg
separately and preserves its original second input. -/
def blockMixerLinearEquiv {Leg : Type*} (scale shear : Leg → FieldScalar)
    (hscale : ∀ leg, scale leg ≠ 0) :
    (Leg → Fin 2 → FieldScalar) ≃ₗ[FieldScalar] (Leg → Fin 2 → FieldScalar) :=
  LinearEquiv.piCongrRight (fun leg => mixerLinearEquiv (scale leg) (shear leg) (hscale leg))

theorem blockMixerLinearEquiv_action {Leg : Type*} (scale shear : Leg → FieldScalar)
    (hscale : ∀ leg, scale leg ≠ 0) (input : Leg → Fin 2 → FieldScalar) (leg : Leg) :
    blockMixerLinearEquiv scale shear hscale input leg =
      ![scale leg * input leg 0 + shear leg * input leg 1, input leg 1] :=
  coordinateMixer_action (scale leg) (shear leg) (input leg)

end Field

/-- In the manuscript's prime field, nonzero public scale is enough;
the inverse is constructed rather than assumed. -/
def modularMixerLinearEquiv (modulus : ℕ) [Fact modulus.Prime]
    (scale shear : ZMod modulus) (hscale : scale ≠ 0) :
    (Fin 2 → ZMod modulus) ≃ₗ[ZMod modulus] (Fin 2 → ZMod modulus) :=
  mixerLinearEquiv scale shear hscale

theorem modularMixer_inverse (modulus : ℕ) [Fact modulus.Prime]
    (scale shear : ZMod modulus) (hscale : scale ≠ 0) (output : Fin 2 → ZMod modulus) :
    (modularMixerLinearEquiv modulus scale shear hscale).symm output =
      ![(output 0 - shear * output 1) / scale, output 1] := rfl

end LegMixer

end CurrentAFT
