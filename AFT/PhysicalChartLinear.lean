import AFT.PhysicalBlockIncidence

/-! # The actual affine chart as an invertible triangular edge map -/
namespace AFT.V7Calibration
open GaussianSource BoundaryCalibration
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
attribute [local instance] actualModulusNeZero

variable {Index R : Type*} [CommRing R]

def legTriangularLinear (scale shear : Index → R) : (Index → R × R) →ₗ[R] (Index → R × R) where
  toFun input index := (scale index*(input index).1+shear index*(input index).2,(input index).2)
  map_add' := by
    intro first second
    funext index
    apply Prod.ext <;> simp
    all_goals ring
  map_smul' := by
    intro scalar input
    funext index
    apply Prod.ext <;> simp [smul_eq_mul]
    all_goals ring

/-- All chart scales are nonzero on their proved support, so the actual
leg shear has an explicit inverse over the residue field. -/
def legTriangularEquiv {K : Type*} [Field K] (scale shear : Index → K) (hscale : ∀ index,scale index ≠ 0) :
    (Index → K × K) ≃ₗ[K] (Index → K × K) where
  toLinearMap := legTriangularLinear scale shear
  invFun output index := ((output index).1/scale index-shear index*(output index).2/scale index,(output index).2)
  left_inv := by
    intro input
    funext index
    apply Prod.ext
    · dsimp only [legTriangularLinear,LinearMap.coe_mk,AddHom.coe_mk]
      field_simp [hscale index]
      ring
    · rfl
  right_inv := by
    intro output
    funext index
    apply Prod.ext
    · dsimp only [legTriangularLinear,LinearMap.coe_mk,AddHom.coe_mk]
      field_simp [hscale index]
      ring
    · rfl

def actualChartLegLinear (n : ℕ)
    (chart : Fin (Parameters.legs n) → Chart (ZMod (Parameters.modulus n))) :
    (Fin (Parameters.legs n) → ℤ × ℤ) →ₗ[ℤ] (Fin (Parameters.legs n) → ℤ × ℤ) :=
  legTriangularLinear (fun leg => ((chart leg).2.1.val : ℤ)) (fun leg => ((chart leg).2.2.val : ℤ))

def actualChartLegEquiv (n : ℕ)
    (chart : Fin (Parameters.legs n) → Chart (ZMod (Parameters.modulus n)))
    (hscale : ∀ leg,(chart leg).2.1 ≠ 0) :
    (Fin (Parameters.legs n) → ZMod (Parameters.modulus n) × ZMod (Parameters.modulus n)) ≃ₗ[ZMod (Parameters.modulus n)]
      (Fin (Parameters.legs n) → ZMod (Parameters.modulus n) × ZMod (Parameters.modulus n)) :=
  legTriangularEquiv (fun leg => (chart leg).2.1) (fun leg => (chart leg).2.2) hscale

/-- The integer coefficients used in the protected loads reduce exactly to
the invertible field map; no alternative chart is substituted. -/
theorem actualChartLegLinear_reduce (n : ℕ)
    (chart : Fin (Parameters.legs n) → Chart (ZMod (Parameters.modulus n)))
    (hscale : ∀ leg,(chart leg).2.1 ≠ 0) (input : Fin (Parameters.legs n) → ℤ × ℤ) (leg : Fin (Parameters.legs n)) :
    (((actualChartLegLinear n chart input leg).1 : ZMod (Parameters.modulus n)),
      ((actualChartLegLinear n chart input leg).2 : ZMod (Parameters.modulus n)))=
      actualChartLegEquiv n chart hscale (fun leg => ((input leg).1,(input leg).2)) leg := by
  simp [actualChartLegLinear,actualChartLegEquiv,legTriangularEquiv,legTriangularLinear]

/-- The complete protected physical loads are literally affine in their
source coordinates: a triangular leg map, the zero-sum body field, the
shared queue field, and one fixed initial load. -/
theorem actualIntegerBlockLoad_affine (C : ℝ) (n : ℕ)
    (chart : Fin (Parameters.legs n) → Chart (ZMod (Parameters.modulus n)))
    (baseline : Fin (Parameters.legs n) → ℤ)
    (center : blockIndex n → Fin (Parameters.modulus n))
    (roots queue : blockIndex n → ℤ) (input : Fin (Parameters.legs n) → V7Input C n)
    (coordinate : Sigma (blockSlots n)) :
    actualIntegerBlockLoad C n chart baseline center roots queue input coordinate.1 coordinate.2=
      physicalBlockIncidence n (actualChartLegLinear n chart
        (fun leg => ((input leg).1,(input leg).2))) roots coordinate.1 coordinate.2+
      physicalBlockIncidence n (fun _ => (0,0)) queue coordinate.1 coordinate.2+
      actualIntegerBlockLoad C n chart baseline center (fun _ => 0) (fun _ => 0)
        (fun _ => (windowZero _,windowZero _)) coordinate.1 coordinate.2 := by
  rcases coordinate with ⟨index,slot⟩
  cases index with
  | inl leg =>
    change Fin 3 at slot
    fin_cases slot <;>
      simp [actualIntegerBlockLoad,physicalBlockIncidence,actualChartLegLinear,legTriangularLinear,chartIntegerLoad,windowZero] <;> ring
  | inr body =>
    change Fin 1 at slot
    fin_cases slot
    simp [actualIntegerBlockLoad,physicalBlockIncidence]
    ring

end
end AFT.V7Calibration
