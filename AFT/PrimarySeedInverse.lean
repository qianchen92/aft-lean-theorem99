import AFT.V7MixedInverse
import AFT.MixedCoordinateIteration
import AFT.RepresentedCovariance
import AFT.RepresentedSubstitution

/-! # Actual primary inverses on every coordinate of a literal input seed -/

namespace AFT.MixedKernel
open scoped BigOperators Classical
noncomputable section
variable {Slot Color : Type*} [Fintype Slot] [DecidableEq Slot] [Fintype Color]

omit [Fintype Slot] in
theorem inputIteration_append (first second : List Slot)
    (operator : Slot → Module.End ℝ (Color → ℝ)) (reference : Slot → FiniteDist Color)
    (kernel : (Slot → Color) → ℝ) :
    inputIteration (first++second) operator reference kernel =
      inputIteration first operator reference (inputIteration second operator reference kernel) := by
  induction first with
  | nil => rfl
  | cons slot tail ih => simp only [List.cons_append,inputIteration_cons,ih]

omit [Fintype Slot] in
/-- Reverse the actual list of coordinate operations; each inverse
cancellation is performed on the complete joint kernel. -/
theorem inputIteration_inverse (coordinates : List Slot)
    (operator : (Color → ℝ) ≃ₗ[ℝ] (Color → ℝ)) (reference : Slot → FiniteDist Color)
    (hreference : ∀ slot ∈ coordinates, ∀ color, (reference slot).weight color ≠ 0)
    (kernel : (Slot → Color) → ℝ) :
    inputIteration coordinates.reverse (fun _ => operator.toLinearMap) reference
      (inputIteration coordinates (fun _ => operator.symm.toLinearMap) reference kernel) = kernel := by
  induction coordinates with
  | nil => rfl
  | cons slot tail ih =>
    rw [List.reverse_cons,inputIteration_append,inputIteration_cons,inputIteration_cons]
    simp only [inputIteration_nil,LinearMap.id_apply]
    rw [partialInputOperator_inverse slot operator (reference slot).weight
      (hreference slot (List.mem_cons_self ..))]
    exact ih (fun other hm => hreference other (List.mem_cons_of_mem _ hm))

end
end AFT.MixedKernel

namespace AFT.RepresentedPolynomial
open scoped BigOperators Classical
noncomputable section
variable {Color : Type*} [Fintype Color]

def primaryCoordinates (seed : InputSeed Color) : List (Fin (seed.primaryOrder+seed.bodyOrder)) :=
  List.ofFn (fun index : Fin seed.primaryOrder => Fin.castAdd seed.bodyOrder index)

def inversePrimarySeed (primary body : FiniteDist Color) (rho : ℝ)
    (operator : (Color → ℝ) ≃ₗ[ℝ] (Color → ℝ)) (seed : InputSeed Color) : InputSeed Color where
  primaryOrder := seed.primaryOrder
  bodyOrder := seed.bodyOrder
  kernel := (rho⁻¹)^seed.primaryOrder •
    MixedKernel.inputIteration (primaryCoordinates seed) (fun _ => operator.symm.toLinearMap)
      (inputReference primary body seed) seed.kernel

theorem primaryCoordinates_reference (primary body : FiniteDist Color) (seed : InputSeed Color)
    (slot : Fin (seed.primaryOrder+seed.bodyOrder)) (hslot : slot ∈ primaryCoordinates seed) :
    inputReference primary body seed slot = primary := by
  obtain ⟨index,rfl⟩ := List.mem_ofFn.mp hslot
  simp [inputReference]

omit [Fintype Color] in
theorem primaryCoordinates_rate (primaryPool bodyPool : ℝ) (seed : InputSeed Color)
    (slot : Fin (seed.primaryOrder+seed.bodyOrder)) (hslot : slot ∈ primaryCoordinates seed) :
    inputRate primaryPool bodyPool seed slot = (Real.sqrt primaryPool)⁻¹ := by
  obtain ⟨index,rfl⟩ := List.mem_ofFn.mp hslot
  simp [inputRate]

/-- The density of the inverse seed has the exact intended forward image,
including all activation powers, before any output identification. -/
theorem inversePrimarySeed_exact (primary body : FiniteDist Color) (rho : ℝ) (hrho : rho ≠ 0)
    (operator : (Color → ℝ) ≃ₗ[ℝ] (Color → ℝ)) (seed : InputSeed Color)
    (hprimary : ∀ color, primary.weight color ≠ 0) :
    rho^seed.primaryOrder •
      MixedKernel.inputIteration (primaryCoordinates seed).reverse (fun _ => operator.toLinearMap)
        (inputReference primary body seed) (inversePrimarySeed primary body rho operator seed).kernel = seed.kernel := by
  change rho^seed.primaryOrder • MixedKernel.inputIteration _ _ _
    ((rho⁻¹)^seed.primaryOrder • MixedKernel.inputIteration _ _ _ seed.kernel) = _
  rw [map_smul, MixedKernel.inputIteration_inverse (primaryCoordinates seed) operator _ (by
    intro slot hs color
    rw [primaryCoordinates_reference primary body seed slot hs]
    exact hprimary color)]
  rw [smul_smul,← mul_pow,mul_inv_cancel₀ hrho,one_pow,one_smul]

theorem inversePrimarySeed_activity_le (primary body : FiniteDist Color)
    (primaryPool bodyPool radius rho : ℝ) (hradius : 0 ≤ radius) (hrho : 0 < rho)
    (operator : (Color → ℝ) ≃ₗ[ℝ] (Color → ℝ)) (seed : InputSeed Color)
    (hoperator : ∀ slot ∈ primaryCoordinates seed, ∀ kernel,
      MixedKernel.activity (inputRate primaryPool bodyPool seed) (inputReference primary body seed)
        (MixedKernel.partialInputOperator slot operator.symm.toLinearMap (inputReference primary body seed slot).weight kernel) ≤
        4*MixedKernel.activity (inputRate primaryPool bodyPool seed) (inputReference primary body seed) kernel) :
    inputWeight primary body primaryPool bodyPool radius (inversePrimarySeed primary body rho operator seed) ≤
      responseInputWeight primary body primaryPool bodyPool radius (4/rho) seed := by
  have hi := MixedKernel.inputIteration_activity_le (primaryCoordinates seed) (fun _ => operator.symm.toLinearMap)
    (inputReference primary body seed) (inputRate primaryPool bodyPool seed) 4 (by norm_num) hoperator seed.kernel
  simp only [primaryCoordinates,List.length_ofFn] at hi
  change radius^seed.bodyOrder*MixedKernel.activity (inputRate primaryPool bodyPool seed) (inputReference primary body seed)
      ((rho⁻¹)^seed.primaryOrder • MixedKernel.inputIteration (primaryCoordinates seed) (fun _ => operator.symm.toLinearMap)
        (inputReference primary body seed) seed.kernel) ≤ _
  rw [MixedKernel.activity_smul,abs_of_nonneg (pow_nonneg (inv_nonneg.mpr hrho.le) _)]
  apply (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hi (pow_nonneg (inv_nonneg.mpr hrho.le) _))
    (pow_nonneg hradius _)).trans_eq
  unfold responseInputWeight inputWeight MixedKernel.analyticActivity
  rw [div_pow]
  ring

/-- The finite table keeps every transformed input seed literally. -/
def inversePrimaryTable (primary body : FiniteDist Color) (rho : ℝ)
    (operator : (Color → ℝ) ≃ₗ[ℝ] (Color → ℝ)) :
    Table (InputSeed Color) →ₐ[ℝ] Table (InputSeed Color) :=
  MvPolynomial.aeval (fun seed => MvPolynomial.X (inversePrimarySeed primary body rho operator seed))

theorem inversePrimaryTable_activity_le (primary body : FiniteDist Color)
    (primaryPool bodyPool radius rho : ℝ) (hradius : 0 ≤ radius)
    (operator : (Color → ℝ) ≃ₗ[ℝ] (Color → ℝ))
    (hseed : ∀ seed, inputWeight primary body primaryPool bodyPool radius (inversePrimarySeed primary body rho operator seed) ≤
      responseInputWeight primary body primaryPool bodyPool radius (4/rho) seed)
    (table : Table (InputSeed Color)) :
    activity (inputWeight primary body primaryPool bodyPool radius) (inversePrimaryTable primary body rho operator table) ≤
      activity (responseInputWeight primary body primaryPool bodyPool radius (4/rho)) table := by
  apply activity_aeval_le _ _ (fun seed => inputWeight_nonneg _ _ _ _ _ seed hradius)
  intro seed
  simpa only [activity_X] using hseed seed

theorem inversePrimaryTable_hasOrder (primary body : FiniteDist Color) (rho : ℝ)
    (operator : (Color → ℝ) ≃ₗ[ℝ] (Color → ℝ)) (minimum : ℕ)
    (table : Table (InputSeed Color))
    (htable : HasOrder (fun seed => seed.primaryOrder+seed.bodyOrder) minimum table) :
    HasOrder (fun seed => seed.primaryOrder+seed.bodyOrder) minimum (inversePrimaryTable primary body rho operator table) := by
  apply aeval_hasOrder_of_lower_bounds _ _ _ _ minimum table htable
  intro seed
  simpa only [map_one,one_mul] using hasOrder_C_mul_X (fun input : InputSeed Color => input.primaryOrder+input.bodyOrder)
    (seed.primaryOrder+seed.bodyOrder) (inversePrimarySeed primary body rho operator seed) 1 (le_refl _)

end
end AFT.RepresentedPolynomial

namespace AFT.V7Calibration
open GaussianSource Filter RepresentedPolynomial
open scoped BigOperators Classical Topology
noncomputable section

/-- A single actual response inverse works for every literal finite input
seed and every body pool; its cost is charged only on primary coordinates. -/
theorem actual_primary_seed_inverse_eventually (cutoffScale : ℝ) (hscale : 1 ≤ cutoffScale)
    (beta : ℕ → ℝ) (pool : ℕ → ℕ)
    (htypical : ∀ᶠ parameter in atTop,
      (Parameters.legs parameter : ℝ)/(2*Parameters.dimension parameter) ≤ beta parameter ∧
      beta parameter ≤ 2*(Parameters.legs parameter : ℝ)/Parameters.dimension parameter ∧
      Parameters.legs parameter ≤ 2*pool parameter) :
    ∀ᶠ parameter in atTop,
      ∃ operator : (Fin (Parameters.modulus parameter) → ℝ) ≃ₗ[ℝ] (Fin (Parameters.modulus parameter) → ℝ),
        operator.toLinearMap = actualResponse cutoffScale parameter ∧
        ∀ body : FiniteDist (Fin (Parameters.modulus parameter)), ∀ bodyPool radius : ℝ, 0 ≤ radius →
        ∀ seed : InputSeed (Fin (Parameters.modulus parameter)),
        inputWeight (actualPrimaryLaw cutoffScale parameter (beta parameter)) body (pool parameter) bodyPool radius
          (inversePrimarySeed (actualPrimaryLaw cutoffScale parameter (beta parameter)) body (v7Activation cutoffScale parameter) operator seed) ≤
          responseInputWeight (actualPrimaryLaw cutoffScale parameter (beta parameter)) body (pool parameter) bodyPool radius
            (4/v7Activation cutoffScale parameter) seed := by
  filter_upwards [actual_primary_inverse_mixed_uniform_eventually cutoffScale hscale beta pool htypical,
    eventually_ge_atTop 1] with parameter hi hp
  obtain ⟨operator,hop,hi⟩ := hi
  refine ⟨operator,hop,?_⟩
  intro body bodyPool radius hradius seed
  apply inversePrimarySeed_activity_le _ _ _ _ _ _ hradius
    (activation_positive _ _ _ _ (legFeatureCount_positive cutoffScale parameter hscale hp))
  intro slot hs kernel
  apply hi (Fin (seed.primaryOrder+seed.bodyOrder)) (inputReference _ _ seed) (inputRate _ _ seed) slot
  · intro index
    cases index using Fin.addCases <;> simp only [inputRate,Fin.addCases_left,Fin.addCases_right] <;> positivity
  · exact primaryCoordinates_reference _ _ seed slot hs
  · simpa only [one_div] using primaryCoordinates_rate (pool parameter) bodyPool seed slot hs

/-- The covariance table now consists of actual input kernels, rather than
only assigned upper weights on un-inverted output kernels. -/
theorem actual_covariance_inverse_table_eventually (cutoffScale : ℝ) (hscale : 1 ≤ cutoffScale)
    (beta : ℕ → ℝ) (pool : ℕ → ℕ)
    (htypical : ∀ᶠ parameter in atTop,
      (Parameters.legs parameter : ℝ)/(2*Parameters.dimension parameter) ≤ beta parameter ∧
      beta parameter ≤ 2*(Parameters.legs parameter : ℝ)/Parameters.dimension parameter ∧
      Parameters.legs parameter ≤ 2*pool parameter) :
    ∀ᶠ parameter in atTop,
      ∃ operator : (Fin (Parameters.modulus parameter) → ℝ) ≃ₗ[ℝ] (Fin (Parameters.modulus parameter) → ℝ),
        operator.toLinearMap = actualResponse cutoffScale parameter ∧
        ∀ queue : ℤ, ∀ body : FiniteDist (Fin (Parameters.modulus parameter)),
        ∀ bodyPool radius : ℝ, 0 ≤ radius →
        (Parameters.legs parameter : ℝ)*activity
          (inputWeight (actualPrimaryLaw cutoffScale parameter (beta parameter)) body (pool parameter) bodyPool radius)
          (inversePrimaryTable (actualPrimaryLaw cutoffScale parameter (beta parameter)) body (v7Activation cutoffScale parameter) operator
            (actualCovarianceTable cutoffScale parameter (beta parameter) queue)) ≤ 268435456/(parameter : ℝ)^2 := by
  have hbeta := htypical.mono fun _ h => And.intro h.1 h.2.1
  filter_upwards [actual_primary_seed_inverse_eventually cutoffScale hscale beta pool htypical,
    actual_covariance_table_mixed_activity_eventually cutoffScale hscale beta hbeta,
    actual_reference_laws_eventually cutoffScale hscale beta hbeta,htypical]
    with parameter hi hc hl ht
  obtain ⟨operator,hop,hi⟩ := hi
  refine ⟨operator,hop,?_⟩
  intro queue body bodyPool radius hradius
  have hh := inversePrimaryTable_activity_le (actualPrimaryLaw cutoffScale parameter (beta parameter)) body
    (pool parameter) bodyPool radius (v7Activation cutoffScale parameter) hradius operator (hi body bodyPool radius hradius)
    (actualCovarianceTable cutoffScale parameter (beta parameter) queue)
  exact (mul_le_mul_of_nonneg_left hh (Nat.cast_nonneg _)).trans
    (hc queue _ body hl.1 (pool parameter) ht.2.2 bodyPool radius hradius)

end
end AFT.V7Calibration
