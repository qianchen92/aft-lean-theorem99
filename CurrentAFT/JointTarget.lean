import CurrentAFT.CharacterPolynomial

/-!
# The current manuscript's Fourier criterion for the joint target

The bound uses the actual all-degree coefficient energy of the literal
character polynomial. Only low-support cancellation is a premise; the
complete weighted Fourier comparison and ambient Parseval estimate are
supplied by their checked finite-sum proofs.
-/

namespace CurrentAFT.JointTarget

open AFT FourierCoordinates FourierSupportIsometry FrequencySupport
open scoped BigOperators Classical

noncomputable section

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

variable {Index : Type*} [Fintype Index] {modulus : ℕ} [NeZero modulus]

theorem fourier_identity (mass : (Index → ZMod modulus) → ℝ)
    (frequency : Index → ZMod modulus) :
    fourier (Equiv.refl (ZMod modulus)) (fun point => (mass point : ℂ)) frequency =
      signedFourier mass (coordinateCharacter frequency) := rfl

theorem complete_target_energy (mass : (Index → ZMod modulus) → ℝ)
    (hmass : ∑ point, mass point = 1)
    (hexchangeable : HistogramNormalization.ExchangeableMass mass)
    (hpopulation : 0 < Fintype.card Index) (order : ℕ)
    (radius : ℝ) (hradius : Real.sqrt (Real.exp 1) ≤ radius)
    (hcancel : ∀ frequency : Index → ZMod modulus, frequency ≠ 0 →
      (support frequency).card ≤ order →
        signedFourier mass (coordinateCharacter frequency) = 0) :
    (∑ frequency ∈ Finset.univ.erase (0 : Index → ZMod modulus),
      ‖signedFourier mass (coordinateCharacter frequency)‖ ^ 2) ≤
      (colorFockEnergy mass radius - 1) /
        (radius / Real.sqrt (Real.exp 1)) ^ (2 * (order + 1)) := by
  have hsqrt : 0 < Real.sqrt (Real.exp 1) := Real.sqrt_pos.mpr (Real.exp_pos 1)
  have hcharge : 1 ≤ radius / Real.sqrt (Real.exp 1) :=
    (le_div_iff₀ hsqrt).mpr (by simpa only [one_mul] using hradius)
  have hweighted := complete_weighted_energy_le_fock (Equiv.refl (ZMod modulus))
    mass hexchangeable hpopulation radius
  simp only [fourier_identity] at hweighted
  have hzero : signedFourier mass (coordinateCharacter (0 : Index → ZMod modulus)) = 1 := by
    rw [coordinateCharacter_zero, signedFourier_zero, hmass]
    norm_num
  exact complete_fourier_tail_of_full_weighted_bound
    (fun frequency : Index → ZMod modulus => (support frequency).card)
    (fun frequency => signedFourier mass (coordinateCharacter frequency)) order
    (radius / Real.sqrt (Real.exp 1)) (colorFockEnergy mass radius) hcharge
    (by simp [support]) hzero hcancel hweighted

theorem joint_target (mass : (Index → ZMod modulus) → ℝ)
    (hmass : ∑ point, mass point = 1)
    (hexchangeable : HistogramNormalization.ExchangeableMass mass)
    (hpopulation : 0 < Fintype.card Index) (order : ℕ)
    (radius : ℝ) (hradius : Real.sqrt (Real.exp 1) ≤ radius)
    (hcancel : ∀ frequency : Index → ZMod modulus, frequency ≠ 0 →
      (support frequency).card ≤ order →
        signedFourier mass (coordinateCharacter frequency) = 0) :
    (∑ point, |uniformDeviation mass point|) / 2 ≤
      Real.sqrt ((colorFockEnergy mass radius - 1) /
        (radius / Real.sqrt (Real.exp 1)) ^ (2 * (order + 1))) / 2 := by
  exact (coordinate_ambient_signed_half_l1 mass hmass).trans
    (div_le_div_of_nonneg_right (Real.sqrt_le_sqrt
      (complete_target_energy mass hmass hexchangeable hpopulation order radius hradius hcancel))
      (by norm_num))

theorem joint_target_quotient (mass : (Index → ZMod modulus) → ℝ)
    (hmass : ∑ point, mass point = 1)
    (hexchangeable : HistogramNormalization.ExchangeableMass mass)
    (hpopulation : 0 < Fintype.card Index) (order : ℕ)
    (radius : ℝ) (hradius : Real.sqrt (Real.exp 1) ≤ radius)
    (hcancel : ∀ frequency : Index → ZMod modulus, frequency ≠ 0 →
      (support frequency).card ≤ order →
        signedFourier mass (coordinateCharacter frequency) = 0) :
    (∑ point, |uniformDeviation mass point|) / 2 ≤
      Real.sqrt (colorFockEnergy mass radius - 1) /
        (2 * (radius / Real.sqrt (Real.exp 1)) ^ (order + 1)) := by
  have h := joint_target mass hmass hexchangeable hpopulation order radius hradius hcancel
  have hcharge : 0 ≤ radius / Real.sqrt (Real.exp 1) :=
    div_nonneg ((Real.sqrt_nonneg _).trans hradius) (Real.sqrt_nonneg _)
  have hpower : (radius / Real.sqrt (Real.exp 1)) ^ (2 * (order + 1)) =
      ((radius / Real.sqrt (Real.exp 1)) ^ (order + 1)) ^ 2 := by
    rw [← pow_mul, Nat.mul_comm]
  rw [hpower, Real.sqrt_div' _ (sq_nonneg _),
    Real.sqrt_sq (pow_nonneg hcharge _)] at h
  simpa only [div_div, mul_comm] using h

end

end CurrentAFT.JointTarget
