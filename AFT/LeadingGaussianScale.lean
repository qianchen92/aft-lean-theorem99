import AFT.LeadingGaussian

/-! # Population and Fock radius scaling of the actual leading output -/
namespace AFT.RepresentedPolynomial
open MeasureTheory
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {Color : Type*} [Fintype Color]

 theorem leading_monomial_dilate (primary body : FiniteDist Color) (reference : Color → ℝ)
    (primaryChannel bodyChannel : Color → Color → ℝ) (powers : InputSeed Color →₀ ℕ)
    (scale : ℝ) (value : Color → ℂ) :
    leadingGaussianValue reference (outputHom primary body primaryChannel bodyChannel (MvPolynomial.monomial powers 1))
      (fun color => (scale : ℂ)*value color)=
    ((scale^weightedOrder (fun seed : InputSeed Color => seed.primaryOrder+seed.bodyOrder) powers : ℝ) : ℂ)*
      leadingGaussianValue reference (outputHom primary body primaryChannel bodyChannel (MvPolynomial.monomial powers 1)) value := by
  rw [← mixedMonomialSeed_output]
  simp only [leadingGaussianValue,leadingSeedTensor_evaluation,
    NonlinearFock.tensorEvaluation_dilate,NonlinearFock.tensorEvaluation_smul,Fintype.card_fin,mixedMonomialSeed_order]

 theorem leading_monomial_scaled_memLp (primary body : FiniteDist Color) (reference : Color → ℝ)
    (primaryChannel bodyChannel : Color → Color → ℝ) (powers : InputSeed Color →₀ ℕ) (scale : ℝ) :
    MemLp (fun value => leadingGaussianValue reference
      (outputHom primary body primaryChannel bodyChannel (MvPolynomial.monomial powers 1))
        (fun color => (scale : ℂ)*value color)) 2 FockGaussian.field := by
  simp_rw [leading_monomial_dilate]
  exact (leading_monomial_memLp primary body reference primaryChannel bodyChannel powers).const_mul _

 theorem leading_monomial_scaled_energy_le (primary body : FiniteDist Color) (reference : Color → ℝ)
    (primaryChannel bodyChannel : Color → Color → ℝ) (powers : InputSeed Color →₀ ℕ)
    (scale : ℝ) (hs : 0 ≤ scale) (hs1 : scale ≤ 1) :
    (∫ value,Complex.normSq (leadingGaussianValue reference
      (outputHom primary body primaryChannel bodyChannel (MvPolynomial.monomial powers 1))
        (fun color => (scale : ℂ)*value color)) ∂FockGaussian.field) ≤
    (∫ value,Complex.normSq (leadingGaussianValue reference
      (outputHom primary body primaryChannel bodyChannel (MvPolynomial.monomial powers 1)) value) ∂FockGaussian.field) := by
  simp_rw [leading_monomial_dilate,map_mul,Complex.normSq_ofReal]
  rw [integral_const_mul]
  exact mul_le_of_le_one_left (integral_nonneg fun _ => Complex.normSq_nonneg _)
    (by simpa only [pow_two] using (pow_le_one₀ (pow_nonneg hs _) (pow_le_one₀ hs hs1) :
      (scale^weightedOrder (fun seed : InputSeed Color => seed.primaryOrder+seed.bodyOrder) powers)^2 ≤ 1))

end
end AFT.RepresentedPolynomial

namespace AFT.V7Calibration
open MeasureTheory GaussianSource RepresentedPolynomial Filter
open scoped BigOperators Classical Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false

 theorem actual_leading_monomial_scaled_energy_eventually (C : ℝ) (hC : 1 ≤ C) (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ n in atTop,(Parameters.legs n : ℝ)/(2*Parameters.dimension n) ≤ beta n ∧
      beta n ≤ 2*(Parameters.legs n : ℝ)/Parameters.dimension n) :
    ∀ᶠ n in atTop,∀ primaryPool bodyPool : ℕ,0<primaryPool →0<bodyPool →
    primaryPool ≤ Parameters.dimension n →bodyPool ≤ Parameters.dimension n →
    ∀ cutoff powers,weightedOrder (fun seed : InputSeed (Fin (Parameters.modulus n)) => seed.primaryOrder+seed.bodyOrder) powers ≤ cutoff →
    ∀ scale : ℝ,0 ≤ scale →scale ≤ 1 →
    (∫ value,Complex.normSq (leadingGaussianValue (actualReferenceLaw C n (beta n)).weight
      (actualLeadingOutput C n (beta n) (MvPolynomial.monomial powers 1))
        (fun color => (scale : ℂ)*value color)) ∂FockGaussian.field) ≤
    (leadingGaussianFactor n cutoff * monomialWeight
      (inputWeight (actualPrimaryLaw C n (beta n)) (actualBodyLaw C n (beta n)) primaryPool bodyPool ((n : ℝ)^2)) powers)^2 := by
  filter_upwards [actual_leading_monomial_energy_eventually C hC beta hbeta]
    with n h primaryPool bodyPool hp hb hpN hbN cutoff powers ho scale hs hs1
  exact (leading_monomial_scaled_energy_le _ _ _ _ _ powers scale hs hs1).trans
    (h primaryPool bodyPool hp hb hpN hbN cutoff powers ho)

end
end AFT.V7Calibration
