import AFT.LeadingTableEnergy

/-! # Gaussian orthogonality of the literal polynomial degree cutoff -/
namespace AFT.RepresentedPolynomial
open MeasureTheory
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {Color : Type*} [Fintype Color]

def gaussianCoefficient (multiplier : Color → ℂ) (table : Table Color) (powers : Color →₀ ℕ) : ℂ :=
  ((MvPolynomial.coeff powers table : ℝ) : ℂ)*∏ color,multiplier color^powers color

theorem gaussian_polynomial_evaluation (multiplier : Color → ℂ) (table : Table Color) (value : Color → ℂ) :
    MvPolynomial.eval₂ Complex.ofRealHom (fun color => multiplier color*value color) table=
    ∑ powers∈table.support,gaussianCoefficient multiplier table powers*FockGaussian.monomial powers value := by
  conv_lhs => rw [MvPolynomial.as_sum table]
  simp only [MvPolynomial.eval₂_sum,MvPolynomial.eval₂_monomial]
  apply Finset.sum_congr rfl
  intro powers _
  rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  simp only [mul_pow,Finset.prod_mul_distrib,gaussianCoefficient,FockGaussian.monomial]
  exact (mul_assoc _ _ _).symm

theorem gaussian_polynomial_energy (multiplier : Color → ℂ) (table : Table Color) :
    (∫ value,Complex.normSq (MvPolynomial.eval₂ Complex.ofRealHom
      (fun color => multiplier color*value color) table) ∂FockGaussian.field)=
    ∑ powers∈table.support,Complex.normSq (gaussianCoefficient multiplier table powers)*
      (FockGaussian.monomialWeight powers : ℝ) := by
  let embed : (Color →₀ ℕ) ↪ (Color → ℕ) := ⟨fun powers => powers,fun _ _ h => DFunLike.ext' h⟩
  let coeff : (Color → ℕ) → ℂ := fun powers => gaussianCoefficient multiplier table (Finsupp.equivFunOnFinite.symm powers)
  have he (value) : MvPolynomial.eval₂ Complex.ofRealHom (fun color => multiplier color*value color) table=
      FockGaussian.polynomialEvaluation (table.support.map embed) coeff value := by
    rw [gaussian_polynomial_evaluation,FockGaussian.polynomialEvaluation,Finset.sum_map]
    apply Finset.sum_congr rfl
    intro powers _
    simp only [coeff,embed,Function.Embedding.coeFn_mk,Finsupp.equivFunOnFinite_symm_coe]
  simp_rw [he]
  rw [FockGaussian.polynomial_fock_isometry,Finset.sum_map]
  apply Finset.sum_congr rfl
  intro powers _
  simp only [coeff,embed,Function.Embedding.coeFn_mk,Finsupp.equivFunOnFinite_symm_coe]

/-- Deleting polynomial coefficients is an orthogonal projection for the
actual Gaussian field, including arbitrary coordinate normalizations. -/
theorem gaussian_truncate_energy_le (multiplier : Color → ℂ) (table : Table Color)
    (order : Color → ℕ) (cutoff : ℕ) :
    (∫ value,Complex.normSq (MvPolynomial.eval₂ Complex.ofRealHom
      (fun color => multiplier color*value color) (truncate order cutoff table)) ∂FockGaussian.field)≤
    (∫ value,Complex.normSq (MvPolynomial.eval₂ Complex.ofRealHom
      (fun color => multiplier color*value color) table) ∂FockGaussian.field) := by
  rw [gaussian_polynomial_energy,gaussian_polynomial_energy]
  have he (powers) (hp : powers∈(truncate order cutoff table).support) :
      gaussianCoefficient multiplier (truncate order cutoff table) powers=gaussianCoefficient multiplier table powers := by
    unfold gaussianCoefficient
    rw [coeff_truncate,if_pos (Finset.mem_filter.mp hp).2]
  calc
    _ = ∑ powers∈(truncate order cutoff table).support,
        Complex.normSq (gaussianCoefficient multiplier table powers)*(FockGaussian.monomialWeight powers : ℝ) := by
      apply Finset.sum_congr rfl
      intro powers hp
      rw [he powers hp]
    _ ≤ _ := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      intro powers _ _
      exact mul_nonneg (Complex.normSq_nonneg _) (Nat.cast_nonneg _)

theorem leadingGaussianValue_truncate_energy_le (reference : Color → ℝ) (table : Table Color)
    (scale : ℝ) (order : Color → ℕ) (cutoff : ℕ) :
    (∫ value,Complex.normSq (leadingGaussianValue reference (truncate order cutoff table)
      (fun color => (scale : ℂ)*value color)) ∂FockGaussian.field)≤
    (∫ value,Complex.normSq (leadingGaussianValue reference table
      (fun color => (scale : ℂ)*value color)) ∂FockGaussian.field) := by
  simpa only [leadingGaussianValue,mul_div_assoc,div_mul_eq_mul_div] using
    gaussian_truncate_energy_le (fun color => (scale : ℂ)/(Real.sqrt (reference color) : ℂ)) table order cutoff

end
end AFT.RepresentedPolynomial
