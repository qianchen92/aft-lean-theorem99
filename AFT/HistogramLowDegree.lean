import AFT.GaussianPolynomialTruncation
import AFT.CenteredGaussianEvaluation
import AFT.ReferenceCoefficientPolynomial
import AFT.SymmetricCoefficients

/-! # Actual low-degree histogram energy from the literal physical PGF -/
namespace AFT.RepresentedPolynomial
open MeasureTheory
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000
variable {Slot Color : Type*} [Fintype Slot] [Fintype Color]

omit [Fintype Color] in
 theorem truncate_homogeneous (table : Table Color) (degree cutoff : ℕ)
    (h : table.IsHomogeneous degree) :
    truncate (fun _ : Color => 1) cutoff table=if degree≤cutoff then table else 0 := by
  ext powers
  rw [coeff_truncate]
  have hc (hne : weightedOrder (fun _ : Color => 1) powers≠degree) : MvPolynomial.coeff powers table=0 := by
    apply h.coeff_eq_zero
    simpa only [weightedOrder,mul_one] using hne
  by_cases hd : degree≤cutoff
  · rw [if_pos hd]
    by_cases hp : weightedOrder (fun _ : Color => 1) powers≤cutoff
    · rw [if_pos hp]
    · rw [if_neg hp,hc (by omega)]
  · rw [if_neg hd,MvPolynomial.coeff_zero]
    by_cases hp : weightedOrder (fun _ : Color => 1) powers≤cutoff
    · rw [if_pos hp,hc (by omega)]
    · rw [if_neg hp]

 theorem referenceCoefficientForm_homogeneous (reference : FiniteDist Color)
    (mass : (Slot → Color) → ℝ) (selected : Finset Slot) :
    (referenceCoefficientForm reference reference mass selected).IsHomogeneous selected.card := by
  apply MvPolynomial.IsHomogeneous.sum
  intro word _
  apply MvPolynomial.IsHomogeneous.C_mul
  convert MvPolynomial.IsHomogeneous.prod Finset.univ
    (fun slot : selected => MvPolynomial.X (R := ℝ) (word slot))
    (fun _ => 1) (fun slot _ => MvPolynomial.isHomogeneous_X ℝ (word slot)) using 1
  simp

 theorem referenceCoefficientForm_gaussian (reference : FiniteDist Color)
    (href : ∀ color,0<reference.weight color) (mass : (Slot → Color) → ℝ)
    (selected : Finset Slot) (value : Color → ℂ) :
    leadingGaussianValue reference.weight (referenceCoefficientForm reference reference mass selected) value=
    TensorFock.tensorEvaluation (LocalTensors.localTensor (fun _ : Slot => reference) mass selected) value := by
  rw [referenceCoefficientForm_formula reference reference href]
  simp only [leadingGaussianValue,MvPolynomial.eval₂_sum,MvPolynomial.eval₂_mul,
    MvPolynomial.eval₂_C,MvPolynomial.eval₂_prod]
  rw [LocalTensors.localTensor_evaluation]
  apply Finset.sum_congr rfl
  intro source _
  congr 1
  apply Finset.prod_congr rfl
  intro slot _
  have he := centeredFactor_gaussian reference href (source slot) value
  simp only [centeredFactor,MvPolynomial.eval₂_sub,MvPolynomial.eval₂_add,MvPolynomial.eval₂_one] at he
  simp only [MvPolynomial.eval₂_sub]
  linear_combination he

 theorem centeredGenerating_truncate_gaussian (reference : FiniteDist Color)
    (href : ∀ color,0<reference.weight color) (mass : (Slot → Color) → ℝ)
    (cutoff : ℕ) (value : Color → ℂ) :
    leadingGaussianValue reference.weight
      (truncate (fun _ : Color => 1) cutoff (centeredGeneratingLinear reference.weight mass)) value=
    TensorFock.seriesEvaluation ((Finset.range (Fintype.card Slot+1)).filter (·≤cutoff))
      (LocalTensors.degreeTensor (fun _ : Slot => reference) mass) value := by
  rw [centeredGeneratingLinear_reference_expansion reference reference href]
  have hsum (indices : Finset (Finset Slot)) :
      truncate (fun _ : Color => 1) cutoff (∑ selected∈indices,referenceCoefficientForm reference reference mass selected)=
      ∑ selected∈indices,truncate (fun _ : Color => 1) cutoff (referenceCoefficientForm reference reference mass selected) := by
    induction indices using Finset.induction_on with
    | empty => simp
    | @insert index indices hnot ih => rw [Finset.sum_insert hnot,truncate_add,ih,Finset.sum_insert hnot]
  rw [hsum]
  simp_rw [truncate_homogeneous _ _ _ (referenceCoefficientForm_homogeneous reference mass _)]
  simp only [leadingGaussianValue,MvPolynomial.eval₂_sum]
  have he (selected : Finset Slot) :
      MvPolynomial.eval₂ Complex.ofRealHom (fun color => value color/(Real.sqrt (reference.weight color) : ℂ))
        (if selected.card≤cutoff then referenceCoefficientForm reference reference mass selected else 0)=
      if selected.card≤cutoff then
        TensorFock.tensorEvaluation (LocalTensors.localTensor (fun _ : Slot => reference) mass selected) value else 0 := by
    split_ifs with h
    · exact referenceCoefficientForm_gaussian reference href mass selected value
    · simp
  simp_rw [he]
  simp only [TensorFock.seriesEvaluation,LocalTensors.degreeTensor_evaluation]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro selected _
  have hs : selected.card<Fintype.card Slot+1 := Nat.lt_succ_of_le (Finset.card_le_univ _)
  simp [Fintype.card_coe,hs]

end
end AFT.RepresentedPolynomial

namespace AFT.HistogramNormalization
open MeasureTheory RepresentedPolynomial
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000
variable {Slot Color : Type*} [Fintype Slot] [Fintype Color]

def densityLow (reference : FiniteDist Color) (mass : (Slot → Color) → ℝ)
    (cutoff : ℕ) (word : Slot → Color) : ℝ :=
  ∑ selected ∈ Finset.univ.filter (fun selected : Finset Slot => selected.card≤cutoff),
    Hoeffding.densityComponent (fun _ : Slot => reference) mass selected word

theorem densityLow_energy (reference : FiniteDist Color)
    (hreference : ∀ color,0<reference.weight color) (mass : (Slot → Color) → ℝ)
    (hexchangeable : ExchangeableMass mass) (cutoff : ℕ) :
    (FiniteDist.independent (fun _ : Slot => reference)).l2Sq (densityLow reference mass cutoff)=
    ∑ degree∈(Finset.range (Fintype.card Slot+1)).filter (·≤cutoff),
      (degree.factorial : ℝ)*BlockFock.tensorEnergy
        (LocalTensors.degreeTensor (fun _ : Slot => reference) mass degree)/
        ((Fintype.card Slot).descFactorial degree : ℝ) := by
  unfold densityLow
  rw [Hoeffding.canonical_sum_l2Sq _ _ _
    (fun selected _ => Hoeffding.densityComponent_canonical _ (fun _ color => hreference color) mass selected)]
  have hgroup := Finset.sum_fiberwise_of_maps_to
    (s := Finset.univ.filter (fun selected : Finset Slot => selected.card≤cutoff))
    (t := (Finset.range (Fintype.card Slot+1)).filter (·≤cutoff))
    (g := fun selected : Finset Slot => selected.card) (by
      intro selected hselected
      simp only [Finset.mem_filter,Finset.mem_univ,true_and] at hselected
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.card_le_univ _)),hselected⟩)
    (fun selected => (FiniteDist.independent (fun _ : Slot => reference)).l2Sq
      (Hoeffding.densityComponent (fun _ : Slot => reference) mass selected))
  rw [← hgroup]
  apply Finset.sum_congr rfl
  intro degree hdegree
  obtain ⟨hrange,hcutoff⟩ := Finset.mem_filter.mp hdegree
  have hsets : ((Finset.univ.filter fun selected : Finset Slot => selected.card≤cutoff).filter
      fun selected => selected.card=degree)=Finset.univ.powersetCard degree := by
    ext selected
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_powersetCard_univ]
    constructor
    · exact And.right
    · intro h; exact ⟨by simpa only [h] using hcutoff,h⟩
  rw [hsets]
  exact degree_energy_identity reference mass hexchangeable degree
    (Nat.lt_succ_iff.mp (Finset.mem_range.mp hrange))

/-- The literal low-degree PGF has precisely the normalized Gaussian
coefficient energy of the actual signed physical mass. -/
theorem low_degree_gaussian_energy (reference : FiniteDist Color)
    (hreference : ∀ color,0<reference.weight color) (mass : (Slot → Color) → ℝ)
    (cutoff : ℕ) (radius : ℝ) :
    (∫ value,Complex.normSq (leadingGaussianValue reference.weight
      (truncate (fun _ : Color => 1) cutoff (centeredGeneratingLinear reference.weight mass))
      (fun color => ((radius/Real.sqrt (Fintype.card Slot) : ℝ) : ℂ)*value color)) ∂FockGaussian.field)=
    ∑ degree∈(Finset.range (Fintype.card Slot+1)).filter (·≤cutoff),
      (degree.factorial : ℝ)*radius^(2*degree)*BlockFock.tensorEnergy
        (LocalTensors.degreeTensor (fun _ : Slot => reference) mass degree)/(Fintype.card Slot : ℝ)^degree := by
  simp_rw [centeredGenerating_truncate_gaussian reference hreference]
  have he (value) : TensorFock.seriesEvaluation ((Finset.range (Fintype.card Slot+1)).filter (·≤cutoff))
      (LocalTensors.degreeTensor (fun _ : Slot => reference) mass)
      (fun color => ((radius/Real.sqrt (Fintype.card Slot) : ℝ) : ℂ)*value color)=
    TensorFock.seriesEvaluation ((Finset.range (Fintype.card Slot+1)).filter (·≤cutoff))
      (TensorFock.normalizedTensor (Fintype.card Slot) radius (LocalTensors.degreeTensor (fun _ : Slot => reference) mass)) value := by
    unfold TensorFock.normalizedTensor
    simp only [TensorFock.seriesEvaluation,NonlinearFock.tensorEvaluation_dilate,Fintype.card_fin,
      NonlinearFock.tensorEvaluation_smul]
  simp_rw [he]
  rw [TensorFock.complete_tensor_fock_isometry _ _ (by
    intro degree _ word permutation
    simp only [TensorFock.normalizedTensor,LocalTensors.degreeTensor_symmetric])]
  apply Finset.sum_congr rfl
  intro degree _
  unfold TensorFock.normalizedTensor
  rw [TensorFock.tensorEnergy_smul]
  have hn : ((radius/Real.sqrt (Fintype.card Slot : ℝ))^degree)^2=
      radius^(2*degree)/(Fintype.card Slot : ℝ)^degree := by
    rw [← pow_mul,Nat.mul_comm degree 2,pow_mul,div_pow,
      Real.sq_sqrt (Nat.cast_nonneg _),div_pow,← pow_mul]
  rw [hn]
  ring

/-- Every retained histogram degree is bounded by the actual normalized
Gaussian energy. The finite-population denominator is kept exact. -/
theorem densityLow_energy_le_gaussian (reference : FiniteDist Color)
    (hreference : ∀ color,0<reference.weight color) (mass : (Slot → Color) → ℝ)
    (hexchangeable : ExchangeableMass mass) (cutoff : ℕ) (radius : ℝ)
    (hpopulation : 0<Fintype.card Slot) (hradius : Real.exp 1≤radius^2) :
    (FiniteDist.independent (fun _ : Slot => reference)).l2Sq (densityLow reference mass cutoff)≤
    (∫ value,Complex.normSq (leadingGaussianValue reference.weight
      (truncate (fun _ : Color => 1) cutoff (centeredGeneratingLinear reference.weight mass))
      (fun color => ((radius/Real.sqrt (Fintype.card Slot) : ℝ) : ℂ)*value color)) ∂FockGaussian.field) := by
  rw [densityLow_energy reference hreference mass hexchangeable,
    low_degree_gaussian_energy reference hreference]
  apply Finset.sum_le_sum
  intro degree hd
  have hdN : degree≤Fintype.card Slot := Nat.lt_succ_iff.mp (Finset.mem_range.mp (Finset.mem_filter.mp hd).1)
  have he : 0≤BlockFock.tensorEnergy (LocalTensors.degreeTensor (fun _ : Slot => reference) mass degree) :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hfac := HistogramTail.reciprocal_descFactorial_le (Fintype.card Slot) degree hpopulation hdN
  have hpow : Real.exp 1^degree≤radius^(2*degree) := by
    simpa only [← pow_mul] using pow_le_pow_left₀ (Real.exp_pos 1).le hradius degree
  have hpoint := hfac.trans (div_le_div_of_nonneg_right hpow (pow_nonneg (Nat.cast_nonneg _) _))
  have hh := mul_le_mul_of_nonneg_left hpoint (mul_nonneg (Nat.cast_nonneg degree.factorial) he)
  convert hh using 1 <;> ring


/-- Symmetrization leaves the generating coefficients unchanged, so the
same bound applies directly to the histogram likelihood of an arbitrary
signed physical mass. -/
theorem symmetrized_densityLow_energy_le_gaussian (reference : FiniteDist Color)
    (hreference : ∀ color,0<reference.weight color) (mass : (Slot → Color) → ℝ)
    (cutoff : ℕ) (radius : ℝ) (hpopulation : 0<Fintype.card Slot)
    (hradius : Real.exp 1≤radius^2) :
    (FiniteDist.independent (fun _ : Slot => reference)).l2Sq
      (densityLow reference (symmetrizedMass mass) cutoff)≤
    (∫ value,Complex.normSq (leadingGaussianValue reference.weight
      (truncate (fun _ : Color => 1) cutoff (centeredGeneratingLinear reference.weight mass))
      (fun color => ((radius/Real.sqrt (Fintype.card Slot) : ℝ) : ℂ)*value color)) ∂FockGaussian.field) := by
  have h := densityLow_energy_le_gaussian reference hreference (symmetrizedMass mass)
    (symmetrizedMass_exchangeable mass) cutoff radius hpopulation hradius
  rw [low_degree_gaussian_energy reference hreference] at h ⊢
  refine h.trans_eq ?_
  apply Finset.sum_congr rfl
  intro degree hd
  rw [degreeTensor_symmetrizedMass reference mass degree
    (Nat.lt_succ_iff.mp (Finset.mem_range.mp (Finset.mem_filter.mp hd).1))]

/-- A low-degree physical PGF identity transfers an actual analytic bound
to the labeled, symmetrized histogram likelihood with no coefficient loss. -/
theorem densityLow_energy_le_of_truncate_eq (reference : FiniteDist Color)
    (hreference : ∀ color,0<reference.weight color) (mass : (Slot → Color) → ℝ)
    (polynomial : Table Color) (cutoff : ℕ) (radius bound : ℝ)
    (hpopulation : 0<Fintype.card Slot) (hradius : Real.exp 1≤radius^2)
    (hidentity : truncate (fun _ : Color => 1) cutoff (centeredGeneratingLinear reference.weight mass)=
      truncate (fun _ : Color => 1) cutoff polynomial)
    (henergy : (∫ value,Complex.normSq (leadingGaussianValue reference.weight polynomial
      (fun color => ((radius/Real.sqrt (Fintype.card Slot) : ℝ) : ℂ)*value color)) ∂FockGaussian.field)≤bound) :
    (FiniteDist.independent (fun _ : Slot => reference)).l2Sq
      (densityLow reference (symmetrizedMass mass) cutoff)≤bound := by
  have h := symmetrized_densityLow_energy_le_gaussian reference hreference mass cutoff radius hpopulation hradius
  rw [hidentity] at h
  exact h.trans ((leadingGaussianValue_truncate_energy_le reference.weight polynomial
    (radius/Real.sqrt (Fintype.card Slot)) (fun _ => 1) cutoff).trans henergy)

end
end AFT.HistogramNormalization
