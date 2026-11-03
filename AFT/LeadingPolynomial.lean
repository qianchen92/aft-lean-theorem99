import AFT.LeadingChannelEnergy

/-! # The joint leading tensor is the actual evaluated output polynomial -/
namespace AFT.RepresentedPolynomial
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {Color Output : Type*} [Fintype Color] [Fintype Output]

omit [Fintype Output] in
theorem leadingSeedTensor_formula (primary body : FiniteDist Color) (reference : Output → ℝ)
    (primaryChannel bodyChannel : Color → Output → ℝ) (seed : InputSeed Color)
    (word : Fin (seed.primaryOrder+seed.bodyOrder) → Output) :
    leadingSeedTensor primary body reference primaryChannel bodyChannel seed word=
      seedOutputMass primary body primaryChannel bodyChannel seed word/
        ∏ slot,Real.sqrt (reference (word slot)) := by
  rw [leadingSeedTensor]
  change TensorChannel.apply _ (fun slot => TensorChannel.ofKernel (inputReference primary body seed slot)
    (fun input output => seedChannel primaryChannel bodyChannel seed slot input output/Real.sqrt (reference output))) seed.kernel word=_
  rw [TensorChannel.apply_ofKernel]
  simp only [FiniteDist.expectation,FiniteDist.independent,Finset.prod_div_distrib,
    seedOutputMass,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro input _
  ring

/-- The coefficient vector used in the Hilbert estimate is precisely the
literal leading output evaluated at the reference-normalized Gaussian. -/
theorem leadingSeedTensor_evaluation (primary body : FiniteDist Color) (reference : Output → ℝ)
    (primaryChannel bodyChannel : Color → Output → ℝ) (seed : InputSeed Color) (value : Output → ℂ) :
    MvPolynomial.eval₂ Complex.ofRealHom (fun output => value output/(Real.sqrt (reference output) : ℂ))
      (seedOutput primary body primaryChannel bodyChannel seed)=
    TensorFock.tensorEvaluation (leadingSeedTensor primary body reference primaryChannel bodyChannel seed) value := by
  rw [seedOutput_eq_mass]
  simp only [MvPolynomial.eval₂_sum,MvPolynomial.eval₂_mul,MvPolynomial.eval₂_C,
    MvPolynomial.eval₂_prod,MvPolynomial.eval₂_X,TensorFock.tensorEvaluation,TensorFock.wordMonomial]
  rw [show (fun a b : Fin (seed.primaryOrder+seed.bodyOrder) => Classical.propDecidable (a=b))=instDecidableEqFin (seed.primaryOrder+seed.bodyOrder) from Subsingleton.elim _ _]
  apply Finset.sum_congr rfl
  intro word _
  rw [leadingSeedTensor_formula]
  simp only [Finset.prod_div_distrib]
  push_cast
  change (seedOutputMass primary body primaryChannel bodyChannel seed word : ℂ)*_= _
  ring

 theorem leadingSeedTensor_gaussian_energy (primary body : FiniteDist Color) (reference : Output → ℝ)
    (primaryChannel bodyChannel : Color → Output → ℝ) (seed : InputSeed Color) :
    (∫ value,Complex.normSq (MvPolynomial.eval₂ Complex.ofRealHom
      (fun output => value output/(Real.sqrt (reference output) : ℂ))
      (seedOutput primary body primaryChannel bodyChannel seed)) ∂FockGaussian.field) ≤
    ((seed.primaryOrder+seed.bodyOrder).factorial : ℝ)*
      BlockFock.tensorEnergy (leadingSeedTensor primary body reference primaryChannel bodyChannel seed) := by
  simp_rw [leadingSeedTensor_evaluation]
  simpa only [Fintype.card_fin] using TensorFock.tensor_gaussian_energy_le
    (leadingSeedTensor primary body reference primaryChannel bodyChannel seed)

end
end AFT.RepresentedPolynomial
