import AFT.ActualConditionalPairProgram
import AFT.ActualAnchorProgram
import AFT.ActualShiftedBodyProgram
import AFT.NumericalProbabilityKernel
import AFT.PublicChartGaussian

/-! # Executable conditional triples with the actual shared Gaussian source -/
namespace AFT.V7Calibration
open GaussianSource RationalNumerics Filter
open scoped BigOperators

/-- Removing the marked atom algebraically avoids numerical division by
an inactive probability; both factors use exactly the same source. -/
def conditionalJointProgram (constant n mark : ℕ) (attached : ℤ → ℚ) (first second : ℕ) : ℚ :=
  (∑ source : Window (actualLegCutoffProgram constant n-1),
    windowTicketWeightProgram (actualAuxiliarySquaredWidth 10 n) (actualLegCutoffProgram constant n-1) n source*
      probabilityClamp (conditionalPairAtSourceProgram constant n mark source first second)*attached source)+
  probabilityClamp (actualActivationApprox constant n n)*
    ((if first=mark then 1 else 0)*probabilityClamp (actualAnchorProgram constant n false mark second)-
      probabilityClamp (conditionalPairAtSourceProgram constant n mark 0 first second))*attached 0

noncomputable section
open scoped Classical Topology
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
local instance conditionalJointProgramFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _

theorem conditionalPairAtSource_probability (C : ℝ) (n : ℕ) (mark first second : Fin (Parameters.modulus n))
    (source : ℤ) : 0 ≤ conditionalPairAtSource C n mark source first second ∧
      conditionalPairAtSource C n mark source first second ≤ 1 := by
  refine ⟨TrimmedSlice.mixedPair_nonneg _ _ _ _ _ _ (FiniteDist.nonneg _) _ _,?_⟩
  have hp (sample : bodySample C n × Bool) :
      TrimmedSlice.averagedPair (Parameters.modulus n) (boundaryHalf C n)
        (conditionalPairStart C n mark sample) source (Parameters.anchorWidth n) first second ≤ 1 := by
    rw [←averagedPairProgram_cast]
    exact (le_abs_self _).trans (averagedPairProgram_abs_le_one _ _ _ _ _ _ _)
  calc
    _ ≤ ∑ sample,(errorLaw (bodyBlur C n)).weight sample*1 :=
      Finset.sum_le_sum fun sample _ => mul_le_mul_of_nonneg_left (hp sample) (FiniteDist.nonneg _ _)
    _ = 1 := by simp only [mul_one,FiniteDist.sum_one]

theorem actualAnchorMatrix_body (C : ℝ) (n : ℕ) (mark : Fin (Parameters.modulus n)) (output : ℤ) :
    actualAnchorMatrix C n false mark output=
      blurredAnchorKernel (Parameters.modulus n) (Parameters.anchorWidth n) (bodyShift C n) (bodyBlur C n) mark output := by
  simp only [actualAnchorMatrix,Bool.false_eq_true,if_false,blurredAnchorKernel,pairSourceLaw,FiniteDist.prod_weight]
  change (∑ x : bodySample C n × Window (legCutoff C n-1),_) = _
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro sample _
  rw [show (∑ source,(bodyBlur C n).weight sample*
      (windowGaussian (10*n) (legCutoff C n-1)).weight source*
        publicAnchorKernel (Parameters.modulus n) (Parameters.anchorWidth n) mark (output-bodyShift C n sample))=
      (bodyBlur C n).weight sample*
        publicAnchorKernel (Parameters.modulus n) (Parameters.anchorWidth n) mark (output-bodyShift C n sample)*
          ∑ source,(windowGaussian (10*n) (legCutoff C n-1)).weight source by rw [Finset.mul_sum];apply Finset.sum_congr rfl;intros;ring,
    FiniteDist.sum_one,mul_one]

theorem actualAnchorMatrix_probability (C : ℝ) (n : ℕ) (rootOnly : Bool)
    (mark : Fin (Parameters.modulus n)) (output : ℤ) :
    0 ≤ actualAnchorMatrix C n rootOnly mark output ∧ actualAnchorMatrix C n rootOnly mark output ≤ 1 := by
  refine ⟨blurredAnchorKernel_nonneg _ _ _ _ _ _,?_⟩
  unfold actualAnchorMatrix blurredAnchorKernel
  calc
    _ ≤ ∑ sample,(pairSourceLaw C n).weight sample*1 := by
      apply Finset.sum_le_sum
      intro sample _
      apply mul_le_mul_of_nonneg_left _ (FiniteDist.nonneg _ _)
      rw [←publicAnchorKernelProgram_cast]
      exact (le_abs_self _).trans (publicAnchorKernelProgram_abs_le_one _ _ _ _)
    _ = 1 := by simp only [mul_one,FiniteDist.sum_one]

theorem conditionalJointOutput_atom_removed (C : ℝ) (n : ℕ)
    (mark first second : Fin (Parameters.modulus n))
    (attached : Window (legCutoff C n-1) → ℝ) :
    conditionalJointOutput C n mark attached first second=
      (∑ source,(windowGaussian (10*n) (legCutoff C n-1)).weight source*
        conditionalPairAtSource C n mark source first second*attached source)+
      v7Activation C n*((if first=mark then 1 else 0)*actualAnchorMatrix C n false mark second.val-
        conditionalPairAtSource C n mark 0 first second)*attached (windowZero _) := by
  unfold conditionalJointOutput
  rw [actualAnchorMatrix_body,Finset.mul_sum]
  simp_rw [←mul_assoc]
  have he (source : Window (legCutoff C n-1)) :
      (1-v7Activation C n)*(inactiveLegSource C n).weight source=
        (windowGaussian (10*n) (legCutoff C n-1)).weight source-
          if source=windowZero _ then v7Activation C n else 0 := by
    linarith only [inactiveLegSource_mixture C n source]
  simp_rw [he,sub_mul]
  rw [Finset.sum_sub_distrib]
  have hs : (∑ source : Window (legCutoff C n-1),
      (if source=windowZero _ then v7Activation C n else 0)*
        conditionalPairAtSource C n mark source first second*attached source)=
      v7Activation C n*conditionalPairAtSource C n mark 0 first second*attached (windowZero _) := by
    simp only [ite_mul,zero_mul,Finset.sum_ite_eq',Finset.mem_univ,if_true,windowZero]
  rw [hs]
  ring

/-- All actual scalar errors used by this triple evaluator are negligible. -/
def conditionalJointProgramError (n : ℕ) : ℝ :=
  3/(2 : ℝ)^n+2*actualBodyBlurProgramError n+actualPairSourceProgramError n

theorem conditionalJointProgramError_negligible : Negligible conditionalJointProgramError := by
  have hm : Negligible (fun n : ℕ => 1/(2 : ℝ)^n) := by
    convert betaGridMesh_negligible using 1
    funext n;simp only [betaGridMesh,Nat.cast_pow,Nat.cast_ofNat]
  convert ((hm.const_mul 3).add (actualBodyBlurProgramError_negligible.const_mul 2)).add
    actualPairSourceProgramError_negligible using 1
  funext n;unfold conditionalJointProgramError;ring

/-- The retained-source triple evaluator is uniformly stable for arbitrary
attached profiles. Thus later joint input fibers are not restricted to
rank-one tensors. -/
theorem conditional_joint_program_eventually (constant : ℕ) (hc : 1 ≤ constant) :
    ∀ᶠ n : ℕ in atTop,∀ (mark first second : Fin (Parameters.modulus n))
      (attached : ℤ → ℝ) (approximateAttached : ℤ → ℚ) (error : ℝ),
      (∀ source,|attached source| ≤ 1) →
      (∀ source,|(approximateAttached source : ℝ)| ≤ 1) →
      (∀ source : Window (actualLegCutoffProgram constant n-1),
        |(approximateAttached source : ℝ)-attached source| ≤ error) →
      |(conditionalJointProgram constant n mark.val approximateAttached first.val second.val : ℝ)-
        conditionalJointOutput constant n mark (fun source => attached source) first second| ≤
          conditionalJointProgramError n+3*error := by
  filter_upwards [conditional_pair_at_source_program_eventually constant,
    actual_anchor_program_eventually constant,eventually_ge_atTop 2] with n hpair hanchor hn
  intro mark first second attached approximateAttached error hatt happ herr
  let sourceLaw := windowGaussian (10*(n : ℝ)) (legCutoff (constant : ℝ) n-1)
  let pair := fun source : ℤ => conditionalPairAtSource (constant : ℝ) n mark source first second
  let pairApprox := fun source : ℤ => (probabilityClamp
    (conditionalPairAtSourceProgram constant n mark.val source first.val second.val) : ℝ)
  let rho := v7Activation (constant : ℝ) n
  let rhoApprox : ℝ := probabilityClamp (actualActivationApprox constant n n)
  let anchor := actualAnchorMatrix (constant : ℝ) n false mark second.val
  let anchorApprox : ℝ := probabilityClamp (actualAnchorProgram constant n false mark.val second.val)
  have clamp_abs (value : ℚ) : |(probabilityClamp value : ℝ)| ≤ 1 := by
    rw [abs_of_nonneg (probabilityClamp_bounds value).1]
    exact (probabilityClamp_bounds value).2
  have hpbound (source : ℤ) : |pairApprox source| ≤ 1 := clamp_abs _
  have hperror (source : ℤ) : |pairApprox source-pair source| ≤ actualBodyBlurProgramError n :=
    (probabilityClamp_error _ _ (conditionalPairAtSource_probability constant n mark first second source).1
      (conditionalPairAtSource_probability constant n mark first second source).2).trans (hpair mark first second source)
  have hrbound : |rhoApprox| ≤ 1 := clamp_abs _
  have habound : |anchorApprox| ≤ 1 := clamp_abs _
  have herror0 := herr (windowZero (actualLegCutoffProgram constant n-1))
  change |(approximateAttached 0 : ℝ)-attached 0| ≤ error at herror0
  have hrnonneg : 0 ≤ rho := (activation_positive _ _ _ _
    (legFeatureCount_positive (constant : ℝ) n (by exact_mod_cast hc) (by omega))).le
  have hrerror : |rhoApprox-rho| ≤ 1/(2 : ℝ)^n :=
    (probabilityClamp_error _ _ hrnonneg (activation_le_one _ _ _ _)).trans
      (actualActivationApprox_error constant n n hc (by omega))
  have haerror : |anchorApprox-anchor| ≤ actualPairSourceProgramError n :=
    (probabilityClamp_error _ _ (actualAnchorMatrix_probability constant n false mark second.val).1
      (actualAnchorMatrix_probability constant n false mark second.val).2).trans (hanchor false mark second.val)
  have hlaw : (∑ source : Window (actualLegCutoffProgram constant n-1),
      |(windowTicketWeightProgram (actualAuxiliarySquaredWidth 10 n) (actualLegCutoffProgram constant n-1) n source : ℝ)-
        sourceLaw.weight (actualLegWindowEquiv constant n source)|) ≤ 1/(2 : ℝ)^n := by
    simp only [←actualLegTicketLaw_program_weight]
    rw [(actualLegWindowEquiv constant n).sum_comp (fun source =>
      |(actualLegTicketLaw constant 10 n n).weight source-sourceLaw.weight source|)]
    exact actualLegTicketLaw_l1 constant 10 n n (by decide) (by omega)
  have hmass : (∑ source : Window (actualLegCutoffProgram constant n-1),
      sourceLaw.weight (actualLegWindowEquiv constant n source))=1 := by
    rw [(actualLegWindowEquiv constant n).sum_comp,sourceLaw.sum_one]
  have hfirst := probability_expectation_perturbation
    (fun source => sourceLaw.weight (actualLegWindowEquiv constant n source))
    (fun source => (windowTicketWeightProgram (actualAuxiliarySquaredWidth 10 n)
      (actualLegCutoffProgram constant n-1) n source : ℝ))
    (fun source => pair source*attached source)
    (fun source => pairApprox source*(approximateAttached source : ℝ))
    (1/(2 : ℝ)^n) (actualBodyBlurProgramError n+error)
    (fun source => sourceLaw.nonneg _) hmass
    (fun source => by rw [abs_mul];exact (mul_le_mul (hpbound source) (happ source) (abs_nonneg _) (by norm_num)).trans_eq (mul_one _))
    hlaw (fun source => bounded_product_error _ _ _ _ _ _ (hpbound source) (hatt source) (hperror source) (herr source))
  have hsum : (∑ source : Window (actualLegCutoffProgram constant n-1),
      sourceLaw.weight (actualLegWindowEquiv constant n source)*(pair source*attached source))=
      ∑ source,sourceLaw.weight source*pair source*attached source := by
    have hh := (actualLegWindowEquiv constant n).sum_comp
      (fun source => sourceLaw.weight source*pair source*attached source)
    simpa only [actualLegWindowEquiv,mul_assoc] using hh
  rw [hsum] at hfirst
  have ha0 : |anchor| ≤ 1 := by
    rw [abs_of_nonneg (actualAnchorMatrix_probability constant n false mark second.val).1]
    exact (actualAnchorMatrix_probability constant n false mark second.val).2
  have hp0 : |pair 0| ≤ 1 := by
    rw [abs_of_nonneg (conditionalPairAtSource_probability constant n mark first second 0).1]
    exact (conditionalPairAtSource_probability constant n mark first second 0).2
  have hactive := bounded_product_error (rhoApprox*anchorApprox) (approximateAttached 0)
    (rho*anchor) (attached 0) (1/(2 : ℝ)^n+actualPairSourceProgramError n) error
    (by rw [abs_mul];exact (mul_le_mul hrbound habound (abs_nonneg _) (by norm_num)).trans_eq (mul_one _))
    (hatt 0) (bounded_product_error _ _ _ _ _ _ hrbound ha0 hrerror haerror) herror0
  have hinactive := bounded_product_error (rhoApprox*pairApprox 0) (approximateAttached 0)
    (rho*pair 0) (attached 0) (1/(2 : ℝ)^n+actualBodyBlurProgramError n) error
    (by rw [abs_mul];exact (mul_le_mul hrbound (hpbound 0) (abs_nonneg _) (by norm_num)).trans_eq (mul_one _))
    (hatt 0) (bounded_product_error _ _ _ _ _ _ hrbound hp0 hrerror (hperror 0)) herror0
  rw [conditionalJointOutput_atom_removed]
  simp only [conditionalJointProgram,Rat.cast_add,Rat.cast_sum,Rat.cast_mul,Rat.cast_sub,
    apply_ite,Rat.cast_one,Rat.cast_zero]
  have heq : first.val=mark.val ↔ first=mark := Fin.ext_iff.symm
  simp only [heq]
  change |((∑ source : Window (actualLegCutoffProgram constant n-1),
    (windowTicketWeightProgram (actualAuxiliarySquaredWidth 10 n) (actualLegCutoffProgram constant n-1) n source : ℝ)*
      pairApprox source*(approximateAttached source : ℝ))+
    rhoApprox*((if first=mark then 1 else 0)*anchorApprox-pairApprox 0)*(approximateAttached 0 : ℝ))-
    ((∑ source,sourceLaw.weight source*pair source*attached source)+
      rho*((if first=mark then 1 else 0)*anchor-pair 0)*attached 0)| ≤ _
  have ht (a b c d e f : ℝ) : |(a+b-c)-(d+e-f)| ≤ |a-d|+|b-e|+|c-f| := by
    rw [show (a+b-c)-(d+e-f)=((a-d)+(b-e))-(c-f) by ring]
    exact (abs_sub _ _).trans (add_le_add (abs_add_le _ _) (le_refl _))
  split_ifs with heq
  · simp only [one_mul]
    rw [show rhoApprox*(anchorApprox-pairApprox 0)*(approximateAttached 0 : ℝ)=
        rhoApprox*anchorApprox*(approximateAttached 0 : ℝ)-rhoApprox*pairApprox 0*(approximateAttached 0 : ℝ) by ring,
      show rho*(anchor-pair 0)*attached 0=rho*anchor*attached 0-rho*pair 0*attached 0 by ring,
      ←add_sub_assoc,←add_sub_assoc]
    have h := (ht _ _ _ _ _ _).trans (add_le_add (add_le_add (by simpa only [mul_assoc] using hfirst) hactive) hinactive)
    have h' := h.trans_eq (show 1/(2 : ℝ)^n+(actualBodyBlurProgramError n+error)+
      (1/(2 : ℝ)^n+actualPairSourceProgramError n+error)+
      (1/(2 : ℝ)^n+actualBodyBlurProgramError n+error)=conditionalJointProgramError n+3*error by
      unfold conditionalJointProgramError;ring)
    simpa only [mul_assoc] using h' 
  · simp only [zero_mul,zero_sub,mul_neg,neg_mul,←sub_eq_add_neg]
    have h := (approximation_sub_error _ _ _ _).trans (add_le_add (by simpa only [mul_assoc] using hfirst) hinactive)
    have hnonneg : 0 ≤ 1/(2 : ℝ)^n+actualPairSourceProgramError n+error := (abs_nonneg _).trans hactive
    have h' := h.trans (show 1/(2 : ℝ)^n+(actualBodyBlurProgramError n+error)+
      (1/(2 : ℝ)^n+actualBodyBlurProgramError n+error) ≤ conditionalJointProgramError n+3*error by
      unfold conditionalJointProgramError
      linarith [show (3 : ℝ)/2^n=3*(1/(2 : ℝ)^n) by ring])
    simpa only [mul_assoc] using h' 

end
end AFT.V7Calibration
