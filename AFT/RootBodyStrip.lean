import AFT.BodyReferenceEnergy
import AFT.PrimaryLawLower
import AFT.ActualTripleEnergy
import AFT.JointSignedChannel

/-! # Actual centered root/body channels and their complete strip bounds -/

namespace AFT
open scoped BigOperators Classical
noncomputable section

theorem profileSquareNorm_reference_domination {Color : Type*} [Fintype Color]
    (first second profile : Color → ℝ) (cost : ℝ)
    (hfirst : ∀ color, 0 < first color) (hsecond : ∀ color, 0 < second color)
    (hcompare : ∀ color, second color ≤ cost * first color) :
    profileSquareNorm first profile ≤ cost * profileSquareNorm second profile := by
  unfold profileSquareNorm
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro color _
  apply (div_le_iff₀ (hfirst color)).mpr
  have hd := hsecond color
  have hh := mul_le_mul_of_nonneg_left (hcompare color)
    (show 0 ≤ profile color ^ 2 / second color by positivity)
  calc
    _ = (profile color ^ 2 / second color) * second color := by field_simp
    _ ≤ _ := hh
    _ = _ := by ring

/-- Centering a genuine probability family about its own mean costs at
most four times a common comparison profile's squared energy. -/
theorem centeredFamily_profile_energy_le {Source Color : Type*} [Fintype Source] [Fintype Color]
    (source : FiniteDist Source) (reference comparison : Color → ℝ)
    (family : Source → Color → ℝ) (budget : ℝ)
    (href : ∀ color, 0 ≤ reference color)
    (hfamily : ∀ point, profileSquareNorm reference (family point - comparison) ≤ budget)
    (point : Source) :
    profileSquareNorm reference (fun color => family point color - ∑ other, source.weight other * family other color) ≤
      4 * budget := by
  have hmean := profileSquareNorm_average_le source reference href (fun other => family other - comparison)
  have hmeanBound : profileSquareNorm reference
      (fun color => ∑ other, source.weight other * (family other - comparison) color) ≤ budget := by
    apply hmean.trans
    calc
      _ ≤ ∑ other, source.weight other * budget :=
        Finset.sum_le_sum fun other _ => mul_le_mul_of_nonneg_left (hfamily other) (source.nonneg other)
      _ = budget := by rw [← Finset.sum_mul,source.sum_one,one_mul]
  have heq : (fun color => family point color - ∑ other, source.weight other * family other color) =
      (family point - comparison) - (fun color => ∑ other, source.weight other * (family other - comparison) color) := by
    funext color
    simp only [Pi.sub_apply,mul_sub,Finset.sum_sub_distrib,← Finset.sum_mul,source.sum_one,one_mul]
    ring
  rw [heq]
  exact (profileSquareNorm_sub_le_two reference _ _ href).trans (by linarith [hfamily point])

end
end AFT

namespace AFT.V7Calibration
open GaussianSource Filter
open scoped BigOperators Classical Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- The independent one-root law used by the actual ANOVA decomposition. -/
def bodyRootReference (parameter : ℕ) : FiniteDist (Window (v7RootCutoff parameter)) :=
  rootMarginal (v7RootWidth parameter) (v7RootCutoff parameter) (Parameters.bodies parameter)
    (Parameters.bodies_positive parameter)

/-- This centered channel keeps any fixed leg-source and queue translation.
It uses the true calibrated body and the true clipped root marginal. -/
def centeredRootBodyProfile (cutoffScale : ℝ) (parameter : ℕ) (beta : ℝ)
    (offset : ℤ) (root : Window (v7RootCutoff parameter)) (output : Fin (Parameters.modulus parameter)) : ℝ :=
  (actualShiftedBodyLaw cutoffScale parameter beta (root + offset)).weight output -
    ∑ other, (bodyRootReference parameter).weight other *
      (actualShiftedBodyLaw cutoffScale parameter beta (other + offset)).weight output

theorem centeredRootBodyProfile_root_mean (cutoffScale : ℝ) (parameter : ℕ) (beta : ℝ)
    (offset : ℤ) (output : Fin (Parameters.modulus parameter)) :
    (∑ root, (bodyRootReference parameter).weight root *
      centeredRootBodyProfile cutoffScale parameter beta offset root output) = 0 := by
  simp only [centeredRootBodyProfile,mul_sub,Finset.sum_sub_distrib,← Finset.sum_mul,
    FiniteDist.sum_one,one_mul,sub_self]

theorem centeredRootBodyProfile_mass (cutoffScale : ℝ) (parameter : ℕ) (beta : ℝ)
    (offset : ℤ) (root : Window (v7RootCutoff parameter)) :
    (∑ output, centeredRootBodyProfile cutoffScale parameter beta offset root output) = 0 := by
  simp only [centeredRootBodyProfile,Finset.sum_sub_distrib,FiniteDist.sum_one]
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum,FiniteDist.sum_one,mul_one,sub_self]

/-- Both the Hilbert strip bound and every fixed-output row hold uniformly
in a realized legal leg source, queue value, and root. -/
theorem actual_centered_root_body_strip_eventually (cutoffScale : ℝ) (hscale : 1 ≤ cutoffScale)
    (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ parameter in atTop,
      (Parameters.legs parameter : ℝ)/(2*Parameters.dimension parameter) ≤ beta parameter ∧
      beta parameter ≤ 2*(Parameters.legs parameter : ℝ)/Parameters.dimension parameter) :
    ∀ᶠ parameter in atTop, ∀ offset : ℤ,
    (∀ root : Window (v7RootCutoff parameter), |(root : ℤ)+offset| ≤ maxBodyShift cutoffScale parameter) →
    ∀ root : Window (v7RootCutoff parameter),
    profileSquareNorm (actualPrimaryLaw cutoffScale parameter (beta parameter)).weight
      (centeredRootBodyProfile cutoffScale parameter (beta parameter) offset root) ≤ 175104 / (parameter : ℝ)^38 ∧
    ∀ output, |centeredRootBodyProfile cutoffScale parameter (beta parameter) offset root output /
      (actualPrimaryLaw cutoffScale parameter (beta parameter)).weight output| ≤ 16 := by
  filter_upwards [actual_shifted_body_reference_energy_eventually cutoffScale hscale beta hbeta,
    actual_shifted_body_law_eventually cutoffScale hscale beta hbeta,
    actual_reference_laws_eventually cutoffScale hscale beta hbeta,
    actual_reference_probability_eventually cutoffScale hscale beta hbeta,
    actual_reference_lower_eventually cutoffScale hscale beta hbeta,
    actual_primary_law_quarter_lower_eventually cutoffScale hscale beta hbeta]
    with parameter he hs hl hr hrl hp offset hoff root
  let primary := actualPrimaryLaw cutoffScale parameter (beta parameter)
  let reference := actualReferenceLaw cutoffScale parameter (beta parameter)
  let family := fun point : Window (v7RootCutoff parameter) =>
    (actualShiftedBodyLaw cutoffScale parameter (beta parameter) (point + offset)).weight
  have hq : (0 : ℝ) < Parameters.modulus parameter := Nat.cast_pos.mpr (Parameters.modulus_prime parameter).pos
  have hp0 (color) : 0 < primary.weight color := lt_of_lt_of_le (by positivity) (hp color)
  have hr0 (color) : 0 < reference.weight color := by
    change 0 < (actualReferenceLaw cutoffScale parameter (beta parameter)).weight color
    rw [hl.2.2]
    exact lt_of_lt_of_le (by positivity) (hrl color)
  have hcompare (color) : reference.weight color ≤ 8 * primary.weight color := by
    have hh := (hr.1 color).2
    have hh' := hp color
    change (actualReferenceLaw cutoffScale parameter (beta parameter)).weight color ≤ _
    rw [hl.2.2]
    change _ ≤ 8 * (actualPrimaryLaw cutoffScale parameter (beta parameter)).weight color
    simp only [div_eq_mul_inv,mul_inv_rev] at hh hh'
    norm_num at hh'
    linarith
  have hf (point) : profileSquareNorm primary.weight (family point - reference.weight) ≤ 43776 / (parameter : ℝ)^38 := by
    have hh := profileSquareNorm_reference_domination primary.weight reference.weight
      (family point - reference.weight) 8 hp0 hr0 hcompare
    have ht : profileSquareNorm reference.weight (family point - reference.weight) ≤ 5472 / (parameter : ℝ)^38 := by
      change profileSquareNorm (actualReferenceLaw cutoffScale parameter (beta parameter)).weight
        ((actualShiftedBodyLaw cutoffScale parameter (beta parameter) (point + offset)).weight -
          (actualReferenceLaw cutoffScale parameter (beta parameter)).weight) ≤ _
      rw [(hs _ (hoff point)).1, hl.2.2]
      exact he _ (hoff point)
    exact hh.trans ((mul_le_mul_of_nonneg_left ht (by norm_num : (0 : ℝ) ≤ 8)).trans_eq (by ring))
  constructor
  · exact (centeredFamily_profile_energy_le (bodyRootReference parameter) primary.weight reference.weight family
      (43776 / (parameter : ℝ)^38) primary.nonneg hf root).trans_eq (by ring)
  · intro output
    have hu (point) : family point output ≤ 4 / (Parameters.modulus parameter : ℝ) := (hs _ (hoff point)).2 output
    have hn (point) : 0 ≤ family point output := FiniteDist.nonneg _ _
    have hm0 : 0 ≤ ∑ point, (bodyRootReference parameter).weight point * family point output :=
      Finset.sum_nonneg fun point _ => mul_nonneg (FiniteDist.nonneg _ _) (hn point)
    have hmu : (∑ point, (bodyRootReference parameter).weight point * family point output) ≤ 4 / (Parameters.modulus parameter : ℝ) := by
      calc
        _ ≤ ∑ point, (bodyRootReference parameter).weight point * (4 / (Parameters.modulus parameter : ℝ)) :=
          Finset.sum_le_sum fun point _ => mul_le_mul_of_nonneg_left (hu point) (FiniteDist.nonneg _ _)
        _ = _ := by rw [← Finset.sum_mul,FiniteDist.sum_one,one_mul]
    have hfour : 4 / (Parameters.modulus parameter : ℝ) ≤ 16 * primary.weight output := by
      have hh := hp output
      change _ ≤ 16 * (actualPrimaryLaw cutoffScale parameter (beta parameter)).weight output
      simp only [div_eq_mul_inv,mul_inv_rev] at hh ⊢
      norm_num at hh
      linarith
    change |(family root output - ∑ point, (bodyRootReference parameter).weight point * family point output) / primary.weight output| ≤ 16
    rw [abs_div,abs_of_pos (hp0 output)]
    apply (div_le_iff₀ (hp0 output)).mpr
    apply abs_le.mpr
    constructor <;> linarith [hu root,hn root]

end
end AFT.V7Calibration
