import AFT.MatrixPrimaryActivity

/-! # Stable rational preconditioned iteration, retaining the true target -/
namespace AFT
open scoped BigOperators
noncomputable section

variable {Color : Type*} [Fintype Color]

theorem primaryActivity_operator_perturbation
    (primary : Color → ℝ) (rate bound error : ℝ)
    (actual approximate : Module.End ℝ (Color → ℝ))
    (hrate : 0≤rate) (hp : ∀ color,0<primary color)
    (hactual : ∀profile,primaryActivity rate primary (actual profile)≤bound*primaryActivity rate primary profile)
    (herror : ∀profile,primaryActivity rate primary (approximate profile-actual profile)≤error*primaryActivity rate primary profile)
    (profile : Color → ℝ) :
    primaryActivity rate primary (approximate profile)≤(bound+error)*primaryActivity rate primary profile := by
  have hid : approximate profile=actual profile+(approximate profile-actual profile) := by abel
  rw [hid]
  exact (primaryActivity_add_le _ _ _ _ hrate hp).trans ((add_le_add (hactual profile) (herror profile)).trans_eq (by ring))

theorem primaryActivity_composition_perturbation
    (primary : Color → ℝ) (rate rankBound errorBound rankError errorError : ℝ)
    (rank error rankApprox errorApprox : Module.End ℝ (Color → ℝ))
    (hrate : 0≤rate) (hp : ∀ color,0<primary color) (hrankError : 0≤rankError)
    (hrank : ∀profile,primaryActivity rate primary (rank profile)≤rankBound*primaryActivity rate primary profile)
    (herror : ∀profile,primaryActivity rate primary (error profile)≤errorBound*primaryActivity rate primary profile)
    (hrankDiff : ∀profile,primaryActivity rate primary (rankApprox profile-rank profile)≤rankError*primaryActivity rate primary profile)
    (herrorDiff : ∀profile,primaryActivity rate primary (errorApprox profile-error profile)≤errorError*primaryActivity rate primary profile)
    (profile : Color → ℝ) :
    primaryActivity rate primary (rankApprox (errorApprox profile)-rank (error profile))≤
      (rankError*(errorBound+errorError)+rankBound*errorError)*primaryActivity rate primary profile := by
  have hid : rankApprox (errorApprox profile)-rank (error profile)=
      (rankApprox (errorApprox profile)-rank (errorApprox profile))+rank (errorApprox profile-error profile) := by
    rw [map_sub]
    abel
  rw [hid]
  apply (primaryActivity_add_le _ _ _ _ hrate hp).trans
  apply (add_le_add (hrankDiff _) (hrank _)).trans
  have hb := primaryActivity_operator_perturbation primary rate errorBound errorError error errorApprox hrate hp herror herrorDiff profile
  have h1 := mul_le_mul_of_nonneg_left hb hrankError
  have hrankNonneg : 0≤rankBound ∨ ∀ f,primaryActivity rate primary f=0 := by
    by_cases h : 0≤rankBound
    · exact Or.inl h
    · right
      intro f
      have hfa := primaryActivity_nonneg rate primary f hrate
      have hfb := primaryActivity_nonneg rate primary (rank f) hrate
      have h := hrank f
      nlinarith
  rcases hrankNonneg with hrankNonneg | hzero
  · have h2 := mul_le_mul_of_nonneg_left (herrorDiff profile) hrankNonneg
    nlinarith only [h1,h2]
  · simp only [hzero,mul_zero,add_zero,le_refl]

/-- The true inverse satisfies an approximate preconditioned equation.
All perturbations are measured once; iteration does not amplify them. -/
theorem preconditioned_residual_bound
    (primary : Color → ℝ) (rate rankBound errorBound rankError errorError inverseBound : ℝ)
    (rank error rankApprox errorApprox : Module.End ℝ (Color → ℝ))
    (target solution : Color → ℝ)
    (hrate : 0≤rate) (hp : ∀ color,0<primary color)
    (hrankError : 0≤rankError) (hcombined : 0≤rankError*(errorBound+errorError)+rankBound*errorError)
    (hrank : ∀profile,primaryActivity rate primary (rank profile)≤rankBound*primaryActivity rate primary profile)
    (herror : ∀profile,primaryActivity rate primary (error profile)≤errorBound*primaryActivity rate primary profile)
    (hrankDiff : ∀profile,primaryActivity rate primary (rankApprox profile-rank profile)≤rankError*primaryActivity rate primary profile)
    (herrorDiff : ∀profile,primaryActivity rate primary (errorApprox profile-error profile)≤errorError*primaryActivity rate primary profile)
    (hsolution : rank target-rank (error solution)=solution)
    (hbound : primaryActivity rate primary solution ≤ inverseBound*primaryActivity rate primary target) :
    primaryActivity rate primary (rankApprox target-rankApprox (errorApprox solution)-solution)≤
      (rankError+inverseBound*(rankError*(errorBound+errorError)+rankBound*errorError))*primaryActivity rate primary target := by
  have hid : rankApprox target-rankApprox (errorApprox solution)-solution=
      (rankApprox target-rank target)+-(rankApprox (errorApprox solution)-rank (error solution)) := by
    conv_lhs => rhs; rw [←hsolution]
    abel
  rw [hid]
  apply (primaryActivity_add_le _ _ _ _ hrate hp).trans
  rw [primaryActivity_neg]
  apply (add_le_add (hrankDiff _) (primaryActivity_composition_perturbation primary rate
    rankBound errorBound rankError errorError rank error rankApprox errorApprox hrate hp hrankError
      hrank herror hrankDiff herrorDiff solution)).trans
  have hh := mul_le_mul_of_nonneg_left hbound hcombined
  nlinarith only [hh]

end
end AFT
