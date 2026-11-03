import AFT.RootBodyStrip

/-! # Literal root-to-output operators with Hilbert and row bounds -/

namespace AFT
open scoped BigOperators Classical
noncomputable section
variable {Source Color : Type*} [Fintype Source] [Fintype Color]

/-- The root tensor is integrated once against the actual centered family. -/
def rootProfileChannel (source : FiniteDist Source) (family : Source → Color → ℝ) :
    (Source → ℝ) →ₗ[ℝ] (Color → ℝ) where
  toFun input color := ∑ point, source.weight point * input point * family point color
  map_add' first second := by
    funext color
    simp only [Pi.add_apply,mul_add,add_mul,Finset.sum_add_distrib]
  map_smul' scalar input := by
    funext color
    simp only [Pi.smul_apply,smul_eq_mul,RingHom.id_apply,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro point _
    ring

omit [Fintype Color] in
theorem rootProfileChannel_square_le (source : FiniteDist Source) (family : Source → Color → ℝ)
    (input : Source → ℝ) (color : Color) :
    rootProfileChannel source family input color ^ 2 ≤
      source.l2Sq input * ∑ point, source.weight point * family point color ^ 2 := by
  change (∑ point, source.weight point * input point * family point color)^2 ≤ _
  unfold FiniteDist.l2Sq
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul
  · intro point _; exact mul_nonneg (source.nonneg point) (sq_nonneg _)
  · intro point _; exact mul_nonneg (source.nonneg point) (sq_nonneg _)
  · intro point _; ring

theorem rootProfileChannel_energy_le (source : FiniteDist Source) (reference : Color → ℝ)
    (family : Source → Color → ℝ) (href : ∀ color, 0 ≤ reference color) (input : Source → ℝ) :
    profileSquareNorm reference (rootProfileChannel source family input) ≤
      (∑ point, source.weight point * profileSquareNorm reference (family point)) * source.l2Sq input := by
  calc
    _ ≤ ∑ color, source.l2Sq input * (∑ point, source.weight point * family point color ^ 2) / reference color :=
      Finset.sum_le_sum fun color _ => div_le_div_of_nonneg_right
        (rootProfileChannel_square_le source family input color) (href color)
    _ = _ := by
      simp only [Finset.mul_sum,Finset.sum_div,profileSquareNorm,Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro point _
      apply Finset.sum_congr rfl
      intro color _
      ring

omit [Fintype Color] in
theorem rootProfileChannel_row_square_le (source : FiniteDist Source) (reference : Color → ℝ)
    (family : Source → Color → ℝ) (input : Source → ℝ) (color : Color) :
    (rootProfileChannel source family input color / reference color)^2 ≤
      ((∑ point, source.weight point * family point color ^ 2) / reference color^2) * source.l2Sq input := by
  rw [div_pow]
  exact (div_le_div_of_nonneg_right (rootProfileChannel_square_le source family input color)
    (sq_nonneg _)).trans_eq (by ring)

theorem rootProfileChannel_mass_zero (source : FiniteDist Source) (family : Source → Color → ℝ)
    (hmass : ∀ point, ∑ color, family point color = 0) (input : Source → ℝ) :
    (∑ color, rootProfileChannel source family input color) = 0 := by
  change (∑ color, ∑ point, source.weight point * input point * family point color) = 0
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum,hmass,mul_zero,Finset.sum_const_zero]

end
end AFT

namespace AFT.V7Calibration
open GaussianSource Filter
open scoped BigOperators Classical Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- The actual body/root response, as a linear map on the entire root input. -/
def actualRootBodyChannel (C : ℝ) (n : ℕ) (beta : ℝ) (offset : ℤ) :
    (Window (v7RootCutoff n) → ℝ) →ₗ[ℝ] (Fin (Parameters.modulus n) → ℝ) :=
  rootProfileChannel (bodyRootReference n) (centeredRootBodyProfile C n beta offset)

theorem actual_root_body_channel_strip_eventually (C : ℝ) (hC : 1 ≤ C)
    (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ n in atTop, (Parameters.legs n : ℝ)/(2*Parameters.dimension n) ≤ beta n ∧
      beta n ≤ 2*(Parameters.legs n : ℝ)/Parameters.dimension n) :
    ∀ᶠ n in atTop, ∀ offset : ℤ,
    (∀ root : Window (v7RootCutoff n), |(root : ℤ)+offset| ≤ maxBodyShift C n) →
    ∀ input : Window (v7RootCutoff n) → ℝ,
      profileSquareNorm (actualPrimaryLaw C n (beta n)).weight (actualRootBodyChannel C n (beta n) offset input) ≤
        (175104 / (n : ℝ)^38) * (bodyRootReference n).l2Sq input ∧
      (∀ color, (actualRootBodyChannel C n (beta n) offset input color / (actualPrimaryLaw C n (beta n)).weight color)^2 ≤
        256 * (bodyRootReference n).l2Sq input) ∧
      (∑ color, actualRootBodyChannel C n (beta n) offset input color) = 0 := by
  filter_upwards [actual_centered_root_body_strip_eventually C hC beta hbeta]
    with n hb offset hoff input
  have hE : 0 ≤ (bodyRootReference n).l2Sq input := by
    unfold FiniteDist.l2Sq
    exact Finset.sum_nonneg fun point _ => mul_nonneg (FiniteDist.nonneg _ _) (sq_nonneg _)
  refine ⟨?_,?_,rootProfileChannel_mass_zero _ _ (centeredRootBodyProfile_mass C n (beta n) offset) input⟩
  · apply (rootProfileChannel_energy_le (bodyRootReference n) (actualPrimaryLaw C n (beta n)).weight
      (centeredRootBodyProfile C n (beta n) offset) (FiniteDist.nonneg _) input).trans
    apply mul_le_mul_of_nonneg_right _ hE
    calc
      _ ≤ ∑ point, (bodyRootReference n).weight point * (175104 / (n : ℝ)^38) :=
        Finset.sum_le_sum fun point _ => mul_le_mul_of_nonneg_left (hb offset hoff point).1 (FiniteDist.nonneg _ _)
      _ = _ := by rw [← Finset.sum_mul,FiniteDist.sum_one,one_mul]
  · intro color
    apply (rootProfileChannel_row_square_le (bodyRootReference n) (actualPrimaryLaw C n (beta n)).weight
      (centeredRootBodyProfile C n (beta n) offset) input color).trans
    apply mul_le_mul_of_nonneg_right _ hE
    rw [Finset.sum_div]
    calc
      _ = ∑ point, (bodyRootReference n).weight point *
          (centeredRootBodyProfile C n (beta n) offset point color / (actualPrimaryLaw C n (beta n)).weight color)^2 := by
        apply Finset.sum_congr rfl
        intro point _
        rw [div_pow]
        ring
      _ ≤ ∑ point, (bodyRootReference n).weight point * 256 := by
        apply Finset.sum_le_sum
        intro point _
        apply mul_le_mul_of_nonneg_left _ (FiniteDist.nonneg _ _)
        have hh := (sq_le_sq₀ (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 16)).mpr ((hb offset hoff point).2 color)
        norm_num only [sq_abs] at hh
        exact hh
      _ = _ := by rw [← Finset.sum_mul,FiniteDist.sum_one,one_mul]

end
end AFT.V7Calibration
