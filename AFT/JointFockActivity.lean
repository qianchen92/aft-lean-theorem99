import AFT.JointPhysicalFock
import AFT.MixedKernel

/-! # The full mixed activity controls the actual joint Fock input energy -/
namespace AFT.JointPhysicalChannel
open scoped BigOperators Classical
noncomputable section
variable {Slot Color : Type*} [Fintype Slot] [Fintype Color]

/-- The integrated Hilbert tensor is one of the actual mixed activity's
fibers. Squaring retains the complete product of inverse pool sizes. -/
theorem integrated_energy_le_activity_square (rate : Slot → ℝ) (reference : Slot → FiniteDist Color)
    (kernel : (Slot → Color) → ℝ) (hrate : ∀ slot, 0 ≤ rate slot) :
    (∏ slot, rate slot ^ 2) * (FiniteDist.independent reference).l2Sq kernel ≤
      MixedKernel.activity rate reference kernel ^ 2 := by
  have hh := MixedKernel.integrated_norm_le_activity rate reference kernel hrate
  have hleft : 0 ≤ (∏ slot, rate slot) * Real.sqrt ((FiniteDist.independent reference).l2Sq kernel) :=
    mul_nonneg (Finset.prod_nonneg fun slot _ => hrate slot) (Real.sqrt_nonneg _)
  have hr := (sq_le_sq₀ hleft (hleft.trans hh)).mpr hh
  simpa only [mul_pow, Finset.prod_pow, Real.sq_sqrt (FiniteDist.l2Sq_nonneg _ _)] using hr

/-- Replacing local operator rates by their explicit pool-rate bounds costs
only their scalar factors; arbitrary fixed and integrated fibers stay in the
same mixed activity, without introducing a palette factor. -/
theorem product_energy_le_activity_square (rate factor bound : Slot → ℝ)
    (reference : Slot → FiniteDist Color) (kernel : (Slot → Color) → ℝ)
    (hrate : ∀ slot, 0 ≤ rate slot) (_hfactor : ∀ slot, 0 ≤ factor slot)
    (hbound0 : ∀ slot, 0 ≤ bound slot) (hbound : ∀ slot, bound slot ≤ factor slot * rate slot) :
    (∏ slot, bound slot ^ 2) * (FiniteDist.independent reference).l2Sq kernel ≤
      (∏ slot, factor slot ^ 2) * MixedKernel.activity rate reference kernel ^ 2 := by
  have hp : (∏ slot, bound slot ^ 2) ≤ ∏ slot, (factor slot * rate slot) ^ 2 :=
    Finset.prod_le_prod (fun slot _ => sq_nonneg _) (fun slot _ =>
      pow_le_pow_left₀ (hbound0 slot) (hbound slot) 2)
  simp only [mul_pow, Finset.prod_mul_distrib] at hp
  apply (mul_le_mul_of_nonneg_right hp (FiniteDist.l2Sq_nonneg _ _)).trans
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left (integrated_energy_le_activity_square rate reference kernel hrate)
    (Finset.prod_nonneg fun slot _ => sq_nonneg _)

end
end AFT.JointPhysicalChannel
