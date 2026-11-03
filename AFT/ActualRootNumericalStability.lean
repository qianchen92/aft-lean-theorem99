import AFT.RootConvolutionStability
import AFT.RootProbabilityParameters
import AFT.BetaGridParameters

/-! # Polynomial numerical precision suffices for the actual conditioned root law -/
namespace AFT.V7Calibration
open GaussianSource Filter FiniteDist
open scoped BigOperators Classical Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
local instance actualRootNumericalFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _

def actualRootNumericalError (n : ℕ) : ℝ := 64*Real.exp 2*(n : ℝ)^91/(2 : ℝ)^n

theorem actualRootNumericalError_negligible : Negligible actualRootNumericalError := by
  have hm : Negligible (fun n : ℕ => 1/(2 : ℝ)^n) := by
    convert betaGridMesh_negligible using 1
    funext n
    simp only [betaGridMesh,Nat.cast_pow,Nat.cast_ofNat]
  convert (hm.mul_polynomial 91).const_mul (64*Real.exp 2) using 1
  funext n
  unfold actualRootNumericalError
  ring

/-- Approximation of the true clipped scalar Gaussian in L1 is enough.
The complete zero-sum root law incurs only a polynomial precision loss;
there is never division by an exponentially small one-root probability. -/
theorem actual_root_numerical_conditioning_eventually :
    ∀ᶠ n : ℕ in atTop,
      ∀ approximate : FiniteDist (Window (v7RootCutoff n)),
      (∑ point,|approximate.weight point-(windowGaussian (v7RootWidth n) (v7RootCutoff n)).weight point|) ≤
        1/(2 : ℝ)^n →
      ∃ hpos : 0 < RootSlice.sumProbability approximate (fun point => (point : ℤ)) (Parameters.bodies n) 0,
        TVBound (RootSlice.law (fun _ : Fin (Parameters.bodies n) => approximate) (fun point => (point : ℤ)) 0 hpos)
          (RootSlice.law (fun _ : Fin (Parameters.bodies n) => windowGaussian (v7RootWidth n) (v7RootCutoff n))
            (fun point => (point : ℤ)) 0 (window_root_probability_positive _ _ _))
          (actualRootNumericalError n) := by
  have hsmall := actualRootNumericalError_negligible.tendsto_zero.eventually
    (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num))
  filter_upwards [v7_rootProbability_order,hsmall,eventually_ge_atTop 2] with n hp hs hn approximate ha
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hN : (Parameters.bodies n : ℝ) ≤ 2*(n : ℝ)^60 := by
    exact_mod_cast (show Parameters.bodies n ≤ 2*n^60 from
      (Nat.sub_le _ _).trans (by simpa only [Parameters.security_eq n hn] using (Parameters.dimension_bounds n).2))
  let lower : ℝ := 1/(8*Real.exp 2*(n : ℝ)^31)
  let error : ℝ := 1/(2 : ℝ)^n
  have hlower : 0 < lower := by dsimp [lower]; positivity
  have hevent : lower ≤ RootSlice.sumProbability (windowGaussian (v7RootWidth n) (v7RootCutoff n))
      (fun point => (point : ℤ)) (Parameters.bodies n) 0 := hp.1
  have hbound : 4*((Parameters.bodies n : ℝ)*error)/lower ≤ actualRootNumericalError n := by
    calc
      _ ≤ 4*((2*(n : ℝ)^60)*error)/lower := by gcongr
      _ = _ := by
        dsimp [lower,error,actualRootNumericalError]
        rw [show (n : ℝ)^91=(n : ℝ)^60*(n : ℝ)^31 by rw [← pow_add]]
        field_simp
        ring
  have hc : 2*((Parameters.bodies n : ℝ)*error) ≤ lower/2 := by
    have hh := (div_le_one hlower).mp (hbound.trans hs.le)
    linarith
  obtain ⟨hpos,hclose⟩ := RootSlice.conditioned_root_l1_error approximate
    (windowGaussian (v7RootWidth n) (v7RootCutoff n)) (fun point => (point : ℤ))
    (Parameters.bodies n) 0 error lower ha hlower hevent hc
  exact ⟨hpos,hclose.mono hbound⟩

end
end AFT.V7Calibration
