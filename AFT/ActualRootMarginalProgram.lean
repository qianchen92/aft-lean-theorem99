import AFT.ActualRootTicketConvolution
import AFT.ActualRootTicketRejection
import AFT.RootMarginalStability
import AFT.ActualRootSamplerProgram

/-! # Executable rational queries for the actual one-root marginal -/
namespace AFT.V7Calibration
open GaussianSource RationalNumerics FiniteConvolutionProgram FiniteDist
open scoped BigOperators

/-- Both convolution entries and the scalar ticket mass are computed exactly
as rationals. The denominator is one full-root normalizer. -/
def actualRootTicketMarginal (n count : ℕ) (point : Window (3*n^2-1)) : ℚ :=
  (actualRootTicketCounts n n ((windowIndexEquiv _).symm point) : ℚ)/(2 : ℚ)^(actualRootTicketBits n n)*
    actualRootTicketProbability n (count-1) (-(point : ℤ))/actualRootTicketProbability n count 0

/-- The actual population is obtained by the proved bounded prime program. -/
def actualRootMarginalProgram (n : ℕ) (point : Window (3*n^2-1)) : ℚ :=
  actualRootTicketMarginal n (actualRootPopulationProgram n) point

noncomputable section
open scoped Classical Topology
set_option backward.isDefEq.respectTransparency false
local instance actualRootMarginalProgramFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _

theorem actualRootTicketMarginal_exact (n count : ℕ) (hc : 0 < count)
    (hpos : 0 < RootSlice.sumProbability (actualRootTicketLaw n n) (fun point => (point : ℤ)) count 0)
    (point : Window (v7RootCutoff n)) :
    (actualRootTicketMarginal n count point : ℝ)=
      (RootSlice.marginalLaw (actualRootTicketLaw n n) (fun point => (point : ℤ)) count hc hpos).weight point := by
  rw [RootSlice.marginalLaw_weight,actualRootTicketLaw_weight]
  unfold actualRootTicketMarginal
  push_cast
  rw [actualRootTicketProbability_exact,actualRootTicketProbability_exact]

def actualRootMarginalError (n : ℕ) : ℝ := 4*(n : ℝ)^92/(2 : ℝ)^n

theorem actualRootMarginalError_negligible : Negligible actualRootMarginalError := by
  have hm : Negligible (fun n : ℕ => 1/(2 : ℝ)^n) := by
    convert betaGridMesh_negligible using 1
    funext n
    simp only [betaGridMesh,Nat.cast_pow,Nat.cast_ofNat]
  convert (hm.mul_polynomial 92).const_mul 4 using 1
  funext n
  unfold actualRootMarginalError
  ring

/-- No supplied approximator or inverse marginal-atom bound remains: every
actual one-root probability is returned within this negligible error. -/
theorem actual_root_marginal_program_eventually :
    ∀ᶠ n : ℕ in Filter.atTop,
      ∀ point : Window (v7RootCutoff n),
        |(actualRootMarginalProgram n point : ℝ)-
          (rootMarginal (v7RootWidth n) (v7RootCutoff n) (Parameters.bodies n)
            (Parameters.bodies_positive n)).weight point| ≤ actualRootMarginalError n := by
  filter_upwards [actual_root_ticket_acceptance_eventually,Filter.eventually_ge_atTop 2] with n ha hn point
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hpos : 0 < RootSlice.sumProbability (actualRootTicketLaw n n) (fun point => (point : ℤ)) (Parameters.bodies n) 0 :=
    (by positivity : (0 : ℝ) < 1/(n : ℝ)^32).trans_le ha
  have hh := RootSlice.marginalLaw_point_error (actualRootTicketLaw n n)
    (windowGaussian (v7RootWidth n) (v7RootCutoff n)) (fun point => (point : ℤ))
    (Parameters.bodies n) (Parameters.bodies_positive n) hpos (window_root_probability_positive _ _ _)
    (1/(2 : ℝ)^n) (actualRootTicketLaw_l1 n n (by omega)) point
  unfold actualRootMarginalProgram
  rw [actualRootPopulationProgram_eq,actualRootTicketMarginal_exact n _ (Parameters.bodies_positive n) hpos]
  apply hh.trans
  have hN : (Parameters.bodies n : ℝ) ≤ 2*(n : ℝ)^60 := by
    exact_mod_cast (show Parameters.bodies n ≤ 2*n^60 from
      (Nat.sub_le _ _).trans (by simpa only [Parameters.security_eq n hn] using (Parameters.dimension_bounds n).2))
  calc
    _ ≤ 2*(Parameters.bodies n : ℝ)*(1/(2 : ℝ)^n)/(1/(n : ℝ)^32) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) ha
    _ ≤ 2*(2*(n : ℝ)^60)*(1/(2 : ℝ)^n)/(1/(n : ℝ)^32) := by gcongr
    _ = _ := by unfold actualRootMarginalError; rw [show (n : ℝ)^92=(n : ℝ)^60*(n : ℝ)^32 by rw [← pow_add]]; field_simp; ring

end
end AFT.V7Calibration
