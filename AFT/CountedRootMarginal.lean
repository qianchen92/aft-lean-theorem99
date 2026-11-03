import AFT.CountedWindowQuery
import AFT.ActualPrimaryProgramHeight

/-! # Actual root-marginal queries with cached ticket and convolution arrays -/
namespace AFT.V7Calibration
open GaussianSource RationalNumerics FiniteConvolutionProgram
open scoped BigOperators

/-- The scalar table is evaluated once before either dynamic program. -/
def countedRootTicketMarginal (n count : ℕ) (point : Window (3*n^2-1)) : GaussianArithmetic :=
  let tickets := countedWindowTickets (actualRootSquaredWidth n) (3*n^2-1) n
  let scalarDen := GaussianArithmetic.power 2 (actualRootTicketBits n n)
  let remaining := run (2*(3*n^2-1)) tickets.value.get (count-1)
  let full := run (2*(3*n^2-1)) tickets.value.get count
  let remainingDen := GaussianArithmetic.power 2 (actualRootTicketBits n n*(count-1))
  let fullDen := GaussianArithmetic.power 2 (actualRootTicketBits n n*count)
  let scalar := (tickets.value.get ((windowIndexEquiv _).symm point) : ℚ)/scalarDen.value
  let remainProbability := ((integerLookup remaining.data ((3*n^2-1)*(count-1)) (-(point : ℤ)) : ℕ) : ℚ)/remainingDen.value
  let fullProbability := ((integerLookup full.data ((3*n^2-1)*count) 0 : ℕ) : ℚ)/fullDen.value
  ⟨scalar*remainProbability/fullProbability,
    tickets.work+scalarDen.work+remaining.work+full.work+remainingDen.work+fullDen.work+20⟩

theorem countedRootTicketMarginal_value (n count : ℕ) (point : Window (3*n^2-1)) :
    (countedRootTicketMarginal n count point).value=actualRootTicketMarginal n count point := by
  have he : (countedWindowTickets (actualRootSquaredWidth n) (3*n^2-1) n).value.get=
      actualRootTicketCounts n n := by
    funext index
    rw [countedWindowTickets_value]
    rfl
  simp only [countedRootTicketMarginal,he,GaussianArithmetic.power_value,
    actualRootTicketMarginal,actualRootTicketProbability,actualRootTicketConvolution,actualRootIntegerConvolution]

def rootMarginalQueryWork (n : ℕ) : ℕ :=
  windowQueryWork (3*n^2) n+2550*n^124+32*n^62+8*n^2+20

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000

theorem windowQueryWork_mono {first second bits precision : ℕ} (hc : first≤second) (hb : bits≤precision) :
    windowQueryWork first bits≤windowQueryWork second precision := by
  unfold windowQueryWork windowTicketBits
  gcongr

theorem countedRootTicketMarginal_work (n count : ℕ) (hn : 2≤n)
    (hcount : count≤actualRootPopulationProgram n) (point : Window (3*n^2-1)) :
    (countedRootTicketMarginal n count point).work≤rootMarginalQueryWork n := by
  have hw : (1 : ℚ)≤actualRootSquaredWidth n := by
    have hnq : (2 : ℚ)≤n := by exact_mod_cast hn
    unfold actualRootSquaredWidth
    nlinarith
  have hweights := countedWindowTicketWeight_work (actualRootSquaredWidth n) (3*n^2-1) n hw point
  simp only [countedWindowTicketWeight,GaussianArithmetic.power_work] at hweights
  have he : (countedWindowTickets (actualRootSquaredWidth n) (3*n^2-1) n).value.get=
      actualRootTicketCounts n n := by
    funext index
    rw [countedWindowTickets_value]
    rfl
  have hc : count≤Parameters.bodies n := by simpa only [actualRootPopulationProgram_eq] using hcount
  have hf := (actualRootTicketConvolution_bounds n count 0 hn hc).2.1
  have hr := (actualRootTicketConvolution_bounds n (count-1) 0 hn ((Nat.sub_le _ _).trans hc)).2.1
  change (run (2*(3*n^2-1)) (actualRootTicketCounts n n) count).work≤_ at hf
  change (run (2*(3*n^2-1)) (actualRootTicketCounts n n) (count-1)).work≤_ at hr
  have hb := actualRootTicketBits_bound n hn
  have hc' := hcount.trans (actual_root_population_program_le n hn)
  have hprod : actualRootTicketBits n n*count≤16*n^62 := by
    calc
      _ ≤ (8*n^2)*(2*n^60) := by gcongr
      _ = _ := by ring
  have hprod' : actualRootTicketBits n n*(count-1)≤16*n^62 :=
    (Nat.mul_le_mul_left _ (Nat.sub_le _ _)).trans hprod
  have hm := windowQueryWork_mono (Nat.sub_le (3*n^2) 1) (le_refl n)
  simp only [countedRootTicketMarginal,he,GaussianArithmetic.power_work]
  unfold rootMarginalQueryWork
  omega

end
end AFT.V7Calibration
