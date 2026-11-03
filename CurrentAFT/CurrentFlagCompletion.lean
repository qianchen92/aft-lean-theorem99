import CurrentAFT.AffineLegCompletion

/-! # The actual public completion law is the canonical rational ideal -/

namespace CurrentAFT.CurrentFlagCompletion

open AFT AffineFlagCalibration ActualPublicLegCharge
open scoped BigOperators Classical
noncomputable section

local instance completionTablePrime (security : ℕ) : Fact (Parameters.modulus security).Prime :=
  ⟨(Parameters.modulus_spec security).2⟩

def model (security : ℕ) (primary : AffineFlagCalibration.Palette security) (seed : PublicSeed security) :=
  CurrentFlagProgram.current security (publicShift security primary seed)
    (by simpa only [legOffsetBound, add_sub_assoc] using publicShift_bound security primary seed)
    ((ZMod.finEquiv (Parameters.modulus security)) primary) (1 / 2 : ℚ) (by norm_num) (by norm_num)

def table (security : ℕ) (primary : AffineFlagCalibration.Palette security) (seed : PublicSeed security) :
    Bool × BoundaryCalibration.Chart (ZMod (Parameters.modulus security)) → ℚ :=
  (model security primary seed).table

theorem completionLaw_eq (security : ℕ) (primary : AffineFlagCalibration.Palette security)
    (seed : PublicSeed security) :
    completionLaw security primary seed = (model security primary seed).model.joint := by
  have hm := currentLaw_rat security (publicShift security primary seed)
    (by simpa only [legOffsetBound, add_sub_assoc] using publicShift_bound security primary seed)
    ((ZMod.finEquiv (Parameters.modulus security)) primary) (1 / 2 : ℚ) (by norm_num) (by norm_num)
  convert congrArg (fun law => law.joint) hm using 1
  norm_num [completionLaw, model]
  congr 2 <;> norm_num

theorem table_cast (security : ℕ) (primary : AffineFlagCalibration.Palette security)
    (seed : PublicSeed security) (point : Bool × BoundaryCalibration.Chart (ZMod (Parameters.modulus security))) :
    (table security primary seed point : ℝ) = (completionLaw security primary seed).weight point := by
  rw [completionLaw_eq]
  exact (model security primary seed).table_cast point

theorem table_nonneg (security : ℕ) (primary : AffineFlagCalibration.Palette security)
    (seed : PublicSeed security) (point : Bool × BoundaryCalibration.Chart (ZMod (Parameters.modulus security))) :
    0 ≤ table security primary seed point := (model security primary seed).table_nonneg point

theorem table_mass (security : ℕ) (primary : AffineFlagCalibration.Palette security)
    (seed : PublicSeed security) :
    ∑ point, table security primary seed point = 1 := (model security primary seed).table_mass

end
end CurrentAFT.CurrentFlagCompletion
