import CurrentAFT.AffineLegCompletion
import CurrentAFT.AffineLegSupport

/-! # Exact paired integer carries of the actual public chart law -/
namespace CurrentAFT.CurrentAffineLegCarry
open AFT AFT.BoundaryCalibration AffineFlagCalibration ActualPublicLegCharge
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

local instance modulusPrime (security : ℕ) : Fact (Parameters.modulus security).Prime :=
  ⟨(Parameters.modulus_spec security).2⟩

abbrev PublicChart (security : ℕ) := Bool × Chart (ZMod (Parameters.modulus security))

def integerPrimary (security : ℕ) (chart : PublicChart security) (first second : ℤ) : ℤ :=
  (chart.2.1.val : ℤ) + (chart.2.2.1.val : ℤ) * first + (chart.2.2.2.val : ℤ) * second

def integerCompanion (security : ℕ) (shift : ℤ) (chart : PublicChart security)
    (first second : ℤ) : ℤ :=
  (Parameters.modulus security : ℤ) - 1 + shift - second - integerPrimary security chart first second

theorem finEquiv_symm_val (modulus : ℕ) [NeZero modulus] (value : ZMod modulus) :
    ((ZMod.finEquiv modulus).symm value).val = value.val := by
  cases modulus with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ modulus => rfl

theorem integerPrimary_cast (security : ℕ) (chart : PublicChart security) (first second : ℤ) :
    (integerPrimary security chart first second : ZMod (Parameters.modulus security)) =
      feature (first : ZMod (Parameters.modulus security)) (second : ZMod (Parameters.modulus security)) chart.2 := by
  simp [integerPrimary, feature]

theorem evaluatePrimary_value (security : ℕ) (chart : PublicChart security)
    (first second : AffineFlagCalibration.Scalar security) :
    ((evaluatePrimary security chart first second).val : ℤ) =
      integerPrimary security chart first.val second.val % Parameters.modulus security := by
  rw [← ZMod.val_intCast, integerPrimary_cast]
  exact congrArg (fun value : ℕ => (value : ℤ)) (finEquiv_symm_val _ _)

theorem companion_value (security : ℕ) (shift : ℤ) (chart : PublicChart security)
    (first second : AffineFlagCalibration.Scalar security) :
    ((companion security (shift - second.val) (evaluatePrimary security chart first second)).val : ℤ) =
      integerCompanion security shift chart first.val second.val % Parameters.modulus security := by
  rw [← ZMod.val_intCast]
  unfold integerCompanion
  push_cast
  rw [ZMod.natCast_self, zero_sub, integerPrimary_cast]
  change (((ZMod.finEquiv (Parameters.modulus security)).symm
    (-1 + ((shift - second.val : ℤ) : ZMod (Parameters.modulus security)) -
      (ZMod.finEquiv (Parameters.modulus security))
        ((ZMod.finEquiv (Parameters.modulus security)).symm
          (feature ((first.val : ℤ) : ZMod (Parameters.modulus security))
            ((second.val : ℤ) : ZMod (Parameters.modulus security)) chart.2)))).val : ℤ) = _
  rw [RingEquiv.apply_symm_apply, finEquiv_symm_val]
  push_cast
  congr 2
  ring

theorem trimmed_pair_charge (security : ℕ) (shift : ℤ) (color : AffineFlagCalibration.Palette security)
    (hcolor : (color.val : ℤ) ∈ TrimmedSlice.slice (Parameters.modulus security) 1 shift) :
    (color.val : ℤ) + (companion security shift color).val =
      (Parameters.modulus security : ℤ) - 1 + shift := by
  have h := (companion_trimmed_iff security shift color (companion security shift color) hcolor).mp rfl
  omega

/-- Every supported chart satisfies the correct integer pair sum at every
protected input.  The public chart is fixed before either input is chosen. -/
theorem supported_pair_charge (security : ℕ) (primary : AffineFlagCalibration.Palette security)
    (seed : PublicSeed security) (chart : PublicChart security)
    (hchart : (completionLaw security primary seed).weight chart ≠ 0)
    (first second : AffineFlagCalibration.Scalar security) :
    ((evaluatePrimary security chart first second).val : ℤ) +
      (companion security (publicShift security primary seed - second.val)
        (evaluatePrimary security chart first second)).val =
      (Parameters.modulus security : ℤ) - 1 + publicShift security primary seed - second.val := by
  let input : ProtectedInput security := (first, second)
  let model := currentLaw security (publicShift security primary seed)
    (by simpa only [legOffsetBound, add_sub_assoc] using publicShift_bound security primary seed)
    ((ZMod.finEquiv (Parameters.modulus security)) primary) (1 / 2) (by norm_num) (by norm_num)
  have hsupport : model.joint.weight chart ≠ 0 := hchart
  have htrimmed (hallowed : feature
      (protectedInputs (Parameters.sourceCutoff security - 1) (Parameters.modulus security) input).1
      (protectedInputs (Parameters.sourceCutoff security - 1) (Parameters.modulus security) input).2 chart.2 ∈
        protectedPalettes (Parameters.sourceCutoff security - 1) (Parameters.modulus security) 1
          (publicShift security primary seed) input) :
      ((evaluatePrimary security chart first second).val : ℤ) ∈
        TrimmedSlice.slice (Parameters.modulus security) 1 (publicShift security primary seed - second.val) := by
    simpa only [protectedPalettes, fieldPalette, Finset.mem_map_equiv, protectedInputs, input,
      TrimmedSlice.paletteSlice, Finset.mem_filter, Finset.mem_univ, true_and, evaluatePrimary] using hallowed
  have hfinish (hallowed : feature
      (protectedInputs (Parameters.sourceCutoff security - 1) (Parameters.modulus security) input).1
      (protectedInputs (Parameters.sourceCutoff security - 1) (Parameters.modulus security) input).2 chart.2 ∈
        protectedPalettes (Parameters.sourceCutoff security - 1) (Parameters.modulus security) 1
          (publicShift security primary seed) input) := trimmed_pair_charge security
            (publicShift security primary seed - second.val) _ (htrimmed hallowed)
  rcases chart with ⟨flag, chart⟩
  cases flag
  · have h := hfinish ((model.regular_of_supported chart hsupport).2 input)
    omega
  · by_cases hfirst : first.val = 0
    · have hon := model.marked_on_line chart hsupport input
        ((protected_first_cast_eq_zero_iff security input).mpr hfirst)
      have heval : evaluatePrimary security (true, chart) first second = primary := by
        unfold evaluatePrimary
        change (ZMod.finEquiv (Parameters.modulus security)).symm
          (feature (protectedInputs _ _ input).1 (protectedInputs _ _ input).2 chart) = primary
        rw [hon, RingEquiv.symm_apply_apply]
      rw [heval]
      have hp := pairProjection_mark security primary second seed
      have hc := markedLaw_charge security primary second seed
        (primary, markedPoint security primary second seed) (by rw [markedLaw_weight]; simp)
      have he := congrArg Prod.snd hp
      change companion security (publicShift security primary seed - second.val) primary = _ at he
      rw [he]
      exact hc
    · have h := hfinish (model.supported_off_line (true, chart) hsupport input
        (fun hz => hfirst ((protected_first_cast_eq_zero_iff security input).mp hz)))
      omega

theorem paired_carry_zero (security : ℕ) (primary : AffineFlagCalibration.Palette security)
    (seed : PublicSeed security) (chart : PublicChart security)
    (hchart : (completionLaw security primary seed).weight chart ≠ 0)
    (first second : AffineFlagCalibration.Scalar security) :
    integerPrimary security chart first.val second.val / Parameters.modulus security +
      integerCompanion security (publicShift security primary seed) chart first.val second.val /
        Parameters.modulus security = 0 := by
  have hsum := supported_pair_charge security primary seed chart hchart first second
  rw [evaluatePrimary_value, companion_value] at hsum
  have hfirst := Int.emod_add_mul_ediv (integerPrimary security chart first.val second.val)
    (Parameters.modulus security : ℤ)
  have hsecond := Int.emod_add_mul_ediv
    (integerCompanion security (publicShift security primary seed) chart first.val second.val)
    (Parameters.modulus security : ℤ)
  have hq : (0 : ℤ) < Parameters.modulus security := by exact_mod_cast (Parameters.modulus_spec security).2.pos
  unfold integerCompanion at *
  nlinarith

end
end CurrentAFT.CurrentAffineLegCarry
