import CurrentAFT.CurrentBinaryAffinePrimitives
import CurrentAFT.BinaryProposalGuard

/-! The emitter executes the same public validity predicate as assemble.
The test reads every stored chart and uses the actual binary public-charge guard. -/
namespace CurrentAFT.CurrentBinaryAffineGuard
open AFT BinaryArithmetic RationalRejectionProgram CurrentCoreProposal CurrentBinaryChartData
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.legCount Parameters.dimension Parameters.bodySize

def scale (security : ℕ) (charts : Charts security) (leg : Fin (Parameters.legCount security)) : CountedValue Bool :=
  let chart := readVector (defaultChart security) charts leg
  let tested := equalCounter chart.value.2.2.1.val 0
  ⟨!tested.value, chart.work + tested.work + 2⟩

 theorem scale_value (security : ℕ) (charts : Charts security) (leg : Fin (Parameters.legCount security)) :
    (scale security charts leg).value = true ↔ (charts.get leg).2.2.1 ≠ 0 := by
  have he : (equalCounter (charts.get leg).2.2.1.val 0).value = true ↔ (charts.get leg).2.2.1 = 0 := by
    rw [equalCounter_value, ZMod.val_eq_zero]
  simp only [scale, readVector_value, Bool.not_eq_true', Bool.eq_false_iff]
  exact not_congr he

 theorem scale_work (security : ℕ) (charts : Charts security) (leg : Fin (Parameters.legCount security)) :
    (scale security charts leg).work ≤ 3 * Parameters.legCount security + 3 * Parameters.modulus security + 9 := by
  have hr := readVector_work (defaultChart security) charts leg
  have he := equalCounter_work (readVector (defaultChart security) charts leg).value.2.2.1.val 0
  have hv := (ZMod.val_lt (readVector (defaultChart security) charts leg).value.2.2.1).le
  change (readVector (defaultChart security) charts leg).work + (equalCounter _ 0).work + 2 ≤ _
  omega


def current (security : ℕ) (core : MaterializedCore security) (charts : Charts security) : CountedValue Bool :=
  let charge := BinaryCoreCharge.current security core
  let scales := BinaryProposalGuard.allFin (Parameters.legCount security) (scale security charts)
  ⟨charge.value && scales.value, charge.work + scales.work + 2⟩

 theorem current_value (security : ℕ) (core : MaterializedCore security) (charts : Charts security) :
    (current security core charts).value = true ↔ CurrentAffineData.Valid security core.core charts.get := by
  simp only [current, Bool.and_eq_true, BinaryCoreCharge.current_value,
    BinaryProposalGuard.allFin_value, scale_value, CurrentAffineData.Valid]

 theorem current_work (security : ℕ) (core : MaterializedCore security) (charts : Charts security) :
    (current security core charts).work ≤ (BinaryCoreCharge.current security core).work +
      Parameters.legCount security * (3 * Parameters.legCount security + 3 * Parameters.modulus security + 11) + 3 := by
  have hs := BinaryProposalGuard.allFin_work (Parameters.legCount security)
    (3 * Parameters.legCount security + 3 * Parameters.modulus security + 9) (scale security charts)
    (scale_work security charts)
  change _ + (BinaryProposalGuard.allFin _ _).work + 2 ≤ _
  norm_num only [Nat.add_assoc] at hs ⊢
  omega

end CurrentAFT.CurrentBinaryAffineGuard
