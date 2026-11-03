import CurrentAFT.CurrentCoreProposal
import CurrentAFT.CurrentPublicShiftCost
import AFT.BinaryIntegerDivision

/-! # The actual public charge test on materialized core buffers -/
namespace CurrentAFT.BinaryCoreCharge
open AFT BinaryArithmetic RationalRejectionProgram CurrentCoreProposal CurrentProposalDimensions ActualPublicCharge
open scoped BigOperators
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.legCount Parameters.bodySize Parameters.dimension

def controlTerm (security : ℕ) (data : MaterializedCore security) (index : Fin (CurrentProposalDimensions.current security).controls) :
    CountedValue IntegerBits :=
  let control := readVector (defaultControl security) data.controls index
  let result := CurrentPublicShiftProgram.encode (control.value.2.val.val : ℤ)
  ⟨result.value, control.work+result.work+2⟩

def legTerm (security : ℕ) (data : MaterializedCore security) (index : Fin (CurrentProposalDimensions.current security).legs) :
    CountedValue IntegerBits :=
  let leg := readVector (defaultLeg security) data.legs index
  let input := readVector (CurrentChartsDraw.defaultInput security) data.inputs (legEquiv security index)
  let baseline := CurrentPublicShiftProgram.encode (leg.value.2.val : ℤ)
  let shift := CurrentPublicShiftProgram.current security input.value.1 input.value.2
  let result := IntegerBits.add baseline.value shift.value
  ⟨result.value, leg.work+input.work+baseline.work+shift.work+result.work+5⟩

def queueTerm (security : ℕ) (data : MaterializedCore security) (index : Fin (CurrentProposalDimensions.current security).colors) :
    CountedValue IntegerBits :=
  let baseline := readVector (defaultControl security).1 data.baselines index
  let result := CurrentPublicShiftProgram.encode (baseline.value.val : ℤ)
  ⟨result.value, baseline.work+result.work+2⟩

def total (security : ℕ) (data : MaterializedCore security) : CountedValue IntegerBits :=
  let sizes := CurrentProposalDimensions.current security
  let controls := IntegerBits.sumFin sizes.controls (controlTerm security data)
  let legs := IntegerBits.sumFin sizes.legs (legTerm security data)
  let queues := IntegerBits.sumFin sizes.colors (queueTerm security data)
  let first := IntegerBits.add controls.value legs.value
  let second := IntegerBits.add first.value queues.value
  let removed := CurrentPublicShiftProgram.encode (sizes.legs : ℤ)
  let result := IntegerBits.subtract second.value removed.value
  ⟨result.value, sizes.work+controls.work+legs.work+queues.work+first.work+second.work+removed.work+result.work+8⟩

def current (security : ℕ) (data : MaterializedCore security) : CountedValue Bool :=
  let modulus := PublicParameterProgram.modulus security
  let encoded := canonicalCounter modulus.count
  let numerator := total security data
  let residue := IntegerBits.residue numerator.value encoded.digits
  let reduced := normalize residue.digits
  ⟨reduced.digits.isEmpty, modulus.work+encoded.work+numerator.work+residue.work+reduced.work+6⟩

noncomputable section
open scoped Classical

def numerator (security : ℕ) (core : Core security) : ℤ :=
  (∑ index : PublicOutputExperiment.PublicIndex security, (core.controls index).2.val.val) +
    (∑ leg, (((core.legs leg).2.val : ℤ) + legShift security core leg)) +
    (∑ index, ((core.queueBaselines index).val : ℤ)) - Parameters.legCount security

theorem numerator_cast (security : ℕ) (core : Core security) :
    (numerator security core : ZMod (Parameters.modulus security)) = chargeValue security core := by
  unfold numerator chargeValue
  simp only [Fintype.sum_sum_type, Int.cast_sum, Int.cast_add, Int.cast_sub,
    Int.cast_natCast, Finset.sum_add_distrib]
  push_cast
  ring

theorem controlTerm_value (security : ℕ) (data : MaterializedCore security)
    (index : Fin (CurrentProposalDimensions.current security).controls) :
    (controlTerm security data index).value.decode =
      ((data.core.controls (controlsEquiv security index)).2.val.val : ℤ) := by
  simp only [controlTerm, CurrentPublicShiftProgram.encode_value, readVector_value,
    MaterializedCore.core, decode, Equiv.symm_apply_apply]

theorem legTerm_value (security : ℕ) (data : MaterializedCore security)
    (index : Fin (CurrentProposalDimensions.current security).legs) :
    (legTerm security data index).value.decode =
      ((data.core.legs (legEquiv security index)).2.val : ℤ) + legShift security data.core (legEquiv security index) := by
  simp only [legTerm, IntegerBits.add_value, CurrentPublicShiftProgram.encode_value,
    CurrentPublicShiftProgram.current_value, readVector_value, data.inputs_correct,
    legShift, MaterializedCore.core, decode, Equiv.symm_apply_apply]

theorem queueTerm_value (security : ℕ) (data : MaterializedCore security)
    (index : Fin (CurrentProposalDimensions.current security).colors) :
    (queueTerm security data index).value.decode =
      ((data.core.queueBaselines (queueEquiv security index)).val : ℤ) := by
  simp only [queueTerm, CurrentPublicShiftProgram.encode_value, readVector_value,
    MaterializedCore.core, decode, Equiv.symm_apply_apply]

theorem total_value (security : ℕ) (data : MaterializedCore security) :
    (total security data).value.decode = numerator security data.core := by
  simp only [total, IntegerBits.subtract_value, IntegerBits.add_value, IntegerBits.sumFin_value,
    CurrentPublicShiftProgram.encode_value, controlTerm_value, legTerm_value, queueTerm_value]
  rw [Equiv.sum_comp (controlsEquiv security) (fun index => ((data.core.controls index).2.val.val : ℤ)),
    Equiv.sum_comp (legEquiv security) (fun leg => ((data.core.legs leg).2.val : ℤ) + legShift security data.core leg),
    Equiv.sum_comp (queueEquiv security) (fun index => ((data.core.queueBaselines index).val : ℤ)),
    (current_values security).2.1]
  unfold numerator
  norm_cast

theorem current_value (security : ℕ) (data : MaterializedCore security) :
    (current security data).value = true ↔ publicCharge security data.core := by
  have hq : 0 < value (canonicalCounter (PublicParameterProgram.modulus security).count).digits := by
    rw [canonicalCounter_value, PublicParameterProgram.modulus_value]
    exact (Parameters.modulus_spec security).2.pos
  have hr := IntegerBits.residue_value (total security data).value
    (canonicalCounter (PublicParameterProgram.modulus security).count).digits hq
  rw [total_value, canonicalCounter_value, PublicParameterProgram.modulus_value] at hr
  change (normalize (IntegerBits.residue (total security data).value
    (canonicalCounter (PublicParameterProgram.modulus security).count).digits).digits).digits.isEmpty = true ↔ _
  rw [List.isEmpty_iff, normalize_nil_iff]
  have he : value (IntegerBits.residue (total security data).value
      (canonicalCounter (PublicParameterProgram.modulus security).count).digits).digits = 0 ↔
      numerator security data.core % (Parameters.modulus security : ℤ) = 0 := by
    rw [PublicParameterProgram.modulus_value]
    omega
  rw [he, ← Int.dvd_iff_emod_eq_zero]
  unfold publicCharge
  rw [← numerator_cast]
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).symm

end
end CurrentAFT.BinaryCoreCharge
