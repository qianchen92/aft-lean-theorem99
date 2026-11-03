import CurrentAFT.BinaryCoreCharge

/-! Complete bit work of the source-independent public charge test. -/
namespace CurrentAFT.BinaryCoreCharge
open AFT BinaryArithmetic RationalRejectionProgram CurrentCoreProposal CurrentProposalDimensions ActualPublicCharge
set_option maxHeartbeats 1200000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.legCount Parameters.bodySize Parameters.dimension CurrentProposalDimensions.current

def colorsBound (security : ℕ) : ℕ := 131072*(security+2)^64
def leafLength (security : ℕ) : ℕ := colorsBound security+2*(security+2)^48+2*(security+2)^2+3
def leafWork (security : ℕ) : ℕ :=
  CurrentPublicShiftProgram.workBound security+100*(colorsBound security+1)^2+
    6*(CurrentProposalDimensions.current security).controls+6*(CurrentProposalDimensions.current security).legs+
    6*(CurrentProposalDimensions.current security).colors+20*leafLength security+30

theorem palette_bound (security : ℕ) (color : FirstHistogram.Palette security) : color.val ≤ colorsBound security :=
  color.isLt.le.trans (by simpa only [colorsBound, Parameters.base] using (Parameters.modulus_bounds security).2)

theorem controlTerm_bounds (security : ℕ) (data : MaterializedCore security)
    (index : Fin (CurrentProposalDimensions.current security).controls) :
    (controlTerm security data index).value.digits.length ≤ leafLength security ∧
      (controlTerm security data index).work ≤ leafWork security := by
  let read := readVector (defaultControl security) data.controls index
  have hc := palette_bound security read.value.2.val
  have hl := CurrentPublicShiftProgram.encode_length (read.value.2.val.val : ℤ)
  have hw := CurrentPublicShiftProgram.encode_work (read.value.2.val.val : ℤ)
  have hr := readVector_work (defaultControl security) data.controls index
  simp only [Int.natAbs_natCast] at hl hw
  have hw' : (CurrentPublicShiftProgram.encode (read.value.2.val.val : ℤ)).work ≤
      50*(colorsBound security+1)^2+1 := hw.trans (Nat.add_le_add_right (Nat.mul_le_mul_left 50 (Nat.pow_le_pow_left (Nat.add_le_add_right hc 1) 2)) 1)
  constructor
  · exact hl.trans (by unfold leafLength; omega)
  · change read.work + (CurrentPublicShiftProgram.encode (read.value.2.val.val : ℤ)).work+2 ≤ _
    change read.work ≤ _ at hr
    unfold leafWork
    omega

theorem queueTerm_bounds (security : ℕ) (data : MaterializedCore security)
    (index : Fin (CurrentProposalDimensions.current security).colors) :
    (queueTerm security data index).value.digits.length ≤ leafLength security ∧
      (queueTerm security data index).work ≤ leafWork security := by
  let read := readVector (defaultControl security).1 data.baselines index
  have hc := palette_bound security read.value
  have hl := CurrentPublicShiftProgram.encode_length (read.value.val : ℤ)
  have hw := CurrentPublicShiftProgram.encode_work (read.value.val : ℤ)
  have hr := readVector_work (defaultControl security).1 data.baselines index
  simp only [Int.natAbs_natCast] at hl hw
  have hw' : (CurrentPublicShiftProgram.encode (read.value.val : ℤ)).work ≤
      50*(colorsBound security+1)^2+1 := hw.trans (Nat.add_le_add_right (Nat.mul_le_mul_left 50 (Nat.pow_le_pow_left (Nat.add_le_add_right hc 1) 2)) 1)
  constructor
  · exact hl.trans (by unfold leafLength; omega)
  · change read.work + (CurrentPublicShiftProgram.encode (read.value.val : ℤ)).work+2 ≤ _
    change read.work ≤ _ at hr
    unfold leafWork
    omega

theorem legTerm_bounds (security : ℕ) (data : MaterializedCore security)
    (index : Fin (CurrentProposalDimensions.current security).legs) :
    (legTerm security data index).value.digits.length ≤ leafLength security ∧
      (legTerm security data index).work ≤ leafWork security := by
  let leg := readVector (defaultLeg security) data.legs index
  let input := readVector (CurrentChartsDraw.defaultInput security) data.inputs (legEquiv security index)
  let baseline := CurrentPublicShiftProgram.encode (leg.value.2.val : ℤ)
  let shift := CurrentPublicShiftProgram.current security input.value.1 input.value.2
  have hc := palette_bound security leg.value.2
  have hb := CurrentPublicShiftProgram.encode_length (leg.value.2.val : ℤ)
  have wb := CurrentPublicShiftProgram.encode_work (leg.value.2.val : ℤ)
  simp only [Int.natAbs_natCast] at hb wb
  change baseline.value.digits.length ≤ _ at hb
  have hs := CurrentPublicShiftProgram.current_length security input.value.1 input.value.2
  change shift.value.digits.length ≤ _ at hs
  have ws := CurrentPublicShiftProgram.current_work security input.value.1 input.value.2
  change shift.work ≤ _ at ws
  have wl := readVector_work (defaultLeg security) data.legs index
  change leg.work ≤ _ at wl
  have wi := readVector_work (CurrentChartsDraw.defaultInput security) data.inputs (legEquiv security index)
  change input.work ≤ _ at wi
  rw [← (current_values security).2.1] at wi
  have hl := IntegerBits.add_length baseline.value shift.value
  have wa := IntegerBits.add_work baseline.value shift.value
  have hb' : baseline.work ≤ 50*(colorsBound security+1)^2+1 := wb.trans (Nat.add_le_add_right (Nat.mul_le_mul_left 50 (Nat.pow_le_pow_left (Nat.add_le_add_right hc 1) 2)) 1)
  have hm : max baseline.value.digits.length shift.value.digits.length+1 ≤ leafLength security := by
    unfold leafLength
    omega
  constructor
  · exact hl.trans hm
  · change leg.work+input.work+baseline.work+shift.work+(IntegerBits.add baseline.value shift.value).work+5 ≤ _
    unfold leafWork
    omega

def totalLength (security : ℕ) : ℕ :=
  (CurrentProposalDimensions.current security).controls+2*(CurrentProposalDimensions.current security).legs+
    (CurrentProposalDimensions.current security).colors+3*leafLength security+5

def totalWork (security : ℕ) : ℕ :=
  let sizes := CurrentProposalDimensions.current security
  sizes.work + sizes.controls*(leafWork security+20*(sizes.controls+leafLength security)+11)+
    sizes.legs*(leafWork security+20*(sizes.legs+leafLength security)+11)+
    sizes.colors*(leafWork security+20*(sizes.colors+leafLength security)+11)+
    50*(sizes.legs+1)^2+60*totalLength security+60

theorem total_bounds (security : ℕ) (data : MaterializedCore security) :
    (total security data).value.digits.length ≤ totalLength security ∧
      (total security data).work ≤ totalWork security := by
  let sizes := CurrentProposalDimensions.current security
  let controls := IntegerBits.sumFin sizes.controls (controlTerm security data)
  let legs := IntegerBits.sumFin sizes.legs (legTerm security data)
  let queues := IntegerBits.sumFin sizes.colors (queueTerm security data)
  let first := IntegerBits.add controls.value legs.value
  let second := IntegerBits.add first.value queues.value
  let removed := CurrentPublicShiftProgram.encode (sizes.legs : ℤ)
  let result := IntegerBits.subtract second.value removed.value
  have hc := IntegerBits.sumFin_length sizes.controls (leafLength security) (controlTerm security data)
    (fun index => (controlTerm_bounds security data index).1)
  have hl := IntegerBits.sumFin_length sizes.legs (leafLength security) (legTerm security data)
    (fun index => (legTerm_bounds security data index).1)
  have hq := IntegerBits.sumFin_length sizes.colors (leafLength security) (queueTerm security data)
    (fun index => (queueTerm_bounds security data index).1)
  change controls.value.digits.length ≤ _ at hc
  change legs.value.digits.length ≤ _ at hl
  change queues.value.digits.length ≤ _ at hq
  have hfirst := IntegerBits.add_length controls.value legs.value
  change first.value.digits.length ≤ _ at hfirst
  have hsecond := IntegerBits.add_length first.value queues.value
  change second.value.digits.length ≤ _ at hsecond
  have hremoved := CurrentPublicShiftProgram.encode_length (sizes.legs : ℤ)
  simp only [Int.natAbs_natCast] at hremoved
  change removed.value.digits.length ≤ _ at hremoved
  have hresult := IntegerBits.subtract_length second.value removed.value
  change result.value.digits.length ≤ _ at hresult
  have hcW := IntegerBits.sumFin_work sizes.controls (leafLength security) (leafWork security) (controlTerm security data)
    (fun index => (controlTerm_bounds security data index).1) (fun index => (controlTerm_bounds security data index).2)
  have hlW := IntegerBits.sumFin_work sizes.legs (leafLength security) (leafWork security) (legTerm security data)
    (fun index => (legTerm_bounds security data index).1) (fun index => (legTerm_bounds security data index).2)
  have hqW := IntegerBits.sumFin_work sizes.colors (leafLength security) (leafWork security) (queueTerm security data)
    (fun index => (queueTerm_bounds security data index).1) (fun index => (queueTerm_bounds security data index).2)
  change controls.work ≤ _ at hcW
  change legs.work ≤ _ at hlW
  change queues.work ≤ _ at hqW
  have hfW := IntegerBits.add_work controls.value legs.value
  change first.work ≤ _ at hfW
  have hsW := IntegerBits.add_work first.value queues.value
  change second.work ≤ _ at hsW
  have hrW := CurrentPublicShiftProgram.encode_work (sizes.legs : ℤ)
  simp only [Int.natAbs_natCast] at hrW
  change removed.work ≤ _ at hrW
  have houtW := IntegerBits.subtract_work second.value removed.value
  change result.work ≤ _ at houtW
  have hfirstmax : max controls.value.digits.length legs.value.digits.length ≤ totalLength security := by
    change _ ≤ sizes.controls+2*sizes.legs+sizes.colors+3*leafLength security+5
    omega
  have hsecondmax : max first.value.digits.length queues.value.digits.length ≤ totalLength security := by
    change _ ≤ sizes.controls+2*sizes.legs+sizes.colors+3*leafLength security+5
    omega
  have hresultmax : max second.value.digits.length removed.value.digits.length+1 ≤ totalLength security := by
    change _ ≤ sizes.controls+2*sizes.legs+sizes.colors+3*leafLength security+5
    omega
  constructor
  · exact hresult.trans hresultmax
  · change sizes.work+controls.work+legs.work+queues.work+first.work+second.work+removed.work+result.work+8 ≤ _
    change _ ≤ sizes.work+sizes.controls*(leafWork security+20*(sizes.controls+leafLength security)+11)+
      sizes.legs*(leafWork security+20*(sizes.legs+leafLength security)+11)+
      sizes.colors*(leafWork security+20*(sizes.colors+leafLength security)+11)+
      50*(sizes.legs+1)^2+60*totalLength security+60
    omega

def work (security : ℕ) : ℕ :=
  PublicParameterProgram.workBound security+50*(colorsBound security+1)^2+totalWork security+
    60*(totalLength security+colorsBound security+1)^2+4*(totalLength security+colorsBound security)+18

theorem current_work (security : ℕ) (data : MaterializedCore security) :
    (current security data).work ≤ work security := by
  let modulus := PublicParameterProgram.modulus security
  let encoded := canonicalCounter modulus.count
  let numerator := total security data
  let residue := IntegerBits.residue numerator.value encoded.digits
  have hm : modulus.count ≤ colorsBound security := by
    rw [show modulus.count = Parameters.modulus security from PublicParameterProgram.modulus_value security]
    simpa only [colorsBound, Parameters.base] using (Parameters.modulus_bounds security).2
  have hl : encoded.digits.length ≤ colorsBound security := by
    change (canonicalCounter modulus.count).digits.length ≤ _
    rw [canonicalCounter_length]
    exact (Nat.size_le.mpr (Nat.lt_two_pow_self (n := _))).trans hm
  have ht := total_bounds security data
  change numerator.value.digits.length ≤ _ ∧ numerator.work ≤ _ at ht
  have hr := IntegerBits.residue_length numerator.value encoded.digits
  change residue.digits.length ≤ _ at hr
  have wr := IntegerBits.residue_work numerator.value encoded.digits
  change residue.work ≤ _ at wr
  have wr' : residue.work ≤ 60*(totalLength security+colorsBound security+1)^2+10 := wr.trans (Nat.add_le_add_right (Nat.mul_le_mul_left 60 (Nat.pow_le_pow_left (Nat.add_le_add_right (Nat.add_le_add ht.1 hl) 1) 2)) 10)
  have wm := PublicParameterProgram.modulus_work security
  change modulus.work ≤ _ at wm
  have we := canonicalCounter_work modulus.count
  change encoded.work ≤ _ at we
  have we' : encoded.work ≤ 50*(colorsBound security+1)^2 := we.trans (Nat.mul_le_mul_left 50 (Nat.pow_le_pow_left (Nat.add_le_add_right hm 1) 2))
  have wn := normalize_work residue.digits
  change modulus.work+encoded.work+numerator.work+residue.work+(normalize residue.digits).work+6 ≤ _
  unfold work
  omega

end CurrentAFT.BinaryCoreCharge
