import AFT.ActualProtectedCarry
import AFT.V7PublicPlacement

/-! # Integer loads and simultaneous carries of the actual V7 blocks -/
namespace AFT.V7Calibration
open GaussianSource BoundaryCalibration Filter
open scoped BigOperators Classical Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
attribute [local instance] actualModulusNeZero

/-- The complete integer output before reduction: two complementary leg
loads and their attached body, or one ordinary body. -/
def actualIntegerBlockLoad (C : ℝ) (n : ℕ)
    (chart : Fin (Parameters.legs n) → Chart (ZMod (Parameters.modulus n)))
    (baseline : Fin (Parameters.legs n) → ℤ)
    (center : blockIndex n → Fin (Parameters.modulus n))
    (roots queue : blockIndex n → ℤ) (input : Fin (Parameters.legs n) → V7Input C n) :
    (index : blockIndex n) → blockSlots n index → ℤ
  | .inl leg => ![chartIntegerLoad (chart leg) (input leg).1 (input leg).2,
      (Parameters.modulus n : ℤ)-1+baseline leg-(input leg).2-
        chartIntegerLoad (chart leg) (input leg).1 (input leg).2,
      (center (.inl leg)).val+roots (.inl leg)+(input leg).2+queue (.inl leg)]
  | .inr body => ![(center (.inr body)).val+roots (.inr body)+queue (.inr body)]

theorem actualIntegerBlockLoad_leg_sum (C : ℝ) (n : ℕ)
    (chart : Fin (Parameters.legs n) → Chart (ZMod (Parameters.modulus n)))
    (baseline : Fin (Parameters.legs n) → ℤ)
    (center : blockIndex n → Fin (Parameters.modulus n))
    (roots queue : blockIndex n → ℤ) (input : Fin (Parameters.legs n) → V7Input C n)
    (leg : Fin (Parameters.legs n)) :
    (∑ slot,actualIntegerBlockLoad C n chart baseline center roots queue input (.inl leg) slot)=
      (Parameters.modulus n : ℤ)-1+baseline leg+(center (.inl leg)).val+roots (.inl leg)+queue (.inl leg) := by
  simp [actualIntegerBlockLoad,Fin.sum_univ_three]
  ring

theorem actualIntegerBlockLoad_sum (C : ℝ) (n : ℕ)
    (chart : Fin (Parameters.legs n) → Chart (ZMod (Parameters.modulus n)))
    (baseline : Fin (Parameters.legs n) → ℤ)
    (center : blockIndex n → Fin (Parameters.modulus n))
    (roots queue : blockIndex n → ℤ) (input : Fin (Parameters.legs n) → V7Input C n) :
    (∑ coordinate : Sigma (blockSlots n),
      actualIntegerBlockLoad C n chart baseline center roots queue input coordinate.1 coordinate.2)=
      (Parameters.legs n : ℤ)*((Parameters.modulus n : ℤ)-1)+(∑ leg,baseline leg)+
        (∑ index,((center index).val : ℤ))+(∑ index,roots index)+(∑ index,queue index) := by
  rw [Fintype.sum_sigma,Fintype.sum_sum_type]
  simp [actualIntegerBlockLoad,Fin.sum_univ_three,Fintype.sum_sum_type,
    Finset.sum_add_distrib]
  ring

/-- With the actual shared queue, only the baseline and center charge
remains after the full zero-sum root vector is inserted. -/
theorem actualIntegerBlockLoad_charge (C : ℝ) (n : ℕ)
    (chart : Fin (Parameters.legs n) → Chart (ZMod (Parameters.modulus n)))
    (baseline : Fin (Parameters.legs n) → ℤ)
    (center : blockIndex n → Fin (Parameters.modulus n))
    (roots : blockIndex n → ℤ) (hroot : ∑ index,roots index=0)
    (sample : Window (queueCutoff n) × Equiv.Perm (blockIndex n))
    (input : Fin (Parameters.legs n) → V7Input C n)
    (hcharge : (Parameters.modulus n : ℤ) ∣
      (∑ leg,baseline leg)+(∑ index,((center index).val : ℤ))-(Parameters.legs n : ℤ)) :
    (Parameters.modulus n : ℤ) ∣ ∑ coordinate : Sigma (blockSlots n),
      actualIntegerBlockLoad C n chart baseline center roots (actualQueueShifts n sample) input coordinate.1 coordinate.2 := by
  rw [actualIntegerBlockLoad_sum,hroot,actualQueueShifts_sum]
  obtain ⟨multiple,hmultiple⟩ := hcharge
  refine ⟨(Parameters.legs n : ℤ)+multiple+(sample.1 : ℤ),?_⟩
  nlinarith

/-- A single family of actual positive charts simultaneously has the full
source-dependent response and zero total carry throughout all protected
leg inputs, safe centers, bounded roots, and the one shared queue. -/
theorem actual_integer_block_carry_eventually (C : ℝ) (hC : 1 ≤ C) :
    ∀ᶠ n in atTop,∃ charts : (mark : Fin (Parameters.modulus n)) → PublicChartFamily C n mark,
    (∀ mark attached first second,publicChartRaw C n mark (charts mark) attached first second=
      conditionalJointOutput C n mark attached first second) ∧
    ∀ (mark : Fin (Parameters.legs n) → Fin (Parameters.modulus n))
      (samples : Fin (Parameters.legs n) → bodySample C n × Bool)
      (baseline : (leg : Fin (Parameters.legs n)) → PublicOffsets C n (mark leg) (samples leg))
      (chart : Fin (Parameters.legs n) → Chart (ZMod (Parameters.modulus n))),
      (∀ leg,(charts (mark leg) (samples leg) (baseline leg)).weight (chart leg) ≠ 0) →
    ∀ center : blockIndex n → Fin (Parameters.modulus n),(∀ index,center index ∈ safePalette n) →
    ∀ roots : blockIndex n → ℤ,(∀ index,|roots index| ≤ (v7RootCutoff n : ℤ)) →
    ∀ sample : Window (queueCutoff n) × Equiv.Perm (blockIndex n),
    ∀ input : Fin (Parameters.legs n) → V7Input C n,
      (∀ leg,(chart leg).2.1 ≠ 0) ∧
      (∑ coordinate : Sigma (blockSlots n),
        actualIntegerBlockLoad C n chart (fun leg => baseline leg) center roots (actualQueueShifts n sample) input
          coordinate.1 coordinate.2/(Parameters.modulus n : ℤ))=0 := by
  filter_upwards [actual_public_chart_carry_eventually C hC,actual_protected_body_carry_eventually C hC]
    with n hchart hbody
  choose charts hresponse hcarry using hchart
  refine ⟨charts,hresponse,?_⟩
  intro mark samples baseline chart hchart center hcenter roots hroots sample input
  refine ⟨fun leg => (hcarry (mark leg) (samples leg) (baseline leg) (chart leg) (hchart leg)).1,?_⟩
  rw [Fintype.sum_sigma]
  apply Finset.sum_eq_zero
  intro index _
  cases index with
  | inl leg =>
    simp [actualIntegerBlockLoad,Fin.sum_univ_three]
    have hp := (hcarry (mark leg) (samples leg) (baseline leg) (chart leg) (hchart leg)).2 (input leg)
    have hb := hbody (center (.inl leg)) (hcenter _) (roots (.inl leg)) (actualQueueShifts n sample (.inl leg))
      (hroots _) (actualQueueShifts_bound n sample _) (some (input leg).2)
    change ((center (.inl leg)).val+roots (.inl leg)+(input leg).2+actualQueueShifts n sample (.inl leg))/
      (Parameters.modulus n : ℤ)=0 at hb
    omega
  | inr body =>
    simp only [actualIntegerBlockLoad,Fin.sum_univ_one,Matrix.cons_val_zero]
    have hb := hbody (center (.inr body)) (hcenter _) (roots (.inr body)) (actualQueueShifts n sample (.inr body))
      (hroots _) (actualQueueShifts_bound n sample _) none
    simpa only [optionalShift,add_zero] using hb

end
end AFT.V7Calibration
