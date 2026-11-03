import AFT.RecordJointRepair
import AFT.SignedConditioning
import AFT.Rejection
import AFT.ConditionalNormalization
import AFT.FiniteRefresh

/-! # Unconditional finite rejection approximates record-preserving repair

The complete record-conditioned law remains the reference law. Its raw L1
estimate also certifies global rejection from the unconditioned proposal,
so the algorithm never has to condition on an exponentially rare record.
-/
namespace AFT.FiniteDist
open CanonicalMoments
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {State Public Record Center : Type*} [Fintype State] [Fintype Public]
  [Fintype Record] [Fintype Center]

omit [Fintype Public] [Fintype Record] [Fintype Center] in
theorem signedMass_ge_one_sub_l1 (raw : State → ℝ) (reference : FiniteDist State)
    (error : ℝ) (herror : (∑ point,|raw point-reference.weight point|)≤error) :
    1-error≤signedMass raw := by
  have hh := (SignedConditioning.mass_difference_le_l1 raw reference.weight).trans herror
  rw [reference.sum_one] at hh
  unfold signedMass
  exact sub_le_iff_le_add.mpr (by linarith [(abs_le.mp hh).1])

omit [Fintype Public] [Fintype Record] [Fintype Center] in
theorem positiveRepairLaw_l1_of_raw_error (proposal reference : FiniteDist State)
    (score : State → ℝ) (error : ℝ)
    (herror : (∑ point,|weightedMass proposal score point-reference.weight point|)≤error)
    (hsmall : error≤1/2) :
    ∃ hmean : 1/2≤signedMass (weightedMass proposal score),
      (∑ point,|(positiveRepairLaw proposal score
        (lt_of_lt_of_le (by norm_num : (0 : ℝ)<1/2) hmean)).weight point-reference.weight point|)≤4*error := by
  have hm := signedMass_ge_one_sub_l1 (weightedMass proposal score) reference error herror
  have hmean : 1/2≤signedMass (weightedMass proposal score) := by linarith
  refine ⟨hmean,?_⟩
  let positive := fun point => max (weightedMass proposal score point) 0
  have hp : (∑ point,|positive point-reference.weight point|)≤error := by
    apply le_trans _ herror
    apply Finset.sum_le_sum
    intro point _
    have hh := abs_max_sub_max_le_abs (weightedMass proposal score point) (reference.weight point) 0
    simpa only [max_eq_left (reference.nonneg point)] using hh
  have hmass := (SignedConditioning.mass_difference_le_l1 positive reference.weight).trans hp
  rw [reference.sum_one] at hmass
  have hlower : 1/2≤∑ point,positive point := by linarith [(abs_le.mp hmass).1]
  have hpos : 0<∑ point,positive point := lt_of_lt_of_le (by norm_num) hlower
  have hn := SignedConditioning.normalized_signed_l1 positive reference.weight reference.nonneg
    hpos (by rw [reference.sum_one];norm_num)
  simp only [reference.sum_one,div_one] at hn
  change (∑ point,|positive point/(∑ point,positive point)-reference.weight point|)≤4*error
  apply hn.trans
  have herr0 : 0≤error := (Finset.sum_nonneg fun point _ => abs_nonneg _).trans hp
  calc
    _ ≤ 2*error/(∑ point,positive point) := div_le_div_of_nonneg_right (by linarith) hpos.le
    _ ≤ 2*error/(1/2) := div_le_div_of_nonneg_left (by positivity) (by norm_num) hlower
    _ = _ := by ring

omit [Fintype State] in
theorem record_raw_forget (law : FiniteDist Public) (record : Public → Record)
    (conditional : Public → FiniteDist Center) (score : Public × Center → ℝ)
    (point : Public × Center) :
    (∑ pair,conditionalRawMass (recordSkeleton law record)
      (fun cell => joint (recordConditional law record cell) conditional) (fun _ => score) pair*
        (pointLaw pair.2).weight point)=weightedMass (joint law conditional) score point := by
  rcases point with ⟨pub,center⟩
  have hh := recordSkeleton_joint_expectation law record conditional
    (fun input => score input*(pointLaw input).weight (pub,center))
  simp only [expectation,Fintype.sum_prod_type,conditionalRawMass,weightedMass,
    Finset.mul_sum,mul_assoc] at hh ⊢
  rw [hh]
  simp [pointLaw,Prod.mk.injEq,ite_and]

omit [Fintype Public] [Fintype Record] [Fintype Center] in
/-- The mean floor and all clipping costs come from the raw approximation
certificate. The retry loop itself samples the unconditional proposal. -/
theorem globalPositive_capped_tv (proposal reference fallback : FiniteDist State)
    (score : State → ℝ) (error envelope : ℝ) (attempts : ℕ)
    (herror : (∑ point,|weightedMass proposal score point-reference.weight point|)≤error)
    (hsmall : error≤1/2) (henvelope : 0<envelope)
    (hbound : ∀ point,max (score point) 0≤envelope) :
    TVBound (cappedRejection proposal (positiveCoin score envelope)
      (positiveCoin_bounds score envelope henvelope hbound) fallback attempts)
      reference (Real.exp (-(attempts : ℝ)*(1/2)/envelope)+2*error) := by
  obtain ⟨hmean,hl1⟩ := positiveRepairLaw_l1_of_raw_error proposal reference score error herror hsmall
  have ht := positiveRepair_capped_tv proposal score envelope (1/2) henvelope (by norm_num)
    hbound hmean fallback attempts
  apply ht.triangle
  rw [tvBound_iff_totalVariation_le,totalVariation_eq_half_l1]
  linarith

end
end AFT.FiniteDist
