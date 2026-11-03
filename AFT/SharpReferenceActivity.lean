import AFT.MixedReferenceCanonicalFibers
import AFT.ThreeFiberActivity

/-! # Sharp mixed activity of the physical reference-centered coefficients -/
namespace AFT.LocalTensors
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {Slot Color : Type*} [Fintype Slot] [Fintype Color] [Nonempty Color] [DecidableEq Slot]
local instance sharpReferenceSubtypeDecEq (selected : Finset Slot) : DecidableEq selected := Classical.decEq _

/-- Centering the actual output at `r` while measuring its input at `p`
retains all pool powers. The fixed comparison eight changes only a constant. -/
theorem referenceRestrictedComponent_activity_sharp (p r : Slot → FiniteDist Color)
    (hp : ∀ slot color, 0 < (p slot).weight color)
    (hr : ∀ slot color, (r slot).weight color ≤ 8 * (p slot).weight color)
    (mass : (Slot → Color) → ℝ) (selected : Finset Slot) (hcard : selected.card ≤ 4)
    (rate full oneFixed scale : ℝ)
    (hrate : 0 ≤ rate) (hrate1 : rate ≤ 1) (hfull : 0 ≤ full) (hone : 0 ≤ oneFixed) (hscale : 0 ≤ scale)
    (hsmall : rate * scale ≤ 1)
    (hf : (FiniteDist.independent p).l2Sq
      (fun word => mass word / (FiniteDist.independent p).weight word) ≤ full ^ 2)
    (hg : ∀ slot values, MixedKernel.fiberSq p
      (fun word => mass word / (FiniteDist.independent p).weight word) {slot} values ≤ oneFixed ^ 2)
    (hh : ∀ word, |mass word / (FiniteDist.independent p).weight word| ≤ scale * oneFixed) :
    MixedKernel.activity (fun _ : selected => rate) (fun slot : selected => p slot)
      (referenceRestrictedComponent p r mass selected) ≤
      2097152 * rate ^ selected.card * (full + rate * oneFixed) := by
  let factor : ℝ := 16 ^ selected.card
  have hfactor0 : 0 ≤ factor := by positivity
  have hfactor : factor ≤ 65536 := by
    exact (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 16) hcard).trans_eq (by norm_num)
  have hF : (FiniteDist.independent (fun slot : selected => p slot)).l2Sq
      (referenceRestrictedComponent p r mass selected) ≤ (factor * full) ^ 2 := by
    apply (referenceRestrictedComponent_l2Sq_le p r hp mass selected 8 (by norm_num) hr).trans
    convert mul_le_mul_of_nonneg_left hf (sq_nonneg factor) using 1 <;> norm_num [factor, mul_pow]
  have hG (slot : selected) (values : selected → Color) :
      MixedKernel.fiberSq (fun slot : selected => p slot)
        (referenceRestrictedComponent p r mass selected) {slot} values ≤ (factor * (full + oneFixed)) ^ 2 := by
    apply (MixedKernel.fiberSq_le_norm_sq _ _ _ _).trans
    apply (sq_le_sq₀ (MixedKernel.fiberNorm_nonneg _ _ _) (by positivity)).mpr
    simpa only [factor, show (2 : ℝ) * 8 = 16 by norm_num] using
      referenceRestrictedComponent_singleton_sharp p r hp mass selected 8 full oneFixed
        (by norm_num) hr hfull hone hf hg slot
  have hH : ‖referenceRestrictedComponent p r mass selected‖ ≤ factor * (scale * oneFixed) := by
    simpa only [factor, show (2 : ℝ) * 8 = 16 by norm_num] using
      referenceRestrictedComponent_sup_sharp p r hp mass selected 8 (scale * oneFixed)
        (by norm_num) hr (mul_nonneg hscale hone) hh
  have hact := MixedKernel.activity_le_three_fibers (fun slot : selected => p slot)
    (referenceRestrictedComponent p r mass selected) rate (factor * full) (factor * (full + oneFixed))
    (factor * (scale * oneFixed)) hrate hrate1 (by positivity) (by positivity) (by positivity) hF hG
    (fun word => by
      have hn : |referenceRestrictedComponent p r mass selected word| ≤ ‖referenceRestrictedComponent p r mass selected‖ := by
        simpa only [Real.norm_eq_abs] using norm_le_pi_norm (referenceRestrictedComponent p r mass selected) word
      exact hn.trans hH)
  simp only [Fintype.card_coe] at hact
  have hb : factor * full + rate * (factor * (full + oneFixed)) + rate ^ 2 * (factor * (scale * oneFixed)) ≤
      2 * factor * (full + rate * oneFixed) := by
    have h1 := mul_le_mul_of_nonneg_right hrate1 (mul_nonneg hfactor0 hfull)
    have h2 := mul_le_mul_of_nonneg_right hsmall (mul_nonneg (mul_nonneg hrate hfactor0) hone)
    nlinarith
  have htwo : (2 : ℝ)^selected.card ≤ 16 :=
    (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hcard).trans_eq (by norm_num)
  calc
    _ ≤ 2 ^ selected.card * rate ^ selected.card * (2 * factor * (full + rate * oneFixed)) :=
      hact.trans (mul_le_mul_of_nonneg_left hb (by positivity))
    _ ≤ 16 * rate ^ selected.card * (2 * 65536 * (full + rate * oneFixed)) := by
      gcongr
    _ = _ := by ring

end
end AFT.LocalTensors
