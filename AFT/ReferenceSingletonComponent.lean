import AFT.MixedReferenceCanonicalFibers
import AFT.ThreeFiberActivity

/-! # The actual linear coefficient uses only a positive singleton marginal -/
namespace AFT.LocalTensors
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {Slot Color : Type*} [Fintype Slot] [Fintype Color] [DecidableEq Slot]
local instance referenceSingletonSubtypeDecEq (selected : Finset Slot) : DecidableEq selected := Classical.decEq _

theorem referenceRestrictedComponent_singleton (p r : Slot → FiniteDist Color)
    (mass : (Slot → Color) → ℝ) (slot : Slot) (values : ({slot} : Finset Slot) → Color) :
    referenceRestrictedComponent p r mass {slot} values =
      ((∑ word,if word slot=values ⟨slot,Finset.mem_singleton_self slot⟩ then mass word else 0) -
        (r slot).weight (values ⟨slot,Finset.mem_singleton_self slot⟩)*(∑ word,mass word)) /
      (p slot).weight (values ⟨slot,Finset.mem_singleton_self slot⟩) := by
  have hprod (source : Slot → Color) :
      (∏ index : ({slot} : Finset Slot),MixedKernel.referenceAtom (p index) (r index) (source index) (values index)) =
      MixedKernel.referenceAtom (p slot) (r slot) (source slot) (values ⟨slot,Finset.mem_singleton_self slot⟩) :=
    Fintype.prod_subsingleton _ (⟨slot,Finset.mem_singleton_self slot⟩ : ({slot} : Finset Slot))
  unfold referenceRestrictedComponent
  simp_rw [hprod,MixedKernel.referenceAtom_eq]
  rw [sub_div,Finset.sum_div,Finset.mul_sum,Finset.sum_div,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro word _
  split_ifs <;> ring

/-- No full output density enters a first-degree coefficient. -/
theorem referenceRestrictedComponent_linear_sup_le (p r : Slot → FiniteDist Color)
    (hp : ∀ slot color,0 < (p slot).weight color)
    (mass : (Slot → Color) → ℝ) (hmass : ∀ word,0 ≤ mass word)
    (htotal : (∑ word,mass word)=1) (comparison marginal : ℝ)
    (hc : 0 ≤ comparison) (hm : 0 ≤ marginal)
    (hr : ∀ slot color,(r slot).weight color ≤ comparison*(p slot).weight color)
    (hmargin : ∀ slot color,(∑ word,if word slot=color then mass word else 0) ≤ marginal*(p slot).weight color)
    (selected : Finset Slot) (hselected : selected.card=1) :
    ‖referenceRestrictedComponent p r mass selected‖ ≤ marginal+comparison := by
  obtain ⟨slot,rfl⟩ := Finset.card_eq_one.mp hselected
  apply (pi_norm_le_iff_of_nonneg (add_nonneg hm hc)).mpr
  intro values
  rw [Real.norm_eq_abs,referenceRestrictedComponent_singleton,htotal,mul_one,abs_div,abs_of_pos (hp _ _)]
  apply (div_le_iff₀ (hp _ _)).mpr
  have hn : 0 ≤ ∑ word,if word slot=values ⟨slot,Finset.mem_singleton_self slot⟩ then mass word else 0 :=
    Finset.sum_nonneg fun word _ => by split_ifs; exact hmass word; rfl
  exact (abs_sub _ _).trans (by
    rw [abs_of_nonneg hn,abs_of_nonneg (FiniteDist.nonneg _ _)]
    exact (add_le_add (hmargin _ _) (hr _ _)).trans_eq (by ring))

theorem referenceRestrictedComponent_linear_activity_le (p r : Slot → FiniteDist Color)
    (hp : ∀ slot color,0 < (p slot).weight color)
    (mass : (Slot → Color) → ℝ) (hmass : ∀ word,0 ≤ mass word)
    (htotal : (∑ word,mass word)=1) (comparison marginal rate : ℝ)
    (hc : 0 ≤ comparison) (hm : 0 ≤ marginal) (hrate : 0 ≤ rate) (hrate1 : rate ≤ 1)
    (hr : ∀ slot color,(r slot).weight color ≤ comparison*(p slot).weight color)
    (hmargin : ∀ slot color,(∑ word,if word slot=color then mass word else 0) ≤ marginal*(p slot).weight color)
    (selected : Finset Slot) (hselected : selected.card=1) :
    MixedKernel.activity (fun _ : selected => rate) (fun slot : selected => p slot)
      (referenceRestrictedComponent p r mass selected) ≤ 2*rate*(marginal+comparison) := by
  have hs := referenceRestrictedComponent_linear_sup_le p r hp mass hmass htotal comparison marginal hc hm hr hmargin selected hselected
  have hbound : ∀ word,|referenceRestrictedComponent p r mass selected word| ≤ marginal+comparison := by
    intro word
    exact (show |referenceRestrictedComponent p r mass selected word| ≤ ‖referenceRestrictedComponent p r mass selected‖ by
      simpa only [Real.norm_eq_abs] using norm_le_pi_norm (referenceRestrictedComponent p r mass selected) word).trans hs
  unfold MixedKernel.activity
  simp only [Finset.prod_const,Finset.card_univ,Fintype.card_coe,hselected,pow_one]
  have hsum : (∑ frozen : Finset selected,(∏ _ ∈ frozen,rate)*MixedKernel.fiberNorm
      (fun slot : selected => p slot) (referenceRestrictedComponent p r mass selected) frozen) ≤ 2*(marginal+comparison) := by
    calc
      _ ≤ ∑ _ : Finset selected,(marginal+comparison) := by
        apply Finset.sum_le_sum
        intro frozen _
        have hf := MixedKernel.fiberNorm_le_sup (fun slot : selected => p slot)
          (referenceRestrictedComponent p r mass selected) (marginal+comparison) (add_nonneg hm hc) hbound frozen
        have hpw : (∏ _ ∈ frozen,rate) ≤ 1 := by
          simp only [Finset.prod_const]
          exact pow_le_one₀ hrate hrate1
        exact (mul_le_mul hpw hf (MixedKernel.fiberNorm_nonneg _ _ _) (by norm_num)).trans_eq (one_mul _)
      _ = _ := by simp [Fintype.card_finset,Fintype.card_coe,hselected]; ring
  have hh := mul_le_mul_of_nonneg_left hsum hrate
  simp only [Finset.prod_const] at hh
  exact hh.trans_eq (by ring)

end
end AFT.LocalTensors
