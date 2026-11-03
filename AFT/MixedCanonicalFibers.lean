import AFT.ChannelMixedFibers
import AFT.CanonicalTaylor
import AFT.CanonicalFiberEnergy

/-! # Canonical projection preserves sharp one-fixed fibers without an atom penalty -/
namespace AFT.MixedKernel
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {Slot Color : Type*} [Fintype Slot] [DecidableEq Slot] [Fintype Color]

def atomMajorant (p : FiniteDist Color) (source value : Color) : ℝ :=
  (if source=value then (p.weight value)⁻¹ else 0)+1

theorem atomMajorant_nonneg (p : FiniteDist Color) (source value : Color) :
    0 ≤ atomMajorant p source value := by
  have hh := p.nonneg value
  unfold atomMajorant
  split_ifs <;> positivity

theorem atomMajorant_one_le (p : FiniteDist Color) (source value : Color) :
    1 ≤ atomMajorant p source value := by
  unfold atomMajorant
  split_ifs
  · exact le_add_of_nonneg_left (inv_nonneg.mpr (p.nonneg value))
  · norm_num

theorem centeredAtom_abs_le (p : FiniteDist Color) (source value : Color) :
    |Hoeffding.centeredAtom p source value| ≤ atomMajorant p source value := by
  unfold Hoeffding.centeredAtom atomMajorant
  split_ifs
  · exact (abs_sub _ _).trans_eq (by rw [abs_of_nonneg (inv_nonneg.mpr (p.nonneg value)),abs_one])
  · norm_num

theorem atomMajorant_source (p : FiniteDist Color) (hp : ∀ color,0<p.weight color) (value : Color) :
    (∑ source,p.weight source*atomMajorant p source value)=2 := by
  simp only [atomMajorant,mul_add,mul_one,Finset.sum_add_distrib,mul_ite,mul_zero,
    Finset.sum_ite_eq',Finset.mem_univ,if_true,p.sum_one,mul_inv_cancel₀ (hp value).ne']
  norm_num

theorem atomMajorant_value (p : FiniteDist Color) (hp : ∀ color,0<p.weight color) (source : Color) :
    (∑ value,p.weight value*atomMajorant p source value)=2 := by
  have he (value) : p.weight value*atomMajorant p source value =
      (if source=value then (1:ℝ) else 0)+p.weight value := by
    unfold atomMajorant
    rw [mul_add]
    split_ifs
    · rw [mul_inv_cancel₀ (hp value).ne',mul_one]
    · ring
  simp only [he,Finset.sum_add_distrib,p.sum_one]
  norm_num

def projectionMajorant (p : Slot → FiniteDist Color) (selected : Finset Slot)
    (source value : Slot → Color) : ℝ := ∏ slot ∈ selected,atomMajorant (p slot) (source slot) (value slot)

omit [Fintype Slot] [DecidableEq Slot] in
theorem projectionMajorant_nonneg (p : Slot → FiniteDist Color) (selected : Finset Slot)
    (source value : Slot → Color) : 0 ≤ projectionMajorant p selected source value :=
  Finset.prod_nonneg fun _ _ => atomMajorant_nonneg _ _ _

theorem expectation_partial_product (p : Slot → FiniteDist Color) (selected : Finset Slot)
    (values : Slot → Color → ℝ) :
    (∑ word,(FiniteDist.independent p).weight word*∏ slot ∈ selected,values slot (word slot)) =
      ∏ slot ∈ selected,∑ color,(p slot).weight color*values slot color := by
  have he (word : Slot → Color) : (∏ slot ∈ selected,values slot (word slot)) =
      ∏ slot,if slot ∈ selected then values slot (word slot) else 1 := (Fintype.prod_ite_mem _ _).symm
  simp_rw [he]
  change (∑ word : Slot → Color,(∏ slot,(p slot).weight (word slot))*
      ∏ slot,if slot ∈ selected then values slot (word slot) else 1) = _
  simp only [← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun slot color => (p slot).weight color*(if slot ∈ selected then values slot color else 1))]
  have ht (slot) : (∑ color,(p slot).weight color*(if slot ∈ selected then values slot color else 1)) =
      if slot ∈ selected then ∑ color,(p slot).weight color*values slot color else 1 := by
    split_ifs <;> simp only [mul_one,FiniteDist.sum_one]
  simp_rw [ht]
  exact Fintype.prod_ite_mem _ _

theorem projectionMajorant_source (p : Slot → FiniteDist Color)
    (hp : ∀ slot color,0<(p slot).weight color) (selected : Finset Slot) (value : Slot → Color) :
    (∑ source,(FiniteDist.independent p).weight source*projectionMajorant p selected source value)=2^selected.card := by
  unfold projectionMajorant
  rw [expectation_partial_product p selected (fun slot source => atomMajorant (p slot) source (value slot))]
  simp only [atomMajorant_source _ (hp _),Finset.prod_const]

theorem projection_square_majorant (p : Slot → FiniteDist Color)
    (hp : ∀ slot color,0<(p slot).weight color) (selected : Finset Slot) (f : (Slot → Color) → ℝ)
    (value : Slot → Color) :
    Hoeffding.projection p selected f value ^ 2 ≤ 2^selected.card*
      ∑ source,(FiniteDist.independent p).weight source*projectionMajorant p selected source value*f source^2 := by
  cases Subsingleton.elim (inferInstance : DecidableEq Slot) (Classical.decEq Slot)
  let kernel (source : Slot → Color) := ∏ slot ∈ selected,Hoeffding.centeredAtom (p slot) (source slot) (value slot)
  have hk (source) : |kernel source| ≤ projectionMajorant p selected source value := by
    dsimp only [kernel]
    rw [Finset.abs_prod]
    exact Finset.prod_le_prod (fun _ _ => abs_nonneg _) (fun slot _ => centeredAtom_abs_le _ _ _)
  have hc : (∑ source,(FiniteDist.independent p).weight source*f source*kernel source)^2 ≤
      (∑ source,(FiniteDist.independent p).weight source*|kernel source|)*
      ∑ source,(FiniteDist.independent p).weight source*|kernel source| *f source^2 := by
    apply Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul
    · intro source _; exact mul_nonneg (FiniteDist.nonneg _ _) (abs_nonneg _)
    · intro source _; exact mul_nonneg (mul_nonneg (FiniteDist.nonneg _ _) (abs_nonneg _)) (sq_nonneg _)
    · intro source _
      ring_nf
      rw [sq_abs]
  apply hc.trans
  have hm : (∑ source,(FiniteDist.independent p).weight source*|kernel source|) ≤ 2^selected.card := by
    rw [← projectionMajorant_source p hp selected value]
    exact Finset.sum_le_sum fun source _ => mul_le_mul_of_nonneg_left (hk source) (FiniteDist.nonneg _ _)
  apply mul_le_mul hm
  · exact Finset.sum_le_sum fun source _ => mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hk source) (FiniteDist.nonneg _ _)) (sq_nonneg _)
  · exact Finset.sum_nonneg fun source _ => mul_nonneg
      (mul_nonneg (FiniteDist.nonneg _ _) (abs_nonneg _)) (sq_nonneg _)
  · positivity

theorem projectionMajorant_fixed_average (p : Slot → FiniteDist Color)
    (hp : ∀ slot color,0<(p slot).weight color) (selected : Finset Slot)
    (source values : Slot → Color) (fixed : Slot) :
    (∑ integrated,(FiniteDist.independent p).weight integrated*
      projectionMajorant p selected source (freeze {fixed} values integrated)) ≤
      2^selected.card*atomMajorant (p fixed) (source fixed) (values fixed) := by
  have he (integrated : Slot → Color) : projectionMajorant p selected source (freeze {fixed} values integrated) =
      ∏ slot ∈ selected,
        (if slot=fixed then atomMajorant (p slot) (source slot) (values slot)
          else atomMajorant (p slot) (source slot) (integrated slot)) := by
    apply Finset.prod_congr rfl
    intro slot _
    simp only [freeze,Finset.mem_singleton]
    split_ifs <;> rfl
  simp_rw [he]
  rw [expectation_partial_product p selected (fun slot color => if slot=fixed then
    atomMajorant (p slot) (source slot) (values slot) else atomMajorant (p slot) (source slot) color)]
  have ht (slot) : (∑ color,(p slot).weight color*
      (if slot=fixed then atomMajorant (p slot) (source slot) (values slot) else atomMajorant (p slot) (source slot) color)) =
      if slot=fixed then atomMajorant (p slot) (source slot) (values slot) else 2 := by
    split_ifs
    · rw [← Finset.sum_mul,FiniteDist.sum_one,one_mul]
    · exact atomMajorant_value _ (hp slot) _
  simp_rw [ht]
  by_cases hi : fixed ∈ selected
  · rw [← Finset.mul_prod_erase _ _ hi,if_pos rfl]
    have hr : (∏ slot ∈ selected.erase fixed,
        if slot=fixed then atomMajorant (p slot) (source slot) (values slot) else 2) = 2^(selected.erase fixed).card := by
      apply (Finset.prod_congr rfl ?_).trans (Finset.prod_const _)
      intro slot hs
      exact if_neg (Finset.mem_erase.mp hs).1
    rw [hr]
    have hpow : (2:ℝ)^(selected.erase fixed).card ≤ 2^selected.card :=
      pow_le_pow_right₀ (by norm_num) Finset.card_erase_le
    exact (mul_le_mul_of_nonneg_left hpow (atomMajorant_nonneg _ _ _)).trans_eq (mul_comm _ _)
  · have he : (∏ slot ∈ selected,
        if slot=fixed then atomMajorant (p slot) (source slot) (values slot) else 2) = 2^selected.card := by
      apply (Finset.prod_congr rfl ?_).trans (Finset.prod_const _)
      intro slot hs
      exact if_neg (by rintro rfl; exact hi hs)
    rw [he]
    exact le_mul_of_one_le_right (by positivity) (atomMajorant_one_le _ _ _)


theorem atomMajorant_square_average (p : Slot → FiniteDist Color)
    (hp : ∀ slot color,0<(p slot).weight color) (f : (Slot → Color) → ℝ)
    (values : Slot → Color) (fixed : Slot) :
    (∑ source,(FiniteDist.independent p).weight source*atomMajorant (p fixed) (source fixed) (values fixed)*f source^2) =
      (FiniteDist.independent p).l2Sq f+fiberSq p f {fixed} values := by
  cases Subsingleton.elim (inferInstance : DecidableEq Slot) (Classical.decEq Slot)
  have hfixed : (∑ source,(FiniteDist.independent p).weight source*
      (f source^2*(if source fixed=values fixed then ((p fixed).weight (values fixed))⁻¹ else 0))) =
      fiberSq p f {fixed} values := by
    change (FiniteDist.independent p).expectation _ = _
    rw [FiniteDist.expectation_independent_split,fiberSq_singleton_split]
    apply Finset.sum_congr rfl
    intro rest _
    congr 1
    have he (color : Color) : (p fixed).weight color*
        (f ((Equiv.funSplitAt fixed Color).symm (color,rest))^2*
          (if ((Equiv.funSplitAt fixed Color).symm (color,rest)) fixed=values fixed
            then ((p fixed).weight (values fixed))⁻¹ else 0)) =
        if color=values fixed then f ((Equiv.funSplitAt fixed Color).symm (values fixed,rest))^2 else 0 := by
      have hself : ((Equiv.funSplitAt fixed Color).symm (color,rest)) fixed=color := by
        simp [Equiv.funSplitAt,Equiv.piSplitAt]
      rw [hself]
      split_ifs with heq
      · subst color
        field_simp [(hp fixed (values fixed)).ne']
      · ring
    simp_rw [he]
    simp only [Finset.sum_ite_eq',Finset.mem_univ,if_true]
  have he (source) : (FiniteDist.independent p).weight source*atomMajorant (p fixed) (source fixed) (values fixed)*f source^2 =
      (FiniteDist.independent p).weight source*f source^2+
        (FiniteDist.independent p).weight source*(f source^2*
          (if source fixed=values fixed then ((p fixed).weight (values fixed))⁻¹ else 0)) := by
    unfold atomMajorant
    ring
  simp_rw [he]
  rw [Finset.sum_add_distrib,hfixed]
  rfl

/-- Sharp singleton fibers use the original full and singleton energies.
There is no inverse minimum-atom cost from canonical projection. -/
theorem projection_singleton_fiberSq_le (p : Slot → FiniteDist Color)
    (hp : ∀ slot color,0<(p slot).weight color) (selected : Finset Slot)
    (f : (Slot → Color) → ℝ) (fixed : Slot) (values : Slot → Color) :
    fiberSq p (Hoeffding.projection p selected f) {fixed} values ≤
      ((2:ℝ)^selected.card)^2*((FiniteDist.independent p).l2Sq f+fiberSq p f {fixed} values) := by
  calc
    _ ≤ ∑ integrated,(FiniteDist.independent p).weight integrated*((2:ℝ)^selected.card*
        ∑ source,(FiniteDist.independent p).weight source*
          projectionMajorant p selected source (freeze {fixed} values integrated)*f source^2) :=
      Finset.sum_le_sum fun integrated _ => mul_le_mul_of_nonneg_left
        (projection_square_majorant p hp selected f _) (FiniteDist.nonneg _ _)
    _ = (2:ℝ)^selected.card*∑ source,(FiniteDist.independent p).weight source*f source^2*
        ∑ integrated,(FiniteDist.independent p).weight integrated*
          projectionMajorant p selected source (freeze {fixed} values integrated) := by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro source _
      apply Finset.sum_congr rfl
      intro integrated _
      ring
    _ ≤ (2:ℝ)^selected.card*∑ source,(FiniteDist.independent p).weight source*f source^2*
        ((2:ℝ)^selected.card*atomMajorant (p fixed) (source fixed) (values fixed)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact Finset.sum_le_sum fun source _ => mul_le_mul_of_nonneg_left
        (projectionMajorant_fixed_average p hp selected source values fixed)
        (mul_nonneg (FiniteDist.nonneg _ _) (sq_nonneg _))
    _ = ((2:ℝ)^selected.card)^2*
        ∑ source,(FiniteDist.independent p).weight source*atomMajorant (p fixed) (source fixed) (values fixed)*f source^2 := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro source _
      ring
    _ = _ := by rw [atomMajorant_square_average p hp]

theorem projection_singleton_fiber_le (p : Slot → FiniteDist Color)
    (hp : ∀ slot color,0<(p slot).weight color) (selected : Finset Slot)
    (f : (Slot → Color) → ℝ) (fixed : Slot) (full single : ℝ)
    (hfull : 0 ≤ full) (hsingle : 0 ≤ single)
    (hf : (FiniteDist.independent p).l2Sq f ≤ full^2)
    (hs : ∀ values,fiberSq p f {fixed} values ≤ single^2) :
    fiberNorm p (Hoeffding.projection p selected f) {fixed} ≤ 2^selected.card*(full+single) := by
  apply (pi_norm_le_iff_of_nonneg (by positivity : 0 ≤ (2:ℝ)^selected.card*(full+single))).mpr
  intro values
  rw [Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _)]
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity,?_⟩
  apply (projection_singleton_fiberSq_le p hp selected f fixed values).trans
  have hsum : (FiniteDist.independent p).l2Sq f+fiberSq p f {fixed} values ≤ (full+single)^2 := by
    nlinarith [hf,hs values,mul_nonneg hfull hsingle]
  simpa only [mul_pow] using mul_le_mul_of_nonneg_left hsum (sq_nonneg ((2:ℝ)^selected.card))

theorem projection_sup_le (p : Slot → FiniteDist Color)
    (hp : ∀ slot color,0<(p slot).weight color) (selected : Finset Slot)
    (f : (Slot → Color) → ℝ) (bound : ℝ) (hb : 0 ≤ bound) (hf : ∀ value,|f value|≤bound) :
    ‖Hoeffding.projection p selected f‖ ≤ 2^selected.card*bound := by
  apply (pi_norm_le_iff_of_nonneg (by positivity : 0 ≤ (2:ℝ)^selected.card*bound)).mpr
  intro values
  rw [Real.norm_eq_abs]
  apply (sq_le_sq₀ (abs_nonneg _) (by positivity)).mp
  rw [sq_abs,mul_pow]
  apply (projection_square_majorant p hp selected f values).trans
  have hterm : (∑ source,(FiniteDist.independent p).weight source*projectionMajorant p selected source values*f source^2) ≤
      (2:ℝ)^selected.card*bound^2 := by
    rw [← projectionMajorant_source p hp selected values,Finset.sum_mul]
    apply Finset.sum_le_sum
    intro source _
    apply mul_le_mul_of_nonneg_left _
      (mul_nonneg (FiniteDist.nonneg _ _) (projectionMajorant_nonneg _ _ _ _))
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hb).mpr (hf source)
  exact (mul_le_mul_of_nonneg_left hterm (by positivity)).trans_eq (by ring)

end
end AFT.MixedKernel

namespace AFT.LocalTensors
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {Slot Color : Type*} [Fintype Slot] [DecidableEq Slot] [Fintype Color] [Nonempty Color]
local instance mixedCanonicalFibersSubtypeDecEq (selected : Finset Slot) : DecidableEq selected := Classical.decEq _

private def extendSelected (selected : Finset Slot) (values : selected → Color) : Slot → Color :=
  fun slot => if h : slot ∈ selected then values ⟨slot,h⟩ else Classical.choice inferInstance

omit [Fintype Slot] [Fintype Color] in
private theorem extendSelected_apply (selected : Finset Slot) (values : selected → Color) (slot : selected) :
    extendSelected selected values slot = values slot := by
  simp only [extendSelected,dif_pos slot.property]

/-- Lifting the selected arguments preserves the actual one-fixed fiber exactly. -/
theorem restrictedComponent_singleton_fiberSq_eq (p : Slot → FiniteDist Color)
    (mass : (Slot → Color) → ℝ) (selected : Finset Slot) (fixed : selected) (values : selected → Color) :
    MixedKernel.fiberSq (fun slot : selected => p slot) (restrictedComponent p mass selected) {fixed} values =
      MixedKernel.fiberSq p (Hoeffding.densityComponent p mass selected) {fixed.val} (extendSelected selected values) := by
  cases Subsingleton.elim (inferInstance : DecidableEq Slot) (Classical.decEq Slot)
  have he (integrated : Slot → Color) :
      restrictedComponent p mass selected (MixedKernel.freeze {fixed} values (fun slot : selected => integrated slot)) =
      Hoeffding.densityComponent p mass selected
        (MixedKernel.freeze {fixed.val} (extendSelected selected values) integrated) := by
    rw [← restrictedComponent_eq]
    congr 1
    funext slot
    have heq : (slot : Slot)=fixed.val ↔ slot=fixed := Subtype.ext_iff.symm
    simp only [MixedKernel.freeze,Finset.mem_singleton,heq]
    split_ifs
    · exact (extendSelected_apply selected values slot).symm
    · rfl
  have hh := independent_restriction_expectation p selected
    (fun word => restrictedComponent p mass selected (MixedKernel.freeze {fixed} values word)^2)
  simp_rw [he] at hh
  unfold MixedKernel.fiberSq FiniteDist.l2Sq
  convert hh.symm using 1
  unfold FiniteDist.expectation
  apply Finset.sum_congr (by ext; simp)
  intro word _
  rfl

omit [Nonempty Color] in
private theorem densityComponent_eq_projection (p : Slot → FiniteDist Color)
    (hp : ∀ slot color,0<(p slot).weight color) (mass : (Slot → Color) → ℝ) (selected : Finset Slot) :
    Hoeffding.densityComponent p mass selected =
      Hoeffding.projection p selected (fun word => mass word/(FiniteDist.independent p).weight word) := by
  cases Subsingleton.elim (inferInstance : DecidableEq Slot) (Classical.decEq Slot)
  have he : (fun word => (FiniteDist.independent p).weight word*(mass word/(FiniteDist.independent p).weight word)) = mass := by
    funext word
    have hpos : (FiniteDist.independent p).weight word ≠ 0 :=
      ne_of_gt (Finset.prod_pos fun slot _ => hp slot (word slot))
    field_simp
  change _ = Hoeffding.densityComponent p _ selected
  rw [he]

/-- The genuine restricted local coefficient inherits the sharp singleton
budget of its raw signed density, with no palette-dependent factor. -/
theorem restrictedComponent_singleton_sharp (p : Slot → FiniteDist Color)
    (hp : ∀ slot color,0<(p slot).weight color) (mass : (Slot → Color) → ℝ) (selected : Finset Slot)
    (full single : ℝ) (hfull : 0 ≤ full) (hsingle : 0 ≤ single)
    (hf : (FiniteDist.independent p).l2Sq (fun word => mass word/(FiniteDist.independent p).weight word) ≤ full^2)
    (hs : ∀ (fixed : Slot) values,MixedKernel.fiberSq p
      (fun word => mass word/(FiniteDist.independent p).weight word) {fixed} values ≤ single^2)
    (fixed : selected) :
    MixedKernel.fiberNorm (fun slot : selected => p slot) (restrictedComponent p mass selected) {fixed} ≤
      2^selected.card*(full+single) := by
  apply (pi_norm_le_iff_of_nonneg (by positivity : 0 ≤ (2:ℝ)^selected.card*(full+single))).mpr
  intro values
  rw [Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _)]
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity,?_⟩
  rw [restrictedComponent_singleton_fiberSq_eq,densityComponent_eq_projection p hp]
  apply (MixedKernel.projection_singleton_fiberSq_le p hp selected _ fixed.val _).trans
  have hsum : (FiniteDist.independent p).l2Sq (fun word => mass word/(FiniteDist.independent p).weight word)+
      MixedKernel.fiberSq p (fun word => mass word/(FiniteDist.independent p).weight word) {fixed.val}
        (extendSelected selected values) ≤ (full+single)^2 := by
    nlinarith [hf,hs fixed.val (extendSelected selected values),mul_nonneg hfull hsingle]
  simpa only [mul_pow] using mul_le_mul_of_nonneg_left hsum (sq_nonneg ((2:ℝ)^selected.card))

theorem restrictedComponent_sup_sharp (p : Slot → FiniteDist Color)
    (hp : ∀ slot color,0<(p slot).weight color) (mass : (Slot → Color) → ℝ) (selected : Finset Slot)
    (bound : ℝ) (hb : 0 ≤ bound)
    (hf : ∀ word,|mass word/(FiniteDist.independent p).weight word|≤bound) :
    ‖restrictedComponent p mass selected‖ ≤ 2^selected.card*bound := by
  apply (pi_norm_le_iff_of_nonneg (by positivity : 0 ≤ (2:ℝ)^selected.card*bound)).mpr
  intro values
  have he : restrictedComponent p mass selected values =
      Hoeffding.densityComponent p mass selected (extendSelected selected values) := by
    rw [← restrictedComponent_eq]
    congr 1
    funext slot
    exact (extendSelected_apply selected values slot).symm
  rw [he,densityComponent_eq_projection p hp]
  exact (norm_le_pi_norm _ _).trans (MixedKernel.projection_sup_le p hp selected _ bound hb hf)

end
end AFT.LocalTensors
