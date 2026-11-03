import AFT.MixedCanonicalFibers

/-! # Centering at one reference and measuring fibers at another

These are the actual coefficients with atoms `δ - r`, divided by `p`.
Only the upper comparison `r ≤ R p` is used; no lower comparison or inverse
minimum atom enters the full, singleton, or supremum bounds.
-/
namespace AFT.MixedKernel
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {Slot Color : Type*} [Fintype Slot] [DecidableEq Slot] [Fintype Color]

def referenceAtom (p r : FiniteDist Color) (source value : Color) : ℝ :=
  (if source=value then (p.weight value)⁻¹ else 0)-r.weight value/p.weight value

def referenceProjection (p r : Slot → FiniteDist Color) (selected : Finset Slot)
    (f : (Slot → Color) → ℝ) (value : Slot → Color) : ℝ :=
  ∑ source,(FiniteDist.independent p).weight source*f source*
    ∏ slot ∈ selected,referenceAtom (p slot) (r slot) (source slot) (value slot)

theorem referenceAtom_eq (p r : FiniteDist Color) (source value : Color) :
    referenceAtom p r source value = ((if source=value then 1 else 0)-r.weight value)/p.weight value := by
  unfold referenceAtom
  split_ifs <;> simp [sub_div,neg_div]

theorem referenceAtom_mean (p r : FiniteDist Color) (hp : ∀ color,0<p.weight color) (source : Color) :
    (∑ value,p.weight value*referenceAtom p r source value)=0 := by
  have he (value : Color) : p.weight value*referenceAtom p r source value =
      (if source=value then 1 else 0)-r.weight value := by
    rw [referenceAtom_eq]
    field_simp [(hp value).ne']
  simp_rw [he]
  simp only [Finset.sum_sub_distrib,r.sum_one]
  simp

theorem referenceAtom_abs_le (p r : FiniteDist Color) (hp : ∀ color,0<p.weight color)
    (bound : ℝ) (hb : 1 ≤ bound) (hr : ∀ color,r.weight color ≤ bound*p.weight color)
    (source value : Color) : |referenceAtom p r source value| ≤ bound*atomMajorant p source value := by
  have hd : 0 ≤ r.weight value/p.weight value := div_nonneg (r.nonneg value) (hp value).le
  have hu : r.weight value/p.weight value ≤ bound := (div_le_iff₀ (hp value)).mpr (hr value)
  unfold referenceAtom atomMajorant
  split_ifs
  · have hi : 0 ≤ (p.weight value)⁻¹ := inv_nonneg.mpr (hp value).le
    apply (abs_sub _ _).trans
    rw [abs_of_nonneg hi,abs_of_nonneg hd]
    nlinarith
  · simpa only [zero_sub,abs_neg,abs_of_nonneg hd,zero_add,mul_one] using hu

theorem referenceProjection_square_majorant (p r : Slot → FiniteDist Color)
    (hp : ∀ slot color,0<(p slot).weight color) (selected : Finset Slot)
    (f : (Slot → Color) → ℝ) (bound : ℝ) (hb : 1 ≤ bound)
    (hr : ∀ slot color,(r slot).weight color ≤ bound*(p slot).weight color) (value : Slot → Color) :
    referenceProjection p r selected f value^2 ≤ bound^(2*selected.card)*(2:ℝ)^selected.card*
      ∑ source,(FiniteDist.independent p).weight source*projectionMajorant p selected source value*f source^2 := by
  let kernel (source : Slot → Color) := ∏ slot ∈ selected,referenceAtom (p slot) (r slot) (source slot) (value slot)
  have hk (source) : |kernel source| ≤ bound^selected.card*projectionMajorant p selected source value := by
    dsimp only [kernel]
    rw [Finset.abs_prod]
    exact (Finset.prod_le_prod (fun _ _ => abs_nonneg _)
      (fun slot _ => referenceAtom_abs_le _ _ (hp slot) bound hb (hr slot) _ _)).trans_eq
      (by rw [Finset.prod_mul_distrib,Finset.prod_const]; rfl)
  have hc : (∑ source,(FiniteDist.independent p).weight source*f source*kernel source)^2 ≤
      (∑ source,(FiniteDist.independent p).weight source*|kernel source|)*
      ∑ source,(FiniteDist.independent p).weight source*|kernel source| *f source^2 := by
    apply Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul
    · intro source _; exact mul_nonneg (FiniteDist.nonneg _ _) (abs_nonneg _)
    · intro source _; exact mul_nonneg (mul_nonneg (FiniteDist.nonneg _ _) (abs_nonneg _)) (sq_nonneg _)
    · intro source _; ring_nf; rw [sq_abs]
  have hm : (∑ source,(FiniteDist.independent p).weight source*|kernel source|) ≤
      bound^selected.card*(2:ℝ)^selected.card := by
    rw [← projectionMajorant_source p hp selected value,Finset.mul_sum]
    apply Finset.sum_le_sum
    intro source _
    exact (mul_le_mul_of_nonneg_left (hk source) (FiniteDist.nonneg _ _)).trans_eq (by ring)
  have hs : (∑ source,(FiniteDist.independent p).weight source*|kernel source| *f source^2) ≤
      bound^selected.card*∑ source,(FiniteDist.independent p).weight source*
        projectionMajorant p selected source value*f source^2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro source _
    exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hk source)
      (FiniteDist.nonneg _ _)) (sq_nonneg _)).trans_eq (by ring)
  apply hc.trans
  apply (mul_le_mul hm hs
    (Finset.sum_nonneg fun source _ => mul_nonneg (mul_nonneg (FiniteDist.nonneg _ _) (abs_nonneg _)) (sq_nonneg _))
    (by positivity)).trans_eq
  rw [pow_mul]
  ring

theorem referenceProjection_singleton_fiberSq_le (p r : Slot → FiniteDist Color)
    (hp : ∀ slot color,0<(p slot).weight color) (selected : Finset Slot)
    (f : (Slot → Color) → ℝ) (bound : ℝ) (hb : 1 ≤ bound)
    (hr : ∀ slot color,(r slot).weight color ≤ bound*(p slot).weight color)
    (fixed : Slot) (values : Slot → Color) :
    fiberSq p (referenceProjection p r selected f) {fixed} values ≤
      ((2*bound)^selected.card)^2*((FiniteDist.independent p).l2Sq f+fiberSq p f {fixed} values) := by
  have hb0 : 0 ≤ bound := le_trans (by norm_num) hb
  calc
    _ ≤ ∑ integrated,(FiniteDist.independent p).weight integrated*(bound^(2*selected.card)*(2:ℝ)^selected.card*
        ∑ source,(FiniteDist.independent p).weight source*
          projectionMajorant p selected source (freeze {fixed} values integrated)*f source^2) :=
      Finset.sum_le_sum fun integrated _ => mul_le_mul_of_nonneg_left
        (referenceProjection_square_majorant p r hp selected f bound hb hr _) (FiniteDist.nonneg _ _)
    _ = bound^(2*selected.card)*(2:ℝ)^selected.card*∑ source,(FiniteDist.independent p).weight source*f source^2*
        ∑ integrated,(FiniteDist.independent p).weight integrated*
          projectionMajorant p selected source (freeze {fixed} values integrated) := by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro source _
      apply Finset.sum_congr rfl
      intro integrated _
      ring
    _ ≤ bound^(2*selected.card)*(2:ℝ)^selected.card*∑ source,(FiniteDist.independent p).weight source*f source^2*
        ((2:ℝ)^selected.card*atomMajorant (p fixed) (source fixed) (values fixed)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact Finset.sum_le_sum fun source _ => mul_le_mul_of_nonneg_left
        (projectionMajorant_fixed_average p hp selected source values fixed)
        (mul_nonneg (FiniteDist.nonneg _ _) (sq_nonneg _))
    _ = ((2*bound)^selected.card)^2*
        ∑ source,(FiniteDist.independent p).weight source*atomMajorant (p fixed) (source fixed) (values fixed)*f source^2 := by
      simp only [Finset.mul_sum,mul_pow,pow_mul]
      apply Finset.sum_congr rfl
      intro source _
      ring
    _ = _ := by rw [atomMajorant_square_average p hp]

theorem referenceProjection_sup_le (p r : Slot → FiniteDist Color)
    (hp : ∀ slot color,0<(p slot).weight color) (selected : Finset Slot)
    (f : (Slot → Color) → ℝ) (comparison bound : ℝ) (hc : 1 ≤ comparison)
    (hr : ∀ slot color,(r slot).weight color ≤ comparison*(p slot).weight color)
    (hb : 0 ≤ bound) (hf : ∀ value,|f value|≤bound) :
    ‖referenceProjection p r selected f‖ ≤ (2*comparison)^selected.card*bound := by
  have hc0 : 0 ≤ comparison := le_trans (by norm_num) hc
  apply (pi_norm_le_iff_of_nonneg (by positivity : 0 ≤ (2*comparison)^selected.card*bound)).mpr
  intro values
  rw [Real.norm_eq_abs]
  apply (sq_le_sq₀ (abs_nonneg _) (by positivity)).mp
  rw [sq_abs,mul_pow]
  apply (referenceProjection_square_majorant p r hp selected f comparison hc hr values).trans
  have hterm : (∑ source,(FiniteDist.independent p).weight source*projectionMajorant p selected source values*f source^2) ≤
      (2:ℝ)^selected.card*bound^2 := by
    rw [← projectionMajorant_source p hp selected values,Finset.sum_mul]
    apply Finset.sum_le_sum
    intro source _
    apply mul_le_mul_of_nonneg_left _
      (mul_nonneg (FiniteDist.nonneg _ _) (projectionMajorant_nonneg _ _ _ _))
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hb).mpr (hf source)
  exact (mul_le_mul_of_nonneg_left hterm (by positivity)).trans_eq (by simp only [mul_pow,pow_mul]; ring)

theorem referenceProjection_l2Sq_le (p r : Slot → FiniteDist Color)
    (hp : ∀ slot color,0<(p slot).weight color) (selected : Finset Slot)
    (f : (Slot → Color) → ℝ) (bound : ℝ) (hb : 1 ≤ bound)
    (hr : ∀ slot color,(r slot).weight color ≤ bound*(p slot).weight color) :
    (FiniteDist.independent p).l2Sq (referenceProjection p r selected f) ≤
      ((2*bound)^selected.card)^2*(FiniteDist.independent p).l2Sq f := by
  have hb0 : 0 ≤ bound := le_trans (by norm_num) hb
  have hm (source : Slot → Color) :
      (∑ value,(FiniteDist.independent p).weight value*projectionMajorant p selected source value) =
      (2:ℝ)^selected.card := by
    unfold projectionMajorant
    rw [expectation_partial_product p selected (fun slot value => atomMajorant (p slot) (source slot) value)]
    simp only [atomMajorant_value _ (hp _),Finset.prod_const]
  calc
    _ ≤ ∑ value,(FiniteDist.independent p).weight value*(bound^(2*selected.card)*(2:ℝ)^selected.card*
        ∑ source,(FiniteDist.independent p).weight source*projectionMajorant p selected source value*f source^2) :=
      Finset.sum_le_sum fun value _ => mul_le_mul_of_nonneg_left
        (referenceProjection_square_majorant p r hp selected f bound hb hr value) (FiniteDist.nonneg _ _)
    _ = bound^(2*selected.card)*(2:ℝ)^selected.card*∑ source,(FiniteDist.independent p).weight source*f source^2*
        ∑ value,(FiniteDist.independent p).weight value*projectionMajorant p selected source value := by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro source _
      apply Finset.sum_congr rfl
      intro value _
      ring
    _ = _ := by
      simp_rw [hm]
      rw [← Finset.sum_mul]
      simp only [FiniteDist.l2Sq,FiniteDist.expectation,mul_pow]
      rw [Nat.mul_comm 2 selected.card,pow_mul]
      ring

end
end AFT.MixedKernel

namespace AFT.LocalTensors
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {Slot Color : Type*} [Fintype Slot] [DecidableEq Slot] [Fintype Color]
local instance mixedReferenceCanonicalFibersSubtypeDecEq (selected : Finset Slot) : DecidableEq selected := Classical.decEq _

/-- The literal selected coefficient centered at `r`, expressed as a density
relative to `p` on precisely the selected slots. -/
def referenceRestrictedComponent (p r : Slot → FiniteDist Color)
    (mass : (Slot → Color) → ℝ) (selected : Finset Slot) (word : selected → Color) : ℝ :=
  ∑ input,mass input*∏ slot : selected,MixedKernel.referenceAtom (p slot) (r slot) (input slot) (word slot)

theorem referenceRestrictedComponent_canonical (p r : Slot → FiniteDist Color)
    (hp : ∀ slot color,0<(p slot).weight color) (mass : (Slot → Color) → ℝ) (selected : Finset Slot) :
    Hoeffding.Canonical (fun slot : selected => p slot) Finset.univ
      (referenceRestrictedComponent p r mass selected) := by
  constructor
  · intro first second heq
    have heq : first=second := funext (fun slot => heq slot (Finset.mem_univ slot))
    rw [heq]
  · intro fixed _ values
    simp only [referenceRestrictedComponent,Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro source _
    have hprod (color : Color) :
        (∏ slot : selected,MixedKernel.referenceAtom (p slot) (r slot) (source slot) (Function.update values fixed color slot)) =
          MixedKernel.referenceAtom (p fixed) (r fixed) (source fixed) color*
            ∏ slot ∈ Finset.univ.erase fixed,MixedKernel.referenceAtom (p slot) (r slot) (source slot) (values slot) := by
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ fixed),Function.update_self]
      congr 1
      apply Finset.prod_congr rfl
      intro slot hs
      rw [Function.update_of_ne (Finset.mem_erase.mp hs).1]
    simp_rw [hprod]
    have hterm (color : Color) : (p fixed).weight color*(mass source*
        (MixedKernel.referenceAtom (p fixed) (r fixed) (source fixed) color*
          ∏ slot ∈ Finset.univ.erase fixed,MixedKernel.referenceAtom (p slot) (r slot) (source slot) (values slot))) =
        (mass source*∏ slot ∈ Finset.univ.erase fixed,MixedKernel.referenceAtom (p slot) (r slot) (source slot) (values slot))*
          ((p fixed).weight color*MixedKernel.referenceAtom (p fixed) (r fixed) (source fixed) color) := by ring
    simp_rw [hterm]
    rw [← Finset.mul_sum,MixedKernel.referenceAtom_mean _ _ (hp fixed),mul_zero]

theorem referenceRestrictedComponent_eq (p r : Slot → FiniteDist Color)
    (hp : ∀ slot color,0<(p slot).weight color) (mass : (Slot → Color) → ℝ)
    (selected : Finset Slot) (word : Slot → Color) :
    referenceRestrictedComponent p r mass selected (fun slot => word slot) =
      MixedKernel.referenceProjection p r selected
        (fun source => mass source/(FiniteDist.independent p).weight source) word := by
  unfold referenceRestrictedComponent MixedKernel.referenceProjection
  apply Finset.sum_congr rfl
  intro source _
  have hpos : (FiniteDist.independent p).weight source ≠ 0 :=
    ne_of_gt (Finset.prod_pos fun slot _ => hp slot (source slot))
  rw [mul_div_cancel₀ _ hpos]
  congr 1
  exact Finset.prod_coe_sort selected (fun slot => MixedKernel.referenceAtom (p slot) (r slot) (source slot) (word slot))

/-- The definition is exactly the `r`-canonical physical coefficient, with
the product `r/p` required when its norm is measured under `p`. -/
theorem referenceRestrictedComponent_change_reference (p r : Slot → FiniteDist Color)
    (hp : ∀ slot color,0<(p slot).weight color) (hr : ∀ slot color,0<(r slot).weight color)
    (mass : (Slot → Color) → ℝ) (selected : Finset Slot) (word : selected → Color) :
    referenceRestrictedComponent p r mass selected word =
      restrictedComponent r mass selected word * ∏ slot : selected,(r slot).weight (word slot)/(p slot).weight (word slot) := by
  cases Subsingleton.elim (inferInstance : DecidableEq Slot) (Classical.decEq Slot)
  unfold referenceRestrictedComponent restrictedComponent
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro source _
  rw [mul_assoc,← Finset.prod_mul_distrib]
  congr 1
  apply Finset.prod_congr rfl
  intro slot _
  unfold MixedKernel.referenceAtom Hoeffding.centeredAtom
  split_ifs
  · field_simp [(hp slot (word slot)).ne',(hr slot (word slot)).ne']
  · field_simp [(hp slot (word slot)).ne',(hr slot (word slot)).ne']
    ring

theorem referenceRestrictedComponent_l2Sq_le (p r : Slot → FiniteDist Color)
    (hp : ∀ slot color,0<(p slot).weight color) (mass : (Slot → Color) → ℝ)
    (selected : Finset Slot) (bound : ℝ) (hb : 1 ≤ bound)
    (hr : ∀ slot color,(r slot).weight color ≤ bound*(p slot).weight color) :
    (FiniteDist.independent (fun slot : selected => p slot)).l2Sq (referenceRestrictedComponent p r mass selected) ≤
      ((2*bound)^selected.card)^2*(FiniteDist.independent p).l2Sq
        (fun source => mass source/(FiniteDist.independent p).weight source) := by
  cases Subsingleton.elim (inferInstance : DecidableEq Slot) (Classical.decEq Slot)
  have hh := independent_restriction_expectation p selected
    (fun word => referenceRestrictedComponent p r mass selected word^2)
  simp_rw [referenceRestrictedComponent_eq p r hp] at hh
  have he : (FiniteDist.independent (fun slot : selected => p slot)).l2Sq (referenceRestrictedComponent p r mass selected) =
      (FiniteDist.independent p).l2Sq (MixedKernel.referenceProjection p r selected
        (fun source => mass source/(FiniteDist.independent p).weight source)) := by
    convert hh.symm using 1
    all_goals
      unfold FiniteDist.l2Sq FiniteDist.expectation
      apply Finset.sum_congr (by ext; simp)
      intro word _
      rfl
  rw [he]
  exact MixedKernel.referenceProjection_l2Sq_le p r hp selected _ bound hb hr

variable [Nonempty Color]

private def referenceExtend (selected : Finset Slot) (values : selected → Color) : Slot → Color :=
  fun slot => if h : slot ∈ selected then values ⟨slot,h⟩ else Classical.choice inferInstance

omit [Fintype Slot] [Fintype Color] in
private theorem referenceExtend_apply (selected : Finset Slot) (values : selected → Color) (slot : selected) :
    referenceExtend selected values slot = values slot := by simp only [referenceExtend,dif_pos slot.property]

theorem referenceRestrictedComponent_singleton_fiberSq_eq (p r : Slot → FiniteDist Color)
    (hp : ∀ slot color,0<(p slot).weight color) (mass : (Slot → Color) → ℝ)
    (selected : Finset Slot) (fixed : selected) (values : selected → Color) :
    MixedKernel.fiberSq (fun slot : selected => p slot) (referenceRestrictedComponent p r mass selected) {fixed} values =
      MixedKernel.fiberSq p (MixedKernel.referenceProjection p r selected
        (fun source => mass source/(FiniteDist.independent p).weight source)) {fixed.val} (referenceExtend selected values) := by
  cases Subsingleton.elim (inferInstance : DecidableEq Slot) (Classical.decEq Slot)
  have he (integrated : Slot → Color) :
      referenceRestrictedComponent p r mass selected (MixedKernel.freeze {fixed} values (fun slot : selected => integrated slot)) =
      MixedKernel.referenceProjection p r selected (fun source => mass source/(FiniteDist.independent p).weight source)
        (MixedKernel.freeze {fixed.val} (referenceExtend selected values) integrated) := by
    rw [← referenceRestrictedComponent_eq p r hp]
    congr 1
    funext slot
    have heq : (slot : Slot)=fixed.val ↔ slot=fixed := Subtype.ext_iff.symm
    simp only [MixedKernel.freeze,Finset.mem_singleton,heq]
    split_ifs
    · exact (referenceExtend_apply selected values slot).symm
    · rfl
  have hh := independent_restriction_expectation p selected
    (fun word => referenceRestrictedComponent p r mass selected (MixedKernel.freeze {fixed} values word)^2)
  simp_rw [he] at hh
  unfold MixedKernel.fiberSq FiniteDist.l2Sq
  convert hh.symm using 1
  unfold FiniteDist.expectation
  apply Finset.sum_congr (by ext; simp)
  intro word _
  rfl

theorem referenceRestrictedComponent_singleton_sharp (p r : Slot → FiniteDist Color)
    (hp : ∀ slot color,0<(p slot).weight color) (mass : (Slot → Color) → ℝ) (selected : Finset Slot)
    (comparison full single : ℝ) (hc : 1 ≤ comparison)
    (hr : ∀ slot color,(r slot).weight color ≤ comparison*(p slot).weight color)
    (hfull : 0 ≤ full) (hsingle : 0 ≤ single)
    (hf : (FiniteDist.independent p).l2Sq (fun source => mass source/(FiniteDist.independent p).weight source) ≤ full^2)
    (hs : ∀ (fixed : Slot) values,MixedKernel.fiberSq p
      (fun source => mass source/(FiniteDist.independent p).weight source) {fixed} values ≤ single^2)
    (fixed : selected) :
    MixedKernel.fiberNorm (fun slot : selected => p slot) (referenceRestrictedComponent p r mass selected) {fixed} ≤
      (2*comparison)^selected.card*(full+single) := by
  have hc0 : 0 ≤ comparison := le_trans (by norm_num) hc
  apply (pi_norm_le_iff_of_nonneg (by positivity : 0 ≤ (2*comparison)^selected.card*(full+single))).mpr
  intro values
  rw [Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _)]
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity,?_⟩
  rw [referenceRestrictedComponent_singleton_fiberSq_eq p r hp]
  apply (MixedKernel.referenceProjection_singleton_fiberSq_le p r hp selected _ comparison hc hr fixed.val _).trans
  have hsum : (FiniteDist.independent p).l2Sq (fun source => mass source/(FiniteDist.independent p).weight source)+
      MixedKernel.fiberSq p (fun source => mass source/(FiniteDist.independent p).weight source) {fixed.val}
        (referenceExtend selected values) ≤ (full+single)^2 := by
    nlinarith [hf,hs fixed.val (referenceExtend selected values),mul_nonneg hfull hsingle]
  simpa only [mul_pow] using mul_le_mul_of_nonneg_left hsum (sq_nonneg ((2*comparison)^selected.card))

theorem referenceRestrictedComponent_sup_sharp (p r : Slot → FiniteDist Color)
    (hp : ∀ slot color,0<(p slot).weight color) (mass : (Slot → Color) → ℝ) (selected : Finset Slot)
    (comparison bound : ℝ) (hc : 1 ≤ comparison)
    (hr : ∀ slot color,(r slot).weight color ≤ comparison*(p slot).weight color)
    (hb : 0 ≤ bound) (hf : ∀ source,|mass source/(FiniteDist.independent p).weight source|≤bound) :
    ‖referenceRestrictedComponent p r mass selected‖ ≤ (2*comparison)^selected.card*bound := by
  have hc0 : 0 ≤ comparison := le_trans (by norm_num) hc
  apply (pi_norm_le_iff_of_nonneg (by positivity : 0 ≤ (2*comparison)^selected.card*bound)).mpr
  intro values
  have he : referenceRestrictedComponent p r mass selected values =
      MixedKernel.referenceProjection p r selected (fun source => mass source/(FiniteDist.independent p).weight source)
        (referenceExtend selected values) := by
    rw [← referenceRestrictedComponent_eq p r hp]
    congr 1
    funext slot
    exact (referenceExtend_apply selected values slot).symm
  rw [he]
  exact (norm_le_pi_norm _ _).trans (MixedKernel.referenceProjection_sup_le p r hp selected _ comparison bound hc hr hb hf)

end
end AFT.LocalTensors
