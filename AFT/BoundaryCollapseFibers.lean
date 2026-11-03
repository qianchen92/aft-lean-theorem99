import AFT.Inverse
import AFT.MixedCoordinateOperator

/-! # Boundary collapse contracts every genuine finite Hilbert fiber -/
namespace AFT
open scoped BigOperators Classical
noncomputable section
variable {Color Rest : Type*} [Fintype Color] [DecidableEq Color] [Fintype Rest]

omit [Fintype Color] [DecidableEq Color] in
private theorem boundaryAverage_square_le (interior : Finset Color) (primary value : Color → ℝ)
    (hp : ∀ color,0 ≤ primary color) (hmass : 0 < ∑ color ∈ interior,primary color) :
    ((∑ color ∈ interior,primary color*value color)/(∑ color ∈ interior,primary color))^2 ≤
      (∑ color ∈ interior,primary color*value color^2)/(∑ color ∈ interior,primary color) := by
  have hh : (∑ color ∈ interior,primary color*value color)^2 ≤
      (∑ color ∈ interior,primary color)*(∑ color ∈ interior,primary color*value color^2) := by
    apply Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul
    · intro color _; exact hp color
    · intro color _; exact mul_nonneg (hp color) (sq_nonneg _)
    · intro color _; ring
  rw [div_pow]
  apply (div_le_iff₀ (sq_pos_of_pos hmass)).mpr
  exact hh.trans_eq (by field_simp)

omit [Fintype Color] [Fintype Rest] in
/-- In density coordinates the interior is replaced by its conditional
weighted mean, while every boundary atom is retained exactly. -/
theorem partialProfileOperator_boundaryCollapse (interior : Finset Color) (primary : Color → ℝ)
    (hp : ∀ color,0<primary color) (kernel : Color → Rest → ℝ) (color : Color) (rest : Rest) :
    partialProfileOperator (boundaryCollapse interior primary) primary kernel color rest =
      if color ∈ interior then (∑ point ∈ interior,primary point*kernel point rest)/
        (∑ point ∈ interior,primary point) else kernel color rest := by
  unfold partialProfileOperator boundaryCollapse
  dsimp only [LinearMap.coe_mk,AddHom.coe_mk]
  split_ifs <;> field_simp [(hp color).ne']

omit [Fintype Rest] in
private theorem boundaryCollapse_density_energy_le (interior : Finset Color) (primary : Color → ℝ)
    (hp : ∀ color,0<primary color) (kernel : Color → Rest → ℝ) (rest : Rest)
    (hmass : 0 < ∑ color ∈ interior,primary color) :
    (∑ color,primary color*(partialProfileOperator (boundaryCollapse interior primary) primary kernel color rest)^2) ≤
      ∑ color,primary color*kernel color rest^2 := by
  have hinside : (∑ color ∈ interior,primary color*
      (partialProfileOperator (boundaryCollapse interior primary) primary kernel color rest)^2) ≤
      ∑ color ∈ interior,primary color*kernel color rest^2 := by
    have he : (∑ color ∈ interior,primary color*
        (partialProfileOperator (boundaryCollapse interior primary) primary kernel color rest)^2) =
        (∑ color ∈ interior,primary color)*
          ((∑ color ∈ interior,primary color*kernel color rest)/(∑ color ∈ interior,primary color))^2 := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro color hc
      rw [partialProfileOperator_boundaryCollapse interior primary hp,if_pos hc]
    rw [he]
    have hh := mul_le_mul_of_nonneg_left
      (boundaryAverage_square_le interior primary (fun color => kernel color rest) (fun color => (hp color).le) hmass) hmass.le
    exact hh.trans_eq (by field_simp)
  rw [← Finset.sum_filter_add_sum_filter_not (s := Finset.univ) (p := fun color => color ∈ interior),
    ← Finset.sum_filter_add_sum_filter_not (s := Finset.univ) (p := fun color => color ∈ interior)
      (f := fun color => primary color*kernel color rest^2)]
  have he : Finset.univ.filter (fun color => color ∈ interior)=interior := by ext; simp
  rw [he]
  apply add_le_add hinside
  apply Finset.sum_le_sum
  intro color hc
  have hout := (Finset.mem_filter.mp hc).2
  rw [partialProfileOperator_boundaryCollapse interior primary hp,if_neg hout]

/-- The integrated primary/remaining Hilbert norm contracts without any
normalization assumption on the remaining weights. -/
theorem boundaryCollapse_integratedFiber_le (interior : Finset Color) (primary : Color → ℝ)
    (remaining : Rest → ℝ) (hp : ∀ color,0<primary color) (hq : ∀ rest,0≤remaining rest)
    (hmass : 0 < ∑ color ∈ interior,primary color) (kernel : Color → Rest → ℝ) :
    integratedFiberNorm primary remaining (partialProfileOperator (boundaryCollapse interior primary) primary kernel) ≤
      integratedFiberNorm primary remaining kernel := by
  unfold integratedFiberNorm
  apply Real.sqrt_le_sqrt
  exact Finset.sum_le_sum fun rest _ => mul_le_mul_of_nonneg_left
    (boundaryCollapse_density_energy_le interior primary hp kernel rest hmass) (hq rest)

/-- Taking a conditional weighted average is also a contraction in the
supremum of all remaining-coordinate Hilbert fibers. -/
theorem boundaryCollapse_fixedFiber_le (interior : Finset Color) (primary : Color → ℝ)
    (remaining : Rest → ℝ) (hp : ∀ color,0<primary color) (hq : ∀ rest,0≤remaining rest)
    (hmass : 0 < ∑ color ∈ interior,primary color) (kernel : Color → Rest → ℝ) :
    fixedFiberNorm remaining (partialProfileOperator (boundaryCollapse interior primary) primary kernel) ≤
      fixedFiberNorm remaining kernel := by
  let bound := fixedFiberNorm remaining kernel
  have hbound : 0 ≤ bound := norm_nonneg _
  have hf (color) : (∑ rest,remaining rest*kernel color rest^2) ≤ bound^2 := by
    have hh := norm_le_pi_norm (fun color => Real.sqrt (∑ rest,remaining rest*kernel color rest^2)) color
    rw [Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _)] at hh
    have hn := Finset.sum_nonneg (s := Finset.univ) fun rest _ => mul_nonneg (hq rest) (sq_nonneg (kernel color rest))
    exact (Real.sq_sqrt hn).symm.trans_le ((sq_le_sq₀ (Real.sqrt_nonneg _) hbound).mpr hh)
  apply (pi_norm_le_iff_of_nonneg hbound).mpr
  intro color
  rw [Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _)]
  apply Real.sqrt_le_iff.mpr
  refine ⟨hbound,?_⟩
  by_cases hc : color ∈ interior
  · have hsum : (∑ rest,remaining rest*
        (partialProfileOperator (boundaryCollapse interior primary) primary kernel color rest)^2) ≤
        (∑ point ∈ interior,primary point*(∑ rest,remaining rest*kernel point rest^2))/
          (∑ point ∈ interior,primary point) := by
      calc
        _ ≤ ∑ rest,remaining rest*((∑ point ∈ interior,primary point*kernel point rest^2)/
            (∑ point ∈ interior,primary point)) := by
          apply Finset.sum_le_sum
          intro rest _
          rw [partialProfileOperator_boundaryCollapse interior primary hp,if_pos hc]
          exact mul_le_mul_of_nonneg_left
            (boundaryAverage_square_le interior primary (fun point => kernel point rest) (fun point => (hp point).le) hmass) (hq rest)
        _ = _ := by
          simp only [Finset.mul_sum,Finset.sum_div,mul_div_assoc]
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro point _
          apply Finset.sum_congr rfl
          intro rest _
          ring
    apply hsum.trans
    apply (div_le_iff₀ hmass).mpr
    calc
      _ ≤ ∑ point ∈ interior,primary point*bound^2 :=
        Finset.sum_le_sum fun point _ => mul_le_mul_of_nonneg_left (hf point) (hp point).le
      _ = _ := by rw [← Finset.sum_mul]; ring
  · simp_rw [partialProfileOperator_boundaryCollapse interior primary hp,if_neg hc]
    exact hf color

/-- This is the complete coordinate activity bound, including arbitrary
remaining Hilbert weights; both constituent fibers contract. -/
theorem boundaryCollapse_coordinateActivity_le (interior : Finset Color) (primary : Color → ℝ)
    (remaining : Rest → ℝ) (hp : ∀ color,0<primary color) (hq : ∀ rest,0≤remaining rest)
    (hmass : 0 < ∑ color ∈ interior,primary color) (rate : ℝ) (hrate : 0≤rate)
    (kernel : Color → Rest → ℝ) :
    coordinateActivity rate primary remaining (partialProfileOperator (boundaryCollapse interior primary) primary kernel) ≤
      coordinateActivity rate primary remaining kernel := by
  unfold coordinateActivity
  exact add_le_add
    (mul_le_mul_of_nonneg_left (boundaryCollapse_integratedFiber_le interior primary remaining hp hq hmass kernel) hrate)
    (mul_le_mul_of_nonneg_left (boundaryCollapse_fixedFiber_le interior primary remaining hp hq hmass kernel) (sq_nonneg rate))

end
end AFT

namespace AFT
open scoped BigOperators Classical
noncomputable section
variable {Color Rest : Type*} [Fintype Color] [DecidableEq Color] [Fintype Rest]

/-- The empty interior also contracts, because its collapse is the identity.
Thus the genuine coordinate contraction needs only positivity of the reference. -/
theorem boundaryCollapse_coordinateActivity_contracts (interior : Finset Color) (primary : Color → ℝ)
    (remaining : Rest → ℝ) (hp : ∀ color,0<primary color) (hq : ∀ rest,0≤remaining rest)
    (rate : ℝ) (hrate : 0≤rate) (kernel : Color → Rest → ℝ) :
    coordinateActivity rate primary remaining (partialProfileOperator (boundaryCollapse interior primary) primary kernel) ≤
      coordinateActivity rate primary remaining kernel := by
  by_cases hi : interior.Nonempty
  · have hm : 0 < ∑ color ∈ interior,primary color := Finset.sum_pos (fun color _ => hp color) hi
    exact boundaryCollapse_coordinateActivity_le interior primary remaining hp hq hm rate hrate kernel
  · have he : interior=∅ := Finset.not_nonempty_iff_eq_empty.mp hi
    have hf : partialProfileOperator (boundaryCollapse interior primary) primary kernel=kernel := by
      funext color rest
      rw [partialProfileOperator_boundaryCollapse interior primary hp,he,if_neg (Finset.notMem_empty _)]
    rw [hf]

end
end AFT

namespace AFT.MixedKernel
open scoped BigOperators Classical
noncomputable section
variable {Slot Color : Type*} [Fintype Slot] [DecidableEq Slot] [Fintype Color] [DecidableEq Color]

/-- Boundary collapse costs at most two in the complete literal mixed
activity; the factor comes only from pairing fixed-coordinate sets. -/
theorem boundaryCollapse_activity_le (reference : Slot → FiniteDist Color)
    (rates : Slot → ℝ) (hrates : ∀ slot,0≤rates slot) (slot : Slot) (hrate : 0<rates slot)
    (interior : Finset Color) (hp : ∀ color,0<(reference slot).weight color)
    (kernel : (Slot → Color) → ℝ) :
    activity rates reference (partialInputOperator slot
      (boundaryCollapse interior (reference slot).weight) (reference slot).weight kernel) ≤
      2*activity rates reference kernel := by
  apply (partialInputOperator_activity_le reference rates hrates slot hrate
    (boundaryCollapse interior (reference slot).weight) 1 (by norm_num) ?_ kernel).trans_eq (by ring)
  intro fiber
  simpa only [one_mul] using boundaryCollapse_coordinateActivity_contracts interior (reference slot).weight
    (FiniteDist.independent (fun other : {other : Slot // other ≠ slot} => reference other)).weight
    hp (FiniteDist.nonneg _) (rates slot) hrate.le fiber

end
end AFT.MixedKernel
