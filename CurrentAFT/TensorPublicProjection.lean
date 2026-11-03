import CurrentAFT.PositivePublicChannels

/-! # Exact removal of unused coordinates in the common control alphabet -/
namespace CurrentAFT.TensorPublicProjection
open AFT JointTaggedPhysicalFock
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
local instance finDecEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _

theorem single_one_canonical {Color : Type*} [DecidableEq Color] (point : Color) :
    (Pi.single point (1 : ℝ) : Color → ℝ) =
      fun value => @ite ℝ (value = point) (Classical.propDecidable _) 1 0 := by
  funext value
  by_cases hequal : value = point <;> simp [Pi.single_apply, hequal]

theorem independent_decision_expectation {Index Color : Type*} [Fintype Index] [Fintype Color]
    (first second : DecidableEq Index) (law : Index → FiniteDist Color) (value : (Index → Color) → ℝ) :
    @FiniteDist.expectation (Index → Color) (@Pi.instFintype Index (fun _ => Color) first _ (fun _ => inferInstance))
      (@FiniteDist.independent Color Index _ _ first law) value =
    @FiniteDist.expectation (Index → Color) (@Pi.instFintype Index (fun _ => Color) second _ (fun _ => inferInstance))
      (@FiniteDist.independent Color Index _ _ second law) value := by
  cases Subsingleton.elim first second
  rfl

section Generic
variable {Index Primary Body : Type*} [Fintype Index] [Fintype Primary] [Fintype Body]
  [DecidableEq Index]

theorem sum_pair_left (body : FiniteDist Body) (value : (Index → Primary) → ℝ) :
    (∑ word : Index → Primary × Body, value (fun index => (word index).1) *
      ∏ index, body.weight (word index).2) = ∑ word, value word := by
  rw [← (Equiv.arrowProdEquivProdArrow Index (fun _ => Primary) (fun _ => Body)).symm.sum_comp,
    Fintype.sum_prod_type]
  simp only [Equiv.arrowProdEquivProdArrow, Equiv.coe_fn_symm_mk]
  apply Finset.sum_congr rfl
  intro primary _
  rw [← Finset.mul_sum]
  have hsum := (FiniteDist.independent (fun _ : Index => body)).sum_one
  change (∑ word : Index → Body, ∏ index, body.weight (word index)) = 1 at hsum
  rw [hsum, mul_one]

theorem sum_pair_right (primary : FiniteDist Primary) (value : (Index → Body) → ℝ) :
    (∑ word : Index → Primary × Body, value (fun index => (word index).2) *
      ∏ index, primary.weight (word index).1) = ∑ word, value word := by
  rw [← (Equiv.arrowProdEquivProdArrow Index (fun _ => Primary) (fun _ => Body)).symm.sum_comp,
    Fintype.sum_prod_type, Finset.sum_comm]
  simp only [Equiv.arrowProdEquivProdArrow, Equiv.coe_fn_symm_mk]
  apply Finset.sum_congr rfl
  intro body _
  rw [← Finset.mul_sum]
  have hsum := (FiniteDist.independent (fun _ : Index => primary)).sum_one
  change (∑ word : Index → Primary, ∏ index, primary.weight (word index)) = 1 at hsum
  rw [hsum, mul_one]

omit [Fintype Body] [DecidableEq Index] in
theorem prod_single (source target : Index → Body) :
    (∏ index, (Pi.single (source index) (1 : ℝ) : Body → ℝ) (target index)) =
      if source = target then 1 else 0 := by
  by_cases hequal : source = target
  · subst source
    simp
  · obtain ⟨index, hindex⟩ : ∃ index, source index ≠ target index :=
      not_forall.mp (fun h => hequal (funext h))
    rw [if_neg hequal]
    apply Finset.prod_eq_zero (Finset.mem_univ index)
    simp [Ne.symm hindex]

theorem sum_single_product (value : (Index → Body) → ℝ) (target : Index → Body) :
    (∑ source, value source * ∏ index,
      (Pi.single (source index) (1 : ℝ) : Body → ℝ) (target index)) = value target := by
  simp only [prod_single, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]

omit [Fintype Primary] in
theorem reducePrimary_single (body : FiniteDist Body) (point : Primary × Body) :
    reducePrimary body (Pi.single point (1 : ℝ)) = body.weight point.2 • (Pi.single point.1 (1 : ℝ) : Primary → ℝ) := by
  rcases point with ⟨first, second⟩
  funext primary
  simp only [reducePrimary, LinearMap.coe_mk, AddHom.coe_mk, FiniteDist.expectation,
    Pi.smul_apply, smul_eq_mul, Pi.single_apply]
  by_cases hequal : primary = first
  · subst primary
    simp only [Prod.mk.injEq, true_and, ite_true]
    simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, mul_one]
  · have hpoint (other : Body) : (primary, other) ≠ (first, second) := fun h => hequal (congrArg Prod.fst h)
    simp [hpoint, hequal]

omit [Fintype Body] in
theorem reduceBody_single (primary : FiniteDist Primary) (point : Primary × Body) :
    reduceBody primary (Pi.single point (1 : ℝ)) = primary.weight point.1 • (Pi.single point.2 (1 : ℝ) : Body → ℝ) := by
  rcases point with ⟨first, second⟩
  funext body
  simp only [reduceBody, LinearMap.coe_mk, AddHom.coe_mk, FiniteDist.expectation,
    Pi.smul_apply, smul_eq_mul, Pi.single_apply]
  by_cases hequal : body = second
  · subst body
    simp only [Prod.mk.injEq, and_true, ite_true]
    simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, mul_one]
  · have hpoint (other : Primary) : (other, body) ≠ (first, second) := fun h => hequal (congrArg Prod.snd h)
    simp [hpoint, hequal]

end Generic

theorem sum_reindex {First Second Color : Type*} [Fintype First] [Fintype Second]
    [Fintype Color] [DecidableEq First] [DecidableEq Second]
    (equiv : First ≃ Second) (kernel : (First → Color) → ℝ) (factor : First → Color → ℝ) :
    (∑ word : Second → Color, kernel (word ∘ equiv) *
      ∏ index, factor (equiv.symm index) (word index)) =
      ∑ word : First → Color, kernel word * ∏ index, factor index (word index) := by
  let words : (First → Color) ≃ (Second → Color) :=
    { toFun := fun word => word ∘ equiv.symm
      invFun := fun word => word ∘ equiv
      left_inv := fun word => funext (fun index => by simp)
      right_inv := fun word => funext (fun index => by simp) }
  rw [← words.sum_comp]
  apply Finset.sum_congr rfl
  intro word _
  have hword : (words word) ∘ equiv = word := by funext index; simp [words]
  rw [hword]
  congr 1
  exact equiv.symm.prod_comp (fun index => factor index (word index))

section TwoPools
variable {Primary Body Public : Type*} [Fintype Primary] [Fintype Body] [Fintype Public]

omit [Fintype Public] in
/-- Augmenting the two original alphabets by independent unused coordinates
and reducing them locally leaves the complete paired tensor exactly intact. -/
theorem paired_projection (primary : FiniteDist Primary) (body : FiniteDist Body)
    (r s : ℕ) (channel : (Primary → ℝ) →ₗ[ℝ] (Public → ℝ))
    (kernel : (Fin r → Primary) → (Fin s → Body) → ℝ)
    (groups : Fin r → Public) (centers : Fin s → Body) :
    (∑ word : (Fin r ⊕ Fin s) → Primary × Body,
      kernel (fun index => (word (.inl index)).1) (fun index => (word (.inr index)).2) *
        (∏ index, channel (reducePrimary body (Pi.single (word (.inl index)) 1)) (groups index)) *
        ∏ index, reduceBody primary (Pi.single (word (.inr index)) 1) (centers index)) =
      TensorChannel.apply r (fun _ => channel) (fun colors => kernel colors centers) groups := by
  rw [← (Equiv.sumArrowEquivProdArrow (Fin r) (Fin s) (Primary × Body)).symm.sum_comp,
    Fintype.sum_prod_type]
  simp only [Equiv.sumArrowEquivProdArrow, Equiv.coe_fn_symm_mk, Sum.elim_inl, Sum.elim_inr,
    reducePrimary_single, reduceBody_single, map_smul, Pi.smul_apply, smul_eq_mul,
    Finset.prod_mul_distrib]
  have hright (left : Fin r → Primary × Body) :
      (∑ right : Fin s → Primary × Body,
        kernel (fun index => (left index).1) (fun index => (right index).2) *
          ((∏ index, body.weight (left index).2) *
            ∏ index, channel (Pi.single (left index).1 1) (groups index)) *
          ((∏ index, primary.weight (right index).1) *
            ∏ index, (Pi.single (right index).2 (1 : ℝ) : Body → ℝ) (centers index))) =
        (∑ right : Fin s → Body, kernel (fun index => (left index).1) right *
          ∏ index, (Pi.single (right index) (1 : ℝ) : Body → ℝ) (centers index)) *
          (∏ index, channel (Pi.single (left index).1 1) (groups index)) *
          ∏ index, body.weight (left index).2 := by
    calc
      _ = ∑ right : Fin s → Primary × Body,
          (kernel (fun index => (left index).1) (fun index => (right index).2) *
            (∏ index, (Pi.single (right index).2 (1 : ℝ) : Body → ℝ) (centers index)) *
            (∏ index, channel (Pi.single (left index).1 1) (groups index)) *
            ∏ index, body.weight (left index).2) *
            ∏ index, primary.weight (right index).1 := by
          apply Finset.sum_congr rfl
          intro right _
          ring
      _ = _ := by
        rw [sum_pair_right primary (fun right : Fin s → Body =>
          (kernel (fun index => (left index).1) right *
            (∏ index, (Pi.single (right index) (1 : ℝ) : Body → ℝ) (centers index)) *
            (∏ index, channel (Pi.single (left index).1 1) (groups index)) *
            ∏ index, body.weight (left index).2))]
        simp only [Finset.sum_mul]
  simp_rw [hright, sum_single_product]
  rw [sum_pair_left body (fun left : Fin r → Primary => kernel left centers *
    ∏ index, channel (Pi.single (left index) 1) (groups index))]
  exact (TensorChannel.apply_formula_instance r (fun _ => channel) (fun colors => kernel colors centers) groups).symm

end TwoPools
end
end CurrentAFT.TensorPublicProjection
