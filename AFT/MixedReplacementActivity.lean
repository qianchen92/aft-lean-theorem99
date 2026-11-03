import AFT.MixedSumFibers

/-! # Replacing one coordinate while retaining every mixed input fiber -/
namespace AFT.MixedKernel
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {New Rest Color : Type*} [Fintype New] [Fintype Rest] [Fintype Color]
  [DecidableEq New] [DecidableEq Rest]

theorem activity_singleton_sum_expand (rate : ℝ) (otherRate : Rest → ℝ)
    (primary : FiniteDist Color) (other : Rest → FiniteDist Color)
    (kernel : (Unit ⊕ Rest → Color) → ℝ) :
    activity (Sum.elim (fun _ : Unit => rate) otherRate) (Sum.elim (fun _ : Unit => primary) other) kernel =
      rate*(∏ slot,otherRate slot)*∑ fixed : Finset Rest,(∏ slot ∈ fixed,otherRate slot)*
        (fiberNorm (Sum.elim (fun _ : Unit => primary) other) kernel ((∅ : Finset Unit).disjSum fixed)+
          rate*fiberNorm (Sum.elim (fun _ : Unit => primary) other) kernel ((Finset.univ : Finset Unit).disjSum fixed)) := by
  have hsets : (Finset.univ : Finset (Finset Unit))={∅,Finset.univ} := by
    ext fixed
    simp only [Finset.mem_univ,Finset.mem_insert,Finset.mem_singleton,true_iff]
    by_cases h : () ∈ fixed
    · right
      ext value
      cases value
      simp [h]
    · left
      ext value
      cases value
      simp [h]
  rw [activity_sum_expand]
  simp only [Fintype.prod_unique]
  rw [hsets,Finset.sum_insert (by simp),Finset.sum_singleton]
  simp only [Finset.prod_empty,one_mul,Fintype.prod_unique]
  rw [← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro fixed _
  ring

/-- The bounds distinguish zero, one, and at least two fixed new outputs.
The result acts on a literal joint kernel and keeps every other pool rate. -/
theorem activity_replacement_le (rate : ℝ) (otherRate : Rest → ℝ)
    (primary : FiniteDist Color) (other : Rest → FiniteDist Color)
    (outputReference : New → FiniteDist Color)
    (input : (Unit ⊕ Rest → Color) → ℝ) (output : (New ⊕ Rest → Color) → ℝ)
    (constant scale : ℝ) (hrate : 0 ≤ rate) (hrate1 : rate ≤ 1)
    (hother : ∀ slot,0 ≤ otherRate slot) (hc : 0 ≤ constant)
    (hsmall : rate*scale ≤ 1) (hnew : 1 ≤ Fintype.card New)
    (hfull : ∀ fixed : Finset Rest,
      fiberNorm (Sum.elim outputReference other) output ((∅ : Finset New).disjSum fixed) ≤
        constant*fiberNorm (Sum.elim (fun _ : Unit => primary) other) input ((∅ : Finset Unit).disjSum fixed))
    (hone : ∀ (slot : New) (fixed : Finset Rest),
      fiberNorm (Sum.elim outputReference other) output (({slot} : Finset New).disjSum fixed) ≤
        constant*(fiberNorm (Sum.elim (fun _ : Unit => primary) other) input ((∅ : Finset Unit).disjSum fixed)+
          fiberNorm (Sum.elim (fun _ : Unit => primary) other) input ((Finset.univ : Finset Unit).disjSum fixed)))
    (hmore : ∀ (selected : Finset New) (fixed : Finset Rest), 2 ≤ selected.card →
      fiberNorm (Sum.elim outputReference other) output (selected.disjSum fixed) ≤
        constant*scale*fiberNorm (Sum.elim (fun _ : Unit => primary) other) input ((Finset.univ : Finset Unit).disjSum fixed)) :
    activity (Sum.elim (fun _ : New => rate) otherRate) (Sum.elim outputReference other) output ≤
      (2:ℝ)^(Fintype.card New+1)*constant*rate^(Fintype.card New-1)*
        activity (Sum.elim (fun _ : Unit => rate) otherRate) (Sum.elim (fun _ : Unit => primary) other) input := by
  let full (fixed : Finset Rest) := fiberNorm (Sum.elim (fun _ : Unit => primary) other) input ((∅ : Finset Unit).disjSum fixed)
  let single (fixed : Finset Rest) := fiberNorm (Sum.elim (fun _ : Unit => primary) other) input ((Finset.univ : Finset Unit).disjSum fixed)
  have hf0 (fixed) : 0 ≤ full fixed := fiberNorm_nonneg _ _ _
  have hg0 (fixed) : 0 ≤ single fixed := fiberNorm_nonneg _ _ _
  have hterm (selected : Finset New) (fixed : Finset Rest) :
      rate^selected.card*fiberNorm (Sum.elim outputReference other) output (selected.disjSum fixed) ≤
        2*constant*(full fixed+rate*single fixed) := by
    by_cases hz : selected.card=0
    · have hz := Finset.card_eq_zero.mp hz
      subst selected
      simp only [Finset.card_empty,pow_zero,one_mul]
      apply (hfull fixed).trans
      change constant*full fixed ≤ _
      nlinarith [mul_nonneg hc (hf0 fixed),mul_nonneg (mul_nonneg hc hrate) (hg0 fixed)]
    · by_cases ho : selected.card=1
      · obtain ⟨slot,rfl⟩ := Finset.card_eq_one.mp ho
        simp only [Finset.card_singleton,pow_one]
        apply (mul_le_mul_of_nonneg_left (hone slot fixed) hrate).trans
        change rate*(constant*(full fixed+single fixed)) ≤ _
        have hh := mul_le_mul_of_nonneg_right hrate1 (mul_nonneg hc (hf0 fixed))
        nlinarith [mul_nonneg hc (hf0 fixed),mul_nonneg (mul_nonneg hc hrate) (hg0 fixed)]
      · have hcard : 2 ≤ selected.card := by omega
        have hh := mul_le_mul (pow_le_pow_of_le_one hrate hrate1 hcard) (hmore selected fixed hcard)
          (fiberNorm_nonneg _ _ _) (sq_nonneg rate)
        apply hh.trans
        change rate^2*(constant*scale*single fixed) ≤ _
        have hm := mul_le_mul_of_nonneg_right hsmall (mul_nonneg (mul_nonneg hc hrate) (hg0 fixed))
        nlinarith [mul_nonneg hc (hf0 fixed),mul_nonneg (mul_nonneg hc hrate) (hg0 fixed)]
  rw [activity_sum_expand,activity_singleton_sum_expand]
  simp only [Finset.prod_const,Finset.card_univ]
  have hsum : (∑ selected : Finset New,∑ fixed : Finset Rest,
      rate^selected.card*(∏ slot ∈ fixed,otherRate slot)*
        fiberNorm (Sum.elim outputReference other) output (selected.disjSum fixed)) ≤
      (2:ℝ)^Fintype.card New*∑ fixed : Finset Rest,
        (∏ slot ∈ fixed,otherRate slot)*(2*constant*(full fixed+rate*single fixed)) := by
    calc
      _ ≤ ∑ _selected : Finset New,∑ fixed : Finset Rest,
        (∏ slot ∈ fixed,otherRate slot)*(2*constant*(full fixed+rate*single fixed)) := by
          apply Finset.sum_le_sum
          intro selected _
          apply Finset.sum_le_sum
          intro fixed _
          calc
            _ = (∏ slot ∈ fixed,otherRate slot)*(rate^selected.card*
              fiberNorm (Sum.elim outputReference other) output (selected.disjSum fixed)) := by ring
            _ ≤ _ := mul_le_mul_of_nonneg_left (hterm selected fixed)
              (Finset.prod_nonneg fun slot _ => hother slot)
      _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_finset,nsmul_eq_mul,Nat.cast_pow,Nat.cast_ofNat]
  apply (mul_le_mul_of_nonneg_left hsum (mul_nonneg (pow_nonneg hrate _)
    (Finset.prod_nonneg fun slot _ => hother slot))).trans_eq
  have hp : rate^Fintype.card New=rate^(Fintype.card New-1)*rate := by
    rw [← pow_succ,Nat.sub_add_cancel hnew]
  rw [hp,pow_succ]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro fixed _
  dsimp [full,single]
  ring

end
end AFT.MixedKernel
