import AFT.BoundarySpike

/-! # The literal normalized surviving marked fiber -/
namespace AFT.BoundaryCalibration
open scoped BigOperators Classical
noncomputable section
variable {Ω C J : Type*} [Fintype Ω] [Fintype C] [Nonempty C] [Fintype J]

omit [Fintype J] in
theorem explicit_surviving_fiber_density (p : FiniteDist Ω) (first : Ω → C)
    (hfirst : p.map first = FiniteDist.uniform C)
    (others : J → Ω → C)
    (hpair : ∀ j, p.map (fun x => (first x, others j x)) =
      (FiniteDist.uniform C).prod (FiniteDist.uniform C))
    (safe : Ω → Prop) (mark : C)
    (hbad : conditional p first (badIndicator safe) mark ≤ 1 / 2) :
    ∃ spike : Ω → ℝ,
      spike = restrictedDensity p (fun x => first x = mark ∧ safe x) ∧
      expectation p spike = 1 ∧ (∀ x, 0 ≤ spike x) ∧
      (∀ x, ¬ (first x = mark ∧ safe x) → spike x = 0) ∧
      (∀ c, conditional p first spike c =
        if c = mark then (Fintype.card C : ℝ) else 0) ∧
      (∀ j c, conditional p (others j) spike c ≤ 2) := by
  let event := fun x => first x = mark ∧ safe x
  have hC : 0 < (Fintype.card C : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  have hmass := survivingFiber_mass p first hfirst safe mark
  have hpos : 0 < eventMass p event := by
    rw [hmass]
    exact div_pos (by linarith) hC
  let spike := restrictedDensity p event
  have hmean : expectation p spike = 1 := restrictedDensity_mean p event hpos
  have hzero : ∀ x, ¬ event x → spike x = 0 := by
    intro x hx
    simp [spike, restrictedDensity, eventIndicator, hx]
  refine ⟨spike, rfl, hmean, restrictedDensity_nonneg p event, hzero, ?_, ?_⟩
  · intro c
    rw [conditional_apply]
    by_cases hc : c = mark
    · subst c
      have heq : (fun x => if first x = mark then spike x else (0 : ℝ)) = spike := by
        funext x
        by_cases hx : first x = mark
        · simp [hx]
        · simp [hx, hzero x (by simp [event, hx])]
      rw [heq, hmean, if_pos rfl, mul_one]
    · have heq : (fun x => if first x = c then spike x else (0 : ℝ)) = 0 := by
        funext x
        by_cases hx : first x = c
        · have hn : ¬ event x := by rintro ⟨hm, _⟩; exact hc (hx.symm.trans hm)
          simp [hx, hzero x hn]
        · simp [hx]
      rw [heq, map_zero, mul_zero, if_neg hc]
  · intro j c
    rw [conditional_restrictedDensity]
    have hnum : eventMass p (fun x => others j x = c ∧ event x) ≤
        (Fintype.card C : ℝ)⁻¹ * (Fintype.card C : ℝ)⁻¹ := by
      rw [← pair_eventMass p first (others j) (hpair j) mark c]
      apply expectation_mono
      intro x
      unfold eventIndicator
      split_ifs with ht hf
      · exact le_rfl
      · exact False.elim (hf ⟨ht.2.1, ht.1⟩)
      · norm_num
      · norm_num
    apply (div_le_iff₀ hpos).mpr
    have hm : 1 / 2 ≤ (Fintype.card C : ℝ) * eventMass p event := by
      rw [hmass]
      field_simp
      linarith
    have hn := mul_le_mul_of_nonneg_left hnum hC.le
    have hcancel : (Fintype.card C : ℝ) *
        ((Fintype.card C : ℝ)⁻¹ * (Fintype.card C : ℝ)⁻¹) = (Fintype.card C : ℝ)⁻¹ := by
      field_simp
    rw [hcancel] at hn
    have hl : (Fintype.card C : ℝ)⁻¹ ≤ 2 * eventMass p event := by
      nlinarith [mul_inv_cancel₀ hC.ne']
    exact hn.trans hl

end
end AFT.BoundaryCalibration
