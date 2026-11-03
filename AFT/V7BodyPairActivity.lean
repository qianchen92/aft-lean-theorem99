import AFT.V7SafeInactivePair
import AFT.MixedCanonical

/-! # The genuine safe two-body seed and all of its input fibers -/

namespace AFT.MixedKernel
open scoped BigOperators Classical
noncomputable section
variable {Color : Type*} [Fintype Color]

/-- A reference may vanish outside the actual signed kernel's support.
Only the lower bound on that support is used. -/
theorem supported_pair_density_fibers (reference : FiniteDist Color) (mass : Color → Color → ℝ)
    (lower row height : ℝ) (hlower : 0 < lower) (hheight : 0 ≤ height)
    (hsupport : ∀ x y, mass x y ≠ 0 → lower ≤ reference.weight x ∧ lower ≤ reference.weight y)
    (hrow : ∀ x, (∑ y, mass x y^2) ≤ row^2)
    (hcol : ∀ y, (∑ x, mass x y^2) ≤ row^2)
    (hsup : ∀ x y, |mass x y| ≤ height) :
    let density := fun x y => mass x y/(reference.weight x*reference.weight y)
    (∀ x, (∑ y, reference.weight y*density x y^2) ≤ row^2/lower^3) ∧
    (∀ y, (∑ x, reference.weight x*density x y^2) ≤ row^2/lower^3) ∧
    ((∑ x, ∑ y, reference.weight x*reference.weight y*density x y^2) ≤ row^2/lower^3) ∧
    (∀ x y, |density x y| ≤ height/lower^2) := by
  dsimp only
  have hp (x y : Color) (h : mass x y ≠ 0) : 0 < reference.weight x ∧ 0 < reference.weight y :=
    ⟨hlower.trans_le (hsupport x y h).1, hlower.trans_le (hsupport x y h).2⟩
  have hterm (x y : Color) : reference.weight y*(mass x y/(reference.weight x*reference.weight y))^2 ≤ mass x y^2/lower^3 := by
    by_cases h : mass x y = 0
    · simp [h]
    · calc
        _ = mass x y^2/(reference.weight x^2*reference.weight y) := by field_simp
        _ ≤ _ := by
          apply div_le_div_of_nonneg_left (sq_nonneg _) (pow_pos hlower 3)
          have hh := mul_le_mul (pow_le_pow_left₀ hlower.le (hsupport x y h).1 2)
            (hsupport x y h).2 hlower.le (sq_nonneg _)
          simpa only [pow_succ] using hh
  have hterm' (x y : Color) : reference.weight x*(mass x y/(reference.weight x*reference.weight y))^2 ≤ mass x y^2/lower^3 := by
    by_cases h : mass x y = 0
    · simp [h]
    · calc
        _ = mass x y^2/(reference.weight y^2*reference.weight x) := by field_simp
        _ ≤ _ := by
          apply div_le_div_of_nonneg_left (sq_nonneg _) (pow_pos hlower 3)
          have hh := mul_le_mul (pow_le_pow_left₀ hlower.le (hsupport x y h).2 2)
            (hsupport x y h).1 hlower.le (sq_nonneg _)
          simpa only [pow_succ] using hh
  have hr (x : Color) : (∑ y, reference.weight y*(mass x y/(reference.weight x*reference.weight y))^2) ≤ row^2/lower^3 := by
    calc
      _ ≤ ∑ y, mass x y^2/lower^3 := Finset.sum_le_sum fun y _ => hterm x y
      _ = (∑ y, mass x y^2)/lower^3 := by rw [Finset.sum_div]
      _ ≤ _ := div_le_div_of_nonneg_right (hrow x) (pow_nonneg hlower.le 3)
  refine ⟨hr, ?_, ?_, ?_⟩
  · intro y
    calc
      _ ≤ ∑ x, mass x y^2/lower^3 := Finset.sum_le_sum fun x _ => hterm' x y
      _ = (∑ x, mass x y^2)/lower^3 := by rw [Finset.sum_div]
      _ ≤ _ := div_le_div_of_nonneg_right (hcol y) (pow_nonneg hlower.le 3)
  · simp only [mul_assoc, ← Finset.mul_sum]
    calc
      _ ≤ ∑ x, reference.weight x*(row^2/lower^3) :=
        Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (hr x) (reference.nonneg x)
      _ = _ := by rw [← Finset.sum_mul, reference.sum_one, one_mul]
  · intro x y
    by_cases h : mass x y = 0
    · simp only [h, zero_div, abs_zero]
      positivity
    · rw [abs_div, abs_of_pos (mul_pos (hp x y h).1 (hp x y h).2)]
      exact (div_le_div_of_nonneg_right (hsup x y) (mul_nonneg (reference.nonneg x) (reference.nonneg y))).trans
        (div_le_div_of_nonneg_left hheight (sq_pos_of_pos hlower) (by
          have hh := mul_le_mul (hsupport x y h).1 (hsupport x y h).2 hlower.le (reference.nonneg x)
          simpa only [sq] using hh))

end
end AFT.MixedKernel

namespace AFT.V7Calibration
open GaussianSource SafeConvolution Filter RepresentedPolynomial
open scoped BigOperators Classical Topology
noncomputable section
attribute [local instance] actualModulusNeZero

def actualInactiveBodyPairMass (cutoffScale : ℝ) (parameter : ℕ) :
    Fin (Parameters.modulus parameter) × Fin (Parameters.modulus parameter) → ℝ :=
  actualCompactRootInput parameter 14 (actualPairCoreSeed parameter 14 (averagedInactivePair cutoffScale parameter))

def actualInactiveBodyPairDensity (cutoffScale : ℝ) (parameter : ℕ) (beta : ℝ)
    (first second : Fin (Parameters.modulus parameter)) : ℝ :=
  actualInactiveBodyPairMass cutoffScale parameter (first,second) /
    ((actualBodyLaw cutoffScale parameter beta).weight first*(actualBodyLaw cutoffScale parameter beta).weight second)

def actualInactiveBodyPairInput (cutoffScale : ℝ) (parameter : ℕ) (beta : ℝ) :
    InputSeed (Fin (Parameters.modulus parameter)) where
  primaryOrder := 0
  bodyOrder := 2
  kernel := MixedKernel.pairKernel (actualInactiveBodyPairDensity cutoffScale parameter beta)

theorem actualInactiveBodyPairInput_weight (cutoffScale : ℝ) (parameter : ℕ) (beta : ℝ)
    (primary : FiniteDist (Fin (Parameters.modulus parameter))) (primaryPool bodyPool radius : ℝ) :
    inputWeight primary (actualBodyLaw cutoffScale parameter beta) primaryPool bodyPool radius
      (actualInactiveBodyPairInput cutoffScale parameter beta) =
      radius^2 * MixedKernel.activity ![(Real.sqrt bodyPool)⁻¹,(Real.sqrt bodyPool)⁻¹]
        (MixedKernel.pairReference (actualBodyLaw cutoffScale parameter beta) (actualBodyLaw cutoffScale parameter beta))
        (MixedKernel.pairKernel (actualInactiveBodyPairDensity cutoffScale parameter beta)) := by
  have hrate : inputRate primaryPool bodyPool (actualInactiveBodyPairInput cutoffScale parameter beta) =
      ![(Real.sqrt bodyPool)⁻¹,(Real.sqrt bodyPool)⁻¹] := by funext i; fin_cases i <;> rfl
  have href : inputReference primary (actualBodyLaw cutoffScale parameter beta) (actualInactiveBodyPairInput cutoffScale parameter beta) =
      MixedKernel.pairReference (actualBodyLaw cutoffScale parameter beta) (actualBodyLaw cutoffScale parameter beta) := by funext i; fin_cases i <;> rfl
  unfold inputWeight MixedKernel.analyticActivity
  rw [hrate,href]
  rfl

theorem actual_body_safe_lower_eventually (cutoffScale : ℝ) (hscale : 1 ≤ cutoffScale) (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ parameter in atTop,
      (Parameters.legs parameter : ℝ)/(2*Parameters.dimension parameter) ≤ beta parameter ∧
      beta parameter ≤ 2*(Parameters.legs parameter : ℝ)/Parameters.dimension parameter) :
    ∀ᶠ parameter in atTop, ∀ color, color ∈ safePalette parameter →
      1/(2*(Parameters.modulus parameter : ℝ)) ≤ (actualBodyLaw cutoffScale parameter (beta parameter)).weight color := by
  filter_upwards [actual_body_center_probability_eventually cutoffScale hscale beta hbeta,
    actual_reference_laws_eventually cutoffScale hscale beta hbeta] with parameter hb hl color hcolor
  rw [hl.2.1]
  have hc : (0 : ℝ) < (safePalette parameter).card := by exact_mod_cast (safePalette_nonempty parameter).card_pos
  have hcard : ((safePalette parameter).card : ℝ) ≤ Parameters.modulus parameter := by
    exact_mod_cast (show (safePalette parameter).card ≤ Parameters.modulus parameter by simpa only [Fintype.card_fin] using Finset.card_le_univ (safePalette parameter))
  have hcore : 1/(Parameters.modulus parameter : ℝ) ≤ (actualCoreLaw parameter).weight color := by
    simpa only [actualCoreLaw, FiniteDist.uniformSafe, if_pos hcolor, one_div] using one_div_le_one_div_of_le hc hcard
  convert (div_le_div_of_nonneg_right hcore (by norm_num : (0 : ℝ) ≤ 2)).trans (hb.2.1 color).1 using 1
  ring

theorem actualInactiveBodyPairMass_safe (cutoffScale : ℝ) (parameter : ℕ)
    (first second : Fin (Parameters.modulus parameter))
    (hn : actualInactiveBodyPairMass cutoffScale parameter (first,second) ≠ 0) :
    first ∈ safePalette parameter ∧ second ∈ safePalette parameter := by
  have hh := actualPairInput_safe parameter 14 (averagedInactivePair cutoffScale parameter) (first,second) hn
  simp only [safePalette, TrimmedSlice.paletteSlice, Finset.mem_filter, Finset.mem_univ, true_and,
    TrimmedSlice.mem_slice]
  simp only at hh
  omega

/-- The actual finite Neumann body input has every weighted fixed fiber
controlled on its genuine safe support. -/
theorem actual_inactive_body_pair_fibers_eventually (cutoffScale : ℝ) (hscale : 1 ≤ cutoffScale) (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ parameter in atTop,
      (Parameters.legs parameter : ℝ)/(2*Parameters.dimension parameter) ≤ beta parameter ∧
      beta parameter ≤ 2*(Parameters.legs parameter : ℝ)/Parameters.dimension parameter) :
    ∀ᶠ parameter in atTop,
      let p := (actualBodyLaw cutoffScale parameter (beta parameter)).weight
      let D := actualInactiveBodyPairDensity cutoffScale parameter (beta parameter)
      let F := 16*pairNeumannConstant*(parameter : ℝ)^4
      (∀ x, (∑ y, p y*D x y^2) ≤ F^2) ∧
      (∀ y, (∑ x, p x*D x y^2) ≤ F^2) ∧
      ((∑ x, ∑ y, p x*p y*D x y^2) ≤ F^2) ∧
      (∀ x y, |D x y| ≤ 64*pairNeumannConstant*(parameter : ℝ)^8) := by
  have hrows := actual_pair_input_fibers_eventually cutoffScale hscale (boundaryHalf cutoffScale)
    (inactivePairStarts cutoffScale) (inactivePairShift cutoffScale) (inactivePairSources cutoffScale)
    (inactivePairSources_physical_eventually cutoffScale hscale)
  simp only [← averagedInactivePair_mixture] at hrows
  filter_upwards [hrows, actual_body_safe_lower_eventually cutoffScale hscale beta hbeta,
    eventually_ge_atTop 2] with parameter hr hl hp
  dsimp only at hr ⊢
  let q : ℝ := Parameters.modulus parameter
  let row := 4*pairNeumannConstant/(q*(parameter : ℝ)^16)
  let height := 8*pairNeumannConstant/(q*(parameter : ℝ)^32)
  have hq : 0 < q := by dsimp only [q]; exact_mod_cast (Parameters.modulus_prime parameter).pos
  have hx : (0 : ℝ) < parameter := by exact_mod_cast (show 0 < parameter by omega)
  have hqBound : q ≤ 2*(parameter : ℝ)^40 := by
    dsimp only [q]
    exact_mod_cast (show Parameters.modulus parameter ≤ 2*parameter^40 by simpa only [Parameters.security_eq parameter hp] using (Parameters.modulus_bounds parameter).2)
  have hsupport (x y : Fin (Parameters.modulus parameter)) (hn : actualInactiveBodyPairMass cutoffScale parameter (x,y) ≠ 0) :
      1/(2*q) ≤ (actualBodyLaw cutoffScale parameter (beta parameter)).weight x ∧
      1/(2*q) ≤ (actualBodyLaw cutoffScale parameter (beta parameter)).weight y := by
    have hs := actualInactiveBodyPairMass_safe cutoffScale parameter x y hn
    exact ⟨hl x hs.1,hl y hs.2⟩
  have hrow (x : Fin (Parameters.modulus parameter)) : (∑ y, actualInactiveBodyPairMass cutoffScale parameter (x,y)^2) ≤ row^2 := by
    have hh := pow_le_pow_left₀ (countingL2_nonneg _) (hr.1 x) 2
    simpa only [countingL2, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)] using hh
  have hcol (y : Fin (Parameters.modulus parameter)) : (∑ x, actualInactiveBodyPairMass cutoffScale parameter (x,y)^2) ≤ row^2 := by
    have hh := pow_le_pow_left₀ (countingL2_nonneg _) (hr.2.1 y) 2
    simpa only [countingL2, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)] using hh
  have hf := MixedKernel.supported_pair_density_fibers (actualBodyLaw cutoffScale parameter (beta parameter))
    (fun x y => actualInactiveBodyPairMass cutoffScale parameter (x,y)) (1/(2*q)) row height
    (by positivity) (by dsimp [height,pairNeumannConstant]; positivity) hsupport hrow hcol
    (fun x y => hr.2.2.1 (x,y))
  have hrowBound : row^2/(1/(2*q))^3 ≤ (16*pairNeumannConstant*(parameter : ℝ)^4)^2 := by
    calc
      _ = 128*pairNeumannConstant^2*q/(parameter : ℝ)^32 := by dsimp [row]; field_simp; ring
      _ ≤ 128*pairNeumannConstant^2*(2*(parameter : ℝ)^40)/(parameter : ℝ)^32 := by gcongr
      _ = _ := by field_simp; ring
  have hheightBound : height/(1/(2*q))^2 ≤ 64*pairNeumannConstant*(parameter : ℝ)^8 := by
    calc
      _ = 32*pairNeumannConstant*q/(parameter : ℝ)^32 := by dsimp [height]; field_simp; ring
      _ ≤ 32*pairNeumannConstant*(2*(parameter : ℝ)^40)/(parameter : ℝ)^32 := by
        gcongr
        norm_num [pairNeumannConstant]
      _ = _ := by field_simp; ring
  exact ⟨fun x => (hf.1 x).trans hrowBound, fun y => (hf.2.1 y).trans hrowBound,
    hf.2.2.1.trans hrowBound, fun x y => (hf.2.2.2 x y).trans hheightBound⟩

/-- Canonicality is proved for the real calibrated body law, whose zeros
outside the safe interval are explicitly respected. -/
theorem actual_inactive_body_pair_canonical_eventually (cutoffScale : ℝ) (hscale : 1 ≤ cutoffScale) (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ parameter in atTop,
      (Parameters.legs parameter : ℝ)/(2*Parameters.dimension parameter) ≤ beta parameter ∧
      beta parameter ≤ 2*(Parameters.legs parameter : ℝ)/Parameters.dimension parameter) :
    ∀ᶠ parameter in atTop,
      Hoeffding.Canonical (fun _ : Fin 2 => actualBodyLaw cutoffScale parameter (beta parameter)) Finset.univ
        (actualInactiveBodyPairInput cutoffScale parameter (beta parameter)).kernel := by
  filter_upwards [actual_body_safe_lower_eventually cutoffScale hscale beta hbeta,
    pairCore_nonempty_eventually 14] with parameter hl hcore
  have hcanonical := actualCompactRootInput_canonical parameter 14 _
    (actualPairCoreSeed_canonical parameter 14 (averagedInactivePair cutoffScale parameter) hcore)
  let p := (actualBodyLaw cutoffScale parameter (beta parameter)).weight
  let mass := actualInactiveBodyPairMass cutoffScale parameter
  change PairCanonical mass at hcanonical
  have hq : (0 : ℝ) < Parameters.modulus parameter := by exact_mod_cast (Parameters.modulus_prime parameter).pos
  have hs (x y : Fin (Parameters.modulus parameter)) (hm : mass (x,y) ≠ 0) : p x ≠ 0 ∧ p y ≠ 0 := by
    have hh := actualInactiveBodyPairMass_safe cutoffScale parameter x y hm
    exact ⟨(lt_of_lt_of_le (by positivity) (hl x hh.1)).ne',
      (lt_of_lt_of_le (by positivity) (hl y hh.2)).ne'⟩
  change Hoeffding.Canonical (fun _ : Fin 2 => actualBodyLaw cutoffScale parameter (beta parameter)) Finset.univ
    (MixedKernel.pairKernel (fun x y => mass (x,y)/(p x*p y)))
  apply MixedKernel.pair_canonical
  · intro x
    change (∑ y, p y*(mass (x,y)/(p x*p y))) = 0
    calc
      _ = (∑ y, mass (x,y))/p x := by
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro y _
        by_cases hm : mass (x,y) = 0
        · simp [hm]
        · field_simp [(hs x y hm).1,(hs x y hm).2]
      _ = 0 := by rw [hcanonical.1,zero_div]
  · intro y
    change (∑ x, p x*(mass (x,y)/(p x*p y))) = 0
    calc
      _ = (∑ x, mass (x,y))/p y := by
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro x _
        by_cases hm : mass (x,y) = 0
        · simp [hm]
        · field_simp [(hs x y hm).1,(hs x y hm).2]
      _ = 0 := by rw [hcanonical.2,zero_div]

theorem body_pair_pool_rate (parameter pool : ℕ) (hp : 2 ≤ parameter)
    (hpool : Parameters.bodies parameter ≤ 2*pool) :
    0 ≤ (Real.sqrt (pool : ℝ))⁻¹ ∧ (Real.sqrt (pool : ℝ))⁻¹ ≤ 1 ∧
      (Real.sqrt (pool : ℝ))⁻¹ ≤ 2/(parameter : ℝ)^30 := by
  have hx : (1 : ℝ) ≤ parameter := by exact_mod_cast (show 1 ≤ parameter by omega)
  have hx0 : (0 : ℝ) < parameter := by positivity
  have hN : parameter^60 ≤ 2*Parameters.bodies parameter := by
    have hi := Parameters.population_identity parameter
    have hm := Parameters.legs_le_half_bodies parameter
    have hd := (Parameters.dimension_bounds parameter).1
    rw [Parameters.security_eq parameter hp] at hd
    omega
  have hbound : (parameter : ℝ)^60 ≤ 4*(pool : ℝ) := by exact_mod_cast (show parameter^60 ≤ 4*pool by omega)
  have hs : (parameter : ℝ)^30/2 ≤ Real.sqrt (pool : ℝ) := by
    have hsq := Real.sq_sqrt (Nat.cast_nonneg pool)
    have hs0 := Real.sqrt_nonneg (pool : ℝ)
    have hp0 : 0 ≤ (parameter : ℝ)^30 := by positivity
    nlinarith [show (parameter : ℝ)^60 = ((parameter : ℝ)^30)^2 by ring]
  have hh := one_div_le_one_div_of_le (by positivity : 0 < (parameter : ℝ)^30/2) hs
  have hb : (Real.sqrt (pool : ℝ))⁻¹ ≤ 2/(parameter : ℝ)^30 := by
    convert hh using 1 <;> ring
  have hpower : (2 : ℝ) ≤ (parameter : ℝ)^30 := by
    have hp' : (2 : ℝ) ≤ parameter := by exact_mod_cast hp
    exact hp'.trans (by simpa only [pow_one] using pow_le_pow_right₀ hx (show 1 ≤ 30 by decide))
  exact ⟨by positivity, hb.trans ((div_le_one (by positivity)).mpr hpower),hb⟩

/-- The genuine safe-body pair seed has a complete input activity bound;
it is one component of the two-seed exact pair certificate. -/
theorem actual_inactive_body_pair_activity_eventually (cutoffScale : ℝ) (hscale : 1 ≤ cutoffScale) (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ parameter in atTop,
      (Parameters.legs parameter : ℝ)/(2*Parameters.dimension parameter) ≤ beta parameter ∧
      beta parameter ≤ 2*(Parameters.legs parameter : ℝ)/Parameters.dimension parameter) :
    ∀ᶠ parameter in atTop,
      ∀ primary : FiniteDist (Fin (Parameters.modulus parameter)), ∀ primaryPool : ℝ,
      ∀ bodyPool : ℕ, Parameters.bodies parameter ≤ 2*bodyPool →
      inputWeight primary (actualBodyLaw cutoffScale parameter (beta parameter)) primaryPool bodyPool ((parameter : ℝ)^2)
        (actualInactiveBodyPairInput cutoffScale parameter (beta parameter)) ≤
          512*pairNeumannConstant/(parameter : ℝ)^48 := by
  filter_upwards [actual_inactive_body_pair_fibers_eventually cutoffScale hscale beta hbeta,
    eventually_ge_atTop 2] with parameter hf hp primary primaryPool pool hpool
  have hx : (1 : ℝ) ≤ parameter := by exact_mod_cast (show 1 ≤ parameter by omega)
  have hx0 : (0 : ℝ) < parameter := by positivity
  have hc : 0 ≤ pairNeumannConstant := by norm_num [pairNeumannConstant]
  let b := (Real.sqrt (pool : ℝ))⁻¹
  let F := 16*pairNeumannConstant*(parameter : ℝ)^4
  let H := 64*pairNeumannConstant*(parameter : ℝ)^8
  have hb := body_pair_pool_rate parameter pool hp hpool
  have hpair := MixedKernel.pair_activity_le (actualBodyLaw cutoffScale parameter (beta parameter))
    (actualBodyLaw cutoffScale parameter (beta parameter)) (actualInactiveBodyPairDensity cutoffScale parameter (beta parameter))
    b b F F F H hb.1 hb.1 (by positivity) (by positivity) (by positivity) (by positivity)
    hf.2.2.1 hf.1 hf.2.1 hf.2.2.2
  have hb2 : b*b ≤ 4/(parameter : ℝ)^60 := by
    have hh := pow_le_pow_left₀ hb.1 hb.2.2 2
    convert hh using 1 <;> ring
  have hbF : b*F ≤ F := by simpa only [one_mul] using mul_le_mul_of_nonneg_right hb.2.1 (show 0 ≤ F by positivity)
  have hbH : b*b*H ≤ H := by
    have hh := mul_le_mul hb.2.1 hb.2.1 hb.1 (by norm_num : (0 : ℝ) ≤ 1)
    exact (mul_le_mul_of_nonneg_right hh (show 0 ≤ H by positivity)).trans_eq (by ring)
  have hF : F ≤ 16*pairNeumannConstant*(parameter : ℝ)^8 := by
    exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hx (show 4 ≤ 8 by decide)) (by positivity)
  have hbracket : F+b*F+b*F+b*b*H ≤ 112*pairNeumannConstant*(parameter : ℝ)^8 := by
    dsimp only [H] at hbH
    linarith
  rw [actualInactiveBodyPairInput_weight]
  calc
    _ ≤ ((parameter : ℝ)^2)^2*(b*b*(F+b*F+b*F+b*b*H)) := mul_le_mul_of_nonneg_left hpair (sq_nonneg _)
    _ ≤ ((parameter : ℝ)^2)^2*((4/(parameter : ℝ)^60)*(112*pairNeumannConstant*(parameter : ℝ)^8)) := by
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
      exact mul_le_mul hb2 hbracket (by positivity) (by positivity)
    _ = 448*pairNeumannConstant/(parameter : ℝ)^48 := by field_simp; ring
    _ ≤ _ := by gcongr; norm_num

/-- Dividing by the actual safe-body references loses no signed mass,
including at their zero-probability colors. -/
theorem actual_inactive_body_pair_mass_eventually (cutoffScale : ℝ) (hscale : 1 ≤ cutoffScale) (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ parameter in atTop,
      (Parameters.legs parameter : ℝ)/(2*Parameters.dimension parameter) ≤ beta parameter ∧
      beta parameter ≤ 2*(Parameters.legs parameter : ℝ)/Parameters.dimension parameter) :
    ∀ᶠ parameter in atTop, ∀ x y,
      (actualBodyLaw cutoffScale parameter (beta parameter)).weight x *
        (actualBodyLaw cutoffScale parameter (beta parameter)).weight y *
        actualInactiveBodyPairDensity cutoffScale parameter (beta parameter) x y =
          actualInactiveBodyPairMass cutoffScale parameter (x,y) := by
  filter_upwards [actual_body_safe_lower_eventually cutoffScale hscale beta hbeta] with parameter hl x y
  have hq : (0 : ℝ) < Parameters.modulus parameter := by exact_mod_cast (Parameters.modulus_prime parameter).pos
  by_cases hm : actualInactiveBodyPairMass cutoffScale parameter (x,y) = 0
  · simp [actualInactiveBodyPairDensity, hm]
  · have hs := actualInactiveBodyPairMass_safe cutoffScale parameter x y hm
    have hx : (actualBodyLaw cutoffScale parameter (beta parameter)).weight x ≠ 0 :=
      (lt_of_lt_of_le (by positivity) (hl x hs.1)).ne'
    have hy : (actualBodyLaw cutoffScale parameter (beta parameter)).weight y ≠ 0 :=
      (lt_of_lt_of_le (by positivity) (hl y hs.2)).ne'
    unfold actualInactiveBodyPairDensity
    field_simp

/-- Summing the safe-body pair costs over every actual leg preserves a
strictly stronger power than the required lambda^-2 background budget. -/
theorem actual_inactive_body_pair_total_activity_eventually (cutoffScale : ℝ) (hscale : 1 ≤ cutoffScale) (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ parameter in atTop,
      (Parameters.legs parameter : ℝ)/(2*Parameters.dimension parameter) ≤ beta parameter ∧
      beta parameter ≤ 2*(Parameters.legs parameter : ℝ)/Parameters.dimension parameter) :
    ∀ᶠ parameter in atTop,
      ∀ primary : FiniteDist (Fin (Parameters.modulus parameter)), ∀ primaryPool : ℝ,
      ∀ bodyPool : ℕ, Parameters.bodies parameter ≤ 2*bodyPool →
      (Parameters.legs parameter : ℝ) *
        inputWeight primary (actualBodyLaw cutoffScale parameter (beta parameter)) primaryPool bodyPool ((parameter : ℝ)^2)
          (actualInactiveBodyPairInput cutoffScale parameter (beta parameter)) ≤
            512*pairNeumannConstant/(parameter : ℝ)^18 := by
  filter_upwards [actual_inactive_body_pair_activity_eventually cutoffScale hscale beta hbeta,
    eventually_ge_atTop 2] with parameter ha hp primary primaryPool bodyPool hpool
  have hx : (0 : ℝ) < parameter := by exact_mod_cast (show 0 < parameter by omega)
  have hm : (Parameters.legs parameter : ℝ) = (parameter : ℝ)^30 := by
    simp only [Parameters.legs, Parameters.security_eq parameter hp, Nat.cast_pow]
  exact (mul_le_mul_of_nonneg_left (ha primary primaryPool bodyPool hpool) (Nat.cast_nonneg _)).trans_eq (by rw [hm]; field_simp)

end
end AFT.V7Calibration
