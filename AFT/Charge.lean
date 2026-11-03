import AFT.Hoeffding
import AFT.Correction

/-!
# Exact finite-group charge mixing

This proves a charge estimate directly by convolution of the signed difference
from uniform. It uses the actual `L¹` distance of the center law, rather than
postulating a Fourier mixing estimate. The bound has `q` instead of `q - 1`,
which suffices for the same eventual parameter regime once the concrete
center law's `L¹` estimate is established.
-/

namespace AFT

open scoped BigOperators
open scoped Classical

namespace FiniteDist

variable {G : Type*} [Fintype G] [AddCommGroup G]

/-- The law of the sum of two independent finite-group variables. -/
noncomputable def convolution (p r : FiniteDist G) : FiniteDist G where
  weight x := ∑ y, p.weight y * r.weight (x - y)
  nonneg x := Finset.sum_nonneg fun y _ => mul_nonneg (p.nonneg y) (r.nonneg _)
  sum_one := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum]
    have hs (y : G) : ∑ x, r.weight (x - y) = 1 := by
      rw [← r.sum_one]
      exact (Equiv.subRight y).sum_comp r.weight
    simp_rw [hs, mul_one]
    exact p.sum_one

/-- The deterministic zero charge. -/
noncomputable def zeroCharge : FiniteDist G where
  weight x := if x = 0 then 1 else 0
  nonneg x := by split_ifs <;> norm_num
  sum_one := by
    classical
    simp

/-- The actual sum law of `n` independent centers. -/
noncomputable def sumLaw (p : FiniteDist G) : ℕ → FiniteDist G
  | 0 => zeroCharge
  | n + 1 => p.convolution (sumLaw p n)

/-- Unnormalized `L¹` distance from the exact uniform law. -/
noncomputable def uniformDeviation (p : FiniteDist G) : ℝ :=
  ∑ x, |p.weight x - (Fintype.card G : ℝ)⁻¹|

omit [AddCommGroup G] in
theorem uniformDeviation_nonneg (p : FiniteDist G) : 0 ≤ p.uniformDeviation :=
  Finset.sum_nonneg fun _ _ => abs_nonneg _

/-- In a convolution, the uniform part cancels exactly. -/
theorem convolution_centered (p r : FiniteDist G) (x : G) :
    (p.convolution r).weight x - (Fintype.card G : ℝ)⁻¹ =
      ∑ y, (p.weight y - (Fintype.card G : ℝ)⁻¹) *
        (r.weight (x - y) - (Fintype.card G : ℝ)⁻¹) := by
  have hs : ∑ y, r.weight (x - y) = 1 := by
    rw [← r.sum_one]
    exact (Equiv.subLeft x).sum_comp r.weight
  have hcard : (Fintype.card G : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  simp only [convolution, sub_mul, mul_sub, Finset.sum_sub_distrib,
    ← Finset.sum_mul, ← Finset.mul_sum, p.sum_one, hs, one_mul, mul_one,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp
  ring

/-- Convolution contracts a pointwise deviation by the *actual* signed
`L¹` deviation of the next independent center. -/
theorem convolution_deviation_le (p r : FiniteDist G) (bound : ℝ)
    (hbound : ∀ x, |r.weight x - (Fintype.card G : ℝ)⁻¹| ≤ bound) (x : G) :
    |(p.convolution r).weight x - (Fintype.card G : ℝ)⁻¹| ≤
      p.uniformDeviation * bound := by
  rw [convolution_centered]
  calc
    _ ≤ ∑ y, |(p.weight y - (Fintype.card G : ℝ)⁻¹) *
        (r.weight (x - y) - (Fintype.card G : ℝ)⁻¹)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ y, |p.weight y - (Fintype.card G : ℝ)⁻¹| * bound := by
      apply Finset.sum_le_sum
      intro y _
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hbound _) (abs_nonneg _)
    _ = p.uniformDeviation * bound := by rw [← Finset.sum_mul]; rfl

/-- Every charge, including impossible charges at population zero, satisfies
the exponential mixing estimate. No positivity of the center atoms is used. -/
theorem sumLaw_deviation_le (p : FiniteDist G) (n : ℕ) (x : G) :
    |(p.sumLaw n).weight x - (Fintype.card G : ℝ)⁻¹| ≤
      p.uniformDeviation ^ n := by
  have hu0 : (0 : ℝ) ≤ (Fintype.card G : ℝ)⁻¹ := by positivity
  have hu1 : (Fintype.card G : ℝ)⁻¹ ≤ 1 := by
    have hc : (1 : ℝ) ≤ Fintype.card G := by
      exact_mod_cast Fintype.card_pos
    exact inv_le_one_of_one_le₀ hc
  induction n generalizing x with
  | zero =>
    simp only [sumLaw, zeroCharge, pow_zero]
    split_ifs <;> rw [abs_le] <;> constructor <;> linarith
  | succ n ih =>
    exact (convolution_deviation_le p (p.sumLaw n) _ ih x).trans_eq
      (pow_succ' _ _).symm

theorem scaled_sumLaw_deviation_le (p : FiniteDist G) (n : ℕ) (x : G) :
    |(Fintype.card G : ℝ) * (p.sumLaw n).weight x - 1| ≤
      (Fintype.card G : ℝ) * p.uniformDeviation ^ n := by
  have hc : (Fintype.card G : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have h := mul_le_mul_of_nonneg_left (p.sumLaw_deviation_le n x)
    (show (0 : ℝ) ≤ Fintype.card G by positivity)
  rw [← abs_of_nonneg (show (0 : ℝ) ≤ Fintype.card G by positivity), ← abs_mul] at h
  simpa [mul_sub, hc] using h

/-- Concrete charge conditioning ratio, with positivity proved from the
mixing estimate. The bound can be applied at every realized partial sum. -/
theorem charge_ratio_deviation (p : FiniteDist G) (n k : ℕ) (required partialSum : G)
    (hsmall : (Fintype.card G : ℝ) * p.uniformDeviation ^ n < 1) :
    0 < (p.sumLaw n).weight required ∧
    |(p.sumLaw (n - k)).weight (required - partialSum) /
        (p.sumLaw n).weight required - 1| ≤
      ((Fintype.card G : ℝ) *
        (p.uniformDeviation ^ (n - k) + p.uniformDeviation ^ n)) /
        (1 - (Fintype.card G : ℝ) * p.uniformDeviation ^ n) := by
  have hc : (0 : ℝ) < Fintype.card G := by exact_mod_cast Fintype.card_pos
  have hd := p.scaled_sumLaw_deviation_le n required
  have hn := p.scaled_sumLaw_deviation_le (n - k) (required - partialSum)
  have hden : 0 < (p.sumLaw n).weight required := by
    have hh := (abs_le.mp hd).1
    by_contra hnonpos
    have := mul_nonpos_of_nonneg_of_nonpos hc.le (le_of_not_gt hnonpos)
    linarith
  refine ⟨hden, ?_⟩
  have h := ratio_deviation_bound _ _ _ _ hn hd hsmall
  simpa only [mul_div_mul_left _ _ hc.ne', ← mul_add] using h

omit [AddCommGroup G] in
/-- Two probability profiles have unnormalized `L¹` distance at most two. -/
theorem l1_distance_le_two (p r : FiniteDist G) : ∑ x, |p.weight x - r.weight x| ≤ 2 := by
  calc
    _ ≤ ∑ x, (p.weight x + r.weight x) := by
      apply Finset.sum_le_sum
      intro x _
      exact (abs_sub (p.weight x) (r.weight x)).trans_eq
        (by rw [abs_of_nonneg (p.nonneg x), abs_of_nonneg (r.nonneg x)])
    _ = 2 := by rw [Finset.sum_add_distrib, p.sum_one, r.sum_one]; norm_num

omit [AddCommGroup G] in
/-- The actual compensated center formula has a small uniform deviation
independently of how concentrated the anchor law is. -/
theorem compensated_uniformDeviation (body core anchor : FiniteDist G) (compensation : ℝ)
    (hcomp : 0 ≤ compensation)
    (hformula : ∀ x, body.weight x = (1 + compensation) * core.weight x -
      compensation * anchor.weight x) :
    body.uniformDeviation ≤ core.uniformDeviation + 2 * compensation := by
  unfold uniformDeviation
  calc
    _ ≤ ∑ x, (|core.weight x - (Fintype.card G : ℝ)⁻¹| +
        compensation * |core.weight x - anchor.weight x|) := by
      apply Finset.sum_le_sum
      intro x _
      rw [hformula]
      have heq : (1 + compensation) * core.weight x - compensation * anchor.weight x -
          (Fintype.card G : ℝ)⁻¹ =
          (core.weight x - (Fintype.card G : ℝ)⁻¹) +
            compensation * (core.weight x - anchor.weight x) := by ring
      rw [heq]
      simpa only [abs_mul, abs_of_nonneg hcomp] using abs_add_le
        (core.weight x - (Fintype.card G : ℝ)⁻¹)
        (compensation * (core.weight x - anchor.weight x))
    _ ≤ _ := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      apply add_le_add le_rfl
      simpa only [mul_comm compensation 2] using
        (mul_le_mul_of_nonneg_left (l1_distance_le_two core anchor) hcomp)

/-- A concrete uniform distribution on a nonempty safe subset. -/
noncomputable def uniformSafe (safe : Finset G) (hsafe : safe.Nonempty) : FiniteDist G where
  weight x := if x ∈ safe then (safe.card : ℝ)⁻¹ else 0
  nonneg x := by split_ifs <;> positivity
  sum_one := by
    have hc : (safe.card : ℝ) ≠ 0 := by exact_mod_cast hsafe.card_ne_zero
    simp [hc]

/-- Trimming a finite uniform law has exactly twice the removed fraction as
its `L¹` deviation. This is the safe-center contribution to charge mixing. -/
theorem uniformSafe_deviation (safe : Finset G) (hsafe : safe.Nonempty) :
    (uniformSafe safe hsafe).uniformDeviation =
      2 * (1 - (safe.card : ℝ) / Fintype.card G) := by
  have hcard : (0 : ℝ) < Fintype.card G := by exact_mod_cast Fintype.card_pos
  have hs : (0 : ℝ) < safe.card := by exact_mod_cast hsafe.card_pos
  have hle : (safe.card : ℝ) ≤ Fintype.card G := by
    exact_mod_cast Finset.card_le_univ safe
  have hi : (Fintype.card G : ℝ)⁻¹ ≤ (safe.card : ℝ)⁻¹ :=
    inv_anti₀ hs hle
  have hpoint (x : G) :
      |(uniformSafe safe hsafe).weight x - (Fintype.card G : ℝ)⁻¹| =
        if x ∈ safe then (safe.card : ℝ)⁻¹ - (Fintype.card G : ℝ)⁻¹
          else (Fintype.card G : ℝ)⁻¹ := by
    by_cases hx : x ∈ safe
    · simp only [uniformSafe, if_pos hx, abs_of_nonneg (sub_nonneg.mpr hi)]
    · simp [uniformSafe, hx, abs_of_nonneg (inv_nonneg.mpr hcard.le)]
  unfold uniformDeviation
  simp_rw [hpoint]
  rw [Finset.sum_ite]
  simp only [Finset.filter_mem_eq_inter, Finset.univ_inter, Finset.sum_const,
    nsmul_eq_mul]
  have hcompl : (Finset.univ.filter fun x : G => x ∉ safe).card =
      Fintype.card G - safe.card := by
    simp [← Finset.sdiff_eq_filter, Finset.card_sdiff]
  rw [hcompl, Nat.cast_sub (Finset.card_le_univ safe)]
  field_simp
  ring

/-- Exact product-law interpretation of the convolution operation. -/
theorem convolution_eq_sum_map (p r : FiniteDist G) :
    p.convolution r = (p.prod r).map (fun pair => pair.1 + pair.2) := by
  classical
  ext x
  simp only [convolution, map_weight, prod_weight, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _
  have heq (b : G) : a + b = x ↔ b = x - a := by rw [eq_sub_iff_add_eq, add_comm]
  simp [heq]

theorem convolution_zeroCharge (p : FiniteDist G) :
    zeroCharge.convolution p = p := by
  classical
  ext x
  simp [convolution, zeroCharge, ite_mul]

theorem convolution_assoc (p r s : FiniteDist G) :
    (p.convolution r).convolution s = p.convolution (r.convolution s) := by
  classical
  ext x
  simp only [convolution, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  rw [← Equiv.sum_comp (Equiv.addLeft a)
    (fun y => p.weight a * r.weight (y - a) * s.weight (x - y))]
  apply Finset.sum_congr rfl
  intro b _
  change p.weight a * r.weight (a + b - a) * s.weight (x - (a + b)) = _
  rw [add_sub_cancel_left]
  have hx : x - (a + b) = x - a - b := by abel
  rw [hx]
  ring

theorem sumLaw_add (p : FiniteDist G) (n m : ℕ) :
    p.sumLaw (n + m) = (p.sumLaw n).convolution (p.sumLaw m) := by
  induction n with
  | zero => simp [sumLaw, convolution_zeroCharge]
  | succ n ih =>
    rw [Nat.succ_add, sumLaw, ih, ← convolution_assoc]
    rfl

/-- The recursive charge law is exactly the sum of the actual `Fin n`
independent coordinate vector. This closes the input premise when applying
charge transfer to a specified subset of center coordinates. -/
theorem independent_sum_map (p : FiniteDist G) (n : ℕ) :
    (independent (fun _ : Fin n => p)).map (fun x => ∑ i, x i) = p.sumLaw n := by
  induction n with
  | zero =>
    ext x
    simp [map_weight, independent, sumLaw, zeroCharge, eq_comm]
  | succ n ih =>
    ext x
    rw [map_weight]
    change (∑ y : Fin (n + 1) → G,
      if (∑ i, y i) = x then ∏ i, p.weight (y i) else 0) = _
    rw [← Equiv.sum_comp (Fin.consEquiv (fun _ : Fin (n + 1) => G))]
    rw [Fintype.sum_prod_type]
    change _ = ∑ a, p.weight a * (p.sumLaw n).weight (x - a)
    apply Finset.sum_congr rfl
    intro a _
    have ht : (∑ y : Fin n → G, if (∑ i, y i) = x - a then
        (∏ i, p.weight (y i)) else 0) = (p.sumLaw n).weight (x - a) :=
      congrArg (fun law : FiniteDist G => law.weight (x - a)) ih
    rw [← ht, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro y _
    change (if (∑ i, (Fin.cons a y : Fin (n + 1) → G) i) = x then
      (∏ i, p.weight ((Fin.cons a y : Fin (n + 1) → G) i)) else 0) = _
    rw [Fin.sum_univ_succ, Fin.prod_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]
    have heq : a + ∑ i, y i = x ↔ (∑ i, y i) = x - a := by
      rw [eq_sub_iff_add_eq, add_comm]
    simp [heq, mul_ite]

section Conditioning

variable {Ω : Type*} [Fintype Ω]

/-- The actual charge event probability for a retained and an independent
remaining sum. A retained may retain all its individual coordinates. -/
noncomputable def chargeProbability (retained : FiniteDist Ω) (remaining : FiniteDist G)
    (charge : Ω → G) (required : G) : ℝ :=
  ∑ x, retained.weight x * remaining.weight (required - charge x)

theorem chargeProbability_eq_convolution (retained : FiniteDist Ω)
    (remaining : FiniteDist G) (charge : Ω → G) (required : G) :
    chargeProbability retained remaining charge required =
      ((retained.map charge).convolution remaining).weight required := by
  classical
  simp only [chargeProbability, convolution, map_weight, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  simp [ite_mul]

/-- The conditioned joint law, defined by restriction of the *independent*
product law to its charge event and its actual event probability. -/
noncomputable def conditionCharge (retained : FiniteDist Ω) (remaining : FiniteDist G)
    (charge : Ω → G) (required : G)
    (hpos : 0 < chargeProbability retained remaining charge required) : FiniteDist (Ω × G) where
  weight pair := if charge pair.1 + pair.2 = required then
    retained.weight pair.1 * remaining.weight pair.2 /
      chargeProbability retained remaining charge required else 0
  nonneg pair := by
    split_ifs
    · exact div_nonneg (mul_nonneg (retained.nonneg _) (remaining.nonneg _)) hpos.le
    · rfl
  sum_one := by
    have heq (x : Ω) (b : G) : charge x + b = required ↔ b = required - charge x := by
      rw [eq_sub_iff_add_eq, add_comm]
    simp_rw [Fintype.sum_prod_type, heq]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [← Finset.sum_div]
    exact div_self hpos.ne'

/-- The density ratio is proved by summing out the remaining charge. It is
not a modeling assumption about the conditional marginal. -/
theorem conditionCharge_prefix_weight (retained : FiniteDist Ω) (remaining : FiniteDist G)
    (charge : Ω → G) (required : G)
    (hpos : 0 < chargeProbability retained remaining charge required) (x : Ω) :
    ((conditionCharge retained remaining charge required hpos).map Prod.fst).weight x =
      retained.weight x * remaining.weight (required - charge x) /
        chargeProbability retained remaining charge required := by
  classical
  simp only [map_weight, conditionCharge, Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have heq (b : G) : charge x + b = required ↔ b = required - charge x := by
    rw [eq_sub_iff_add_eq, add_comm]
  simp [heq]

/-- Charge transfer for the entire retained retained, once its charge law is
identified as the sum of the first `k` independent centers. Zero retained atoms
are allowed and need no artificial division by their probability. -/
theorem conditioned_prefix_deviation (center : FiniteDist G) (retained : FiniteDist Ω)
    (charge : Ω → G) (n k : ℕ) (hk : k ≤ n)
    (hlaw : retained.map charge = center.sumLaw k) (required : G)
    (hsmall : (Fintype.card G : ℝ) * center.uniformDeviation ^ n < 1) :
    ∃ hpos : 0 < chargeProbability retained (center.sumLaw (n - k)) charge required,
      ∀ x, |((conditionCharge retained (center.sumLaw (n - k)) charge required hpos).map
          Prod.fst).weight x - retained.weight x| ≤
        retained.weight x *
          ((Fintype.card G : ℝ) *
            (center.uniformDeviation ^ (n - k) + center.uniformDeviation ^ n) /
            (1 - (Fintype.card G : ℝ) * center.uniformDeviation ^ n)) := by
  have hden : chargeProbability retained (center.sumLaw (n - k)) charge required =
      (center.sumLaw n).weight required := by
    rw [chargeProbability_eq_convolution, hlaw, ← sumLaw_add, Nat.add_sub_of_le hk]
  have hpos : 0 < chargeProbability retained (center.sumLaw (n - k)) charge required := by
    rw [hden]
    exact (charge_ratio_deviation center n k required 0 hsmall).1
  refine ⟨hpos, ?_⟩
  intro x
  rw [conditionCharge_prefix_weight, hden]
  have hb := (charge_ratio_deviation center n k required (charge x) hsmall).2
  have heq : retained.weight x * (center.sumLaw (n - k)).weight (required - charge x) /
        (center.sumLaw n).weight required - retained.weight x =
      retained.weight x * ((center.sumLaw (n - k)).weight (required - charge x) /
        (center.sumLaw n).weight required - 1) := by ring
  rw [heq, abs_mul, abs_of_nonneg (retained.nonneg x)]
  exact mul_le_mul_of_nonneg_left hb (retained.nonneg x)

end Conditioning

end FiniteDist

end AFT
