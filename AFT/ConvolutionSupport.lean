import AFT.CanonicalConvolution

/-! # Integer support accounting for all finite convolution inputs -/

namespace AFT.SafeConvolution

open scoped BigOperators

variable {G σ : Type*} [Fintype G] [AddCommGroup G] [Fintype σ]

/-- A group profile admits representatives in an actual integer square.
This retains the no-wrap information needed for safe center inputs. -/
def SupportedInBox (embedding : ℤ →+ G) (lower upper : ℤ) (profile : G × G → ℝ) : Prop :=
  ∀ color, profile color ≠ 0 → ∃ first second : ℤ,
    lower ≤ first ∧ first ≤ upper ∧ lower ≤ second ∧ second ≤ upper ∧
      color = (embedding first, embedding second)

omit [Fintype G] [Fintype σ] in
theorem SupportedInBox.mono {embedding : ℤ →+ G} {lower upper lower' upper' : ℤ} {profile : G × G → ℝ}
    (h : SupportedInBox embedding lower upper profile) (hl : lower' ≤ lower) (hu : upper ≤ upper') :
    SupportedInBox embedding lower' upper' profile := by
  intro color hc
  obtain ⟨first, second, hf, hf', hs, hs', heq⟩ := h color hc
  exact ⟨first, second, hl.trans hf, hf'.trans hu, hl.trans hs, hs'.trans hu, heq⟩

omit [Fintype G] [Fintype σ] in
theorem SupportedInBox.sub {embedding : ℤ →+ G} {lower upper : ℤ} {first second : G × G → ℝ}
    (hf : SupportedInBox embedding lower upper first) (hs : SupportedInBox embedding lower upper second) :
    SupportedInBox embedding lower upper (first - second) := by
  intro color hc
  by_cases hfirst : first color = 0
  · exact hs color (by intro hsecond; apply hc; simp [hfirst, hsecond])
  · exact hf color hfirst

omit [Fintype G] [Fintype σ] in
theorem SupportedInBox.sum {ι : Type*} {embedding : ℤ →+ G} {lower upper : ℤ}
    (indices : Finset ι) (profiles : ι → G × G → ℝ)
    (h : ∀ index ∈ indices, SupportedInBox embedding lower upper (profiles index)) :
    SupportedInBox embedding lower upper (∑ index ∈ indices, profiles index) := by
  intro color hc
  simp only [Finset.sum_apply] at hc
  obtain ⟨index, hi, hn⟩ := Finset.exists_ne_zero_of_sum_ne_zero hc
  exact h index hi color hn

omit [Fintype σ] in
theorem convolution_supportBox (embedding : ℤ →+ G) (kernel profile : G × G → ℝ)
    (a b c d : ℤ) (hk : SupportedInBox embedding a b kernel) (hf : SupportedInBox embedding c d profile) :
    SupportedInBox embedding (a + c) (b + d) (convolution kernel profile) := by
  intro color hc
  obtain ⟨shift, _, hn⟩ := Finset.exists_ne_zero_of_sum_ne_zero hc
  obtain ⟨x, y, hx, hx', hy, hy', hxy⟩ := hk shift (mul_ne_zero_iff.mp hn).1
  obtain ⟨u, v, hu, hu', hv, hv', huv⟩ := hf (color - shift) (mul_ne_zero_iff.mp hn).2
  refine ⟨x + u, y + v, by omega, by omega, by omega, by omega, ?_⟩
  have hsum : color = shift + (color - shift) := by abel
  rw [hsum, huv, hxy]
  simp only [map_add, Prod.mk_add_mk]

/-- A finite pushed source keeps its original bounded integer shifts as
support witnesses, whether or not the palette map is injective. -/
theorem source_supportBox (embedding : ℤ →+ G) (source : FiniteDist σ)
    (firstShift secondShift : σ → ℤ) (radius : ℤ)
    (hshift : ∀ sample, |firstShift sample| ≤ radius ∧ |secondShift sample| ≤ radius) :
    SupportedInBox embedding (-radius) radius
      (source.map fun sample => (embedding (firstShift sample), embedding (secondShift sample))).weight := by
  classical
  intro color hc
  rw [FiniteDist.map_weight] at hc
  obtain ⟨sample, _, hn⟩ := Finset.exists_ne_zero_of_sum_ne_zero hc
  have heq : (embedding (firstShift sample), embedding (secondShift sample)) = color := by
    by_contra hh
    simp only [if_neg hh] at hn
    exact hn rfl
  exact ⟨firstShift sample, secondShift sample, (abs_le.mp (hshift sample).1).1,
    (abs_le.mp (hshift sample).1).2, (abs_le.mp (hshift sample).2).1,
    (abs_le.mp (hshift sample).2).2, heq.symm⟩

variable [DecidableEq G]

omit [Fintype σ] in
theorem box_supportBox (embedding : ℤ →+ G) (radius : ℕ) :
    SupportedInBox embedding (-(radius : ℤ)) radius
      (boxDistribution embedding (-(radius : ℤ)) (2 * radius + 1) (by omega)).weight := by
  intro color hc
  change intervalKernel embedding (-(radius : ℤ)) (2 * radius + 1) color.1 *
    intervalKernel embedding (-(radius : ℤ)) (2 * radius + 1) color.2 ≠ 0 at hc
  have hfirst := (mul_ne_zero_iff.mp hc).1
  have hsecond := (mul_ne_zero_iff.mp hc).2
  unfold intervalKernel pushIntegerKernel at hfirst hsecond
  obtain ⟨first, hf, hfn⟩ := Finset.exists_ne_zero_of_sum_ne_zero hfirst
  obtain ⟨second, hs, hsn⟩ := Finset.exists_ne_zero_of_sum_ne_zero hsecond
  have heq1 : embedding first = color.1 := by by_contra hh; simp only [if_neg hh] at hfn; exact hfn rfl
  have heq2 : embedding second = color.2 := by by_contra hh; simp only [if_neg hh] at hsn; exact hsn rfl
  simp only [anchorInterval, Finset.mem_Ico] at hf hs
  refine ⟨first, second, by omega, by omega, by omega, by omega, ?_⟩
  rw [heq1, heq2]

omit [Fintype σ] [DecidableEq G] in
theorem convolution_power_supportBox (embedding : ℤ →+ G) (kernel profile : G × G → ℝ)
    (radius : ℤ) (lower upper : ℤ) (hk : SupportedInBox embedding (-radius) radius kernel)
    (hf : SupportedInBox embedding lower upper profile) (order : ℕ) :
    SupportedInBox embedding (lower - order * radius) (upper + order * radius)
      ((convolution kernel ^ order) profile) := by
  induction order with
  | zero => simpa using hf
  | succ order ih =>
    have hh := convolution_supportBox embedding kernel _ (-radius) radius
      (lower - order * radius) (upper + order * radius) hk ih
    simpa only [pow_succ', Module.End.mul_apply, Nat.cast_add, Nat.cast_one] using
      (show SupportedInBox embedding (lower - ((order : ℤ) + 1) * radius)
        (upper + ((order : ℤ) + 1) * radius) (convolution kernel ((convolution kernel ^ order) profile)) by
        convert hh using 1 <;> ring)

omit [Fintype σ] [DecidableEq G] in
theorem defect_power_supportBox (embedding : ℤ →+ G) (kernel profile : G × G → ℝ)
    (radius : ℤ) (lower upper : ℤ) (hr : 0 ≤ radius) (hk : SupportedInBox embedding (-radius) radius kernel)
    (hf : SupportedInBox embedding lower upper profile) (order : ℕ) :
    SupportedInBox embedding (lower - order * radius) (upper + order * radius)
      (((1 - convolution kernel) ^ order) profile) := by
  induction order with
  | zero => simpa using hf
  | succ order ih =>
    have hh := convolution_supportBox embedding kernel _ (-radius) radius
      (lower - order * radius) (upper + order * radius) hk ih
    have hh' := ih.mono (lower' := -radius + (lower - order * radius))
      (upper' := radius + (upper + order * radius)) (by omega) (by omega)
    have hh'' := hh'.sub hh
    simpa only [pow_succ', Module.End.mul_apply, LinearMap.sub_apply, Module.End.one_apply,
      Nat.cast_add, Nat.cast_one] using
      (show SupportedInBox embedding (lower - ((order : ℤ) + 1) * radius)
        (upper + ((order : ℤ) + 1) * radius)
        (((1 - convolution kernel) ^ order) profile - convolution kernel (((1 - convolution kernel) ^ order) profile)) by
        convert hh'' using 1 <;> ring)

omit [Fintype σ] [DecidableEq G] in
/-- Every term of the finite correction remains in the reserved integer
margin; no residual support is silently removed. -/
theorem compactRootInput_supportBox (embedding : ℤ →+ G) (root smooth : FiniteDist (G × G))
    (rootRadius smoothRadius lower upper : ℤ) (hr : 0 ≤ rootRadius)
    (hroot : SupportedInBox embedding (-rootRadius) rootRadius root.weight)
    (hsmooth : SupportedInBox embedding (-smoothRadius) smoothRadius smooth.weight)
    (seed : G × G → ℝ) (hseed : SupportedInBox embedding lower upper seed) (depth : ℕ) :
    SupportedInBox embedding (lower - (depth + 1) * smoothRadius - depth * rootRadius)
      (upper + (depth + 1) * smoothRadius + depth * rootRadius)
      (compactRootInput root smooth depth seed) := by
  have htarget := convolution_power_supportBox embedding smooth.weight seed smoothRadius lower upper hsmooth hseed (depth + 1)
  simp only [Nat.cast_add, Nat.cast_one] at htarget
  have hb : -(convolution root.weight - 1) = 1 - convolution root.weight := by abel
  simp only [compactRootInput, finiteCorrection, LinearMap.sum_apply, hb]
  apply SupportedInBox.sum
  intro index hi
  have hi' : (index : ℤ) ≤ depth := by exact_mod_cast (show index ≤ depth by have := Finset.mem_range.mp hi; omega)
  have hh := defect_power_supportBox embedding root.weight _ rootRadius
    (lower - (depth + 1) * smoothRadius) (upper + (depth + 1) * smoothRadius) hr hroot htarget index
  exact hh.mono (by nlinarith) (by nlinarith)

end AFT.SafeConvolution
