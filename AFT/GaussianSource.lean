import AFT.SupportObstruction

/-!
# A genuine discrete Gaussian source and its full-support residue law

The one-dimensional Gaussian is normalized on the infinite integer lattice.
Its summability is proved by comparison with a geometric exponential series,
not assumed. Independent coordinate products give the source on `ℤ^d`.
Reduction modulo a positive modulus has full support, closing the analytic
source premise in the finite full-support obstruction.
-/

namespace AFT
namespace GaussianSource

open scoped BigOperators Classical ENNReal

/-- The Gaussian convention of the manuscript: `exp(-π z² / width²)`. -/
noncomputable def weight (width : ℝ) (z : ℤ) : ℝ :=
  Real.exp (-(Real.pi / width ^ 2) * (z : ℝ) ^ 2)

theorem weight_pos (width : ℝ) (z : ℤ) : 0 < weight width z :=
  Real.exp_pos _

/-- Polynomial Gaussian decay dominates a geometric exponential on ℕ. -/
theorem summable_weight (width : ℝ) (hwidth : 0 < width) :
    Summable (weight width) := by
  have hcoefficient : -(Real.pi / width ^ 2) < 0 :=
    neg_lt_zero.mpr (div_pos Real.pi_pos (sq_pos_of_pos hwidth))
  have hnat : Summable (fun n : ℕ => Real.exp (-(Real.pi / width ^ 2) * (n : ℝ) ^ 2)) := by
    apply Real.summable_exp_nat_mul_of_ge hcoefficient
    intro n
    by_cases hn : n = 0
    · simp [hn]
    · have hone : (1 : ℝ) ≤ (n : ℝ) := by
        exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hn)
      nlinarith [sq_nonneg ((n : ℝ) - 1)]
  apply summable_int_iff_summable_nat_and_neg.mpr
  constructor
  · simpa only [weight, Int.cast_natCast] using hnat
  · simpa only [weight, Int.cast_neg, Int.cast_natCast, neg_sq] using hnat

/-- The unnormalized total Gaussian mass, before any modular reduction. -/
noncomputable def normalizer (width : ℝ) : ℝ≥0∞ :=
  ∑' z : ℤ, ENNReal.ofReal (weight width z)

theorem normalizer_ne_zero (width : ℝ) : normalizer width ≠ 0 := by
  intro hzero
  have h := (ENNReal.tsum_eq_zero.mp hzero) (0 : ℤ)
  simp [weight] at h

theorem normalizer_pos (width : ℝ) : 0 < normalizer width :=
  pos_iff_ne_zero.mpr (normalizer_ne_zero width)

theorem normalizer_ne_top (width : ℝ) (hwidth : 0 < width) :
    normalizer width ≠ ∞ :=
  (summable_weight width hwidth).tsum_ofReal_ne_top

/-- The actual probability mass function on the infinite integer lattice. -/
noncomputable def integerGaussian (width : ℝ) (hwidth : 0 < width) : PMF ℤ :=
  PMF.normalize (fun z => ENNReal.ofReal (weight width z))
    (normalizer_ne_zero width) (normalizer_ne_top width hwidth)

theorem integerGaussian_full_support (width : ℝ) (hwidth : 0 < width) (z : ℤ) :
    z ∈ (integerGaussian width hwidth).support := by
  apply (PMF.mem_support_normalize_iff _ _ _).mpr
  exact ne_of_gt (ENNReal.ofReal_pos.mpr (weight_pos width z))

/-- Independent coordinate products on integer vectors. -/
noncomputable def independentCoordinates (p : PMF ℤ) :
    (dimension : ℕ) → PMF (Fin dimension → ℤ)
  | 0 => PMF.pure (fun i => Fin.elim0 i)
  | dimension + 1 => p.bind (fun head =>
      (independentCoordinates p dimension).map (Fin.cons head))

theorem independentCoordinates_full_support (p : PMF ℤ)
    (hp : ∀ z, z ∈ p.support) (dimension : ℕ) :
    ∀ vector, vector ∈ (independentCoordinates p dimension).support := by
  induction dimension with
  | zero =>
      intro vector
      apply (PMF.mem_support_pure_iff _ _).mpr
      funext i
      exact Fin.elim0 i
  | succ dimension ih =>
      intro vector
      apply (PMF.mem_support_bind_iff _ _ _).mpr
      refine ⟨vector 0, hp _, ?_⟩
      apply (PMF.mem_support_map_iff _ _ _).mpr
      exact ⟨Fin.tail vector, ih _, Fin.cons_self_tail vector⟩

/-- Exact probability of a vector under independent coordinate sampling. -/
theorem independentCoordinates_apply (p : PMF ℤ) (dimension : ℕ)
    (vector : Fin dimension → ℤ) :
    independentCoordinates p dimension vector = ∏ i, p (vector i) := by
  induction dimension with
  | zero =>
      simp [independentCoordinates, Subsingleton.elim vector (fun i => Fin.elim0 i)]
  | succ dimension ih =>
      have hpair (head : ℤ) (tail : Fin dimension → ℤ) :
          vector = Fin.cons head tail ↔ head = vector 0 ∧ tail = Fin.tail vector := by
        constructor
        · intro h
          constructor
          · simpa using (congrFun h 0).symm
          · simpa using (congrArg Fin.tail h).symm
        · rintro ⟨rfl, rfl⟩
          exact (Fin.cons_self_tail vector).symm
      have hmap (head : ℤ) :
          ((independentCoordinates p dimension).map (Fin.cons head)) vector =
            if head = vector 0 then independentCoordinates p dimension (Fin.tail vector) else 0 := by
        rw [PMF.map_apply]
        by_cases h : head = vector 0 <;> simp [hpair, h]
      simp only [independentCoordinates, PMF.bind_apply, hmap, mul_ite, mul_zero]
      rw [tsum_ite_eq, Fin.prod_univ_succ]
      rw [ih]
      rfl

/-- The isotropic discrete Gaussian on the integer coordinate lattice. -/
noncomputable def latticeGaussian (dimension : ℕ) (width : ℝ) (hwidth : 0 < width) :
    PMF (Fin dimension → ℤ) :=
  independentCoordinates (integerGaussian width hwidth) dimension

/-- The product construction has exactly the usual multivariate Gaussian
mass: an exponential of the squared Euclidean norm, with a scalar normalizer. -/
theorem latticeGaussian_apply (dimension : ℕ) (width : ℝ) (hwidth : 0 < width)
    (vector : Fin dimension → ℤ) :
    latticeGaussian dimension width hwidth vector =
      ENNReal.ofReal (Real.exp (-(Real.pi / width ^ 2) *
        ∑ coordinate, (vector coordinate : ℝ) ^ 2)) * (normalizer width)⁻¹ ^ dimension := by
  rw [latticeGaussian, independentCoordinates_apply]
  simp only [integerGaussian, PMF.normalize_apply]
  change (∏ i, ENNReal.ofReal (weight width (vector i)) * (normalizer width)⁻¹) = _
  rw [Finset.prod_mul_distrib]
  have hweight : (∏ i, ENNReal.ofReal (weight width (vector i))) =
      ENNReal.ofReal (Real.exp (-(Real.pi / width ^ 2) *
        ∑ coordinate, (vector coordinate : ℝ) ^ 2)) := by
    rw [← ENNReal.ofReal_prod_of_nonneg (fun i _ => le_of_lt (weight_pos width (vector i)))]
    congr 1
    simp only [weight, ← Real.exp_sum, ← Finset.mul_sum]
  rw [hweight]
  simp

/-- Unnormalized multivariate Gaussian weight. -/
noncomputable def latticeWeight (dimension : ℕ) (width : ℝ)
    (vector : Fin dimension → ℤ) : ℝ :=
  Real.exp (-(Real.pi / width ^ 2) * ∑ coordinate, (vector coordinate : ℝ) ^ 2)

/-- Tensorization identifies the exact multivariate normalizer. -/
theorem latticeNormalizer_eq (dimension : ℕ) (width : ℝ) (hwidth : 0 < width) :
    (∑' vector : Fin dimension → ℤ, ENNReal.ofReal (latticeWeight dimension width vector)) =
      (normalizer width) ^ dimension := by
  have hpoint (vector : Fin dimension → ℤ) :
      ENNReal.ofReal (latticeWeight dimension width vector) =
        latticeGaussian dimension width hwidth vector * (normalizer width) ^ dimension := by
    rw [latticeGaussian_apply, mul_assoc, ← mul_pow,
      ENNReal.inv_mul_cancel (normalizer_ne_zero width) (normalizer_ne_top width hwidth)]
    simp [latticeWeight]
  simp_rw [hpoint]
  rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

/-- Summability on the entire integer coordinate lattice, not just each
one-dimensional marginal. -/
theorem summable_latticeWeight (dimension : ℕ) (width : ℝ) (hwidth : 0 < width) :
    Summable (latticeWeight dimension width) := by
  have hfinite : (∑' vector : Fin dimension → ℤ,
      ENNReal.ofReal (latticeWeight dimension width vector)) ≠ ∞ := by
    rw [latticeNormalizer_eq dimension width hwidth]
    exact ENNReal.pow_ne_top (normalizer_ne_top width hwidth)
  have hsum := ENNReal.summable_toReal hfinite
  simpa only [latticeWeight, ENNReal.toReal_ofReal (Real.exp_nonneg _)] using hsum

theorem latticeGaussian_full_support (dimension : ℕ) (width : ℝ) (hwidth : 0 < width)
    (vector : Fin dimension → ℤ) : vector ∈ (latticeGaussian dimension width hwidth).support :=
  independentCoordinates_full_support _ (integerGaussian_full_support width hwidth) dimension vector

/-- Convert a finite PMF to the real-weight interface used by the AFT proofs. -/
noncomputable def finiteLaw {α : Type*} [Fintype α] (p : PMF α) : FiniteDist α where
  weight a := (p a).toReal
  nonneg _ := ENNReal.toReal_nonneg
  sum_one := by
    rw [← ENNReal.toReal_sum (fun a _ => p.apply_ne_top a)]
    have hsum : ∑ a, p a = 1 := by simpa only [tsum_fintype] using p.tsum_coe
    rw [hsum, ENNReal.toReal_one]

theorem finiteLaw_full_support {α : Type*} [Fintype α] (p : PMF α)
    (hp : ∀ a, a ∈ p.support) : (finiteLaw p).FullSupport := by
  intro a
  exact ENNReal.toReal_pos (hp a) (p.apply_ne_top a)

/-- Coordinatewise residue reduction of a genuine lattice Gaussian. -/
noncomputable def residueGaussian (dimension modulus : ℕ) [NeZero modulus]
    (width : ℝ) (hwidth : 0 < width) : FiniteDist (Fin dimension → ZMod modulus) :=
  finiteLaw ((latticeGaussian dimension width hwidth).map
    (fun vector coordinate => (vector coordinate : ZMod modulus)))

theorem residueGaussian_full_support (dimension modulus : ℕ) [NeZero modulus]
    (width : ℝ) (hwidth : 0 < width) :
    (residueGaussian dimension modulus width hwidth).FullSupport := by
  apply finiteLaw_full_support
  intro residue
  apply (PMF.mem_support_map_iff _ _ _).mpr
  refine ⟨fun coordinate => (residue coordinate).val, ?_, ?_⟩
  · exact latticeGaussian_full_support dimension width hwidth _
  · funext coordinate
    simp

/-- V7's positive minimum atom now applies to the actual modular discrete
Gaussian, without an assumed finite full-support source. -/
theorem residueGaussian_minimumMass_pos (dimension modulus : ℕ) [NeZero modulus]
    (width : ℝ) (hwidth : 0 < width) :
    0 < (residueGaussian dimension modulus width hwidth).minimumMass :=
  FiniteDist.minimumMass_pos (residueGaussian_full_support dimension modulus width hwidth)

/-- The fixed-parameter obstruction for the actual discrete Gaussian source.
The explicit floor is `(modulus^dimension - |fiber|) * minimumMass > 0`. -/
theorem residueGaussian_error_floor {Ω : Type*} [Fintype Ω]
    (dimension modulus : ℕ) [NeZero modulus] (width : ℝ) (hwidth : 0 < width)
    (sampler : FiniteDist Ω) (target : FiniteDist (Fin dimension → ZMod modulus))
    (permutation : Ω → (Fin dimension → ZMod modulus) ≃ (Fin dimension → ZMod modulus))
    (fiber : Finset (Fin dimension → ZMod modulus)) (hproper : fiber ≠ Finset.univ)
    (htarget : ∀ a, a ∉ fiber → target.weight a = 0) {error : ℝ}
    (herror : FiniteDist.TVBound
      (FiniteDist.permutationMixture sampler (residueGaussian dimension modulus width hwidth)
        permutation) target error) :
    0 < ((modulus ^ dimension - fiber.card : ℕ) : ℝ) *
        (residueGaussian dimension modulus width hwidth).minimumMass ∧
      ((modulus ^ dimension - fiber.card : ℕ) : ℝ) *
        (residueGaussian dimension modulus width hwidth).minimumMass ≤ error := by
  constructor
  · simpa using FiniteDist.support_obstruction_floor_pos
      (residueGaussian_full_support dimension modulus width hwidth) fiber hproper
  · simpa using FiniteDist.support_obstruction_tv_floor sampler
      (residueGaussian dimension modulus width hwidth) target permutation fiber htarget herror

end GaussianSource
end AFT
