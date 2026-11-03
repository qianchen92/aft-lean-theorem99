import CurrentAFT.GradedNewton
import CurrentAFT.CommonQueueNorm

/-!
# Norm control of complete finite background products

Newton's identities retain cancellation in the sum of all actual atoms.
Higher power sums are bounded by their total squared norm. The resulting
constant depends only on the fixed truncation order, not on the number of
factors, the palette, or a coordinate basis.
-/

namespace CurrentAFT.GradedNewtonNorm

open AFT ControlCoordinates GradedControlAlgebra GradedControlNorm GradedControlStability
  GradedInverseNorm CommonQueueAssembly GradedNewton
open scoped BigOperators Classical

noncomputable section

set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

variable {Primary Body Index : Type*} [Fintype Primary] [Fintype Body] [Fintype Index]

omit [Fintype Index] in
theorem norm_sign_mul (primary : FiniteDist Primary) (body : FiniteDist Body) (order : ℕ)
    (pf bf : ℝ) (power : ℕ) (family : KernelFamily primary body order) :
    familyNorm primary body order pf bf ((-1 : KernelFamily primary body order) ^ power * family) =
      familyNorm primary body order pf bf family := by
  induction power generalizing family with
  | zero => rw [pow_zero, one_mul]
  | succ power ih => rw [pow_succ, mul_assoc, neg_one_mul, ih, familyNorm_neg]

omit [Fintype Index] in
theorem norm_nat_mul (primary : FiniteDist Primary) (body : FiniteDist Body) (order : ℕ)
    (pf bf : ℝ) (natural : ℕ) (family : KernelFamily primary body order) :
    familyNorm primary body order pf bf ((natural : KernelFamily primary body order) * family) =
      (natural : ℝ) * familyNorm primary body order pf bf family := by
  have heq : (natural : KernelFamily primary body order) * family = (natural : ℝ) • family := by
    rw [← nsmul_eq_mul, Nat.cast_smul_eq_nsmul]
  rw [heq, familyNorm_smul, abs_of_nonneg (Nat.cast_nonneg natural)]

theorem newton_norm_le (primary : FiniteDist Primary) (body : FiniteDist Body) (order degree : ℕ)
    (pf bf : ℝ) (hpf : 0 ≤ pf) (hbf : 0 ≤ bf) (atoms : Index → KernelFamily primary body order) :
    (degree : ℝ) * familyNorm primary body order pf bf (elementary primary body order atoms degree) ≤
      ∑ pair ∈ (Finset.antidiagonal degree).filter (fun pair => pair.1 < degree),
        familyNorm primary body order pf bf (elementary primary body order atoms pair.1) *
          familyNorm primary body order pf bf (powerSum primary body order atoms pair.2) := by
  rw [← norm_nat_mul, newton_identity, norm_sign_mul]
  calc
    _ ≤ ∑ pair ∈ (Finset.antidiagonal degree).filter (fun pair => pair.1 < degree),
        familyNorm primary body order pf bf
          ((-1 : KernelFamily primary body order) ^ pair.1 * elementary primary body order atoms pair.1 *
            powerSum primary body order atoms pair.2) :=
      familyNorm_sum_le primary body order pf bf hpf hbf _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro pair _
      have h := familyNorm_product_le primary body order pf bf hpf hbf
        ((-1) ^ pair.1 * elementary primary body order atoms pair.1) (powerSum primary body order atoms pair.2)
      simpa only [norm_sign_mul] using h

theorem elementary_norm_le (primary : FiniteDist Primary) (body : FiniteDist Body) (order : ℕ)
    (pf bf : ℝ) (hpf : 0 ≤ pf) (hbf : 0 ≤ bf) (atoms : Index → KernelFamily primary body order)
    (delta : ℝ) (hdelta : 0 ≤ delta) (hsmall : delta ≤ 1)
    (hpowers : ∀ power, 1 ≤ power → power ≤ order →
      familyNorm primary body order pf bf (powerSum primary body order atoms power) ≤ delta) :
    ∀ degree, 1 ≤ degree → degree ≤ order →
      familyNorm primary body order pf bf (elementary primary body order atoms degree) ≤
        delta * ((order + 1 : ℕ) : ℝ) ^ degree := by
  intro degree
  induction degree using Nat.strong_induction_on with
  | h degree ih =>
    intro hpositive hdegree
    let scale : ℝ := ((order + 1 : ℕ) : ℝ)
    have hscale : 1 ≤ scale := by dsimp [scale]; norm_cast; omega
    have hnorm : 0 ≤ familyNorm primary body order pf bf (elementary primary body order atoms degree) :=
      familyNorm_nonneg primary body order pf bf hpf hbf _
    have hterm (pair : ℕ × ℕ)
        (hpair : pair ∈ (Finset.antidiagonal degree).filter (fun pair => pair.1 < degree)) :
        familyNorm primary body order pf bf (elementary primary body order atoms pair.1) *
            familyNorm primary body order pf bf (powerSum primary body order atoms pair.2) ≤
          scale ^ (degree - 1) * delta := by
      have hsum := Finset.mem_antidiagonal.mp (Finset.mem_filter.mp hpair).1
      have hlt := (Finset.mem_filter.mp hpair).2
      have hfirst : familyNorm primary body order pf bf (elementary primary body order atoms pair.1) ≤
          scale ^ (degree - 1) := by
        by_cases hz : pair.1 = 0
        · rw [hz, elementary_zero, familyNorm_one]
          exact one_le_pow₀ hscale
        · have h := ih pair.1 hlt (by omega) (by omega)
          have hscaled : delta * scale ^ pair.1 ≤ scale ^ pair.1 := by
            exact (mul_le_mul_of_nonneg_right hsmall (pow_nonneg (by linarith : 0 ≤ scale) _)).trans_eq (one_mul _)
          exact (h.trans hscaled).trans (pow_le_pow_right₀ hscale (by omega))
      exact mul_le_mul hfirst (hpowers pair.2 (by omega) (by omega))
        (familyNorm_nonneg primary body order pf bf hpf hbf _) (pow_nonneg (by linarith : 0 ≤ scale) _)
    have hcard : (((Finset.antidiagonal degree).filter (fun pair => pair.1 < degree)).card : ℝ) ≤ scale := by
      have h : ((Finset.antidiagonal degree).filter (fun pair => pair.1 < degree)).card ≤ order + 1 :=
        (Finset.card_filter_le (Finset.antidiagonal degree) (fun pair => pair.1 < degree)).trans
          (by simpa using (by omega : degree + 1 ≤ order + 1))
      change (((Finset.antidiagonal degree).filter (fun pair => pair.1 < degree)).card : ℝ) ≤ ((order + 1 : ℕ) : ℝ)
      exact_mod_cast h
    have hnewton := newton_norm_le primary body order degree pf bf hpf hbf atoms
    calc
      _ ≤ (degree : ℝ) * familyNorm primary body order pf bf (elementary primary body order atoms degree) := by
        have hd : (1 : ℝ) ≤ degree := Nat.one_le_cast.mpr hpositive
        nlinarith
      _ ≤ ∑ pair ∈ (Finset.antidiagonal degree).filter (fun pair => pair.1 < degree),
          familyNorm primary body order pf bf (elementary primary body order atoms pair.1) *
            familyNorm primary body order pf bf (powerSum primary body order atoms pair.2) := hnewton
      _ ≤ ∑ _pair ∈ (Finset.antidiagonal degree).filter (fun pair => pair.1 < degree), scale ^ (degree - 1) * delta :=
        Finset.sum_le_sum hterm
      _ = (((Finset.antidiagonal degree).filter (fun pair => pair.1 < degree)).card : ℝ) *
          (scale ^ (degree - 1) * delta) := by simp
      _ ≤ scale * (scale ^ (degree - 1) * delta) :=
        mul_le_mul_of_nonneg_right hcard (mul_nonneg (pow_nonneg (by linarith : 0 ≤ scale) _) hdelta)
      _ = _ := by
        change _ = delta * scale ^ degree
        conv_rhs => rw [show degree = (degree - 1) + 1 by omega, pow_succ]
        ring

theorem product_norm_le (primary : FiniteDist Primary) (body : FiniteDist Body) (order : ℕ)
    (pf bf : ℝ) (hpf : 0 ≤ pf) (hbf : 0 ≤ bf) (atoms : Index → KernelFamily primary body order)
    (hzero : ∀ index, atoms index (zeroArity order) = 0) (hsize : order ≤ Fintype.card Index)
    (delta : ℝ) (hdelta : 0 ≤ delta) (hsmall : delta ≤ 1)
    (hpowers : ∀ power, 1 ≤ power → power ≤ order →
      familyNorm primary body order pf bf (powerSum primary body order atoms power) ≤ delta) :
    familyNorm primary body order pf bf ((∏ index, (1 + atoms index)) - 1) ≤
      (order : ℝ) * delta * ((order + 1 : ℕ) : ℝ) ^ order := by
  rw [product_one_add_sub_one primary body order atoms hzero hsize]
  calc
    _ ≤ ∑ degree ∈ Finset.range order,
        familyNorm primary body order pf bf (elementary primary body order atoms (degree + 1)) :=
      familyNorm_sum_le primary body order pf bf hpf hbf _ _
    _ ≤ ∑ _degree ∈ Finset.range order, delta * ((order + 1 : ℕ) : ℝ) ^ order := by
      apply Finset.sum_le_sum
      intro degree hdegree
      have hd := Finset.mem_range.mp hdegree
      exact (elementary_norm_le primary body order pf bf hpf hbf atoms delta hdelta hsmall hpowers
        (degree + 1) (by omega) (by omega)).trans
          (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by exact_mod_cast (show 1 ≤ order + 1 by omega))
            (by omega : degree + 1 ≤ order)) hdelta)
    _ = _ := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring

theorem powerSum_norm_le_of_square (primary : FiniteDist Primary) (body : FiniteDist Body) (order : ℕ)
    (pf bf : ℝ) (hpf : 0 ≤ pf) (hbf : 0 ≤ bf) (atoms : Index → KernelFamily primary body order)
    (delta : ℝ)
    (hfirst : familyNorm primary body order pf bf (∑ index, atoms index) ≤ delta)
    (hsquares : (∑ index, familyNorm primary body order pf bf (atoms index) ^ 2) ≤ delta)
    (hatoms : ∀ index, familyNorm primary body order pf bf (atoms index) ≤ 1)
    (power : ℕ) (hpower : 1 ≤ power) :
    familyNorm primary body order pf bf (powerSum primary body order atoms power) ≤ delta := by
  by_cases hone : power = 1
  · simpa only [powerSum, hone, pow_one] using hfirst
  · have htwo : 2 ≤ power := by omega
    have hpoint (index : Index) : familyNorm primary body order pf bf (atoms index) ^ power ≤
        familyNorm primary body order pf bf (atoms index) ^ 2 := by
      have hnonneg := familyNorm_nonneg primary body order pf bf hpf hbf (atoms index)
      have htail : familyNorm primary body order pf bf (atoms index) ^ (power - 2) ≤ 1 :=
        pow_le_one₀ hnonneg (hatoms index)
      calc
        _ = familyNorm primary body order pf bf (atoms index) ^ 2 *
            familyNorm primary body order pf bf (atoms index) ^ (power - 2) := by
          rw [← pow_add]
          congr 1
          omega
        _ ≤ familyNorm primary body order pf bf (atoms index) ^ 2 * 1 :=
          mul_le_mul_of_nonneg_left htail (sq_nonneg _)
        _ = _ := mul_one _
    calc
      _ ≤ ∑ index, familyNorm primary body order pf bf (atoms index ^ power) :=
        familyNorm_sum_le primary body order pf bf hpf hbf _ _
      _ ≤ ∑ index, familyNorm primary body order pf bf (atoms index) ^ 2 := by
        apply Finset.sum_le_sum
        intro index _
        exact (familyNorm_pow_le primary body order pf bf hpf hbf (atoms index) power).trans (hpoint index)
      _ ≤ _ := hsquares

/-- Full product stability needs only its genuinely canceled first sum,
the population-weighted square budget, and small individual atoms. -/
theorem complete_product_norm_le (primary : FiniteDist Primary) (body : FiniteDist Body) (order : ℕ)
    (pf bf : ℝ) (hpf : 0 ≤ pf) (hbf : 0 ≤ bf) (atoms : Index → KernelFamily primary body order)
    (hzero : ∀ index, atoms index (zeroArity order) = 0) (hsize : order ≤ Fintype.card Index)
    (delta : ℝ) (hdelta : 0 ≤ delta) (hsmall : delta ≤ 1)
    (hfirst : familyNorm primary body order pf bf (∑ index, atoms index) ≤ delta)
    (hsquares : (∑ index, familyNorm primary body order pf bf (atoms index) ^ 2) ≤ delta)
    (hatoms : ∀ index, familyNorm primary body order pf bf (atoms index) ≤ 1) :
    familyNorm primary body order pf bf ((∏ index, (1 + atoms index)) - 1) ≤
      (order : ℝ) * delta * ((order + 1 : ℕ) : ℝ) ^ order := by
  exact product_norm_le primary body order pf bf hpf hbf atoms hzero hsize delta hdelta hsmall
    (fun power hpower _ => powerSum_norm_le_of_square primary body order pf bf hpf hbf atoms delta
      hfirst hsquares hatoms power hpower)

end

end CurrentAFT.GradedNewtonNorm
