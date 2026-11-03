import CurrentAFT.ProtectedCycle

/-!
# Finite-support path likelihood from the actual latent sampling law

The path is sampled by an initial latent scalar and one fresh independent
scalar for each edge. The transfer matrix has entries
`sqrt(p u) * sqrt(p v) * 1_{difference u v = color}`. Repeated finite
Cauchy--Schwarz proves the joint point-mass bound; it is not a hypothesis.
-/

namespace CurrentAFT.PathLikelihood

open AFT
open scoped BigOperators Classical

noncomputable section

variable {Scalar Difference : Type*} [Fintype Scalar] [Fintype Difference]

/-- The actual law of one difference of two independent latent scalars. -/
def marginal (source : FiniteDist Scalar) (difference : Scalar → Scalar → Difference) :
    FiniteDist Difference :=
  (source.prod source).map (fun pair => difference pair.1 pair.2)

/-- Generate a path after fixing its initial latent scalar. Every next
scalar is an independent draw from exactly the same source. -/
def pathKernel (source : FiniteDist Scalar) (difference : Scalar → Scalar → Difference) :
    (length : ℕ) → Scalar → FiniteDist (Fin length → Difference)
  | 0, _ => FiniteDist.uniform (Fin 0 → Difference)
  | length + 1, previous => source.mix (fun next =>
      (pathKernel source difference length next).map
        (fun tail => Fin.cons (difference previous next) tail))

/-- The initial latent scalar is also independently drawn from the source. -/
def pathLaw (source : FiniteDist Scalar) (difference : Scalar → Scalar → Difference)
    (length : ℕ) : FiniteDist (Fin length → Difference) :=
  source.mix (pathKernel source difference length)

def boundary (source : FiniteDist Scalar) (scalar : Scalar) : ℝ :=
  Real.sqrt (source.weight scalar)

def transfer (source : FiniteDist Scalar) (difference : Scalar → Scalar → Difference)
    (color : Difference) (first second : Scalar) : ℝ :=
  if difference first second = color then boundary source first * boundary source second else 0

def squareSum (vector : Scalar → ℝ) : ℝ := ∑ scalar, vector scalar ^ 2

@[simp] theorem boundary_sq (source : FiniteDist Scalar) (scalar : Scalar) :
    boundary source scalar ^ 2 = source.weight scalar :=
  Real.sq_sqrt (source.nonneg scalar)

@[simp] theorem boundary_squareSum (source : FiniteDist Scalar) : squareSum (boundary source) = 1 := by
  simp only [squareSum, boundary_sq, source.sum_one]

omit [Fintype Difference] in
theorem transfer_nonneg (source : FiniteDist Scalar)
    (difference : Scalar → Scalar → Difference) (color : Difference) (first second : Scalar) :
    0 ≤ transfer source difference color first second := by
  unfold transfer boundary
  split_ifs
  · positivity
  · rfl

/-- The actual Frobenius energy equals the one-difference marginal mass. -/
theorem transfer_square_sum (source : FiniteDist Scalar)
    (difference : Scalar → Scalar → Difference) (color : Difference) :
    (∑ first, ∑ second, transfer source difference color first second ^ 2) =
      (marginal source difference).weight color := by
  simp only [marginal, FiniteDist.map_weight, Fintype.sum_prod_type, FiniteDist.prod_weight]
  apply Finset.sum_congr rfl
  intro first _
  apply Finset.sum_congr rfl
  intro second _
  unfold transfer
  split_ifs
  · rw [mul_pow, boundary_sq, boundary_sq]
  · norm_num

/-- Cauchy--Schwarz in each matrix row gives the Frobenius action bound. -/
theorem transfer_squareSum_le (source : FiniteDist Scalar)
    (difference : Scalar → Scalar → Difference) (color : Difference) (vector : Scalar → ℝ) :
    squareSum (fun first => ∑ second, transfer source difference color first second * vector second) ≤
      (marginal source difference).weight color * squareSum vector := by
  unfold squareSum
  calc
    _ ≤ ∑ first, (∑ second, transfer source difference color first second ^ 2) *
        ∑ second, vector second ^ 2 := by
      apply Finset.sum_le_sum
      intro first _
      exact Finset.sum_mul_sq_le_sq_mul_sq Finset.univ _ _
    _ = _ := by rw [← Finset.sum_mul, transfer_square_sum]

/-- The transfer product applied to the final boundary vector. -/
def amplitude (source : FiniteDist Scalar) (difference : Scalar → Scalar → Difference) :
    (length : ℕ) → (Fin length → Difference) → Scalar → ℝ
  | 0, _, scalar => boundary source scalar
  | length + 1, word, scalar =>
      ∑ next, transfer source difference (word 0) scalar next *
        amplitude source difference length (fun index => word index.succ) next

omit [Fintype Difference] in
theorem amplitude_nonneg (source : FiniteDist Scalar)
    (difference : Scalar → Scalar → Difference) (length : ℕ)
    (word : Fin length → Difference) (scalar : Scalar) :
    0 ≤ amplitude source difference length word scalar := by
  induction length generalizing scalar with
  | zero => exact Real.sqrt_nonneg _
  | succ length ih =>
    exact Finset.sum_nonneg fun next _ =>
      mul_nonneg (transfer_nonneg source difference _ _ _) (ih _ _)

/-- Every transfer multiplication contributes its actual marginal energy. -/
theorem amplitude_squareSum_le (source : FiniteDist Scalar)
    (difference : Scalar → Scalar → Difference) (length : ℕ) (word : Fin length → Difference) :
    squareSum (amplitude source difference length word) ≤
      ∏ index, (marginal source difference).weight (word index) := by
  induction length with
  | zero => simp only [amplitude, boundary_squareSum, Fin.prod_univ_zero, le_refl]
  | succ length ih =>
    apply (transfer_squareSum_le source difference (word 0)
      (amplitude source difference length (fun index => word index.succ))).trans
    rw [Fin.prod_univ_succ]
    exact mul_le_mul_of_nonneg_left (ih _) ((marginal source difference).nonneg _)

/-- Exact weight recurrence of the independently generated path. -/
theorem pathKernel_succ_weight (source : FiniteDist Scalar)
    (difference : Scalar → Scalar → Difference) (length : ℕ) (previous : Scalar)
    (head : Difference) (tail : Fin length → Difference) :
    (pathKernel source difference (length + 1) previous).weight (Fin.cons head tail) =
      ∑ next, source.weight next *
        (if difference previous next = head then
          (pathKernel source difference length next).weight tail else 0) := by
  simp only [pathKernel, FiniteDist.mix_weight, FiniteDist.map_weight, Fin.cons_inj]
  apply Finset.sum_congr rfl
  intro next _
  by_cases hhead : difference previous next = head
  · simp [hhead]
  · simp [hhead]

/-- The boundary-transfer product counts each independent latent mass once. -/
theorem amplitude_kernel_identity (source : FiniteDist Scalar)
    (difference : Scalar → Scalar → Difference) (length : ℕ)
    (word : Fin length → Difference) (previous : Scalar) :
    boundary source previous * amplitude source difference length word previous =
      source.weight previous * (pathKernel source difference length previous).weight word := by
  induction length generalizing previous with
  | zero =>
    simp only [amplitude, pathKernel, FiniteDist.uniform_weight, Fintype.card_unique,
      Nat.cast_one, inv_one, mul_one]
    simpa only [pow_two] using boundary_sq source previous
  | succ length ih =>
    rw [show word = Fin.cons (word 0) (fun index => word index.succ) by ext index; refine Fin.cases rfl (fun _ => rfl) index]
    rw [pathKernel_succ_weight]
    simp only [amplitude, Fin.cons_zero, Fin.cons_succ]
    rw [Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro next _
    by_cases hhead : difference previous next = word 0
    · simp only [transfer, if_pos hhead]
      calc
        _ = boundary source previous ^ 2 *
            (boundary source next * amplitude source difference length (fun index => word index.succ) next) := by ring
        _ = _ := by rw [boundary_sq, ih]
    · simp only [transfer, if_neg hhead, zero_mul, mul_zero]

/-- Exact transfer-product expression for the actual path joint mass. -/
theorem pathLaw_weight_transfer (source : FiniteDist Scalar)
    (difference : Scalar → Scalar → Difference) (length : ℕ) (word : Fin length → Difference) :
    (pathLaw source difference length).weight word =
      ∑ scalar, boundary source scalar * amplitude source difference length word scalar := by
  simp only [pathLaw, FiniteDist.mix_weight]
  apply Finset.sum_congr rfl
  intro scalar _
  exact (amplitude_kernel_identity source difference length word scalar).symm

/-- The true pointwise path-mass bound, proved by repeated finite
Cauchy--Schwarz rather than supplied as an assumption. -/
theorem pathLaw_weight_sq_le (source : FiniteDist Scalar)
    (difference : Scalar → Scalar → Difference) (length : ℕ) (word : Fin length → Difference) :
    (pathLaw source difference length).weight word ^ 2 ≤
      ∏ index, (marginal source difference).weight (word index) := by
  rw [pathLaw_weight_transfer]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (boundary source) (amplitude source difference length word)
  change _ ≤ squareSum (boundary source) * squareSum
    (amplitude source difference length word) at hcs
  rw [boundary_squareSum, one_mul] at hcs
  exact hcs.trans (amplitude_squareSum_le source difference length word)

/-- Product reference used for the actual path likelihood. -/
def reference (source : FiniteDist Scalar) (difference : Scalar → Scalar → Difference)
    (length : ℕ) : FiniteDist (Fin length → Difference) :=
  FiniteDist.independent (fun _ : Fin length => marginal source difference)

/-- The probability bound in its square-root product form. -/
theorem pathLaw_weight_le_sqrt_product (source : FiniteDist Scalar)
    (difference : Scalar → Scalar → Difference) (length : ℕ) (word : Fin length → Difference) :
    (pathLaw source difference length).weight word ≤
      ∏ index, Real.sqrt ((marginal source difference).weight (word index)) := by
  have hsquare := pathLaw_weight_sq_le source difference length word
  have hproduct :
      (∏ index, Real.sqrt ((marginal source difference).weight (word index))) ^ 2 =
      ∏ index, (marginal source difference).weight (word index) := by
    rw [← Finset.prod_pow]
    apply Finset.prod_congr rfl
    intro index _
    exact Real.sq_sqrt ((marginal source difference).nonneg _)
  have hnonneg : 0 ≤ ∏ index, Real.sqrt ((marginal source difference).weight (word index)) :=
    Finset.prod_nonneg fun _ _ => Real.sqrt_nonneg _
  nlinarith [(pathLaw source difference length).nonneg word]

/-- The actual path law has no mass outside its product reference support. -/
theorem pathLaw_absolute_continuous (source : FiniteDist Scalar)
    (difference : Scalar → Scalar → Difference) (length : ℕ) (word : Fin length → Difference)
    (hzero : (reference source difference length).weight word = 0) :
    (pathLaw source difference length).weight word = 0 := by
  have hsquare := pathLaw_weight_sq_le source difference length word
  change (∏ index, (marginal source difference).weight (word index)) = 0 at hzero
  rw [hzero] at hsquare
  nlinarith [(pathLaw source difference length).nonneg word]

/-- Squared L2 likelihood norm under the actual independent marginal reference.
Division by zero is zero, and absolute continuity is proved separately above. -/
def likelihoodEnergy (source : FiniteDist Scalar) (difference : Scalar → Scalar → Difference)
    (length : ℕ) : ℝ :=
  ∑ word, ((pathLaw source difference length).weight word /
    (reference source difference length).weight word) ^ 2 *
      (reference source difference length).weight word

/-- Each word contributes at most one to the squared likelihood energy. -/
theorem likelihood_term_le_one (source : FiniteDist Scalar)
    (difference : Scalar → Scalar → Difference) (length : ℕ) (word : Fin length → Difference) :
    ((pathLaw source difference length).weight word /
        (reference source difference length).weight word) ^ 2 *
      (reference source difference length).weight word ≤ 1 := by
  by_cases hzero : (reference source difference length).weight word = 0
  · simp [hzero]
  · have hpositive : 0 < (reference source difference length).weight word :=
      lt_of_le_of_ne ((reference source difference length).nonneg word) (Ne.symm hzero)
    have hsquare := pathLaw_weight_sq_le source difference length word
    change (pathLaw source difference length).weight word ^ 2 ≤
      (reference source difference length).weight word at hsquare
    calc
      _ = (pathLaw source difference length).weight word ^ 2 /
          (reference source difference length).weight word := by field_simp
      _ ≤ 1 := (div_le_one hpositive).mpr hsquare

/-- Complete finite-support path likelihood estimate, with the difference
alphabet counted only after proving the pointwise transfer bound. -/
theorem likelihoodEnergy_le_card_pow (source : FiniteDist Scalar)
    (difference : Scalar → Scalar → Difference) (length : ℕ) :
    likelihoodEnergy source difference length ≤ (Fintype.card Difference : ℝ) ^ length := by
  unfold likelihoodEnergy
  calc
    _ ≤ ∑ _word : Fin length → Difference, (1 : ℝ) :=
      Finset.sum_le_sum (fun word _ => likelihood_term_le_one source difference length word)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
      Fintype.card_fun, Fintype.card_fin, Nat.cast_pow]

/-- True integer difference, encoded in its finite safe interval. -/
def windowDifference (cutoff : ℕ) (first second : GaussianSource.Window cutoff) :
    GaussianSource.Window (2 * cutoff) :=
  ⟨(second : ℤ) - (first : ℤ), by
    have hfirst := Finset.mem_Icc.mp first.property
    have hsecond := Finset.mem_Icc.mp second.property
    apply Finset.mem_Icc.mpr
    push_cast
    constructor <;> omega⟩

@[simp] theorem windowDifference_val (cutoff : ℕ)
    (first second : GaussianSource.Window cutoff) :
    (windowDifference cutoff first second : ℤ) = (second : ℤ) - (first : ℤ) := rfl

theorem windowDifference_card (cutoff : ℕ) :
    Fintype.card (GaussianSource.Window (2 * cutoff)) = 4 * cutoff + 1 := by
  simp only [GaussianSource.Window, Fintype.card_coe, Int.card_Icc]
  omega

/-- The current manuscript's actual protected-Gaussian path likelihood bound.
The squared norm is at most `(4*cutoff+1)^length`. -/
theorem gaussian_path_likelihoodEnergy (width : ℝ) (cutoff length : ℕ) :
    likelihoodEnergy (GaussianSource.windowGaussian width cutoff)
      (windowDifference cutoff) length ≤ ((4 * cutoff + 1 : ℕ) : ℝ) ^ length := by
  simpa only [windowDifference_card] using
    likelihoodEnergy_le_card_pow (GaussianSource.windowGaussian width cutoff)
      (windowDifference cutoff) length

/-- The corresponding L2 norm estimate, with the exact square-root exponent. -/
theorem gaussian_path_likelihoodNorm (width : ℝ) (cutoff length : ℕ) :
    Real.sqrt (likelihoodEnergy (GaussianSource.windowGaussian width cutoff)
      (windowDifference cutoff) length) ≤ Real.sqrt (((4 * cutoff + 1 : ℕ) : ℝ) ^ length) :=
  Real.sqrt_le_sqrt (gaussian_path_likelihoodEnergy width cutoff length)

/-- The original norm exponent in the current manuscript. -/
theorem gaussian_path_likelihoodNorm_rpow (width : ℝ) (cutoff length : ℕ) :
    Real.sqrt (likelihoodEnergy (GaussianSource.windowGaussian width cutoff)
      (windowDifference cutoff) length) ≤
        (((4 * cutoff + 1 : ℕ) : ℝ) ^ ((length : ℝ) / 2)) := by
  apply (gaussian_path_likelihoodNorm width cutoff length).trans_eq
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast_mul (by positivity)]
  congr 1
  ring

/-- The explicit head-and-tail bijection for the independent latent word. -/
def latentConsEquiv (length : ℕ) : (Scalar × (Fin length → Scalar)) ≃ (Fin (length + 1) → Scalar) where
  toFun pair := Fin.cons pair.1 pair.2
  invFun word := (word 0, fun index => word index.succ)
  left_inv pair := by cases pair; rfl
  right_inv word := by ext index; refine Fin.cases rfl (fun _ => rfl) index

/-- The full independent latent-word law. -/
def latentLaw (source : FiniteDist Scalar) (length : ℕ) : FiniteDist (Fin length → Scalar) :=
  FiniteDist.independent (fun _ : Fin length => source)

/-- Independent words split into one fresh head and an independent tail. -/
theorem latentLaw_succ (source : FiniteDist Scalar) (length : ℕ) :
    latentLaw source (length + 1) =
      (source.prod (latentLaw source length)).map (latentConsEquiv length) := by
  ext word
  rw [FiniteDist.map_equiv_weight]
  change (∏ index : Fin (length + 1), source.weight (word index)) =
    source.weight (word 0) * ∏ index : Fin length, source.weight (word index.succ)
  exact Fin.prod_univ_succ _

/-- The path consists of successive differences of the actual latent word. -/
def pathOutput (difference : Scalar → Scalar → Difference) (length : ℕ)
    (latent : Fin (length + 1) → Scalar) (index : Fin length) : Difference :=
  difference (latent index.castSucc) (latent index.succ)

omit [Fintype Scalar] [Fintype Difference] in
theorem pathOutput_cons_cons (difference : Scalar → Scalar → Difference) (length : ℕ)
    (previous next : Scalar) (tail : Fin length → Scalar) :
    pathOutput difference (length + 1) (Fin.cons previous (Fin.cons next tail)) =
      Fin.cons (difference previous next) (pathOutput difference length (Fin.cons next tail)) := by
  ext index
  refine Fin.cases rfl (fun index => ?_) index
  simp only [pathOutput, Fin.cons_succ, Fin.castSucc_succ]

/-- Mapping an independent pair is the same experiment as sampling its
first component and then independently mapping the second component. -/
theorem prod_map_mix {First Second Output : Type*}
    [Fintype First] [Fintype Second] [Fintype Output]
    (first : FiniteDist First) (second : FiniteDist Second) (output : First × Second → Output) :
    (first.prod second).map output =
      first.mix (fun value => second.map (fun rest => output (value, rest))) := by
  ext point
  simp only [FiniteDist.map_weight, FiniteDist.mix_weight, FiniteDist.prod_weight,
    Fintype.sum_prod_type, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro value _
  apply Finset.sum_congr rfl
  intro rest _
  by_cases h : output (value, rest) = point <;> simp [h]

/-- The recursively generated conditional path is exactly the pushforward
of a genuine independent latent tail, with its initial scalar fixed. -/
theorem pathKernel_eq_latent_map (source : FiniteDist Scalar)
    (difference : Scalar → Scalar → Difference) (length : ℕ) (previous : Scalar) :
    pathKernel source difference length previous =
      (latentLaw source length).map (fun tail => pathOutput difference length (Fin.cons previous tail)) := by
  induction length generalizing previous with
  | zero =>
    ext word
    have hequal (tail : Fin 0 → Scalar) :
        pathOutput difference 0 (Fin.cons previous tail) = word := Subsingleton.elim _ _
    simp [pathKernel, latentLaw, FiniteDist.map_weight, FiniteDist.independent,
      FiniteDist.uniform_weight, hequal]
  | succ length ih =>
    rw [latentLaw_succ, FiniteDist.map_map, prod_map_mix]
    change source.mix (fun next =>
      (pathKernel source difference length next).map (fun tail => Fin.cons (difference previous next) tail)) =
      source.mix (fun next => (latentLaw source length).map (fun tail =>
        pathOutput difference (length + 1) (Fin.cons previous (Fin.cons next tail))))
    congr 1
    funext next
    rw [ih, FiniteDist.map_map]
    congr 1
    funext tail
    exact (pathOutput_cons_cons difference length previous next tail).symm

/-- The exact path law in the manuscript: `length+1` independent protected
latent scalars, followed by all `length` successive differences. -/
theorem pathLaw_eq_independent_pushforward (source : FiniteDist Scalar)
    (difference : Scalar → Scalar → Difference) (length : ℕ) :
    pathLaw source difference length =
      (FiniteDist.independent (fun _ : Fin (length + 1) => source)).map (pathOutput difference length) := by
  change pathLaw source difference length = (latentLaw source (length + 1)).map _
  rw [latentLaw_succ, FiniteDist.map_map, prod_map_mix]
  unfold pathLaw
  congr 1
  funext previous
  exact pathKernel_eq_latent_map source difference length previous

end

end CurrentAFT.PathLikelihood
