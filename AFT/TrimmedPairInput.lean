import AFT.PairInputFibers
import AFT.CanonicalSmoothing
import AFT.TrimmedPairCoreBounds

/-! # Fixed fibers of the actual trimmed pair seed and its finite root input -/

namespace AFT.SafeConvolution

open scoped BigOperators

variable {G : Type*} [Fintype G] [AddCommGroup G] [DecidableEq G]

theorem RowBound.uniformCanonical {bound : ℝ} {profile : G × G → ℝ}
    (h : RowBound bound profile) : RowBound (2 * bound) (uniformCanonical profile) := by
  intro first
  have hh := SafePair.coreSeed_row_L2_le (Finset.univ : Finset G)
    (fun x y => profile (x,y)) Finset.univ_nonempty bound h first
  change countingL2 (fun y => SafePair.coreSeed Finset.univ (fun x y => profile (x,y)) first y) ≤ _ at hh
  simpa only [SafePair.coreSeed, SafePair.canonicalPair, SafePair.restrictPair,
    uniformFiniteProfile, Finset.mem_univ, and_self, if_true, Finset.card_univ,
    uniformCanonical_apply, one_div] using hh

theorem SupBound.uniformCanonical {bound : ℝ} {profile : G × G → ℝ}
    (h : SupBound bound profile) : SupBound (4 * bound) (uniformCanonical profile) := by
  intro point
  have hh := SafePair.coreSeed_abs_le (Finset.univ : Finset G)
    (fun x y => profile (x,y)) Finset.univ_nonempty bound (fun x y => h (x,y)) point.1 point.2
  simpa only [SafePair.coreSeed, SafePair.canonicalPair, SafePair.restrictPair,
    uniformFiniteProfile, Finset.mem_univ, and_self, if_true, Finset.card_univ,
    uniformCanonical_apply, one_div] using hh

/-- Complete coarse fixed-fiber bounds, including the finite root input,
its actual root image, and the entire residual against the full target. -/
theorem compact_pair_fiber_bounds (core : Finset G) (hne : core.Nonempty)
    (mass : G → G → ℝ) (rowBound supBound : ℝ)
    (hrow : RowBound rowBound (fun point : G × G => mass point.1 point.2))
    (hsup : SupBound supBound (fun point : G × G => mass point.1 point.2))
    (root smooth : FiniteDist (G × G)) (depth : ℕ) :
    let seed := fun point : G × G => SafePair.coreSeed core mass point.1 point.2
    let input := compactRootInput root smooth depth seed
    let image := convolution root.weight input
    let target := uniformCanonical (fun point : G × G => mass point.1 point.2)
    let geometric := ∑ i ∈ Finset.range (depth + 1), (2 : ℝ) ^ i
    RowBound (2 * geometric * rowBound) input ∧
    SupBound (4 * geometric * supBound) input ∧
    RowBound (2 * (geometric + 1) * rowBound) (image - target) ∧
    SupBound (4 * (geometric + 1) * supBound) (image - target) := by
  dsimp only
  let geometric := ∑ i ∈ Finset.range (depth + 1), (2 : ℝ) ^ i
  have hsrow : RowBound (2 * rowBound) (fun point : G × G => SafePair.coreSeed core mass point.1 point.2) :=
    fun first => SafePair.coreSeed_row_L2_le core mass hne rowBound hrow first
  have hssup : SupBound (4 * supBound) (fun point : G × G => SafePair.coreSeed core mass point.1 point.2) :=
    fun point : G × G => SafePair.coreSeed_abs_le core mass hne supBound (fun x y => hsup (x,y)) point.1 point.2
  have hir := hsrow.compactRootInput root smooth depth
  have his := hssup.compactRootInput root smooth depth
  have herr := (hir.probability_convolution root).add hrow.uniformCanonical.neg
  have hers := (his.probability_convolution root).add hsup.uniformCanonical.neg
  refine ⟨?_, ?_, ?_, ?_⟩
  · convert hir using 1; ring
  · convert his using 1; ring
  · convert herr using 1; ring
  · convert hers using 1; ring

omit [AddCommGroup G] in
theorem coreSeed_transpose (core : Finset G) (mass : G → G → ℝ) :
    (fun point : G × G => SafePair.coreSeed core mass point.2 point.1) =
      (fun point : G × G => SafePair.coreSeed core (fun x y => mass y x) point.1 point.2) := by
  funext point
  have hrestrict (x y : G) : SafePair.restrictPair core mass y x =
      SafePair.restrictPair core (fun x y => mass y x) x y := by
    simp only [SafePair.restrictPair, and_comm]
  simp only [SafePair.coreSeed, SafePair.canonicalPair]
  simp_rw [hrestrict]
  rw [Finset.sum_comm (f := fun x y => SafePair.restrictPair core (fun x y => mass y x) y x)]
  ring

omit [AddCommGroup G] [DecidableEq G] in
theorem uniformCanonical_transpose (profile : G × G → ℝ) :
    (fun point : G × G => uniformCanonical profile point.swap) =
      uniformCanonical (fun point : G × G => profile point.swap) := by
  funext point
  simp only [uniformCanonical_apply, SafePair.canonicalPair, Prod.swap]
  rw [Finset.sum_comm (f := fun x y => profile (y,x))]
  ring

/-- The other fixed endpoint is covered without requiring the root joint
law or its compact smoothing law to be a product or symmetric. -/
theorem compact_pair_column_bounds (core : Finset G) (hne : core.Nonempty)
    (mass : G → G → ℝ) (rowBound supBound : ℝ)
    (hcolumn : RowBound rowBound (fun point : G × G => mass point.2 point.1))
    (hsup : SupBound supBound (fun point : G × G => mass point.1 point.2))
    (root smooth : FiniteDist (G × G)) (depth : ℕ) :
    let seed := fun point : G × G => SafePair.coreSeed core mass point.1 point.2
    let input := compactRootInput root smooth depth seed
    let image := convolution root.weight input
    let target := uniformCanonical (fun point : G × G => mass point.1 point.2)
    let geometric := ∑ i ∈ Finset.range (depth + 1), (2 : ℝ) ^ i
    RowBound (2 * geometric * rowBound) (fun point : G × G => input point.swap) ∧
    RowBound (2 * (geometric + 1) * rowBound) (fun point : G × G => (image - target) point.swap) := by
  have hh := compact_pair_fiber_bounds core hne (fun x y => mass y x) rowBound supBound
    hcolumn (fun point : G × G => hsup point.swap) (root.map Prod.swap) (smooth.map Prod.swap) depth
  dsimp only at hh ⊢
  have hi := compactRootInput_transpose root smooth depth (fun point : G × G => SafePair.coreSeed core mass point.1 point.2)
  change (fun point : G × G => compactRootInput root smooth depth
    (fun point : G × G => SafePair.coreSeed core mass point.1 point.2) point.swap) =
    compactRootInput (root.map Prod.swap) (smooth.map Prod.swap) depth
      (fun point : G × G => SafePair.coreSeed core mass point.2 point.1) at hi
  rw [coreSeed_transpose] at hi
  constructor
  · rw [hi]
    exact hh.1
  · have himage := convolution_transpose root
      (compactRootInput root smooth depth (fun point : G × G => SafePair.coreSeed core mass point.1 point.2))
    rw [hi] at himage
    change RowBound _ ((fun point : G × G => convolution root.weight _ point.swap) -
      (fun point : G × G => uniformCanonical (fun point : G × G => mass point.1 point.2) point.swap))
    rw [himage, uniformCanonical_transpose]
    exact hh.2.2.1

end AFT.SafeConvolution

namespace AFT.TrimmedSlice

open scoped BigOperators
open SafeConvolution

variable {τ : Type*} [Fintype τ]

/-- The actual integer pair has sharp row and point bounds before any
canonicalization, including its true reciprocal slice denominator. -/
theorem mixedPair_input_bounds
    (modulus : ℕ) (boundary shiftBound cutoff : ℤ) (width : ℕ) (hwidth : width ≠ 0)
    (starts sources : τ → ℤ) (sourceLaw : FiniteDist τ) (hb : 0 ≤ boundary)
    (hstarts : ∀ index shift, shift ∈ anchorInterval (starts index) width → |shift| ≤ shiftBound)
    (hsources : ∀ index, |sources index| ≤ cutoff)
    (hclear : 2 * boundary + shiftBound + cutoff < modulus) :
    let denominator := (modulus : ℝ) - 2 * boundary - shiftBound - cutoff
    let mass := fun point : Fin modulus × Fin modulus =>
      mixedPair modulus boundary starts sources sourceLaw.weight width point.1 point.2
    RowBound (Real.sqrt (1 / ((width : ℝ) * denominator ^ 2))) mass ∧
    SupBound (1 / ((width : ℝ) * denominator)) mass := by
  constructor
  · intro first
    exact Real.sqrt_le_sqrt (mixedPair_fiber_square_le modulus boundary shiftBound cutoff width hwidth
      starts sources sourceLaw hb hstarts hsources hclear first)
  · intro point
    rw [abs_of_nonneg (mixedPair_nonneg modulus boundary starts sources sourceLaw.weight width
      sourceLaw.nonneg point.1 point.2)]
    exact mixedPair_le modulus boundary shiftBound cutoff width starts sources sourceLaw.weight
      sourceLaw.nonneg sourceLaw.sum_one hstarts hsources hclear point.1 point.2

end AFT.TrimmedSlice
