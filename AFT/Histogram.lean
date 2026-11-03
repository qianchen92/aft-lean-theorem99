import AFT.TotalVariation

/-!
# Concrete histograms and uniform position relabeling

This is the finite combinatorial step of reference V7, Corollary 9.21.
Histograms count colors in actual vectors `Fin dimension → Color`. Equality
of histograms is proved equivalent to relabeling positions by a permutation.
-/

namespace AFT

open scoped BigOperators
open scoped Classical

variable {dimension : ℕ} {Color : Type*}

/-- A finite encoding of color counts; every count lies between zero and the
number of positions. Invalid count vectors are permitted in this ambient type. -/
abbrev Histogram (dimension : ℕ) (Color : Type*) := Color → Fin (dimension + 1)

/-- The actual histogram of a vector, with counts defined by color fibers. -/
noncomputable def histogram (vector : Fin dimension → Color) : Histogram dimension Color := by
  classical
  exact fun color => ⟨Fintype.card {position // vector position = color}, by
    have h := Fintype.card_subtype_le (fun position => vector position = color)
    simpa only [Fintype.card_fin, Nat.lt_succ_iff] using h⟩

@[simp] theorem histogram_count (vector : Fin dimension → Color) (color : Color) :
    (histogram vector color : ℕ) = Fintype.card {position // vector position = color} := by
  classical
  rfl

/-- Reindex a vector by a permutation of positions. -/
def relabel (vector : Fin dimension → Color) (permutation : Equiv.Perm (Fin dimension)) :
    Fin dimension → Color := vector ∘ permutation

@[simp] theorem relabel_apply (vector : Fin dimension → Color)
    (permutation : Equiv.Perm (Fin dimension)) (position : Fin dimension) :
    relabel vector permutation position = vector (permutation position) := rfl

theorem histogram_relabel (vector : Fin dimension → Color)
    (permutation : Equiv.Perm (Fin dimension)) :
    histogram (relabel vector permutation) = histogram vector := by
  classical
  funext color
  apply Fin.ext
  simp only [histogram_count]
  let fibers : {position // relabel vector permutation position = color} ≃
      {position // vector position = color} :=
    permutation.subtypeEquiv (fun position => Iff.rfl)
  exact Fintype.card_congr fibers

/-- Equal color counts give a genuine permutation of the finite positions.
The permutation is assembled from bijections of the individual color fibers. -/
theorem histogram_eq_iff_relabel (first second : Fin dimension → Color) :
    histogram first = histogram second ↔
      ∃ permutation : Equiv.Perm (Fin dimension), relabel first permutation = second := by
  classical
  constructor
  · intro hhistogram
    have hcard (color : Color) :
        Fintype.card {position // second position = color} =
          Fintype.card {position // first position = color} := by
      exact (congrArg Fin.val (congrFun hhistogram color)).symm
    let fibers (color : Color) : {position // second position = color} ≃
        {position // first position = color} := Fintype.equivOfCardEq (hcard color)
    refine ⟨Equiv.ofFiberEquiv fibers, ?_⟩
    funext position
    exact Equiv.ofFiberEquiv_map fibers position
  · rintro ⟨permutation, rfl⟩
    exact (histogram_relabel first permutation).symm

/-- Reindexing positions is an equivalence of the entire vector space. -/
def relabelEquiv (permutation : Equiv.Perm (Fin dimension)) :
    (Fin dimension → Color) ≃ (Fin dimension → Color) where
  toFun vector := relabel vector permutation
  invFun vector := relabel vector permutation.symm
  left_inv vector := by ext position; simp [relabel]
  right_inv vector := by ext position; simp [relabel]

variable [Fintype Color]

/-- Apply an independently uniform position permutation to a fixed vector. -/
noncomputable def randomRelabel (vector : Fin dimension → Color) :
    FiniteDist (Fin dimension → Color) :=
  (FiniteDist.uniform (Equiv.Perm (Fin dimension))).map (relabel vector)

/-- Relabeling the input does not change the output law of a uniform relabel. -/
theorem randomRelabel_relabel (vector : Fin dimension → Color)
    (permutation : Equiv.Perm (Fin dimension)) :
    randomRelabel (relabel vector permutation) = randomRelabel vector := by
  calc
    randomRelabel (relabel vector permutation) =
        ((FiniteDist.uniform (Equiv.Perm (Fin dimension))).map
          (Equiv.mulLeft permutation)).map (relabel vector) := by
      rw [FiniteDist.map_map]
      rfl
    _ = randomRelabel vector := by
      rw [FiniteDist.uniform_map_equiv]
      rfl

/-- The entire relabeling law depends only on the concrete color histogram. -/
theorem randomRelabel_eq_of_histogram_eq (first second : Fin dimension → Color)
    (hhistogram : histogram first = histogram second) :
    randomRelabel first = randomRelabel second := by
  obtain ⟨permutation, rfl⟩ := (histogram_eq_iff_relabel first second).mp hhistogram
  exact (randomRelabel_relabel first permutation).symm

/-- The output distribution itself is invariant under every position relabel. -/
theorem randomRelabel_map_relabel (vector : Fin dimension → Color)
    (permutation : Equiv.Perm (Fin dimension)) :
    (randomRelabel vector).map (relabelEquiv permutation) = randomRelabel vector := by
  calc
    (randomRelabel vector).map (relabelEquiv permutation) =
        ((FiniteDist.uniform (Equiv.Perm (Fin dimension))).map
          (Equiv.mulRight permutation)).map (relabel vector) := by
      rw [FiniteDist.map_map]
      change ((FiniteDist.uniform (Equiv.Perm (Fin dimension))).map (relabel vector)).map
          (relabelEquiv permutation) = _
      rw [FiniteDist.map_map]
      rfl
    _ = randomRelabel vector := by
      rw [FiniteDist.uniform_map_equiv]
      rfl

/-- All vectors with a common histogram have the same output mass. -/
theorem randomRelabel_equal_weights (vector first second : Fin dimension → Color)
    (hhistogram : histogram first = histogram second) :
    (randomRelabel vector).weight first = (randomRelabel vector).weight second := by
  obtain ⟨permutation, hpermutation⟩ := (histogram_eq_iff_relabel first second).mp hhistogram
  have hinverse : (relabelEquiv permutation).symm second = first := by
    rw [← hpermutation]
    exact (relabelEquiv permutation).symm_apply_apply first
  have hweight := congrArg (fun law : FiniteDist (Fin dimension → Color) => law.weight second)
    (randomRelabel_map_relabel vector permutation)
  simpa only [FiniteDist.map_equiv_weight, hinverse] using hweight

/-- No random relabeling can change the color counts. -/
theorem randomRelabel_weight_zero (vector output : Fin dimension → Color)
    (hhistogram : histogram output ≠ histogram vector) :
    (randomRelabel vector).weight output = 0 := by
  classical
  unfold randomRelabel
  rw [FiniteDist.map_weight]
  apply Finset.sum_eq_zero
  intro permutation _
  have hne : relabel vector permutation ≠ output := by
    intro heq
    apply hhistogram
    rw [← heq]
    exact histogram_relabel vector permutation
  simp [hne]

/-- Uniform permutation produces the exact uniform law on the histogram
fiber. This includes repeated colors and the zero-dimensional vector. -/
theorem randomRelabel_weight (vector output : Fin dimension → Color) :
    (randomRelabel vector).weight output =
      if histogram output = histogram vector then
        (Fintype.card {candidate : Fin dimension → Color //
          histogram candidate = histogram vector} : ℝ)⁻¹
      else 0 := by
  classical
  let fiber := {candidate : Fin dimension → Color // histogram candidate = histogram vector}
  haveI : Nonempty fiber := ⟨⟨vector, rfl⟩⟩
  have hcard : (Fintype.card fiber : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hsum : 1 = (Fintype.card fiber : ℝ) * (randomRelabel vector).weight vector := by
    calc
      1 = ∑ candidate, (randomRelabel vector).weight candidate :=
        (randomRelabel vector).sum_one.symm
      _ = ∑ candidate : Fin dimension → Color,
          if histogram candidate = histogram vector then
            (randomRelabel vector).weight vector else 0 := by
        apply Finset.sum_congr rfl
        intro candidate _
        by_cases hhistogram : histogram candidate = histogram vector
        · simp only [hhistogram, ↓reduceIte]
          exact randomRelabel_equal_weights vector candidate vector hhistogram
        · simp only [hhistogram, ↓reduceIte]
          exact randomRelabel_weight_zero vector candidate hhistogram
      _ = (Fintype.card fiber : ℝ) * (randomRelabel vector).weight vector := by
        rw [← Finset.sum_filter]
        simp [fiber, Fintype.card_subtype, nsmul_eq_mul]
  have hweight : (randomRelabel vector).weight vector = 1 / (Fintype.card fiber : ℝ) := by
    apply (eq_div_iff hcard).mpr
    nlinarith [hsum]
  by_cases hhistogram : histogram output = histogram vector
  · simp only [hhistogram, ↓reduceIte]
    rw [randomRelabel_equal_weights vector output vector hhistogram, hweight]
    simp [fiber, one_div]
  · simp only [hhistogram, ↓reduceIte]
    exact randomRelabel_weight_zero vector output hhistogram

namespace FiniteDist

variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]

/-- Draw a deterministic image and then apply a kernel, or apply their
composition directly. -/
theorem mix_map (distribution : FiniteDist α) (image : α → β)
    (kernel : β → FiniteDist γ) :
    (distribution.map image).mix kernel =
      distribution.mix (fun input => kernel (image input)) := by
  ext output
  simp only [mix_weight, map_weight]
  simp_rw [Finset.sum_mul, ite_mul, zero_mul]
  rw [Finset.sum_comm]
  simp

/-- Deterministic pushforward commutes with a mixture. -/
theorem map_mix (distribution : FiniteDist α) (kernel : α → FiniteDist β)
    (image : β → γ) :
    (distribution.mix kernel).map image =
      distribution.mix (fun input => (kernel input).map image) := by
  ext output
  simp only [mix_weight, map_weight, Finset.mul_sum]
  trans ∑ candidate, ∑ input,
    if image candidate = output then distribution.weight input * (kernel input).weight candidate
      else 0
  · apply Finset.sum_congr rfl
    intro candidate _
    split_ifs <;> simp
  · rw [Finset.sum_comm]
    simp only [mul_ite, mul_zero]

theorem map_const_weight (distribution : FiniteDist α) (value output : β) :
    (distribution.map (fun _ => value)).weight output = if value = output then 1 else 0 := by
  rw [map_weight]
  split_ifs <;> simp [distribution.sum_one]

end FiniteDist

/-- Relabel every sampled vector by independent fresh uniform randomness. -/
noncomputable def symmetrize (distribution : FiniteDist (Fin dimension → Color)) :
    FiniteDist (Fin dimension → Color) := distribution.mix randomRelabel

/-- Random relabeling preserves the complete histogram law exactly. -/
theorem symmetrize_histogram (distribution : FiniteDist (Fin dimension → Color)) :
    (symmetrize distribution).map histogram = distribution.map histogram := by
  rw [symmetrize, FiniteDist.map_mix]
  ext state
  simp only [FiniteDist.mix_weight, randomRelabel, FiniteDist.map_map, histogram_relabel,
    FiniteDist.map_weight]
  apply Finset.sum_congr rfl
  intro vector _
  split_ifs <;> simp

/-- Drawing the vector first or the independent uniform permutation first
gives the same complete output distribution. -/
theorem symmetrize_eq_permutation_mix (distribution : FiniteDist (Fin dimension → Color)) :
    symmetrize distribution =
      (FiniteDist.uniform (Equiv.Perm (Fin dimension))).mix
        (fun permutation => distribution.map (relabelEquiv permutation)) := by
  ext output
  simp only [symmetrize, randomRelabel, FiniteDist.mix_weight, FiniteDist.map_weight,
    FiniteDist.uniform_weight, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro permutation _
  apply Finset.sum_congr rfl
  intro vector _
  by_cases houtput : relabel vector permutation = output
  · simp [relabelEquiv, houtput, mul_comm]
  · simp [relabelEquiv, houtput]

/-- An exchangeable reference is unchanged by the final independent uniform
position relabeling. -/
theorem symmetrize_eq_of_invariant (distribution : FiniteDist (Fin dimension → Color))
    (hinvariant : ∀ permutation : Equiv.Perm (Fin dimension),
      distribution.map (relabelEquiv permutation) = distribution) :
    symmetrize distribution = distribution := by
  rw [symmetrize_eq_permutation_mix]
  simp only [hinvariant, FiniteDist.mix_const]

section HistogramKernel

variable [Nonempty Color]

/-- Choose an actual vector for a realizable histogram. An unrealizable state
gets an arbitrary vector; such a state has zero probability under any actual
histogram pushforward. -/
noncomputable def histogramRepresentative (state : Histogram dimension Color) :
    Fin dimension → Color :=
  if hexists : ∃ vector : Fin dimension → Color, histogram vector = state then
    Classical.choose hexists
  else Classical.arbitrary (Fin dimension → Color)

theorem histogramRepresentative_spec (vector : Fin dimension → Color) :
    histogram (histogramRepresentative (histogram vector)) = histogram vector := by
  have hexists : ∃ candidate : Fin dimension → Color, histogram candidate = histogram vector :=
    ⟨vector, rfl⟩
  simp only [histogramRepresentative, dif_pos hexists]
  exact Classical.choose_spec hexists

/-- The stochastic channel from a color histogram to its uniform orbit law. -/
noncomputable def histogramKernel (state : Histogram dimension Color) :
    FiniteDist (Fin dimension → Color) := randomRelabel (histogramRepresentative state)

theorem histogramKernel_histogram (vector : Fin dimension → Color) :
    histogramKernel (histogram vector) = randomRelabel vector :=
  randomRelabel_eq_of_histogram_eq _ _ (histogramRepresentative_spec vector)

/-- The reconstruction kernel is derived from actual permutations and fiber
counts; it is not an assumed inverse to the histogram map. -/
theorem symmetrize_from_histogram (distribution : FiniteDist (Fin dimension → Color)) :
    (distribution.map histogram).mix histogramKernel = symmetrize distribution := by
  rw [FiniteDist.mix_map]
  simp only [histogramKernel_histogram, symmetrize]

/-- V7's histogram-to-endpoint error transfer: uniform relabeling cannot
amplify the distance between the actual histogram laws. -/
theorem histogram_tv_transfer (first second : FiniteDist (Fin dimension → Color))
    {error : ℝ}
    (hhistogram : FiniteDist.TVBound (first.map histogram) (second.map histogram) error) :
    FiniteDist.TVBound (symmetrize first) (symmetrize second) error := by
  have h := hhistogram.mix histogramKernel
  simpa only [symmetrize_from_histogram] using h

/-- There is no loss at all: after symmetrization, endpoint TV is exactly
the TV of the original color histograms. -/
theorem symmetrize_totalVariation (first second : FiniteDist (Fin dimension → Color)) :
    FiniteDist.totalVariation (symmetrize first) (symmetrize second) =
      FiniteDist.totalVariation (first.map histogram) (second.map histogram) := by
  apply le_antisymm
  · apply (FiniteDist.tvBound_iff_totalVariation_le _ _ _).mp
    apply histogram_tv_transfer first second
    exact (FiniteDist.tvBound_iff_totalVariation_le _ _ _).mpr le_rfl
  · have h := (FiniteDist.tvBound_iff_totalVariation_le (symmetrize first)
        (symmetrize second) _).mpr le_rfl
    have hmap := h.map histogram
    rw [symmetrize_histogram, symmetrize_histogram] at hmap
    exact (FiniteDist.tvBound_iff_totalVariation_le _ _ _).mp hmap

end HistogramKernel

section ZeroSumReference

variable [AddCommMonoid Color]

/-- The concrete zero-sum endpoint set. -/
abbrev ZeroSumVectors (dimension : ℕ) (Color : Type*) [AddCommMonoid Color] :=
  {vector : Fin dimension → Color // ∑ position, vector position = 0}

instance zeroSumVectorsNonempty : Nonempty (ZeroSumVectors dimension Color) :=
  ⟨⟨fun _ => 0, by simp⟩⟩

/-- Position permutations restrict to bijections of the zero-sum hyperplane. -/
def zeroSumRelabelEquiv (permutation : Equiv.Perm (Fin dimension)) :
    ZeroSumVectors dimension Color ≃ ZeroSumVectors dimension Color :=
  (relabelEquiv permutation).subtypeEquiv (fun vector => by
    change (∑ position, vector position) = 0 ↔
      (∑ position, vector (permutation position)) = 0
    rw [Equiv.sum_comp permutation vector])

/-- Exact uniform law on zero-sum vectors, viewed in the ambient vector space. -/
noncomputable def uniformZeroSum (dimension : ℕ) (Color : Type*)
    [Fintype Color] [AddCommMonoid Color] : FiniteDist (Fin dimension → Color) :=
  (FiniteDist.uniform (ZeroSumVectors dimension Color)).map Subtype.val

theorem uniformZeroSum_invariant (permutation : Equiv.Perm (Fin dimension)) :
    (uniformZeroSum dimension Color).map (relabelEquiv permutation) =
      uniformZeroSum dimension Color := by
  calc
    (uniformZeroSum dimension Color).map (relabelEquiv permutation) =
        ((FiniteDist.uniform (ZeroSumVectors dimension Color)).map
          (zeroSumRelabelEquiv permutation)).map Subtype.val := by
      simp only [uniformZeroSum, FiniteDist.map_map]
      rfl
    _ = uniformZeroSum dimension Color := by
      rw [FiniteDist.uniform_map_equiv]
      rfl

theorem symmetrize_uniformZeroSum :
    symmetrize (uniformZeroSum dimension Color) = uniformZeroSum dimension Color :=
  symmetrize_eq_of_invariant _ uniformZeroSum_invariant

/-- The full finite statement of V7 Corollary 9.21. A bound on the histogram
law becomes the same bound to the actual uniform zero-sum endpoint law after
an independent uniform permutation of all positions. -/
theorem histogram_to_uniformZeroSum (distribution : FiniteDist (Fin dimension → Color))
    {error : ℝ}
    (hhistogram : FiniteDist.TVBound (distribution.map histogram)
      ((uniformZeroSum dimension Color).map histogram) error) :
    FiniteDist.TVBound (symmetrize distribution) (uniformZeroSum dimension Color) error := by
  have h := histogram_tv_transfer distribution (uniformZeroSum dimension Color) hhistogram
  simpa only [symmetrize_uniformZeroSum] using h

end ZeroSumReference

end AFT
