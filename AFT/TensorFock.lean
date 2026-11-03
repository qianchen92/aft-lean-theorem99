import AFT.FockGaussian
import AFT.HistogramTail

/-! # Exact symmetric-tensor and Gaussian Fock norm normalization -/

namespace AFT
namespace TensorFock

open MeasureTheory
open scoped BigOperators Classical

variable {Slot Coordinate : Type*} [Fintype Slot] [Fintype Coordinate]

/-- Multiplicities of coordinate labels in an actual tensor basis word. -/
noncomputable def wordDegree (word : Slot → Coordinate) (coordinate : Coordinate) : ℕ :=
  Fintype.card {slot // word slot = coordinate}

/-- Evaluation of one tensor basis word on a complex vector. -/
noncomputable def wordMonomial (word : Slot → Coordinate) (value : Coordinate → ℂ) : ℂ :=
  ∏ slot, value (word slot)

/-- Grouping equal coordinate labels gives the usual monomial. -/
theorem wordMonomial_eq (word : Slot → Coordinate) (value : Coordinate → ℂ) :
    wordMonomial word value = FockGaussian.monomial (wordDegree word) value := by
  simpa [wordMonomial, FockGaussian.monomial, wordDegree] using
    (Fintype.prod_fiberwise' word value).symm

omit [Fintype Coordinate] in
/-- Slot permutations preserve every multiplicity. -/
theorem wordDegree_comp (word : Slot → Coordinate) (permutation : Equiv.Perm Slot) :
    wordDegree (word ∘ permutation) = wordDegree word := by
  funext coordinate
  exact Fintype.card_congr (Equiv.subtypeEquiv permutation (fun _ => Iff.rfl))

omit [Fintype Coordinate] in
/-- Equal coordinate multiplicities are realized by an actual slot permutation. -/
theorem exists_matching_permutation (first second : Slot → Coordinate)
    (hdegree : wordDegree first = wordDegree second) :
    ∃ permutation : Equiv.Perm Slot, second ∘ permutation = first := by
  have hfiber (coordinate : Coordinate) :
      Nonempty ({slot // first slot = coordinate} ≃ {slot // second slot = coordinate}) :=
    Fintype.card_eq.mp (congrFun hdegree coordinate)
  let fiberEquiv := fun coordinate => Classical.choice (hfiber coordinate)
  exact ⟨Equiv.ofFiberEquiv fiberEquiv, funext (Equiv.ofFiberEquiv_map fiberEquiv)⟩

/-- Matching permutations form a coset of the stabilizer, whose cardinality
is precisely the product of the multiplicity factorials. -/
theorem matching_permutation_card (first second : Slot → Coordinate) :
    Fintype.card {permutation : Equiv.Perm Slot // second ∘ permutation = first} =
      if wordDegree first = wordDegree second then FockGaussian.monomialWeight (wordDegree first)
      else 0 := by
  by_cases hdegree : wordDegree first = wordDegree second
  · rw [if_pos hdegree]
    obtain ⟨permutation, hpermutation⟩ := exists_matching_permutation first second hdegree
    let e : {p : Equiv.Perm Slot // first ∘ p = first} ≃
        {p : Equiv.Perm Slot // second ∘ p = first} :=
      { toFun := fun p => ⟨p.val.trans permutation, by
          change (second ∘ permutation) ∘ p.val = first
          rw [hpermutation, p.property]⟩
        invFun := fun p => ⟨p.val.trans permutation.symm, by
          ext slot
          have h := congrFun hpermutation (permutation.symm (p.val slot))
          simp only [Function.comp_apply, Equiv.apply_symm_apply] at h
          exact h.symm.trans (congrFun p.property slot)⟩
        left_inv := by intro p; apply Subtype.ext; ext slot; simp
        right_inv := by intro p; apply Subtype.ext; ext slot; simp }
    rw [← Fintype.card_congr e, DomMulAct.stabilizer_card]
    rfl
  · rw [if_neg hdegree]
    rw [Fintype.card_eq_zero_iff]
    exact ⟨fun permutation => hdegree (by
      rw [← permutation.property]
      exact wordDegree_comp second permutation.val)⟩

/-- The finite complex Wick identity expressed as an actual sum over all
slot permutations. Its coefficient is proved by stabilizer counting. -/
theorem word_wick (first second : Slot → Coordinate) :
    (∫ value, wordMonomial first value * (starRingEnd ℂ) (wordMonomial second value)
      ∂(FockGaussian.field (Coordinate := Coordinate))) =
      ∑ permutation : Equiv.Perm Slot, if second ∘ permutation = first then (1 : ℂ) else 0 := by
  simp_rw [wordMonomial_eq]
  rw [FockGaussian.monomial_orthogonality]
  have hcard := matching_permutation_card first second
  have hsum : (∑ permutation : Equiv.Perm Slot,
      if second ∘ permutation = first then (1 : ℂ) else 0) =
      (Fintype.card {permutation : Equiv.Perm Slot // second ∘ permutation = first} : ℂ) := by
    simp [Fintype.card_subtype, Finset.sum_boole]
  rw [hsum, hcard]
  split_ifs <;> simp

/-- Actual polynomial evaluation of a finite tensor coordinate array. -/
noncomputable def tensorEvaluation (tensor : BlockFock.Tensor Slot Coordinate)
    (value : Coordinate → ℂ) : ℂ := ∑ word, (tensor word : ℂ) * wordMonomial word value

set_option backward.isDefEq.respectTransparency false in
/-- The Gaussian squared norm of an arbitrary tensor evaluation is the sum
of all permutation pairings of its actual coordinate array. -/
theorem tensor_pairing (tensor : BlockFock.Tensor Slot Coordinate) :
    (∫ value, tensorEvaluation tensor value * (starRingEnd ℂ) (tensorEvaluation tensor value)
      ∂(FockGaussian.field (Coordinate := Coordinate))) =
      ∑ permutation : Equiv.Perm Slot, ∑ word,
        (tensor (word ∘ permutation) : ℂ) * (tensor word : ℂ) := by
  have hterm (first second : Slot → Coordinate) :
      Integrable (fun value => ((tensor first : ℂ) * (tensor second : ℂ)) *
        (wordMonomial first value * (starRingEnd ℂ) (wordMonomial second value)))
        FockGaussian.field := by
    simp_rw [wordMonomial_eq]
    exact (FockGaussian.monomial_pair_integrable _ _).const_mul _
  have hexpand (value : Coordinate → ℂ) :
      tensorEvaluation tensor value * (starRingEnd ℂ) (tensorEvaluation tensor value) =
        ∑ first, ∑ second, ((tensor first : ℂ) * (tensor second : ℂ)) *
          (wordMonomial first value * (starRingEnd ℂ) (wordMonomial second value)) := by
    simp only [tensorEvaluation, map_sum, map_mul, Complex.conj_ofReal,
      Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro first _
    apply Finset.sum_congr rfl
    intro second _
    ring
  simp_rw [hexpand]
  rw [integral_finset_sum _ (fun first _ => integrable_finset_sum _ (fun second _ => hterm first second))]
  simp_rw [integral_finset_sum _ (fun second _ => hterm _ second), integral_const_mul, word_wick,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  calc
    _ = ∑ second, ∑ permutation : Equiv.Perm Slot,
        (tensor (second ∘ permutation) : ℂ) * (tensor second : ℂ) := by
      apply Finset.sum_congr rfl
      intro second _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro permutation _
      simp [mul_ite]
    _ = _ := Finset.sum_comm

set_option backward.isDefEq.respectTransparency false in
/-- Exact normalization of a symmetric coordinate tensor: its Gaussian L2
norm squared equals the degree factorial times its tensor Hilbert norm squared. -/
theorem symmetric_tensor_isometry (tensor : BlockFock.Tensor Slot Coordinate)
    (hsymmetric : ∀ word (permutation : Equiv.Perm Slot), tensor (word ∘ permutation) = tensor word) :
    (∫ value, Complex.normSq (tensorEvaluation tensor value)
      ∂(FockGaussian.field (Coordinate := Coordinate))) =
      (Fintype.card Slot).factorial * BlockFock.tensorEnergy tensor := by
  apply Complex.ofReal_injective
  rw [← integral_complex_ofReal]
  simp_rw [← Complex.mul_conj]
  rw [tensor_pairing]
  simp_rw [hsymmetric]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Fintype.card_perm]
  push_cast
  congr 1
  simp only [BlockFock.tensorEnergy, Complex.ofReal_sum, pow_two, Complex.ofReal_mul]

/-- The total multiplicity is exactly the number of tensor slots. -/
theorem wordDegree_sum (word : Slot → Coordinate) :
    (∑ coordinate, wordDegree word coordinate) = Fintype.card Slot := by
  simpa [wordDegree, Fintype.card_sigma] using Fintype.card_congr (Equiv.sigmaFiberEquiv word)

/-- Products of arbitrary finite tensor evaluations are integrable. -/
theorem tensor_pair_integrable {OtherSlot : Type*} [Fintype OtherSlot]
    (first : BlockFock.Tensor Slot Coordinate) (second : BlockFock.Tensor OtherSlot Coordinate) :
    Integrable (fun value => tensorEvaluation first value * (starRingEnd ℂ) (tensorEvaluation second value))
      FockGaussian.field := by
  simp only [tensorEvaluation, map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
  apply integrable_finset_sum
  intro secondWord _
  apply integrable_finset_sum
  intro firstWord _
  have h := (FockGaussian.monomial_pair_integrable (wordDegree firstWord) (wordDegree secondWord)).const_mul
    ((first firstWord : ℂ) * (second secondWord : ℂ))
  simp_rw [← wordMonomial_eq] at h
  convert h using 1
  ext value
  simp only [Complex.conj_ofReal]
  ring

set_option backward.isDefEq.respectTransparency false in
/-- Tensor evaluations of distinct degrees are exactly orthogonal. -/
theorem tensor_cross_integral {OtherSlot : Type*} [Fintype OtherSlot]
    (first : BlockFock.Tensor Slot Coordinate) (second : BlockFock.Tensor OtherSlot Coordinate)
    (hdegree : Fintype.card Slot ≠ Fintype.card OtherSlot) :
    (∫ value, tensorEvaluation first value * (starRingEnd ℂ) (tensorEvaluation second value)
      ∂(FockGaussian.field (Coordinate := Coordinate))) = 0 := by
  have hterm (firstWord : Slot → Coordinate) (secondWord : OtherSlot → Coordinate) :=
    (FockGaussian.monomial_pair_integrable (wordDegree firstWord) (wordDegree secondWord)).const_mul
      ((first firstWord : ℂ) * (second secondWord : ℂ))
  have hexpand (value : Coordinate → ℂ) :
      tensorEvaluation first value * (starRingEnd ℂ) (tensorEvaluation second value) =
        ∑ firstWord, ∑ secondWord, ((first firstWord : ℂ) * (second secondWord : ℂ)) *
          (FockGaussian.monomial (wordDegree firstWord) value *
            (starRingEnd ℂ) (FockGaussian.monomial (wordDegree secondWord) value)) := by
    simp only [tensorEvaluation, map_sum, map_mul, Complex.conj_ofReal,
      Finset.sum_mul, Finset.mul_sum, wordMonomial_eq]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro firstWord _
    apply Finset.sum_congr rfl
    intro secondWord _
    ring
  simp_rw [hexpand]
  rw [integral_finset_sum _ (fun firstWord _ =>
    integrable_finset_sum _ (fun secondWord _ => hterm firstWord secondWord))]
  apply Finset.sum_eq_zero
  intro firstWord _
  rw [integral_finset_sum _ (fun secondWord _ => hterm firstWord secondWord)]
  apply Finset.sum_eq_zero
  intro secondWord _
  rw [integral_const_mul, FockGaussian.monomial_orthogonality, if_neg, mul_zero]
  intro hequal
  apply hdegree
  rw [← wordDegree_sum firstWord, ← wordDegree_sum secondWord, hequal]

/-- An actual finite sum of homogeneous tensor evaluations. -/
noncomputable def seriesEvaluation (degrees : Finset ℕ)
    (tensor : (degree : ℕ) → BlockFock.Tensor (Fin degree) Coordinate) (value : Coordinate → ℂ) : ℂ :=
  ∑ degree ∈ degrees, tensorEvaluation (tensor degree) value

set_option backward.isDefEq.respectTransparency false in
/-- Exact Fock isometry for all terms of an arbitrary finite symmetric tensor
polynomial, including all degrees in its finite support. -/
theorem complete_tensor_fock_isometry (degrees : Finset ℕ)
    (tensor : (degree : ℕ) → BlockFock.Tensor (Fin degree) Coordinate)
    (hsymmetric : ∀ degree ∈ degrees, ∀ word (permutation : Equiv.Perm (Fin degree)),
      tensor degree (word ∘ permutation) = tensor degree word) :
    (∫ value, Complex.normSq (seriesEvaluation degrees tensor value)
      ∂(FockGaussian.field (Coordinate := Coordinate))) =
      ∑ degree ∈ degrees, (degree.factorial : ℝ) * BlockFock.tensorEnergy (tensor degree) := by
  have hpair (firstDegree secondDegree : ℕ) (hfirst : firstDegree ∈ degrees) :
      (∫ value, tensorEvaluation (tensor firstDegree) value *
        (starRingEnd ℂ) (tensorEvaluation (tensor secondDegree) value) ∂FockGaussian.field) =
        if firstDegree = secondDegree then
          ((firstDegree.factorial : ℝ) * BlockFock.tensorEnergy (tensor firstDegree) : ℂ) else 0 := by
    by_cases hequal : firstDegree = secondDegree
    · subst secondDegree
      rw [if_pos rfl]
      simp_rw [Complex.mul_conj]
      rw [integral_complex_ofReal, symmetric_tensor_isometry _ (hsymmetric firstDegree hfirst), Fintype.card_fin]
      push_cast
      rfl
    · rw [if_neg hequal]
      exact tensor_cross_integral _ _ (by simpa using hequal)
  have hexpand (value : Coordinate → ℂ) :
      seriesEvaluation degrees tensor value * (starRingEnd ℂ) (seriesEvaluation degrees tensor value) =
        ∑ firstDegree ∈ degrees, ∑ secondDegree ∈ degrees,
          tensorEvaluation (tensor firstDegree) value *
            (starRingEnd ℂ) (tensorEvaluation (tensor secondDegree) value) := by
    simp only [seriesEvaluation, map_sum, Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_comm
  apply Complex.ofReal_injective
  rw [← integral_complex_ofReal]
  simp_rw [← Complex.mul_conj, hexpand]
  rw [integral_finset_sum _ (fun firstDegree _ =>
    integrable_finset_sum _ (fun secondDegree _ => tensor_pair_integrable _ _))]
  push_cast
  apply Finset.sum_congr rfl
  intro firstDegree hfirst
  rw [integral_finset_sum _ (fun secondDegree _ => tensor_pair_integrable _ _)]
  simp_rw [hpair firstDegree _ hfirst]
  simp [hfirst]

/-- Population and radius normalization of each concrete homogeneous tensor. -/
noncomputable def normalizedTensor (population : ℕ) (radius : ℝ)
    (tensor : (degree : ℕ) → BlockFock.Tensor (Fin degree) Coordinate)
    (degree : ℕ) : BlockFock.Tensor (Fin degree) Coordinate :=
  fun word => (radius / Real.sqrt population) ^ degree * tensor degree word

/-- Scalar multiplication of an actual coordinate tensor scales its energy quadratically. -/
theorem tensorEnergy_smul (scalar : ℝ) (tensor : BlockFock.Tensor Slot Coordinate) :
    BlockFock.tensorEnergy (fun word => scalar * tensor word) =
      scalar ^ 2 * BlockFock.tensorEnergy tensor := by
  simp only [BlockFock.tensorEnergy, mul_pow, Finset.mul_sum]

set_option backward.isDefEq.respectTransparency false in
/-- The Gaussian realization of the exact population-normalized Fock energy
appearing in the complete histogram tail comparison. -/
theorem normalized_fock_isometry (population : ℕ) (radius : ℝ)
    (tensor : (degree : ℕ) → BlockFock.Tensor (Fin degree) Coordinate)
    (hsymmetric : ∀ degree ≤ population, ∀ word (permutation : Equiv.Perm (Fin degree)),
      tensor degree (word ∘ permutation) = tensor degree word) :
    (∫ value, Complex.normSq (seriesEvaluation (Finset.range (population + 1))
        (normalizedTensor population radius tensor) value) ∂FockGaussian.field) =
      HistogramTail.fockEnergy population radius (fun degree => BlockFock.tensorEnergy (tensor degree)) := by
  rw [complete_tensor_fock_isometry _ _ (by
    intro degree hdegree word permutation
    simp only [normalizedTensor, hsymmetric degree (Nat.le_of_lt_succ (Finset.mem_range.mp hdegree)) word permutation])]
  unfold HistogramTail.fockEnergy
  apply Finset.sum_congr rfl
  intro degree _
  unfold normalizedTensor
  rw [tensorEnergy_smul]
  have hnorm : ((radius / Real.sqrt (population : ℝ)) ^ degree) ^ 2 =
      radius ^ (2 * degree) / (population : ℝ) ^ degree := by
    rw [← pow_mul, Nat.mul_comm degree 2, pow_mul, div_pow,
      Real.sq_sqrt (Nat.cast_nonneg population), div_pow, ← pow_mul]
  rw [hnorm]
  ring

set_option backward.isDefEq.respectTransparency false in
/-- A full finite-population tail bound for a concrete product of linear
blocks. The hypotheses identify its actual symmetric coefficients and bound
the actual block energy; no Fock bound is assumed. -/
theorem complete_linear_histogram_tail {State : Type*} [Fintype State] [Nonempty Coordinate]
    (population cutoff : ℕ) (radius : ℝ)
    (tensor : (degree : ℕ) → BlockFock.Tensor (Fin degree) Coordinate)
    (coefficient : State → Coordinate → ℝ)
    (hpopulation : 0 < population) (hradius : Real.exp 1 ≤ radius ^ 2)
    (hsymmetric : ∀ degree ≤ population, ∀ word (permutation : Equiv.Perm (Fin degree)),
      tensor degree (word ∘ permutation) = tensor degree word)
    (hcoefficients : ∀ value,
      seriesEvaluation (Finset.range (population + 1)) (normalizedTensor population radius tensor) value =
        ∏ state, (1 + ∑ index, (coefficient state index : ℂ) * value index))
    (henergy : (∑ state, ∑ index, coefficient state index ^ 2) ≤ 1 / 4) :
    HistogramTail.likelihoodTailEnergy population cutoff (fun degree => BlockFock.tensorEnergy (tensor degree)) ≤
      (Real.exp 1 / radius ^ 2) ^ (cutoff + 1) *
        (4 * Real.exp (2 * ∑ index, (∑ state, coefficient state index) ^ 2)) := by
  apply (HistogramTail.complete_tail_energy_le population cutoff radius _ hpopulation
    (fun degree => Finset.sum_nonneg (fun _ _ => sq_nonneg _)) hradius).trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  change HistogramTail.fockEnergy population radius (fun degree => BlockFock.tensorEnergy (tensor degree)) ≤ _
  rw [← normalized_fock_isometry population radius tensor hsymmetric]
  simp_rw [hcoefficients, map_prod]
  exact FockGaussian.linear_product_bound coefficient henergy

set_option backward.isDefEq.respectTransparency false in
/-- Unsymmetrized tensors obey the corresponding Gaussian norm upper bound.
This follows directly from the exact permutation pairing and Cauchy--Schwarz. -/
theorem tensor_gaussian_energy_le (tensor : BlockFock.Tensor Slot Coordinate) :
    (∫ value, Complex.normSq (tensorEvaluation tensor value) ∂FockGaussian.field) ≤
      (Fintype.card Slot).factorial * BlockFock.tensorEnergy tensor := by
  have heq : (∫ value, Complex.normSq (tensorEvaluation tensor value) ∂FockGaussian.field) =
      ∑ permutation : Equiv.Perm Slot, ∑ word, tensor (word ∘ permutation) * tensor word := by
    apply Complex.ofReal_injective
    rw [← integral_complex_ofReal]
    simp_rw [← Complex.mul_conj]
    rw [tensor_pairing]
    push_cast
    rfl
  rw [heq]
  calc
    _ ≤ ∑ permutation : Equiv.Perm Slot, BlockFock.tensorEnergy tensor := by
      apply Finset.sum_le_sum
      intro permutation _
      calc
        _ ≤ ∑ word, (tensor (word ∘ permutation) ^ 2 + tensor word ^ 2) / 2 := by
          apply Finset.sum_le_sum
          intro word _
          nlinarith [sq_nonneg (tensor (word ∘ permutation) - tensor word)]
        _ = BlockFock.tensorEnergy tensor := by
          rw [← Finset.sum_div, Finset.sum_add_distrib, BlockFock.permute_energy]
          change (BlockFock.tensorEnergy tensor + BlockFock.tensorEnergy tensor) / 2 = _
          ring
    _ = _ := by simp [Fintype.card_perm]

set_option backward.isDefEq.respectTransparency false in
/-- Tensor multiplication evaluates to actual multiplication of polynomials. -/
theorem tensor_product_evaluation {OtherSlot : Type*} [Fintype OtherSlot]
    (first : BlockFock.Tensor Slot Coordinate) (second : BlockFock.Tensor OtherSlot Coordinate)
    (value : Coordinate → ℂ) :
    tensorEvaluation (BlockFock.tensorProduct first second) value =
      tensorEvaluation first value * tensorEvaluation second value := by
  letI : DecidableEq (Slot ⊕ OtherSlot) := Classical.decEq _
  unfold tensorEvaluation BlockFock.tensorProduct wordMonomial
  simp only [Complex.ofReal_mul, Fintype.prod_sum_type]
  have hequiv := (Equiv.sumArrowEquivProdArrow Slot OtherSlot Coordinate).sum_comp
    (fun point => ((first point.1 : ℂ) * (∏ slot, value (point.1 slot))) *
      ((second point.2 : ℂ) * (∏ slot, value (point.2 slot))))
  calc
    _ = ∑ word : Slot ⊕ OtherSlot → Coordinate,
        ((first (word ∘ Sum.inl) : ℂ) * ∏ slot, value (word (Sum.inl slot))) *
          ((second (word ∘ Sum.inr) : ℂ) * ∏ slot, value (word (Sum.inr slot))) := by
      apply Finset.sum_congr rfl
      intro word _
      ring
    _ = ∑ point : (Slot → Coordinate) × (OtherSlot → Coordinate),
        ((first point.1 : ℂ) * (∏ slot, value (point.1 slot))) *
          ((second point.2 : ℂ) * (∏ slot, value (point.2 slot))) := hequiv
    _ = _ := by rw [Fintype.sum_prod_type, Finset.sum_mul_sum]

set_option backward.isDefEq.respectTransparency false in
/-- Finite Parseval identity for an arbitrary collection of tensor polynomials
whose slot counts are pairwise distinct; the tensors need not be symmetric. -/
theorem distinct_degree_parseval {Degree : Type*} (degrees : Finset Degree)
    (Slots : Degree → Type*) [∀ degree, Fintype (Slots degree)]
    (tensor : (degree : Degree) → BlockFock.Tensor (Slots degree) Coordinate)
    (hdistinct : ∀ first ∈ degrees, ∀ second ∈ degrees, first ≠ second →
      Fintype.card (Slots first) ≠ Fintype.card (Slots second)) :
    (∫ value, Complex.normSq (∑ degree ∈ degrees, tensorEvaluation (tensor degree) value)
      ∂FockGaussian.field) =
      ∑ degree ∈ degrees, ∫ value, Complex.normSq (tensorEvaluation (tensor degree) value)
        ∂FockGaussian.field := by
  have hexpand (value : Coordinate → ℂ) :
      (∑ degree ∈ degrees, tensorEvaluation (tensor degree) value) *
        (starRingEnd ℂ) (∑ degree ∈ degrees, tensorEvaluation (tensor degree) value) =
        ∑ first ∈ degrees, ∑ second ∈ degrees,
          tensorEvaluation (tensor first) value * (starRingEnd ℂ) (tensorEvaluation (tensor second) value) := by
    simp only [map_sum, Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_comm
  apply Complex.ofReal_injective
  rw [← integral_complex_ofReal]
  simp_rw [← Complex.mul_conj, hexpand]
  rw [integral_finset_sum _ (fun first _ =>
    integrable_finset_sum _ (fun second _ => tensor_pair_integrable _ _)), Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro first hfirst
  rw [integral_finset_sum _ (fun second _ => tensor_pair_integrable _ _)]
  rw [Finset.sum_eq_single first]
  · simp_rw [Complex.mul_conj]
    exact integral_complex_ofReal
  · intro second hsecond hne
    exact tensor_cross_integral _ _ (hdistinct first hfirst second hsecond hne.symm)
  · exact fun hnot => (hnot hfirst).elim

set_option backward.isDefEq.respectTransparency false in
/-- Multiplication by an actual homogeneous tensor costs a factorial and
one doubling of squared Fock radius, independently of its degree. -/
theorem homogeneous_times_series_gaussian_le (first : BlockFock.Tensor Slot Coordinate)
    (degrees : Finset ℕ) (second : (degree : ℕ) → BlockFock.Tensor (Fin degree) Coordinate) :
    (∫ value, Complex.normSq (tensorEvaluation first value * seriesEvaluation degrees second value)
      ∂FockGaussian.field) ≤
      ((Fintype.card Slot).factorial : ℝ) * 2 ^ Fintype.card Slot * BlockFock.tensorEnergy first *
        (∑ degree ∈ degrees, (degree.factorial : ℝ) * 2 ^ degree * BlockFock.tensorEnergy (second degree)) := by
  have hpoint (value : Coordinate → ℂ) :
      tensorEvaluation first value * seriesEvaluation degrees second value =
        ∑ degree ∈ degrees, tensorEvaluation (BlockFock.tensorProduct first (second degree)) value := by
    simp only [seriesEvaluation, Finset.mul_sum, tensor_product_evaluation]
  simp_rw [hpoint]
  rw [distinct_degree_parseval degrees (fun degree => Slot ⊕ Fin degree)
    (fun degree => BlockFock.tensorProduct first (second degree)) (by
      intro firstDegree _ secondDegree _ hne
      simpa using hne)]
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro degree _
  apply (tensor_gaussian_energy_le _).trans
  rw [Fintype.card_sum, Fintype.card_fin, BlockFock.tensorProduct_energy]
  have hf : ((Fintype.card Slot + degree).factorial : ℝ) ≤
      2 ^ (Fintype.card Slot + degree) * (Fintype.card Slot).factorial * degree.factorial := by
    exact_mod_cast BlockFock.factorial_add_le (Fintype.card Slot) degree
  have he₁ : 0 ≤ BlockFock.tensorEnergy first := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have he₂ : 0 ≤ BlockFock.tensorEnergy (second degree) := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  calc
    _ ≤ (2 ^ (Fintype.card Slot + degree) * (Fintype.card Slot).factorial * degree.factorial) *
        (BlockFock.tensorEnergy first * BlockFock.tensorEnergy (second degree)) :=
      mul_le_mul_of_nonneg_right hf (mul_nonneg he₁ he₂)
    _ = _ := by rw [pow_add]; ring

end TensorFock
end AFT
