import AFT.TensorChannel

/-! # Exact canonical projection before finite local Hilbert channels -/

namespace AFT.TensorChannel

open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {Input Output : Type*} [Fintype Input] [Fintype Output]

omit [Fintype Output] in
/-- Orthogonal centering with respect to the actual input law. -/
def center (law : FiniteDist Input) : (Input → ℝ) →ₗ[ℝ] (Input → ℝ) where
  toFun kernel := fun point => kernel point - law.expectation kernel
  map_add' first second := by
    funext point
    change first point + second point - law.expectation (fun x => first x + second x) = _
    rw [FiniteDist.expectation_add]
    simp only [Pi.add_apply]
    ring
  map_smul' scalar kernel := by
    funext point
    change scalar * kernel point - law.expectation (fun x => scalar * kernel x) = _
    rw [FiniteDist.expectation_const_mul]
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

omit [Fintype Output] in
@[simp] theorem center_apply (law : FiniteDist Input) (kernel : Input → ℝ) (point : Input) :
    center law kernel point = kernel point - law.expectation kernel := rfl

omit [Fintype Output] in
theorem center_mean (law : FiniteDist Input) (kernel : Input → ℝ) :
    law.expectation (center law kernel) = 0 := by
  simp only [center, LinearMap.coe_mk, AddHom.coe_mk, FiniteDist.expectation_sub,
    FiniteDist.expectation_const, sub_self]

omit [Fintype Output] in
/-- Exact variance identity gives contraction, including laws with zeros. -/
theorem center_energy (law : FiniteDist Input) (kernel : Input → ℝ) :
    law.l2Sq (center law kernel) = law.l2Sq kernel - law.expectation kernel ^ 2 := by
  let mean := law.expectation kernel
  have hpoint (point : Input) : law.weight point * (kernel point - mean) ^ 2 =
      law.weight point * kernel point ^ 2 - 2 * mean * (law.weight point * kernel point) +
        law.weight point * mean ^ 2 := by ring
  change (∑ point, law.weight point * (kernel point - mean) ^ 2) = _
  simp only [hpoint, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    ← Finset.sum_mul, law.sum_one, one_mul]
  change law.l2Sq kernel - 2 * mean * mean + mean ^ 2 = law.l2Sq kernel - mean ^ 2
  ring

omit [Fintype Output] in
theorem center_energy_le (law : FiniteDist Input) (kernel : Input → ℝ) :
    law.l2Sq (center law kernel) ≤ law.l2Sq kernel := by
  rw [center_energy]
  exact sub_le_self _ (sq_nonneg _)

/-- A scalar channel estimate on canonical inputs extends to a genuine
linear operator on the entire Hilbert space by orthogonal projection. -/
theorem centered_channel_energy_le (law : FiniteDist Input)
    (channel : (Input → ℝ) →ₗ[ℝ] (Output → ℝ)) (bound : ℝ)
    (hchannel : ∀ kernel, law.expectation kernel = 0 →
      (∑ output, channel kernel output ^ 2) ≤ bound ^ 2 * law.l2Sq kernel) (kernel : Input → ℝ) :
    (∑ output, (channel.comp (center law)) kernel output ^ 2) ≤ bound ^ 2 * law.l2Sq kernel :=
  (hchannel (center law kernel) (center_mean law kernel)).trans
    (mul_le_mul_of_nonneg_left (center_energy_le law kernel) (sq_nonneg bound))

omit [Fintype Input] [Fintype Output] in
theorem apply_add (count : ℕ) (channel : Fin count → (Input → ℝ) →ₗ[ℝ] (Output → ℝ))
    (first second : (Fin count → Input) → ℝ) (output : Fin count → Output) :
    apply count channel (first + second) output = apply count channel first output + apply count channel second output := by
  induction count with
  | zero => rfl
  | succ count ih =>
    change channel 0 (fun input => apply count (fun index => channel index.succ)
      ((fun rest => first (Fin.cons input rest)) + (fun rest => second (Fin.cons input rest)))
      (fun index => output index.succ)) (output 0) = _
    simp only [ih]
    change channel 0 ((fun input => apply count (fun index => channel index.succ)
      (fun rest => first (Fin.cons input rest)) (fun index => output index.succ)) +
      (fun input => apply count (fun index => channel index.succ)
        (fun rest => second (Fin.cons input rest)) (fun index => output index.succ))) (output 0) = _
    rw [map_add]
    rfl

omit [Fintype Input] [Fintype Output] in
theorem apply_smul (count : ℕ) (channel : Fin count → (Input → ℝ) →ₗ[ℝ] (Output → ℝ))
    (scalar : ℝ) (kernel : (Fin count → Input) → ℝ) (output : Fin count → Output) :
    apply count channel (scalar • kernel) output = scalar * apply count channel kernel output := by
  induction count with
  | zero => rfl
  | succ count ih =>
    change channel 0 (fun input => apply count (fun index => channel index.succ)
      (scalar • (fun rest => kernel (Fin.cons input rest))) (fun index => output index.succ)) (output 0) = _
    simp only [ih]
    change channel 0 (scalar • (fun input => apply count (fun index => channel index.succ)
      (fun rest => kernel (Fin.cons input rest)) (fun index => output index.succ))) (output 0) = _
    rw [map_smul]
    rfl

omit [Fintype Input] [Fintype Output] in
/-- The full tensor operation is itself a literal linear map. -/
def applyLinear (count : ℕ) (channel : Fin count → (Input → ℝ) →ₗ[ℝ] (Output → ℝ)) :
    ((Fin count → Input) → ℝ) →ₗ[ℝ] ((Fin count → Output) → ℝ) where
  toFun := apply count channel
  map_add' first second := funext (apply_add count channel first second)
  map_smul' scalar kernel := funext (apply_smul count channel scalar kernel)

omit [Fintype Input] [Fintype Output] in
/-- Arbitrary finite expectation commutes with the complete tensor channel. -/
theorem apply_expectation {Source : Type*} [Fintype Source] (source : FiniteDist Source)
    (count : ℕ) (channel : Fin count → (Input → ℝ) →ₗ[ℝ] (Output → ℝ))
    (kernel : Source → (Fin count → Input) → ℝ) (output : Fin count → Output) :
    apply count channel (fun word => source.expectation (fun sample => kernel sample word)) output =
      source.expectation (fun sample => apply count channel (kernel sample) output) := by
  have heq : (fun word => source.expectation (fun sample => kernel sample word)) =
      ∑ sample, source.weight sample • kernel sample := by
    funext word
    simp only [FiniteDist.expectation, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  change applyLinear count channel _ output = _
  rw [heq, map_sum]
  simp only [map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, applyLinear,
    LinearMap.coe_mk, AddHom.coe_mk, FiniteDist.expectation]

omit [Fintype Output] in
/-- Centering every local input does not alter the physical response of a
canonical joint kernel. In particular, tensor Hilbert bounds on the centered
local maps apply to the original, unmodified signed physical output. -/
theorem apply_centered_eq [Nonempty Input] (count : ℕ) (input : Fin count → FiniteDist Input)
    (channel : Fin count → (Input → ℝ) →ₗ[ℝ] (Output → ℝ))
    (kernel : (Fin count → Input) → ℝ)
    (hcanonical : Hoeffding.Canonical input Finset.univ kernel) (output : Fin count → Output) :
    apply count (fun index => (channel index).comp (center (input index))) kernel output =
      apply count channel kernel output := by
  induction count with
  | zero => rfl
  | succ count ih =>
    letI : DecidableEq (Fin count) := Classical.decEq _
    letI : DecidableEq (Fin (count + 1)) := Classical.decEq _
    have htail (first : Input) :
        Hoeffding.Canonical (fun index : Fin count => input index.succ) Finset.univ
          (fun rest => kernel (Fin.cons first rest)) := by
      constructor
      · intro firstRest secondRest heq
        congr 1
        funext index
        exact heq index (Finset.mem_univ _)
      · intro index _ rest
        have hh := hcanonical.2 index.succ (Finset.mem_univ _) (Fin.cons first rest)
        convert hh using 1
        apply Finset.sum_congr rfl
        intro value _
        congr 1
        apply congrArg kernel
        funext slot
        refine Fin.cases ?_ (fun slot => ?_) slot
        · simp [Function.update, Ne.symm (Fin.succ_ne_zero index), Fin.cons_zero]
        · by_cases hs : slot = index
          · subst slot
            simp [Function.update, Fin.cons_succ]
          · simp [Function.update, Fin.cons_succ, hs, Fin.succ_inj]
    let tailChannel := fun index : Fin count => channel index.succ
    let tailValue := fun first => apply count tailChannel (fun rest => kernel (Fin.cons first rest)) (fun index => output index.succ)
    have hhead : (input 0).expectation tailValue = 0 := by
      rw [← apply_expectation (input 0) count tailChannel
        (fun first rest => kernel (Fin.cons first rest)) (fun index => output index.succ)]
      have hz : (fun rest => (input 0).expectation (fun first => kernel (Fin.cons first rest))) = 0 := by
        funext rest
        have hh := hcanonical.2 0 (Finset.mem_univ _) (Fin.cons (Classical.arbitrary Input) rest)
        have hupdate (value : Input) :
            Function.update (Fin.cons (Classical.arbitrary Input) rest : Fin (count + 1) → Input) 0 value =
              (Fin.cons value rest : Fin (count + 1) → Input) := by
          funext index
          refine Fin.cases ?_ (fun index => ?_) index
          · simp [Function.update, Fin.cons_zero]
          · simp [Function.update, Fin.cons_succ, Fin.succ_ne_zero]
        simpa only [FiniteDist.expectation, hupdate, Pi.zero_apply] using hh
      rw [hz]
      exact congrFun (map_zero (applyLinear count tailChannel)) _
    change channel 0 (center (input 0) (fun first => apply count
      (fun index => (channel index.succ).comp (center (input index.succ)))
      (fun rest => kernel (Fin.cons first rest)) (fun index => output index.succ))) (output 0) = _
    have ht : (fun first => apply count
      (fun index => (channel index.succ).comp (center (input index.succ)))
      (fun rest => kernel (Fin.cons first rest)) (fun index => output index.succ)) = tailValue := by
      funext first
      exact ih _ _ _ (htail first) _
    rw [ht]
    have hc : center (input 0) tailValue = tailValue := by
      funext first
      simp only [center_apply, hhead, sub_zero]
    rw [hc]
    rfl

/-- The complete tensor bound now only requires the physically relevant
scalar estimates on mean-zero inputs, and applies to arbitrary joint
canonical kernels with their exact original response. -/
theorem canonical_energy_counting_le [Nonempty Input] (count : ℕ) (input : Fin count → FiniteDist Input)
    (channel : Fin count → (Input → ℝ) →ₗ[ℝ] (Output → ℝ)) (bound : Fin count → ℝ)
    (hchannel : ∀ index kernel, (input index).expectation kernel = 0 →
      (∑ output, channel index kernel output ^ 2) ≤ bound index ^ 2 * (input index).l2Sq kernel)
    (kernel : (Fin count → Input) → ℝ) (hcanonical : Hoeffding.Canonical input Finset.univ kernel) :
    (∑ output, apply count channel kernel output ^ 2) ≤
      (∏ index, bound index ^ 2) * (FiniteDist.independent input).l2Sq kernel := by
  have hh := energy_counting_le count input (fun index => (channel index).comp (center (input index))) bound
    (fun index => centered_channel_energy_le (input index) (channel index) (bound index) (hchannel index)) kernel
  simpa only [apply_centered_eq count input channel kernel hcanonical] using hh

end
end AFT.TensorChannel
