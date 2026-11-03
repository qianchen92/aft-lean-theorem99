import AFT.MixedTriple
import AFT.SafePairCore

/-! # Exact weighted canonicality of the finite input products -/

namespace AFT.MixedKernel
open scoped BigOperators Classical
noncomputable section


variable {Color Slot Tag : Type*} [Fintype Color] [Fintype Slot]

theorem canonical_average [Fintype Tag] (reference : Slot → FiniteDist Color)
    (kernels : Tag → (Slot → Color) → ℝ) (law : FiniteDist Tag)
    (h : ∀ tag, Hoeffding.Canonical reference Finset.univ (kernels tag)) :
    Hoeffding.Canonical reference Finset.univ (∑ tag, law.weight tag • kernels tag) := by
  constructor
  · intro x y hxy
    have heq : x = y := funext (fun i => hxy i (Finset.mem_univ i))
    rw [heq]
  · intro slot _ word
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro tag _
    have hh := (h tag).2 slot (Finset.mem_univ slot) word
    calc
      _ = law.weight tag * ∑ color, (reference slot).weight color * kernels tag (Function.update word slot color) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro color _
        ring
      _ = 0 := by rw [hh, mul_zero]

theorem pair_canonical (p : FiniteDist Color) (kernel : Color → Color → ℝ)
    (hrow : ∀ x, (∑ y, p.weight y * kernel x y) = 0)
    (hcol : ∀ y, (∑ x, p.weight x * kernel x y) = 0) :
    Hoeffding.Canonical (fun _ : Fin 2 => p) Finset.univ (pairKernel kernel) := by
  constructor
  · intro x y hxy
    have heq : x = y := funext (fun i => hxy i (Finset.mem_univ i))
    rw [heq]
  · intro slot _ word
    fin_cases slot
    · simpa [pairKernel, Function.update, Fin.ext_iff] using hcol (word 1)
    · simpa [pairKernel, Function.update, Fin.ext_iff] using hrow (word 0)

theorem canonicalPair_density_canonical (p : FiniteDist Color) (reference : Color → ℝ)
    (mass : Color → Color → ℝ) (hp : ∀ color, 0 < p.weight color) (hr : ∑ color, reference color = 1) :
    Hoeffding.Canonical (fun _ : Fin 2 => p) Finset.univ
      (pairKernel (fun x y => SafePair.canonicalPair reference mass x y / (p.weight x * p.weight y))) := by
  apply pair_canonical
  · intro x
    calc
      _ = (∑ y, SafePair.canonicalPair reference mass x y) / p.weight x := by
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro y _
        field_simp [ne_of_gt (hp x), ne_of_gt (hp y)]
      _ = 0 := by rw [SafePair.canonicalPair_first reference mass hr x, zero_div]
  · intro y
    calc
      _ = (∑ x, SafePair.canonicalPair reference mass x y) / p.weight y := by
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro x _
        field_simp [ne_of_gt (hp x), ne_of_gt (hp y)]
      _ = 0 := by rw [SafePair.canonicalPair_second reference mass hr y, zero_div]

theorem tripleProduct_canonical (p : FiniteDist Color) (pair : Color → Color → ℝ) (single : Color → ℝ)
    (hrow : ∀ x, (∑ y, p.weight y * pair x y) = 0)
    (hcol : ∀ y, (∑ x, p.weight x * pair x y) = 0)
    (hsingle : (∑ x, p.weight x * single x) = 0) :
    Hoeffding.Canonical (fun _ : Fin 3 => p) Finset.univ (tripleProductKernel pair single) := by
  constructor
  · intro x y hxy
    have heq : x = y := funext (fun i => hxy i (Finset.mem_univ i))
    rw [heq]
  · intro slot _ word
    fin_cases slot
    · simpa [tripleProductKernel, Function.update, Fin.ext_iff, ← mul_assoc, ← Finset.sum_mul] using
        congrArg (fun value => value * single (word 2)) (hcol (word 1))
    · simpa [tripleProductKernel, Function.update, Fin.ext_iff, ← mul_assoc, ← Finset.sum_mul] using
        congrArg (fun value => value * single (word 2)) (hrow (word 0))
    · simp only [tripleProductKernel]
      simp only [Function.update, Fin.ext_iff]
      norm_num
      calc
        _ = pair (word 0) (word 1) * ∑ color, p.weight color * single color := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro color _
          ring
        _ = 0 := by rw [hsingle, mul_zero]

theorem tripleProduct_canonical_of_pair (p : FiniteDist Color) (pair : Color → Color → ℝ) (single : Color → ℝ)
    (hpair : Hoeffding.Canonical (fun _ : Fin 2 => p) Finset.univ (pairKernel pair))
    (hsingle : (∑ x, p.weight x*single x) = 0) :
    Hoeffding.Canonical (fun _ : Fin 3 => p) Finset.univ (tripleProductKernel pair single) := by
  apply tripleProduct_canonical p pair single _ _ hsingle
  · intro x
    simpa [pairKernel, Function.update, Fin.ext_iff] using hpair.2 1 (Finset.mem_univ 1) ![x,x]
  · intro y
    simpa [pairKernel, Function.update, Fin.ext_iff] using hpair.2 0 (Finset.mem_univ 0) ![y,y]

theorem pair_product_canonical (p : FiniteDist Color) (first second : Color → ℝ)
    (hfirst : (∑ x, p.weight x*first x) = 0) (hsecond : (∑ x, p.weight x*second x) = 0) :
    Hoeffding.Canonical (fun _ : Fin 2 => p) Finset.univ (pairKernel (fun x y => first x*second y)) := by
  apply pair_canonical
  · intro x
    calc
      _ = first x * ∑ y, p.weight y*second y := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro y _
        ring
      _ = 0 := by rw [hsecond, mul_zero]
  · intro y
    simp only [← mul_assoc, ← Finset.sum_mul, hfirst, zero_mul]

end
end AFT.MixedKernel
