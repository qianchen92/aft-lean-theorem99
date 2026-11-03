import CurrentAFT.CommonQueueAssembly

/-!
# Quantitative bounds for the complete same-queue assembly

These estimates use the actual finite-family norm and its proved
submultiplicativity. Bounds on the fixed-queue physical operators are kept
explicit; proving those construction-specific inputs is a separate task.
-/

namespace CurrentAFT.CommonQueueNorm

open AFT ControlCoordinates ControlNorm GradedControlAlgebra GradedControlNorm
  GradedControlStability GradedInverse GradedInverseNorm CommonQueueAssembly
open scoped BigOperators Classical

noncomputable section

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

variable {Primary Body Queue : Type*} [Fintype Primary] [Fintype Body] [Fintype Queue]

omit [Fintype Queue] in
theorem norm_sub_le (primary : FiniteDist Primary) (body : FiniteDist Body) (order : ℕ)
    (pf bf : ℝ) (hpf : 0 ≤ pf) (hbf : 0 ≤ bf) (first second : KernelFamily primary body order) :
    familyNorm primary body order pf bf (first - second) ≤
      familyNorm primary body order pf bf first + familyNorm primary body order pf bf second := by
  simpa only [sub_eq_add_neg, familyNorm_neg] using
    familyNorm_add_le primary body order pf bf hpf hbf first (-second)

omit [Fintype Queue] in
theorem norm_sub_comm (primary : FiniteDist Primary) (body : FiniteDist Body) (order : ℕ)
    (pf bf : ℝ) (first second : KernelFamily primary body order) :
    familyNorm primary body order pf bf (first - second) =
      familyNorm primary body order pf bf (second - first) := by
  rw [← familyNorm_neg primary body order pf bf (first - second), neg_sub]

theorem norm_average_le (primary : FiniteDist Primary) (body : FiniteDist Body) (order : ℕ)
    (pf bf : ℝ) (hpf : 0 ≤ pf) (hbf : 0 ≤ bf) (law : FiniteDist Queue)
    (families : Queue → KernelFamily primary body order) (bound : ℝ)
    (hbound : ∀ queue, familyNorm primary body order pf bf (families queue) ≤ bound) :
    familyNorm primary body order pf bf (average primary body order law families) ≤ bound := by
  calc
    _ ≤ ∑ queue, familyNorm primary body order pf bf (law.weight queue • families queue) :=
      familyNorm_sum_le primary body order pf bf hpf hbf _ _
    _ = ∑ queue, law.weight queue * familyNorm primary body order pf bf (families queue) := by
      apply Finset.sum_congr rfl
      intro queue _
      rw [familyNorm_smul, abs_of_nonneg (law.nonneg queue)]
    _ ≤ ∑ queue, law.weight queue * bound :=
      Finset.sum_le_sum (fun queue _ => mul_le_mul_of_nonneg_left (hbound queue) (law.nonneg queue))
    _ = bound := by rw [← Finset.sum_mul, law.sum_one, one_mul]

theorem average_sub_one (primary : FiniteDist Primary) (body : FiniteDist Body) (order : ℕ)
    (law : FiniteDist Queue) (families : Queue → KernelFamily primary body order) :
    average primary body order law families - 1 =
      average primary body order law (fun queue => families queue - 1) := by
  unfold average
  simp only [smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul, law.sum_one, one_smul]

omit [Fintype Queue] in
theorem norm_of_sub_one_le (primary : FiniteDist Primary) (body : FiniteDist Body) (order : ℕ)
    (pf bf : ℝ) (hpf : 0 ≤ pf) (hbf : 0 ≤ bf)
    (family : KernelFamily primary body order) (bound : ℝ)
    (hbound : familyNorm primary body order pf bf (family - 1) ≤ bound) :
    familyNorm primary body order pf bf family ≤ 1 + bound := by
  have h := familyNorm_add_le primary body order pf bf hpf hbf (family - 1) 1
  rw [sub_add_cancel, familyNorm_one] at h
  linarith

theorem totalBackground_defect_le (primary : FiniteDist Primary) (body : FiniteDist Body) (order : ℕ)
    (pf bf : ℝ) (hpf : 0 ≤ pf) (hbf : 0 ≤ bf) (law : FiniteDist Queue)
    (background defect : Queue → KernelFamily primary body order)
    (beta epsilon : ℝ) (hbeta : 0 ≤ beta)
    (hbackground : ∀ queue, familyNorm primary body order pf bf (background queue - 1) ≤ beta)
    (hdefect : ∀ queue, familyNorm primary body order pf bf (defect queue) ≤ epsilon) :
    familyNorm primary body order pf bf
      (totalBackground primary body order law background defect - 1) ≤ beta + (1 + beta) * epsilon := by
  unfold totalBackground
  rw [average_sub_one]
  apply norm_average_le primary body order pf bf hpf hbf law
  intro queue
  have heq : background queue * (1 + defect queue) - 1 =
      (background queue - 1) + background queue * defect queue := by
    rw [mul_add, mul_one]
    abel
  rw [heq]
  have hB := norm_of_sub_one_le primary body order pf bf hpf hbf _ beta (hbackground queue)
  calc
    _ ≤ familyNorm primary body order pf bf (background queue - 1) +
        familyNorm primary body order pf bf (background queue * defect queue) :=
      familyNorm_add_le primary body order pf bf hpf hbf _ _
    _ ≤ beta + (1 + beta) * epsilon := by
      apply add_le_add (hbackground queue)
      exact (familyNorm_product_le primary body order pf bf hpf hbf _ _).trans
        (mul_le_mul hB (hdefect queue)
          (familyNorm_nonneg primary body order pf bf hpf hbf _) (by linarith))

omit [Fintype Queue] in
theorem connectedRoot_norm_le (primary : FiniteDist Primary) (body : FiniteDist Body) (order : ℕ)
    (pf bf : ℝ) (hpf : 0 ≤ pf) (hbf : 0 ≤ bf)
    (defect : Queue → KernelFamily primary body order)
    (raising : KernelFamily primary body order →ₗ[ℝ] KernelFamily primary body order)
    (rawRoot : Queue → KernelFamily primary body order →ₗ[ℝ] KernelFamily primary body order)
    (upsilon epsilon : ℝ) (hepsilon : 0 ≤ epsilon)
    (hraising : ∀ family, familyNorm primary body order pf bf (raising family) ≤
      upsilon * familyNorm primary body order pf bf family)
    (hdefect : ∀ queue, familyNorm primary body order pf bf (defect queue) ≤ epsilon)
    (hroot : ∀ queue family, familyNorm primary body order pf bf (rawRoot queue family) ≤
      epsilon * familyNorm primary body order pf bf family)
    (queue : Queue) (family : KernelFamily primary body order) :
    familyNorm primary body order pf bf
      (connectedRoot primary body order defect raising rawRoot queue family) ≤
        epsilon * (2 + upsilon) * familyNorm primary body order pf bf family := by
  have hsum : familyNorm primary body order pf bf (family + raising family) ≤
      (1 + upsilon) * familyNorm primary body order pf bf family := by
    have h := familyNorm_add_le primary body order pf bf hpf hbf family (raising family)
    nlinarith only [h, hraising family]
  change familyNorm primary body order pf bf
    (rawRoot queue family - defect queue * (family + raising family)) ≤ _
  calc
    _ ≤ familyNorm primary body order pf bf (rawRoot queue family) +
        familyNorm primary body order pf bf (defect queue * (family + raising family)) :=
      norm_sub_le primary body order pf bf hpf hbf _ _
    _ ≤ epsilon * familyNorm primary body order pf bf family +
        epsilon * ((1 + upsilon) * familyNorm primary body order pf bf family) := by
      apply add_le_add (hroot queue family)
      exact (familyNorm_product_le primary body order pf bf hpf hbf _ _).trans
        (mul_le_mul (hdefect queue) hsum
          (familyNorm_nonneg primary body order pf bf hpf hbf _) hepsilon)
    _ = _ := by ring

theorem normalizedRoot_norm_le (primary : FiniteDist Primary) (body : FiniteDist Body) (order : ℕ)
    (pf bf : ℝ) (hpf : 0 ≤ pf) (hbf : 0 ≤ bf) (law : FiniteDist Queue)
    (background defect : Queue → KernelFamily primary body order)
    (raising : KernelFamily primary body order →ₗ[ℝ] KernelFamily primary body order)
    (rawRoot : Queue → KernelFamily primary body order →ₗ[ℝ] KernelFamily primary body order)
    (beta upsilon epsilon : ℝ) (hbeta : 0 ≤ beta) (hepsilon : 0 ≤ epsilon)
    (hbackground : ∀ queue, familyNorm primary body order pf bf (background queue - 1) ≤ beta)
    (hraising : ∀ family, familyNorm primary body order pf bf (raising family) ≤
      upsilon * familyNorm primary body order pf bf family)
    (hdefect : ∀ queue, familyNorm primary body order pf bf (defect queue) ≤ epsilon)
    (hroot : ∀ queue family, familyNorm primary body order pf bf (rawRoot queue family) ≤
      epsilon * familyNorm primary body order pf bf family)
    (hgap : beta + (1 + beta) * epsilon < 1) (family : KernelFamily primary body order) :
    familyNorm primary body order pf bf
      (normalizedRoot primary body order law background defect raising rawRoot family) ≤
        ((1 + beta) * epsilon * (2 + upsilon) /
          (1 - (beta + (1 + beta) * epsilon))) * familyNorm primary body order pf bf family := by
  have htotal := totalBackground_defect_le primary body order pf bf hpf hbf law background defect
    beta epsilon hbeta hbackground hdefect
  have htotal' : familyNorm primary body order pf bf
      (1 - totalBackground primary body order law background defect) ≤ beta + (1 + beta) * epsilon := by
    rw [norm_sub_comm]
    exact htotal
  have hconnected (queue : Queue) : familyNorm primary body order pf bf
      (background queue * connectedRoot primary body order defect raising rawRoot queue family) ≤
        (1 + beta) * epsilon * (2 + upsilon) * familyNorm primary body order pf bf family := by
    have hB := norm_of_sub_one_le primary body order pf bf hpf hbf _ beta (hbackground queue)
    have hE := connectedRoot_norm_le primary body order pf bf hpf hbf defect raising rawRoot
      upsilon epsilon hepsilon hraising hdefect hroot queue family
    calc
      _ ≤ familyNorm primary body order pf bf (background queue) * familyNorm primary body order pf bf
          (connectedRoot primary body order defect raising rawRoot queue family) :=
        familyNorm_product_le primary body order pf bf hpf hbf _ _
      _ ≤ (1 + beta) * (epsilon * (2 + upsilon) * familyNorm primary body order pf bf family) :=
        mul_le_mul hB hE (familyNorm_nonneg primary body order pf bf hpf hbf _) (by linarith)
      _ = _ := by ring
  have havg : familyNorm primary body order pf bf
      (averagedConnected primary body order law background defect raising rawRoot family) ≤
        (1 + beta) * epsilon * (2 + upsilon) * familyNorm primary body order pf bf family := by
    exact norm_average_le primary body order pf bf hpf hbf law _ _ hconnected
  change familyNorm primary body order pf bf
    (backgroundInverse primary body order (totalBackground primary body order law background defect) *
      averagedConnected primary body order law background defect raising rawRoot family) ≤ _
  calc
    _ ≤ familyNorm primary body order pf bf
        (averagedConnected primary body order law background defect raising rawRoot family) /
          (1 - (beta + (1 + beta) * epsilon)) :=
      backgroundInverse_mul_norm_le primary body order pf bf hpf hbf _ _ hgap htotal' _
    _ ≤ ((1 + beta) * epsilon * (2 + upsilon) * familyNorm primary body order pf bf family) /
        (1 - (beta + (1 + beta) * epsilon)) :=
      div_le_div_of_nonneg_right havg (by linarith)
    _ = _ := by ring

def backgroundBudget (beta epsilon : ℝ) : ℝ := beta + (1 + beta) * epsilon

def rootBudget (beta upsilon epsilon : ℝ) : ℝ :=
  (1 + beta) * epsilon * (2 + upsilon) / (1 - backgroundBudget beta epsilon)

def fullBudget (beta upsilon epsilon : ℝ) : ℝ :=
  backgroundBudget beta epsilon +
    (1 + backgroundBudget beta epsilon) * (upsilon + rootBudget beta upsilon epsilon)

/-- Submultiplicativity transfers the fixed-queue estimates to the actual
full response, after its one complete averaged background is inverted. -/
theorem completeResponse_defect_le (primary : FiniteDist Primary) (body : FiniteDist Body) (order : ℕ)
    (pf bf : ℝ) (hpf : 0 ≤ pf) (hbf : 0 ≤ bf) (law : FiniteDist Queue)
    (background defect : Queue → KernelFamily primary body order)
    (raising : KernelFamily primary body order →ₗ[ℝ] KernelFamily primary body order)
    (rawRoot : Queue → KernelFamily primary body order →ₗ[ℝ] KernelFamily primary body order)
    (beta upsilon epsilon : ℝ) (hbeta : 0 ≤ beta) (hepsilon : 0 ≤ epsilon)
    (hbackground : ∀ queue, familyNorm primary body order pf bf (background queue - 1) ≤ beta)
    (hraising : ∀ family, familyNorm primary body order pf bf (raising family) ≤
      upsilon * familyNorm primary body order pf bf family)
    (hdefect : ∀ queue, familyNorm primary body order pf bf (defect queue) ≤ epsilon)
    (hroot : ∀ queue family, familyNorm primary body order pf bf (rawRoot queue family) ≤
      epsilon * familyNorm primary body order pf bf family)
    (hgap : backgroundBudget beta epsilon < 1)
    (hscalar : totalBackground primary body order law background defect (zeroArity order) =
      (1 : KernelFamily primary body order) (zeroArity order))
    (family : KernelFamily primary body order) :
    familyNorm primary body order pf bf
      (family - completeResponse primary body order law background raising rawRoot family) ≤
        fullBudget beta upsilon epsilon * familyNorm primary body order pf bf family := by
  let total := totalBackground primary body order law background defect
  let normalized := normalizedRoot primary body order law background defect raising rawRoot
  have htheta : 0 ≤ backgroundBudget beta epsilon := by
    unfold backgroundBudget
    positivity
  have htotal : familyNorm primary body order pf bf (total - 1) ≤ backgroundBudget beta epsilon :=
    totalBackground_defect_le primary body order pf bf hpf hbf law background defect
      beta epsilon hbeta hbackground hdefect
  have htotal' : familyNorm primary body order pf bf (1 - total) ≤ backgroundBudget beta epsilon := by
    rw [norm_sub_comm]
    exact htotal
  have htotalNorm := norm_of_sub_one_le primary body order pf bf hpf hbf total _ htotal
  have hnormalized : familyNorm primary body order pf bf (normalized family) ≤
      rootBudget beta upsilon epsilon * familyNorm primary body order pf bf family :=
    normalizedRoot_norm_le primary body order pf bf hpf hbf law background defect raising rawRoot
      beta upsilon epsilon hbeta hepsilon hbackground hraising hdefect hroot hgap family
  have hsum : familyNorm primary body order pf bf (raising family + normalized family) ≤
      (upsilon + rootBudget beta upsilon epsilon) * familyNorm primary body order pf bf family := by
    have h := familyNorm_add_le primary body order pf bf hpf hbf (raising family) (normalized family)
    nlinarith only [h, hraising family, hnormalized]
  have hresponse := LinearMap.congr_fun
    (completeResponse_factorization primary body order law background defect raising rawRoot hscalar) family
  change completeResponse primary body order law background raising rawRoot family =
    total * (family + raising family + normalized family) at hresponse
  have heq : family - completeResponse primary body order law background raising rawRoot family =
      (1 - total) * family - total * (raising family + normalized family) := by
    rw [hresponse]
    simp only [sub_mul, one_mul, mul_add]
    abel
  rw [heq]
  calc
    _ ≤ familyNorm primary body order pf bf ((1 - total) * family) +
        familyNorm primary body order pf bf (total * (raising family + normalized family)) :=
      norm_sub_le primary body order pf bf hpf hbf _ _
    _ ≤ backgroundBudget beta epsilon * familyNorm primary body order pf bf family +
        (1 + backgroundBudget beta epsilon) *
          ((upsilon + rootBudget beta upsilon epsilon) * familyNorm primary body order pf bf family) := by
      apply add_le_add
      · exact (familyNorm_product_le primary body order pf bf hpf hbf _ _).trans
          (mul_le_mul_of_nonneg_right htotal' (familyNorm_nonneg primary body order pf bf hpf hbf _))
      · exact (familyNorm_product_le primary body order pf bf hpf hbf _ _).trans
          (mul_le_mul htotalNorm hsum (familyNorm_nonneg primary body order pf bf hpf hbf _)
            (by linarith))
    _ = _ := by unfold fullBudget; ring

end

end CurrentAFT.CommonQueueNorm
