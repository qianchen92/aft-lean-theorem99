import CurrentAFT.GradedInverseNorm

/-!
# Complete shared-queue response assembly in the actual control algebra

Every product inside each average uses the same queue state. The complete
background is averaged first, and its finite inverse is applied afterwards.
The fixed-queue response operators remain explicit arguments: the physical
construction must supply them and their quantitative estimates.
-/

namespace CurrentAFT.CommonQueueAssembly

open AFT ControlCoordinates ControlProduct GradedControlAlgebra GradedInverse
open scoped BigOperators Classical

noncomputable section

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

variable {Primary Body Queue : Type*} [Fintype Primary] [Fintype Body] [Fintype Queue]

theorem homogeneousProduct_smul_left (primary : FiniteDist Primary) (body : FiniteDist Body)
    {r s r' s' : ℕ} (scalar : ℝ)
    (first : canonicalKernels primary body r s) (second : canonicalKernels primary body r' s') :
    homogeneousProduct primary body (scalar • first) second =
      scalar • homogeneousProduct primary body first second := by
  have hraw : finDisjointTensor (scalar • first.val) second.val =
      scalar • finDisjointTensor first.val second.val := by
    funext colors centers
    simp only [finDisjointTensor, reindexKernel, disjointTensor, Pi.smul_apply, smul_eq_mul]
    ring
  apply Subtype.ext
  change symmetrize (finDisjointTensor (scalar • first.val) second.val) =
    scalar • symmetrize (finDisjointTensor first.val second.val)
  rw [hraw]
  exact map_smul (symmetrizeLinear) scalar _

theorem family_smul_mul (primary : FiniteDist Primary) (body : FiniteDist Body)
    (order : ℕ) (scalar : ℝ) (first second : KernelFamily primary body order) :
    (scalar • first) * second = scalar • (first * second) := by
  funext output
  change familyProduct primary body order (scalar • first) second output =
    scalar • familyProduct primary body order first second output
  simp only [familyProduct, Pi.smul_apply, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro left _
  apply Finset.sum_congr rfl
  intro right _
  split_ifs with hmatch
  · rw [homogeneousProduct_smul_left, transportKernel_smul]
  · rw [smul_zero]

theorem family_mul_smul (primary : FiniteDist Primary) (body : FiniteDist Body)
    (order : ℕ) (scalar : ℝ) (first second : KernelFamily primary body order) :
    first * (scalar • second) = scalar • (first * second) := by
  rw [mul_comm first, family_smul_mul, mul_comm second]

def multiplyLinear (primary : FiniteDist Primary) (body : FiniteDist Body) (order : ℕ)
    (factor : KernelFamily primary body order) :
    KernelFamily primary body order →ₗ[ℝ] KernelFamily primary body order where
  toFun family := factor * family
  map_add' first second := mul_add factor first second
  map_smul' scalar family := family_mul_smul primary body order scalar factor family

def average (primary : FiniteDist Primary) (body : FiniteDist Body) (order : ℕ)
    (queueLaw : FiniteDist Queue) (families : Queue → KernelFamily primary body order) :
    KernelFamily primary body order := ∑ queue, queueLaw.weight queue • families queue

def averageOperator (primary : FiniteDist Primary) (body : FiniteDist Body) (order : ℕ)
    (queueLaw : FiniteDist Queue)
    (operators : Queue → KernelFamily primary body order →ₗ[ℝ] KernelFamily primary body order) :
    KernelFamily primary body order →ₗ[ℝ] KernelFamily primary body order where
  toFun family := ∑ queue, queueLaw.weight queue • operators queue family
  map_add' first second := by simp only [map_add, smul_add, Finset.sum_add_distrib]
  map_smul' scalar family := by
    simp only [map_smul, RingHom.id_apply, Finset.smul_sum, smul_smul]
    apply Finset.sum_congr rfl
    intro queue _
    rw [mul_comm]

def completeResponse (primary : FiniteDist Primary) (body : FiniteDist Body) (order : ℕ)
    (queueLaw : FiniteDist Queue) (background : Queue → KernelFamily primary body order)
    (raising : KernelFamily primary body order →ₗ[ℝ] KernelFamily primary body order)
    (rawRoot : Queue → KernelFamily primary body order →ₗ[ℝ] KernelFamily primary body order) :
    KernelFamily primary body order →ₗ[ℝ] KernelFamily primary body order :=
  averageOperator primary body order queueLaw (fun queue =>
    (multiplyLinear primary body order (background queue)).comp
      (LinearMap.id + raising + rawRoot queue))

def totalBackground (primary : FiniteDist Primary) (body : FiniteDist Body) (order : ℕ)
    (queueLaw : FiniteDist Queue) (background defect : Queue → KernelFamily primary body order) :
    KernelFamily primary body order :=
  average primary body order queueLaw (fun queue => background queue * (1 + defect queue))

def connectedRoot (primary : FiniteDist Primary) (body : FiniteDist Body) (order : ℕ)
    (defect : Queue → KernelFamily primary body order)
    (raising : KernelFamily primary body order →ₗ[ℝ] KernelFamily primary body order)
    (rawRoot : Queue → KernelFamily primary body order →ₗ[ℝ] KernelFamily primary body order)
    (queue : Queue) : KernelFamily primary body order →ₗ[ℝ] KernelFamily primary body order :=
  rawRoot queue - (multiplyLinear primary body order (defect queue)).comp (LinearMap.id + raising)

def averagedConnected (primary : FiniteDist Primary) (body : FiniteDist Body) (order : ℕ)
    (queueLaw : FiniteDist Queue) (background defect : Queue → KernelFamily primary body order)
    (raising : KernelFamily primary body order →ₗ[ℝ] KernelFamily primary body order)
    (rawRoot : Queue → KernelFamily primary body order →ₗ[ℝ] KernelFamily primary body order) :
    KernelFamily primary body order →ₗ[ℝ] KernelFamily primary body order :=
  averageOperator primary body order queueLaw (fun queue =>
    (multiplyLinear primary body order (background queue)).comp
      (connectedRoot primary body order defect raising rawRoot queue))

def normalizedRoot (primary : FiniteDist Primary) (body : FiniteDist Body) (order : ℕ)
    (queueLaw : FiniteDist Queue) (background defect : Queue → KernelFamily primary body order)
    (raising : KernelFamily primary body order →ₗ[ℝ] KernelFamily primary body order)
    (rawRoot : Queue → KernelFamily primary body order →ₗ[ℝ] KernelFamily primary body order) :
    KernelFamily primary body order →ₗ[ℝ] KernelFamily primary body order :=
  (multiplyLinear primary body order
    (backgroundInverse primary body order (totalBackground primary body order queueLaw background defect))).comp
      (averagedConnected primary body order queueLaw background defect raising rawRoot)

omit [Fintype Queue] in
theorem connectedRoot_unit (primary : FiniteDist Primary) (body : FiniteDist Body) (order : ℕ)
    (defect : Queue → KernelFamily primary body order)
    (raising : KernelFamily primary body order →ₗ[ℝ] KernelFamily primary body order)
    (rawRoot : Queue → KernelFamily primary body order →ₗ[ℝ] KernelFamily primary body order)
    (hraising : raising 1 = 0) (hroot : ∀ queue, rawRoot queue 1 = defect queue) (queue : Queue) :
    connectedRoot primary body order defect raising rawRoot queue 1 = 0 := by
  change rawRoot queue 1 - defect queue * (1 + raising 1) = 0
  rw [hraising, hroot, add_zero, mul_one, sub_self]

theorem normalizedRoot_unit (primary : FiniteDist Primary) (body : FiniteDist Body) (order : ℕ)
    (queueLaw : FiniteDist Queue) (background defect : Queue → KernelFamily primary body order)
    (raising : KernelFamily primary body order →ₗ[ℝ] KernelFamily primary body order)
    (rawRoot : Queue → KernelFamily primary body order →ₗ[ℝ] KernelFamily primary body order)
    (hraising : raising 1 = 0) (hroot : ∀ queue, rawRoot queue 1 = defect queue) :
    normalizedRoot primary body order queueLaw background defect raising rawRoot 1 = 0 := by
  have hconnected := connectedRoot_unit primary body order defect raising rawRoot hraising hroot
  simp only [normalizedRoot, averagedConnected, averageOperator, LinearMap.comp_apply,
    multiplyLinear, LinearMap.coe_mk, AddHom.coe_mk, hconnected,
    mul_zero, smul_zero, Finset.sum_const_zero]

theorem completeResponse_factorization (primary : FiniteDist Primary) (body : FiniteDist Body) (order : ℕ)
    (queueLaw : FiniteDist Queue) (background defect : Queue → KernelFamily primary body order)
    (raising : KernelFamily primary body order →ₗ[ℝ] KernelFamily primary body order)
    (rawRoot : Queue → KernelFamily primary body order →ₗ[ℝ] KernelFamily primary body order)
    (hscalar : totalBackground primary body order queueLaw background defect (zeroArity order) =
      (1 : KernelFamily primary body order) (zeroArity order)) :
    completeResponse primary body order queueLaw background raising rawRoot =
      (multiplyLinear primary body order (totalBackground primary body order queueLaw background defect)).comp
        (LinearMap.id + raising + normalizedRoot primary body order queueLaw background defect raising rawRoot) := by
  apply LinearMap.ext
  intro family
  let total := totalBackground primary body order queueLaw background defect
  let inverse := backgroundInverse primary body order total
  let remaining := averagedConnected primary body order queueLaw background defect raising rawRoot family
  have hinverse : total * inverse = 1 := mul_backgroundInverse primary body order total hscalar
  have haverage : completeResponse primary body order queueLaw background raising rawRoot family =
      total * (family + raising family) + remaining := by
    change (∑ queue, queueLaw.weight queue •
      (background queue * (family + raising family + rawRoot queue family))) = _
    change _ = (∑ queue, queueLaw.weight queue • (background queue * (1 + defect queue))) *
      (family + raising family) + ∑ queue, queueLaw.weight queue •
        (background queue * (rawRoot queue family - defect queue * (family + raising family)))
    rw [Finset.sum_mul, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro queue _
    rw [family_smul_mul, ← smul_add]
    congr 1
    simp only [mul_add, add_mul, mul_sub, mul_one, mul_assoc]
    abel
  rw [haverage]
  change total * (family + raising family) + remaining =
    total * (family + raising family + inverse * remaining)
  conv_rhs => rw [mul_add, ← mul_assoc, hinverse, one_mul]

end

end CurrentAFT.CommonQueueAssembly
