import CurrentAFT.RootMeanPrimary

/-! Pure-primary support is preserved by actual convolution and finite inversion. -/

namespace CurrentAFT.PrimaryOnlyFamily

open AFT ControlCoordinates ControlProduct GradedControlAlgebra GradedInverse
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _

variable {Primary Body : Type*} [Fintype Primary] [Fintype Body]

def PrimaryOnly (primary : FiniteDist Primary) (body : FiniteDist Body) (order : ℕ)
    (family : KernelFamily primary body order) : Prop :=
  ∀ arity, 0 < arity.val.2.val → family arity = 0

theorem primaryOnly_zero (primary : FiniteDist Primary) (body : FiniteDist Body) (order : ℕ) :
    PrimaryOnly primary body order 0 := by intro arity _; rfl

theorem primaryOnly_one (primary : FiniteDist Primary) (body : FiniteDist Body) (order : ℕ) :
    PrimaryOnly primary body order 1 := by
  intro arity hbody
  change familyUnit primary body order arity = 0
  unfold familyUnit
  rw [Pi.single_eq_of_ne]
  intro hequal
  have h := congrArg (fun item : TruncatedArity order => item.val.2.val) hequal
  change arity.val.2.val = 0 at h
  omega

theorem primaryOnly_add (primary : FiniteDist Primary) (body : FiniteDist Body) (order : ℕ)
    (first second : KernelFamily primary body order)
    (hfirst : PrimaryOnly primary body order first) (hsecond : PrimaryOnly primary body order second) :
    PrimaryOnly primary body order (first + second) := by
  intro arity hbody
  simp only [Pi.add_apply, hfirst arity hbody, hsecond arity hbody, add_zero]

theorem primaryOnly_sub (primary : FiniteDist Primary) (body : FiniteDist Body) (order : ℕ)
    (first second : KernelFamily primary body order)
    (hfirst : PrimaryOnly primary body order first) (hsecond : PrimaryOnly primary body order second) :
    PrimaryOnly primary body order (first - second) := by
  intro arity hbody
  simp only [Pi.sub_apply, hfirst arity hbody, hsecond arity hbody, sub_self]

theorem primaryOnly_smul (primary : FiniteDist Primary) (body : FiniteDist Body) (order : ℕ)
    (scalar : ℝ) (family : KernelFamily primary body order) (hfamily : PrimaryOnly primary body order family) :
    PrimaryOnly primary body order (scalar • family) := by
  intro arity hbody
  simp only [Pi.smul_apply, hfamily arity hbody, smul_zero]

theorem primaryOnly_single (primary : FiniteDist Primary) (body : FiniteDist Body) (order : ℕ)
    (arity : TruncatedArity order) (hbody : arity.val.2.val = 0)
    (kernel : canonicalKernels primary body arity.val.1.val arity.val.2.val) :
    PrimaryOnly primary body order (Pi.single arity kernel) := by
  intro output hpositive
  rw [Pi.single_eq_of_ne]
  intro hequal
  have h := congrArg (fun item : TruncatedArity order => item.val.2.val) hequal
  change output.val.2.val = arity.val.2.val at h
  omega

theorem primaryOnly_mul (primary : FiniteDist Primary) (body : FiniteDist Body) (order : ℕ)
    (first second : KernelFamily primary body order)
    (hfirst : PrimaryOnly primary body order first) (hsecond : PrimaryOnly primary body order second) :
    PrimaryOnly primary body order (first * second) := by
  intro output hbody
  change familyProduct primary body order first second output = 0
  unfold familyProduct
  apply Finset.sum_eq_zero
  intro left _
  apply Finset.sum_eq_zero
  intro right _
  split_ifs with hmatch
  · by_cases hleft : 0 < left.val.2.val
    · rw [hfirst left hleft, homogeneousProduct_zero_left, transportKernel_zero]
    · have hright : 0 < right.val.2.val := by omega
      rw [hsecond right hright, homogeneousProduct_zero_right, transportKernel_zero]
  · rfl

theorem primaryOnly_pow (primary : FiniteDist Primary) (body : FiniteDist Body) (order : ℕ)
    (family : KernelFamily primary body order) (hfamily : PrimaryOnly primary body order family) (power : ℕ) :
    PrimaryOnly primary body order (family ^ power) := by
  induction power with
  | zero => simpa only [pow_zero] using primaryOnly_one primary body order
  | succ power ih =>
      rw [pow_succ]
      exact primaryOnly_mul primary body order _ _ ih hfamily

theorem primaryOnly_sum {Index : Type*} (primary : FiniteDist Primary) (body : FiniteDist Body) (order : ℕ)
    (indices : Finset Index) (families : Index → KernelFamily primary body order)
    (hfamily : ∀ index ∈ indices, PrimaryOnly primary body order (families index)) :
    PrimaryOnly primary body order (∑ index ∈ indices, families index) := by
  intro arity hbody
  simp only [Finset.sum_apply]
  exact Finset.sum_eq_zero fun index hindex => hfamily index hindex arity hbody

theorem primaryOnly_inverse (primary : FiniteDist Primary) (body : FiniteDist Body) (order : ℕ)
    (family : KernelFamily primary body order) (hfamily : PrimaryOnly primary body order family) :
    PrimaryOnly primary body order (backgroundInverse primary body order family) := by
  unfold backgroundInverse
  apply primaryOnly_sum primary body order
  intro power _
  exact primaryOnly_pow primary body order _
    (primaryOnly_sub primary body order _ _ (primaryOnly_one primary body order) hfamily) power

theorem rootMean_positiveFamily_primaryOnly (security order : ℕ) (horder : 1 ≤ order)
    (role : UniformBodyProfiles.BodyRole) (queue : ℤ) :
    PrimaryOnly (ProposalPrimary.primaryLaw security) (ActualControls.bodyReference security) order
      (RootMeanPrimary.positiveFamily security order horder role queue) := by
  apply primaryOnly_add _ _ _ _ _ (primaryOnly_one _ _ _)
  unfold RootMeanPrimary.positiveAtom PrimaryMassFamilies.massCertificateFamily
  exact primaryOnly_single _ _ _ _ rfl _

theorem rootMean_positiveInverse_primaryOnly (security order : ℕ) (horder : 1 ≤ order)
    (role : UniformBodyProfiles.BodyRole) (queue : ℤ) :
    PrimaryOnly (ProposalPrimary.primaryLaw security) (ActualControls.bodyReference security) order
      (RootMeanPrimary.positiveInverse security order horder role queue) :=
  primaryOnly_inverse _ _ _ _ (rootMean_positiveFamily_primaryOnly security order horder role queue)

end
end CurrentAFT.PrimaryOnlyFamily
