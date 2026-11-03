import CurrentAFT.DiffusePairBounds

/-! The actual diffuse safe seed in the genuine degree-two body fiber. -/

namespace CurrentAFT.PairCertificateFamilies

open AFT ControlCoordinates ControlProduct ControlNorm GradedControlAlgebra GradedControlNorm
  GradedControlStability DiffuseProfiles ProposalPrimary ActualControls
  BackgroundCertificates BackgroundRates BackgroundFamilies DiffusePair DiffusePairBounds
open scoped BigOperators Classical

noncomputable section

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base ProposalPrimary.primaryLaw ProposalPrimary.centerLaw
  ActualControls.bodyReference DiffusePairBounds.bodyPairDensity BackgroundRates.bodyFactor

local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _

variable {Primary Body : Type*} [Fintype Primary] [Fintype Body]

def pairBodyRaw (density : Body → Body → ℝ) : DensityKernel (Primary := Primary) (Body := Body) 0 2 :=
  fun _ centers => density (centers 0) (centers 1)

theorem pairBodyRaw_centered (primary : FiniteDist Primary) (body : FiniteDist Body)
    (density : Body → Body → ℝ)
    (hfirst : ∀ second, ∑ first, body.weight first * density first second = 0)
    (hsecond : ∀ first, ∑ second, body.weight second * density first second = 0) :
    pairBodyRaw (Primary := Primary) density ∈ centeredKernelSpace primary body := by
  constructor
  · intro index
    exact Fin.elim0 index
  · intro index colors centers
    fin_cases index
    · simpa [pairBodyRaw, Function.update_apply]
        using hfirst (centers 1)
    · simpa [pairBodyRaw, Function.update_apply]
        using hsecond (centers 0)

def bodyPairKernel (primary : FiniteDist Primary) (body : FiniteDist Body)
    (density : Body → Body → ℝ)
    (hfirst : ∀ second, ∑ first, body.weight first * density first second = 0)
    (hsecond : ∀ first, ∑ second, body.weight second * density first second = 0) :
    canonicalKernels primary body 0 2 := by
  refine ⟨symmetrize (pairBodyRaw density), ?_, ?_, ?_⟩
  · exact (symmetrize_centered primary body _ (pairBodyRaw_centered primary body density hfirst hsecond)).1
  · exact (symmetrize_centered primary body _ (pairBodyRaw_centered primary body density hfirst hsecond)).2
  · intro primaryOrder bodyOrder colors centers
    rw [symmetrize_primary_permutation, symmetrize_body_permutation]

theorem pairBodyRaw_blockL2 (primary : FiniteDist Primary) (body : FiniteDist Body)
    (density : Body → Body → ℝ) :
    blockL2 primary body (pairBodyRaw density) =
      Real.sqrt (∑ first, ∑ second, body.weight first * body.weight second * density first second ^ 2) := by
  unfold blockL2
  congr 1
  rw [blockEnergy_apply]
  simp only [pairBodyRaw, Fin.prod_univ_zero, one_mul, Fin.prod_univ_two,
    Finset.univ_unique, Finset.sum_singleton]
  simpa only [Fintype.sum_prod_type, finTwoArrowEquiv, Equiv.coe_fn_symm_mk, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_fin_one] using
    ((finTwoArrowEquiv Body).symm.sum_comp (fun centers : Fin 2 → Body =>
      body.weight (centers 0) * body.weight (centers 1) * density (centers 0) (centers 1) ^ 2)).symm

theorem bodyPairKernel_blockL2_le (primary : FiniteDist Primary) (body : FiniteDist Body)
    (density : Body → Body → ℝ)
    (hfirst : ∀ second, ∑ first, body.weight first * density first second = 0)
    (hsecond : ∀ first, ∑ second, body.weight second * density first second = 0) :
    blockL2 primary body (bodyPairKernel primary body density hfirst hsecond).val ≤
      Real.sqrt (∑ first, ∑ second, body.weight first * body.weight second * density first second ^ 2) := by
  exact (blockL2_symmetrize_le primary body (pairBodyRaw density)).trans_eq
    (pairBodyRaw_blockL2 primary body density)

omit [Fintype Primary] [Fintype Body] in
theorem pairBodyRaw_symmetric (density : Body → Body → ℝ)
    (hsymmetric : ∀ first second, density first second = density second first) :
    SeparatelySymmetric (pairBodyRaw (Primary := Primary) density) := by
  intro primaryOrder bodyOrder colors centers
  have hne : (bodyOrder 0).val ≠ (bodyOrder 1).val := by
    intro hequal
    have h := bodyOrder.injective (Fin.ext hequal)
    have hv := congrArg Fin.val h
    norm_num at hv
  have hzero := (bodyOrder 0).isLt
  have hone := (bodyOrder 1).isLt
  have hcases : ((bodyOrder 0).val = 0 ∧ (bodyOrder 1).val = 1) ∨
      ((bodyOrder 0).val = 1 ∧ (bodyOrder 1).val = 0) := by omega
  rcases hcases with hcases | hcases
  · have h0 : bodyOrder 0 = 0 := Fin.ext hcases.1
    have h1 : bodyOrder 1 = 1 := Fin.ext hcases.2
    simp only [pairBodyRaw, Function.comp_apply, h0, h1]
  · have h0 : bodyOrder 0 = 1 := Fin.ext hcases.1
    have h1 : bodyOrder 1 = 0 := Fin.ext hcases.2
    simpa only [pairBodyRaw, Function.comp_apply, h0, h1] using hsymmetric (centers 1) (centers 0)

theorem bodyPairKernel_val (primary : FiniteDist Primary) (body : FiniteDist Body)
    (density : Body → Body → ℝ)
    (hfirst : ∀ second, ∑ first, body.weight first * density first second = 0)
    (hsecond : ∀ first, ∑ second, body.weight second * density first second = 0)
    (hsymmetric : ∀ first second, density first second = density second first) :
    (bodyPairKernel primary body density hfirst hsecond).val = pairBodyRaw density :=
  symmetrize_of_symmetric _ (pairBodyRaw_symmetric density hsymmetric)

def bodyPairArity (order : ℕ) (horder : 2 ≤ order) : TruncatedArity order :=
  ⟨(0, ⟨2, by omega⟩), by simpa⟩

def diffuseBodyCertificate (security order : ℕ) (horder : 2 ≤ order) (scalar : ℤ) : ActualFamily security order :=
  Pi.single (bodyPairArity order horder)
    (bodyPairKernel (primaryLaw security) (bodyReference security) (bodyPairDensity security scalar)
      (bodyPairDensity_centered_first security scalar) (bodyPairDensity_centered_second security scalar))

theorem diffuseBodyCertificate_stored_profile (security order : ℕ) (horder : 2 ≤ order) (scalar : ℤ)
    (centers : Fin 2 → SafePalette security) :
    (∏ index : Fin 2, (bodyReference security).weight (centers index)) *
      ((diffuseBodyCertificate security order horder scalar) (bodyPairArity order horder)).val Fin.elim0 centers =
        safePairProfile security scalar (centers 0).val (centers 1).val := by
  rw [diffuseBodyCertificate, Pi.single_eq_same, bodyPairKernel_val _ _ _ _ _ (bodyPairDensity_symmetric security scalar)]
  simp only [pairBodyRaw, Fin.prod_univ_two]
  exact bodyPairDensity_profile security scalar _ _

theorem diffuseBodyCertificate_norm (security order : ℕ) (horder : 2 ≤ order) (scalar : ℤ)
    (hscalar : |scalar| ≤ Parameters.sourceCutoff security) :
    familyNorm (primaryLaw security) (bodyReference security) order (primaryFactor security) (bodyFactor security)
      (diffuseBodyCertificate security order horder scalar) ≤
        bodyFactor security ^ 2 * (1024 * (Parameters.base security : ℝ) ^ 8) := by
  rw [diffuseBodyCertificate, familyNorm_single]
  have hnorm := (bodyPairKernel_blockL2_le (primaryLaw security) (bodyReference security)
    (bodyPairDensity security scalar) (bodyPairDensity_centered_first security scalar)
    (bodyPairDensity_centered_second security scalar)).trans (bodyPairDensity_norm_growth security scalar hscalar)
  simpa only [bodyPairArity, gradeWeight, Fin.val_zero, pow_zero, one_mul] using
    mul_le_mul_of_nonneg_left hnorm (sq_nonneg (bodyFactor security))

theorem diffuseBodyCertificate_norm_decay (security order : ℕ) (horder : 2 ≤ order) (scalar : ℤ)
    (hscalar : |scalar| ≤ Parameters.sourceCutoff security) :
    familyNorm (primaryLaw security) (bodyReference security) order (primaryFactor security) (bodyFactor security)
      (diffuseBodyCertificate security order horder scalar) ≤
        1024 / (Parameters.base security : ℝ) ^ 150 := by
  have hb := FirstResponse.base_pos security
  have hbody : 0 ≤ bodyFactor security := by unfold bodyFactor radius; positivity
  have hs := pow_le_pow_left₀ hbody (bodyFactor_le security) 2
  calc
    _ ≤ bodyFactor security ^ 2 * (1024 * (Parameters.base security : ℝ) ^ 8) :=
      diffuseBodyCertificate_norm security order horder scalar hscalar
    _ ≤ (1 / (Parameters.base security : ℝ) ^ 79) ^ 2 * (1024 * (Parameters.base security : ℝ) ^ 8) :=
      mul_le_mul_of_nonneg_right hs (by positivity)
    _ = _ := by field_simp

theorem diffuseBodyCertificate_population_bound (security order : ℕ) (horder : 2 ≤ order) (scalar : ℤ)
    (hscalar : |scalar| ≤ Parameters.sourceCutoff security) :
    (Parameters.legCount security : ℝ) *
      familyNorm (primaryLaw security) (bodyReference security) order (primaryFactor security) (bodyFactor security)
        (diffuseBodyCertificate security order horder scalar) ≤
          1024 / (Parameters.base security : ℝ) ^ 22 := by
  have hb := FirstResponse.base_pos security
  calc
    _ ≤ (Parameters.legCount security : ℝ) * (1024 / (Parameters.base security : ℝ) ^ 150) :=
      mul_le_mul_of_nonneg_left (diffuseBodyCertificate_norm_decay security order horder scalar hscalar) (Nat.cast_nonneg _)
    _ = _ := by rw [Parameters.legCount_eq, Nat.cast_pow]; field_simp

end

end CurrentAFT.PairCertificateFamilies
