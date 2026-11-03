import AFT.Correction

/-!
# Exact local inverse and boundary-preserving input projection

The rank-one inverse is the actual formula used in V7 Lemma 9.5.  Its
nonzero denominator is proved from an explicit smallness condition below.
The boundary collapse is defined on finite signed profiles and its
projection and preservation identities are proved directly.  These results
do not supply the unformalized model-dependent mixed-fiber estimates.
-/

namespace AFT

open scoped BigOperators

section RankOne

variable {𝕜 V : Type*} [Field 𝕜] [AddCommGroup V] [Module 𝕜 V]

/-- The rank-one operator `v ⊗ χ`, acting on signed primary profiles. -/
def profileRankOne (v : V) (χ : V →ₗ[𝕜] 𝕜) : V →ₗ[𝕜] V :=
  χ.smulRight v

@[simp] theorem profileRankOne_apply (v : V) (χ : V →ₗ[𝕜] 𝕜) (x : V) :
    profileRankOne v χ x = χ x • v := rfl

/-- The preconditioner `Id + ρ⁻¹ v ⊗ χ` from the local-response proof. -/
def primaryRankOperator (ρ : 𝕜) (v : V) (χ : V →ₗ[𝕜] 𝕜) : V →ₗ[𝕜] V :=
  LinearMap.id + ρ⁻¹ • profileRankOne v χ

/-- The explicit Sherman--Morrison inverse appearing in V7. -/
def primaryRankInverse (ρ : 𝕜) (v : V) (χ : V →ₗ[𝕜] 𝕜) : V →ₗ[𝕜] V :=
  LinearMap.id - (ρ + χ v)⁻¹ • profileRankOne v χ

@[simp] theorem primaryRankOperator_apply (ρ : 𝕜) (v : V)
    (χ : V →ₗ[𝕜] 𝕜) (x : V) :
    primaryRankOperator ρ v χ x = x + (ρ⁻¹ * χ x) • v := by
  simp [primaryRankOperator, smul_smul]

@[simp] theorem primaryRankInverse_apply (ρ : 𝕜) (v : V)
    (χ : V →ₗ[𝕜] 𝕜) (x : V) :
    primaryRankInverse ρ v χ x = x - ((ρ + χ v)⁻¹ * χ x) • v := by
  simp [primaryRankInverse, smul_smul]

/-- The left inverse is an algebraic identity, with the two necessary
nonvanishing assumptions exposed. -/
theorem primaryRankInverse_left (ρ : 𝕜) (v : V) (χ : V →ₗ[𝕜] 𝕜)
    (hρ : ρ ≠ 0) (hden : ρ + χ v ≠ 0) (x : V) :
    primaryRankInverse ρ v χ (primaryRankOperator ρ v χ x) = x := by
  rw [primaryRankInverse_apply, primaryRankOperator_apply]
  simp only [map_add, map_smul, smul_eq_mul]
  have hc : (ρ + χ v)⁻¹ * (χ x + (ρ⁻¹ * χ x) * χ v) = ρ⁻¹ * χ x := by
    field_simp
  rw [hc]
  abel

/-- The same formula is also a right inverse; no finite-dimensionality is
used in either algebraic direction. -/
theorem primaryRankInverse_right (ρ : 𝕜) (v : V) (χ : V →ₗ[𝕜] 𝕜)
    (hρ : ρ ≠ 0) (hden : ρ + χ v ≠ 0) (x : V) :
    primaryRankOperator ρ v χ (primaryRankInverse ρ v χ x) = x := by
  rw [primaryRankOperator_apply, primaryRankInverse_apply]
  simp only [map_sub, map_smul, smul_eq_mul]
  have hc : ρ⁻¹ * (χ x - ((ρ + χ v)⁻¹ * χ x) * χ v) =
      (ρ + χ v)⁻¹ * χ x := by
    field_simp
    ring
  rw [hc]
  abel

/-- A linear equivalence whose inverse is the displayed rank-one formula. -/
def primaryRankEquiv (ρ : 𝕜) (v : V) (χ : V →ₗ[𝕜] 𝕜)
    (hρ : ρ ≠ 0) (hden : ρ + χ v ≠ 0) : V ≃ₗ[𝕜] V where
  toLinearMap := primaryRankOperator ρ v χ
  invFun := primaryRankInverse ρ v χ
  left_inv := primaryRankInverse_left ρ v χ hρ hden
  right_inv := primaryRankInverse_right ρ v χ hρ hden

/-- Any subspace containing the signed sign profile is preserved by the
forward rank-one correction. In particular this applies to canonical
interior profiles once membership of `v` has been verified. -/
theorem primaryRankOperator_mem (S : Submodule 𝕜 V) (ρ : 𝕜) (v : V)
    (χ : V →ₗ[𝕜] 𝕜) (hv : v ∈ S) {x : V} (hx : x ∈ S) :
    primaryRankOperator ρ v χ x ∈ S := by
  rw [primaryRankOperator_apply]
  exact S.add_mem hx (S.smul_mem _ hv)

theorem primaryRankInverse_mem (S : Submodule 𝕜 V) (ρ : 𝕜) (v : V)
    (χ : V →ₗ[𝕜] 𝕜) (hv : v ∈ S) {x : V} (hx : x ∈ S) :
    primaryRankInverse ρ v χ x ∈ S := by
  rw [primaryRankInverse_apply]
  exact S.sub_mem hx (S.smul_mem _ hv)

end RankOne

/-- The V7 condition `|χ(v)| < ρ` supplies the denominator, rather than
assuming existence of an inverse. -/
theorem primaryRank_denominator_pos (ρ scalar : ℝ) (hsmall : |scalar| < ρ) :
    0 < ρ + scalar := by
  have := (abs_lt.mp hsmall).1
  linarith

/-- A quantitative denominator bound used for the inverse estimate. -/
theorem primaryRank_denominator_lower (ρ scalar : ℝ) (hsmall : |scalar| ≤ ρ / 2) :
    ρ / 2 ≤ ρ + scalar := by
  have := (abs_le.mp hsmall).1
  linarith

section ContinuousLocalInverse

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The explicitly constructed rank-one preconditioner as a unit in the
continuous operator ring. Its inverse is `Id - (ρ + χ(v))⁻¹ v ⊗ χ`. -/
noncomputable def primaryRankUnit (ρ : ℝ) (v : E) (χ : E →L[ℝ] ℝ)
    (hρ : ρ ≠ 0) (hden : ρ + χ v ≠ 0) : (E →L[ℝ] E)ˣ where
  val := ContinuousLinearMap.id ℝ E + ρ⁻¹ • χ.smulRight v
  inv := ContinuousLinearMap.id ℝ E - (ρ + χ v)⁻¹ • χ.smulRight v
  val_inv := by
    apply ContinuousLinearMap.ext
    intro x
    change primaryRankOperator ρ v χ.toLinearMap
      (primaryRankInverse ρ v χ.toLinearMap x) = x
    exact primaryRankInverse_right ρ v χ.toLinearMap hρ hden x
  inv_val := by
    apply ContinuousLinearMap.ext
    intro x
    change primaryRankInverse ρ v χ.toLinearMap
      (primaryRankOperator ρ v χ.toLinearMap x) = x
    exact primaryRankInverse_left ρ v χ.toLinearMap hρ hden x

/-- The inverse norm is controlled by the actual sign profile and sign
functional, independently of the dimension of the primary palette. -/
theorem primaryRankUnit_inverse_norm (ρ : ℝ) (v : E) (χ : E →L[ℝ] ℝ)
    (hρ : ρ ≠ 0) (hden : ρ + χ v ≠ 0) :
    ‖(↑((primaryRankUnit ρ v χ hρ hden)⁻¹) : E →L[ℝ] E)‖ ≤
      1 + |(ρ + χ v)⁻¹| * (‖χ‖ * ‖v‖) := by
  change ‖ContinuousLinearMap.id ℝ E - (ρ + χ v)⁻¹ • χ.smulRight v‖ ≤ _
  calc
    _ ≤ ‖ContinuousLinearMap.id ℝ E‖ + ‖(ρ + χ v)⁻¹ • χ.smulRight v‖ :=
      norm_sub_le _ _
    _ ≤ 1 + |(ρ + χ v)⁻¹| * (‖χ‖ * ‖v‖) := by
      rw [norm_smul, Real.norm_eq_abs, ContinuousLinearMap.norm_smulRight_apply]
      exact add_le_add (ContinuousLinearMap.norm_id_le (𝕜 := ℝ) (E := E)) le_rfl

variable [CompleteSpace E]

/-- An explicit Neumann inverse for the primary rank-one operator plus a
translation error. The smallness input is a norm estimate on the displayed
preconditioned error, not an assumption of invertibility. -/
noncomputable def perturbedPrimaryUnit (ρ : ℝ) (v : E) (χ : E →L[ℝ] ℝ)
    (hρ : ρ ≠ 0) (hden : ρ + χ v ≠ 0) (error : E →L[ℝ] E)
    (hsmall : ‖(↑((primaryRankUnit ρ v χ hρ hden)⁻¹) : E →L[ℝ] E) * error‖ < 1) :
    (E →L[ℝ] E)ˣ :=
  primaryRankUnit ρ v χ hρ hden *
    Units.oneSub (-((↑((primaryRankUnit ρ v χ hρ hden)⁻¹) : E →L[ℝ] E) * error))
      (by simpa only [norm_neg] using hsmall)

/-- The constructed unit's forward map is exactly V7's primary operator
`Id + ρ⁻¹ v ⊗ χ + error`. -/
theorem perturbedPrimaryUnit_val (ρ : ℝ) (v : E) (χ : E →L[ℝ] ℝ)
    (hρ : ρ ≠ 0) (hden : ρ + χ v ≠ 0) (error : E →L[ℝ] E)
    (hsmall : ‖(↑((primaryRankUnit ρ v χ hρ hden)⁻¹) : E →L[ℝ] E) * error‖ < 1) :
    (perturbedPrimaryUnit ρ v χ hρ hden error hsmall : E →L[ℝ] E) =
      ContinuousLinearMap.id ℝ E + ρ⁻¹ • χ.smulRight v + error := by
  change (primaryRankUnit ρ v χ hρ hden : E →L[ℝ] E) *
    (1 - -((↑((primaryRankUnit ρ v χ hρ hden)⁻¹) : E →L[ℝ] E) * error)) = _
  rw [sub_neg_eq_add, mul_add, mul_one, ← mul_assoc, Units.mul_inv, one_mul]
  rfl

end ContinuousLocalInverse

section BoundaryCollapse

variable {ι : Type*} [DecidableEq ι]

/-- Collapse the interior mass according to the primary law and keep every
boundary coordinate. `interior` is the complement of the boundary palette. -/
noncomputable def boundaryCollapse (interior : Finset ι) (primary : ι → ℝ) :
    (ι → ℝ) →ₗ[ℝ] (ι → ℝ) where
  toFun profile color := if color ∈ interior then
    (∑ i ∈ interior, profile i) / (∑ i ∈ interior, primary i) * primary color
    else profile color
  map_add' x y := by
    funext color
    simp only [Pi.add_apply]
    split_ifs <;> simp [Finset.sum_add_distrib, add_div, add_mul]
  map_smul' scalar x := by
    funext color
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs <;> simp [← Finset.mul_sum, mul_div_assoc, mul_assoc]

@[simp] theorem boundaryCollapse_boundary (interior : Finset ι) (primary profile : ι → ℝ)
    (color : ι) (hcolor : color ∉ interior) :
    boundaryCollapse interior primary profile color = profile color := by
  simp [boundaryCollapse, hcolor]

@[simp] theorem boundaryCollapse_interior (interior : Finset ι) (primary profile : ι → ℝ)
    (color : ι) (hcolor : color ∈ interior) :
    boundaryCollapse interior primary profile color =
      (∑ i ∈ interior, profile i) / (∑ i ∈ interior, primary i) * primary color := by
  simp [boundaryCollapse, hcolor]

theorem boundaryCollapse_interior_sum (interior : Finset ι) (primary profile : ι → ℝ)
    (hmass : ∑ i ∈ interior, primary i ≠ 0) :
    ∑ i ∈ interior, boundaryCollapse interior primary profile i =
      ∑ i ∈ interior, profile i := by
  calc
    _ = ∑ i ∈ interior,
        (∑ j ∈ interior, profile j) / (∑ j ∈ interior, primary j) * primary i := by
      apply Finset.sum_congr rfl
      intro i hi
      exact boundaryCollapse_interior interior primary profile i hi
    _ = _ := by rw [← Finset.mul_sum, div_mul_cancel₀ _ hmass]

theorem boundaryCollapse_idempotent (interior : Finset ι) (primary : ι → ℝ)
    (hmass : ∑ i ∈ interior, primary i ≠ 0) :
    (boundaryCollapse interior primary).comp (boundaryCollapse interior primary) =
      boundaryCollapse interior primary := by
  apply LinearMap.ext
  intro profile
  funext color
  by_cases hc : color ∈ interior
  · simp only [LinearMap.comp_apply, boundaryCollapse_interior _ _ _ _ hc,
      boundaryCollapse_interior_sum _ _ _ hmass]
  · simp [hc]

/-- The one-coordinate boundary ideal projector from V7. -/
noncomputable def boundaryIdealProjection (interior : Finset ι) (primary : ι → ℝ) :
    (ι → ℝ) →ₗ[ℝ] (ι → ℝ) := LinearMap.id - boundaryCollapse interior primary

@[simp] theorem boundaryIdealProjection_boundary (interior : Finset ι)
    (primary profile : ι → ℝ) (color : ι) (hc : color ∉ interior) :
    boundaryIdealProjection interior primary profile color = 0 := by
  simp [boundaryIdealProjection, hc]

theorem boundaryIdealProjection_interior_sum (interior : Finset ι)
    (primary profile : ι → ℝ) (hmass : ∑ i ∈ interior, primary i ≠ 0) :
    ∑ i ∈ interior, boundaryIdealProjection interior primary profile i = 0 := by
  simp only [boundaryIdealProjection, LinearMap.sub_apply, LinearMap.id_apply, Pi.sub_apply,
    Finset.sum_sub_distrib, boundaryCollapse_interior_sum _ _ _ hmass, sub_self]

/-- The projected profile has total mass zero and is supported on interior
colors. This is the actual canonical safe direction, not a postulated class. -/
theorem boundaryIdealProjection_canonical [Fintype ι] (interior : Finset ι)
    (primary profile : ι → ℝ) (hmass : ∑ i ∈ interior, primary i ≠ 0) :
    (∑ color, boundaryIdealProjection interior primary profile color = 0) ∧
    ∀ color ∉ interior, boundaryIdealProjection interior primary profile color = 0 := by
  constructor
  · have hs : ∑ color, boundaryIdealProjection interior primary profile color =
        ∑ color ∈ interior, boundaryIdealProjection interior primary profile color := by
      symm
      exact Finset.sum_subset (Finset.subset_univ _) (fun color _ hc =>
        boundaryIdealProjection_boundary interior primary profile color hc)
    rw [hs]
    exact boundaryIdealProjection_interior_sum interior primary profile hmass
  · exact fun color hc => boundaryIdealProjection_boundary interior primary profile color hc

theorem boundaryIdealProjection_idempotent (interior : Finset ι) (primary : ι → ℝ)
    (hmass : ∑ i ∈ interior, primary i ≠ 0) :
    (boundaryIdealProjection interior primary).comp (boundaryIdealProjection interior primary) =
      boundaryIdealProjection interior primary := by
  have h := boundaryCollapse_idempotent interior primary hmass
  apply LinearMap.ext
  intro profile
  funext color
  have hc := congrArg (fun f : (ι → ℝ) →ₗ[ℝ] (ι → ℝ) => f profile color) h
  simp only [boundaryIdealProjection, LinearMap.sub_apply, LinearMap.id_apply,
    LinearMap.comp_apply, map_sub, Pi.sub_apply] at *
  linarith

end BoundaryCollapse

section ConjugatedProjection

variable {𝕜 V : Type*} [Field 𝕜] [AddCommGroup V] [Module 𝕜 V]

/-- Conjugate the output boundary projection by the constructed primary
inverse. This implements the all-primary legal input projection. -/
def legalInputProjection (A : V ≃ₗ[𝕜] V) (P : V →ₗ[𝕜] V) : V →ₗ[𝕜] V :=
  A.symm.toLinearMap.comp (P.comp A.toLinearMap)

@[simp] theorem legalInputProjection_evaluation (A : V ≃ₗ[𝕜] V)
    (P : V →ₗ[𝕜] V) (input : V) :
    A (legalInputProjection A P input) = P (A input) := by
  simp [legalInputProjection]

theorem legalInputProjection_idempotent (A : V ≃ₗ[𝕜] V)
    (P : V →ₗ[𝕜] V) (hP : P.comp P = P) :
    (legalInputProjection A P).comp (legalInputProjection A P) =
      legalInputProjection A P := by
  ext input
  simp only [LinearMap.comp_apply, legalInputProjection, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply]
  exact congrArg A.symm (congrArg (fun f : V →ₗ[𝕜] V => f (A input)) hP)

/-- Projection leaves the leading evaluated output unchanged whenever that
output already lies in the boundary ideal. -/
theorem legalInputProjection_preserves_output (A : V ≃ₗ[𝕜] V)
    (P : V →ₗ[𝕜] V) (input : V) (hlegal : P (A input) = A input) :
    A (legalInputProjection A P input) = A input := by
  rw [legalInputProjection_evaluation, hlegal]

end ConjugatedProjection

end AFT
