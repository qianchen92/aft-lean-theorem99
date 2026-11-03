import CurrentAFT.RationalOrdinaryFamilyProgram
import CurrentAFT.RootOrdinaryDataIdentity

/-! # Accuracy of the literal retained-body ordinary hybrid column -/
namespace CurrentAFT.RationalOrdinaryFamilyProgram
open AFT DiffuseProfiles ProposalPrimary ActualControls CycleRootExpansion CoefficientHilbert
  ControlCoordinates GradedControlAlgebra RationalFamilyProductProgram RationalActualFamilyApproximation
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
local instance ordinaryNormalizedFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
local instance ordinaryNormalizedSafeDecidableEq (security : ℕ) : DecidableEq (SafePalette security) := Classical.decEq _
attribute [local irreducible] Parameters.base primaryLaw centerLaw rootReference PublicParameterProgram.modulus

theorem inverse_constants_nonneg (security order : ℕ) : 0 ≤ RationalSingletonProgram.inverseBound security order ∧
    0 ≤ RationalSingletonProgram.inverseErrorConstant security order := by
  have hfirst := RationalSingletonProgram.firstBound_nonneg security
  have hpos : 0 ≤ RationalSingletonProgram.positiveBound security := by unfold RationalSingletonProgram.positiveBound; positivity
  have hE := (RationalRootProfileProgram.densityError_nonneg security).2
  have hg0 := growth_ge_one order (1 + RationalSingletonProgram.positiveBound security) 0 (by positivity) (by norm_num)
  have hg := growth_ge_one order (1 + RationalSingletonProgram.positiveBound security)
    (RationalRootProfileProgram.meanErrorConstant security) (by positivity) hE
  constructor
  · unfold RationalSingletonProgram.inverseBound; positivity
  · unfold RationalSingletonProgram.inverseErrorConstant; positivity

theorem inverse_error (security bits order : ℕ) (horder : 1 ≤ order)
    (hfirst : RationalFirstResponseProgram.PrecisionBudget security bits)
    (hprecision : 1 / (2 : ℝ)^bits ≤ 1 / (4 * (Parameters.base security : ℝ)))
    (hbudget : 64 * (Parameters.base security : ℝ) * Parameters.dimension security * (1 / (2 : ℝ)^bits) ≤
      1 / (4 * (Parameters.modulus security : ℝ)))
    (arity : TruncatedArity order) (colors : Fin arity.val.1.val → Palette security)
    (centers : Fin arity.val.2.val → SafePalette security) :
    |interpret security order (RationalSingletonProgram.inverse security bits order .free 0) arity colors centers -
      (OrdinaryRaising.positiveInverse security order horder arity).val colors centers| ≤
      RationalSingletonProgram.inverseErrorConstant security order * (1 / (2 : ℝ)^bits) := by
  have h := RationalSingletonProgram.inverse_error security bits order horder .free 0 hfirst hprecision hbudget arity colors centers
  rw [RootOrdinaryDataIdentity.positiveInverse_free] at h
  exact h

theorem actual_inverse_bound (security order : ℕ) (horder : 1 ≤ order)
    (arity : TruncatedArity order) (colors : Fin arity.val.1.val → Palette security)
    (centers : Fin arity.val.2.val → SafePalette security) :
    |(OrdinaryRaising.positiveInverse security order horder arity).val colors centers| ≤
      RationalSingletonProgram.inverseBound security order := by
  have h := RationalSingletonProgram.actual_inverse_bound security order horder .free 0 arity colors centers
  rw [RootOrdinaryDataIdentity.positiveInverse_free] at h
  exact h

def atRootError (security order : ℕ) : ℝ := productError order (RationalTensorInverseProgram.actualBound security)
  (RationalSingletonProgram.inverseBound security order) (RationalOrdinaryProfileProgram.errorConstant security)
    (RationalSingletonProgram.inverseErrorConstant security order)

def independentError (security order : ℕ) : ℝ := productError order 1
  (RationalSingletonProgram.inverseBound security order) (RationalBackgroundDensities.centerErrorConstant security)
    (RationalSingletonProgram.inverseErrorConstant security order)

theorem atRoot_error (security bits order : ℕ) (horder : 1 ≤ order) (source : SafePalette security) (root : Root security)
    (hfirst : RationalFirstResponseProgram.PrecisionBudget security bits)
    (hprecision : 1 / (2 : ℝ)^bits ≤ 1 / (4 * (Parameters.base security : ℝ)))
    (hbudget : 64 * (Parameters.base security : ℝ) * Parameters.dimension security * (1 / (2 : ℝ)^bits) ≤
      1 / (4 * (Parameters.modulus security : ℝ)))
    (arity : TruncatedArity order) (colors : Fin arity.val.1.val → Palette security)
    (centers : Fin arity.val.2.val → SafePalette security) :
    |interpret security order (atRoot security bits order source.val.val root.val) arity colors centers -
      (RootReferenceColumns.ordinaryAt security order horder root (Pi.single source 1) arity).val colors centers| ≤
      atRootError security order * (1 / (2 : ℝ)^bits) := by
  exact RationalActualFamilyApproximation.product_error security bits order
    (firstActual security order horder source root) (OrdinaryRaising.positiveInverse security order horder)
    (first security bits order source.val.val root.val) (RationalSingletonProgram.inverse security bits order .free 0)
    (RationalTensorInverseProgram.actualBound security) (RationalSingletonProgram.inverseBound security order)
    (RationalOrdinaryProfileProgram.errorConstant security) (RationalSingletonProgram.inverseErrorConstant security order)
    (RationalTensorInverseProgram.actualBound_nonneg security) (inverse_constants_nonneg security order).1
    (firstError_nonneg security) (inverse_constants_nonneg security order).2
    (actual_first_bound security order horder source root) (actual_inverse_bound security order horder)
    (first_error security bits order horder source root hfirst hprecision hbudget)
    (inverse_error security bits order horder hfirst hprecision hbudget) arity colors centers

theorem independent_error (security bits order : ℕ) (horder : 1 ≤ order) (source : SafePalette security)
    (hfirst : RationalFirstResponseProgram.PrecisionBudget security bits)
    (hprecision : 1 / (2 : ℝ)^bits ≤ 1 / (4 * (Parameters.base security : ℝ)))
    (hbudget : 64 * (Parameters.base security : ℝ) * Parameters.dimension security * (1 / (2 : ℝ)^bits) ≤
      1 / (4 * (Parameters.modulus security : ℝ)))
    (arity : TruncatedArity order) (colors : Fin arity.val.1.val → Palette security)
    (centers : Fin arity.val.2.val → SafePalette security) :
    |interpret security order (independent security bits order source.val.val) arity colors centers -
      (SelectedOrdinaryHybrid.independentChannel security order horder (Pi.single source 1) arity).val colors centers| ≤
      independentError security order * (1 / (2 : ℝ)^bits) := by
  exact RationalActualFamilyApproximation.product_error security bits order
    (RaisingChannels.bodyLeading security order horder (Pi.single source 1)) (OrdinaryRaising.positiveInverse security order horder)
    (bodyFirst security bits order source.val.val) (RationalSingletonProgram.inverse security bits order .free 0)
    1 (RationalSingletonProgram.inverseBound security order) (RationalBackgroundDensities.centerErrorConstant security)
    (RationalSingletonProgram.inverseErrorConstant security order) (by norm_num) (inverse_constants_nonneg security order).1
    (by unfold RationalBackgroundDensities.centerErrorConstant; positivity) (inverse_constants_nonneg security order).2
    (actual_body_bound security order horder source) (actual_inverse_bound security order horder)
    (body_error security bits order horder source hprecision hbudget)
    (inverse_error security bits order horder hfirst hprecision hbudget) arity colors centers

def atRootBound (security order : ℕ) : ℝ := (Fintype.card (TruncatedArity order) : ℝ)^2 *
  (RationalTensorInverseProgram.actualBound security * RationalSingletonProgram.inverseBound security order)

theorem atRootBound_nonneg (security order : ℕ) : 0 ≤ atRootBound security order := by
  unfold atRootBound
  positivity [RationalTensorInverseProgram.actualBound_nonneg security, (inverse_constants_nonneg security order).1]

theorem actual_atRoot_bound (security order : ℕ) (horder : 1 ≤ order) (source : SafePalette security) (root : Root security)
    (arity : TruncatedArity order) (colors : Fin arity.val.1.val → Palette security)
    (centers : Fin arity.val.2.val → SafePalette security) :
    |(RootReferenceColumns.ordinaryAt security order horder root (Pi.single source 1) arity).val colors centers| ≤
      atRootBound security order := by
  have h := product_bound order (data security order (firstActual security order horder source root))
    (data security order (OrdinaryRaising.positiveInverse security order horder))
    (RationalTensorInverseProgram.actualBound security) (RationalSingletonProgram.inverseBound security order)
    (RationalTensorInverseProgram.actualBound_nonneg security) (inverse_constants_nonneg security order).1
    (actual_first_bound security order horder source root) (actual_inverse_bound security order horder) arity colors centers
  rw [data_product] at h
  exact h

def meanError (security order : ℕ) : ℝ :=
  (Parameters.modulus security : ℝ) * (atRootError security order + 2 * atRootBound security order)

theorem mean_interpret (security bits order source : ℕ) (arity : TruncatedArity order)
    (colors : Fin arity.val.1.val → Palette security) (centers : Fin arity.val.2.val → SafePalette security) :
    interpret security order (mean security bits order source) arity colors centers =
      ∑ root : Root security, (RootSignedMassProgram.referenceEntry security bits root.val : ℝ) *
        interpret security order (atRoot security bits order source root.val) arity colors centers := by
  change ((∑ root : Fin (PublicParameterProgram.modulus security).count,
    RootSignedMassProgram.referenceEntry security bits root.val *
      atRoot security bits order source root.val arity (fun index => (colors index).val)
        (fun index => (centers index).val.val) : ℚ) : ℝ) = _
  rw [PublicParameterProgram.modulus_value]
  simp only [Rat.cast_sum, Rat.cast_mul]
  calc
    _ = ∑ root : Palette security, (RootSignedMassProgram.referenceEntry security bits ((ZMod.finEquiv (Parameters.modulus security)) root).val : ℝ) *
        interpret security order (atRoot security bits order source ((ZMod.finEquiv (Parameters.modulus security)) root).val) arity colors centers := by
      apply Finset.sum_congr (by ext; simp)
      intro root _
      simp only [RationalLegMassProgram.finEquiv_val]
      rfl
    _ = _ := (ZMod.finEquiv (Parameters.modulus security)).toEquiv.sum_comp (fun root : Root security =>
      (RootSignedMassProgram.referenceEntry security bits root.val : ℝ) *
        interpret security order (atRoot security bits order source root.val) arity colors centers)

theorem mean_error (security bits order : ℕ) (horder : 1 ≤ order) (source : SafePalette security)
    (hfirst : RationalFirstResponseProgram.PrecisionBudget security bits)
    (hprecision : 1 / (2 : ℝ)^bits ≤ 1 / (4 * (Parameters.base security : ℝ)))
    (hbudget : 64 * (Parameters.base security : ℝ) * Parameters.dimension security * (1 / (2 : ℝ)^bits) ≤
      1 / (4 * (Parameters.modulus security : ℝ)))
    (arity : TruncatedArity order) (colors : Fin arity.val.1.val → Palette security)
    (centers : Fin arity.val.2.val → SafePalette security) :
    |interpret security order (mean security bits order source.val.val) arity colors centers -
      ∑ root : Root security, (rootReference security).weight root *
        (RootReferenceColumns.ordinaryAt security order horder root (Pi.single source 1) arity).val colors centers| ≤
      meanError security order * (1 / (2 : ℝ)^bits) := by
  rw [mean_interpret, ← Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ _root : Root security, (atRootError security order + 2 * atRootBound security order) * (1 / (2 : ℝ)^bits) := by
      apply Finset.sum_le_sum
      intro root _
      have hr := RootSignedMassProgram.referenceEntry_bounds security bits root
      have he := RootSignedMassProgram.referenceEntry_error security bits root
      have ha := atRoot_error security bits order horder source root hfirst hprecision hbudget arity colors centers
      have hb := actual_atRoot_bound security order horder source root arity colors centers
      calc
        _ = |(RootSignedMassProgram.referenceEntry security bits root.val : ℝ) *
            (interpret security order (atRoot security bits order source.val.val root.val) arity colors centers -
              (RootReferenceColumns.ordinaryAt security order horder root (Pi.single source 1) arity).val colors centers) +
            ((RootSignedMassProgram.referenceEntry security bits root.val : ℝ) - (rootReference security).weight root) *
              (RootReferenceColumns.ordinaryAt security order horder root (Pi.single source 1) arity).val colors centers| := by congr 1; ring
        _ ≤ _ := abs_add_le _ _
        _ ≤ 1 * (atRootError security order * (1 / (2 : ℝ)^bits)) + (2 / (2 : ℝ)^bits) * atRootBound security order := by
          simp only [abs_mul]
          exact add_le_add (mul_le_mul (by rw [abs_of_nonneg hr.1]; exact hr.2) ha (abs_nonneg _) (by norm_num))
            (mul_le_mul he hb (abs_nonneg _) (by positivity))
        _ = _ := by ring
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]; unfold meanError; ring

def errorConstant (security order : ℕ) : ℝ := independentError security order + atRootError security order + meanError security order

theorem current_error (security bits order : ℕ) (horder : 1 ≤ order) (source : SafePalette security) (root : Root security)
    (hfirst : RationalFirstResponseProgram.PrecisionBudget security bits)
    (hprecision : 1 / (2 : ℝ)^bits ≤ 1 / (4 * (Parameters.base security : ℝ)))
    (hbudget : 64 * (Parameters.base security : ℝ) * Parameters.dimension security * (1 / (2 : ℝ)^bits) ≤
      1 / (4 * (Parameters.modulus security : ℝ)))
    (arity : TruncatedArity order) (colors : Fin arity.val.1.val → Palette security)
    (centers : Fin arity.val.2.val → SafePalette security) :
    |interpret security order (current security bits order source.val.val root.val) arity colors centers -
      (RootReferenceColumns.hybridAt security order horder root (Pi.single source 1) arity).val colors centers| ≤
      errorConstant security order * (1 / (2 : ℝ)^bits) := by
  have hi := independent_error security bits order horder source hfirst hprecision hbudget arity colors centers
  have ha := atRoot_error security bits order horder source root hfirst hprecision hbudget arity colors centers
  have hm := mean_error security bits order horder source hfirst hprecision hbudget arity colors centers
  have htarget : (RootReferenceColumns.hybridAt security order horder root (Pi.single source 1) arity).val colors centers =
      (SelectedOrdinaryHybrid.independentChannel security order horder (Pi.single source 1) arity).val colors centers +
        (RootReferenceColumns.ordinaryAt security order horder root (Pi.single source 1) arity).val colors centers -
      ∑ other : Root security, (rootReference security).weight other *
        (RootReferenceColumns.ordinaryAt security order horder other (Pi.single source 1) arity).val colors centers := by
    simp only [RootReferenceColumns.hybridAt, Pi.sub_apply, Pi.add_apply, Submodule.coe_sub, Submodule.coe_add,
      Finset.sum_apply, Submodule.coe_sum, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul]
  have hcurrent : interpret security order (current security bits order source.val.val root.val) arity colors centers =
      interpret security order (independent security bits order source.val.val) arity colors centers +
        interpret security order (atRoot security bits order source.val.val root.val) arity colors centers -
      interpret security order (mean security bits order source.val.val) arity colors centers := by
    simp only [interpret, realTable, pullback, current, Pi.sub_apply, Pi.add_apply, Rat.cast_sub, Rat.cast_add]
  rw [hcurrent, htarget]
  have hsplit : interpret security order (independent security bits order source.val.val) arity colors centers +
      interpret security order (atRoot security bits order source.val.val root.val) arity colors centers -
      interpret security order (mean security bits order source.val.val) arity colors centers -
      ((SelectedOrdinaryHybrid.independentChannel security order horder (Pi.single source 1) arity).val colors centers +
        (RootReferenceColumns.ordinaryAt security order horder root (Pi.single source 1) arity).val colors centers -
        ∑ other : Root security, (rootReference security).weight other *
          (RootReferenceColumns.ordinaryAt security order horder other (Pi.single source 1) arity).val colors centers) =
      (interpret security order (independent security bits order source.val.val) arity colors centers -
        (SelectedOrdinaryHybrid.independentChannel security order horder (Pi.single source 1) arity).val colors centers) +
      (interpret security order (atRoot security bits order source.val.val root.val) arity colors centers -
        (RootReferenceColumns.ordinaryAt security order horder root (Pi.single source 1) arity).val colors centers) -
      (interpret security order (mean security bits order source.val.val) arity colors centers -
        ∑ other : Root security, (rootReference security).weight other *
          (RootReferenceColumns.ordinaryAt security order horder other (Pi.single source 1) arity).val colors centers) := by ring
  rw [hsplit]
  exact (abs_sub _ _).trans ((add_le_add ((abs_add_le _ _).trans (add_le_add hi ha)) hm).trans_eq (by unfold errorConstant; ring))

end
end CurrentAFT.RationalOrdinaryFamilyProgram
