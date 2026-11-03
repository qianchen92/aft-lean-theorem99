import CurrentAFT.CanonicalReconstruction
import CurrentAFT.ActualCoordinateBounds

/-! # Explicit point coordinates for the full current calibration

All joint kernel entries are retained. The redundant ambient table is
projected by the exact centered point reconstruction, avoiding a chosen real
basis. Extending the response by the identity on the projection kernel gives
an invertible finite matrix with the same unique calibrated solution.
This identifies the matrix; rational approximation and bit costs are separate.
-/
namespace CurrentAFT.CalibrationPointCoordinates
open AFT ControlCoordinates ControlProduct CanonicalReconstruction
  GradedControlAlgebra ActualControls ProposalPrimary LocalCoefficientFamily
  ActualCompleteStability
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
local instance coordinateFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _

variable {Primary Body : Type*} [Fintype Primary] [Fintype Body]

abbrev PointIndex (Primary Body : Type*) (order : ℕ) :=
  (arity : TruncatedArity order) ×
    ((Fin arity.val.1.val → Primary) × (Fin arity.val.2.val → Body))

abbrev PointTable (Primary Body : Type*) (order : ℕ) := PointIndex Primary Body order → ℝ

def encode (primary : FiniteDist Primary) (body : FiniteDist Body) (order : ℕ) :
    KernelFamily primary body order →ₗ[ℝ] PointTable Primary Body order where
  toFun family point := (family point.1).val point.2.1 point.2.2
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def decode (primary : FiniteDist Primary) (body : FiniteDist Body)
    (hp : ∀ color, 0 < primary.weight color) (hb : ∀ color, 0 < body.weight color) (order : ℕ) :
    PointTable Primary Body order →ₗ[ℝ] KernelFamily primary body order where
  toFun table arity := ∑ colors, ∑ centers,
    ((∏ index, primary.weight (colors index)) * (∏ index, body.weight (centers index)) *
      table ⟨arity, colors, centers⟩) • pointKernel primary body hp hb colors centers
  map_add' first second := by
    funext arity
    simp only [Pi.add_apply, mul_add, add_smul, Finset.sum_add_distrib]
  map_smul' scalar table := by
    funext arity
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.smul_sum, smul_smul]
    congr 1
    funext colors
    congr 1
    funext centers
    congr 1
    ring

theorem decode_encode (primary : FiniteDist Primary) (body : FiniteDist Body)
    (hp : ∀ color, 0 < primary.weight color) (hb : ∀ color, 0 < body.weight color)
    (order : ℕ) (family : KernelFamily primary body order) :
    decode primary body hp hb order (encode primary body order family) = family := by
  funext arity
  exact pointKernel_expansion primary body hp hb (family arity)

theorem decode_single (primary : FiniteDist Primary) (body : FiniteDist Body)
    (hp : ∀ color, 0 < primary.weight color) (hb : ∀ color, 0 < body.weight color)
    (order : ℕ) (source : PointIndex Primary Body order) :
    decode primary body hp hb order (Pi.single source 1) =
      ((∏ index, primary.weight (source.2.1 index)) * (∏ index, body.weight (source.2.2 index))) •
        Pi.single (M := fun arity : TruncatedArity order =>
          canonicalKernels primary body arity.val.1.val arity.val.2.val)
          source.1 (pointKernel primary body hp hb source.2.1 source.2.2) := by
  rcases source with ⟨sourceArity, sourcePrimary, sourceBody⟩
  funext arity
  by_cases hequal : arity = sourceArity
  · subst arity
    simp [decode, Pi.single_apply, ite_and]
  · have hzero (colors : Fin arity.val.1.val → Primary) (centers : Fin arity.val.2.val → Body) :
        (Pi.single (M := fun _ : PointIndex Primary Body order => ℝ)
          ⟨sourceArity, sourcePrimary, sourceBody⟩ (1 : ℝ))
          ⟨arity, colors, centers⟩ = 0 := by
      have hne : (⟨arity, colors, centers⟩ : PointIndex Primary Body order) ≠
          ⟨sourceArity, sourcePrimary, sourceBody⟩ := fun h => hequal (congrArg Sigma.fst h)
      exact Pi.single_eq_of_ne (M := fun _ : PointIndex Primary Body order => ℝ) hne (1 : ℝ)
    simp only [decode, LinearMap.coe_mk, AddHom.coe_mk, hzero, mul_zero, zero_smul, Finset.sum_const_zero,
      Pi.smul_apply, Pi.single_eq_of_ne hequal, smul_zero]

theorem encode_injective (primary : FiniteDist Primary) (body : FiniteDist Body) (order : ℕ) :
    Function.Injective (encode primary body order) := by
  intro first second hequal
  funext arity
  apply Subtype.ext
  funext colors centers
  exact congrFun hequal ⟨arity, colors, centers⟩

def extend (primary : FiniteDist Primary) (body : FiniteDist Body)
    (hp : ∀ color, 0 < primary.weight color) (hb : ∀ color, 0 < body.weight color)
    (order : ℕ) (response : Module.End ℝ (KernelFamily primary body order)) :
    Module.End ℝ (PointTable Primary Body order) :=
  LinearMap.id - (encode primary body order).comp
    ((LinearMap.id - response).comp (decode primary body hp hb order))

theorem extend_encode (primary : FiniteDist Primary) (body : FiniteDist Body)
    (hp : ∀ color, 0 < primary.weight color) (hb : ∀ color, 0 < body.weight color)
    (order : ℕ) (response : Module.End ℝ (KernelFamily primary body order))
    (family : KernelFamily primary body order) :
    extend primary body hp hb order response (encode primary body order family) =
      encode primary body order (response family) := by
  simp only [extend, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply,
    decode_encode, map_sub]
  abel

theorem decode_extend (primary : FiniteDist Primary) (body : FiniteDist Body)
    (hp : ∀ color, 0 < primary.weight color) (hb : ∀ color, 0 < body.weight color)
    (order : ℕ) (response : Module.End ℝ (KernelFamily primary body order))
    (table : PointTable Primary Body order) :
    decode primary body hp hb order (extend primary body hp hb order response table) =
      response (decode primary body hp hb order table) := by
  simp only [extend, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply,
    map_sub, decode_encode]
  abel

theorem extend_injective (primary : FiniteDist Primary) (body : FiniteDist Body)
    (hp : ∀ color, 0 < primary.weight color) (hb : ∀ color, 0 < body.weight color)
    (order : ℕ) (response : Module.End ℝ (KernelFamily primary body order))
    (hinjective : Function.Injective response) :
    Function.Injective (extend primary body hp hb order response) := by
  intro first second hequal
  have hd := congrArg (decode primary body hp hb order) hequal
  simp only [decode_extend] at hd
  have hsame := hinjective hd
  simp only [extend, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply] at hequal
  rw [hsame] at hequal
  exact sub_left_injective hequal

def currentMatrix (security order : ℕ) (horder : 2 ≤ order)
    (hsecurity : threshold order horder ≤ security)
    (layout : ActualBlockFock.BlockIndex security ≃ CycleRootExpansion.Vertex security) :
    Matrix (PointIndex (ActualControls.Palette security) (SafePalette security) order)
      (PointIndex (ActualControls.Palette security) (SafePalette security) order) ℝ :=
  LinearMap.toMatrix' (extend (primaryLaw security) (bodyReference security)
    (primaryReference_positive security) (bodyReference_positive security) order
    (fullResponse security order horder (room security order horder hsecurity) layout))

theorem currentMatrix_injective (security order : ℕ) (horder : 2 ≤ order)
    (hsecurity : threshold order horder ≤ security)
    (layout : ActualBlockFock.BlockIndex security ≃ CycleRootExpansion.Vertex security) :
    Function.Injective (currentMatrix security order horder hsecurity layout).mulVec := by
  intro first second hequal
  simp only [currentMatrix, LinearMap.toMatrix'_mulVec] at hequal
  apply extend_injective _ _ (primaryReference_positive security) (bodyReference_positive security)
    order _ ?_ hequal
  intro first second hs
  obtain ⟨coefficient, _, hunique, _⟩ :=
    calibration_existsUnique security order horder hsecurity layout
      (fullResponse security order horder (room security order horder hsecurity) layout first)
  exact (hunique first rfl).trans (hunique second hs.symm).symm

theorem currentMatrix_solution (security order : ℕ) (horder : 2 ≤ order)
    (hsecurity : threshold order horder ≤ security)
    (layout : ActualBlockFock.BlockIndex security ≃ CycleRootExpansion.Vertex security) :
    (currentMatrix security order horder hsecurity layout).mulVec
      (encode (primaryLaw security) (bodyReference security) order
        (solution security order horder hsecurity layout)) =
      encode (primaryLaw security) (bodyReference security) order 1 := by
  simp only [currentMatrix, LinearMap.toMatrix'_mulVec, extend_encode, solution_response]

theorem currentMatrix_isUnit (security order : ℕ) (horder : 2 ≤ order)
    (hsecurity : threshold order horder ≤ security)
    (layout : ActualBlockFock.BlockIndex security ≃ CycleRootExpansion.Vertex security) :
    IsUnit (currentMatrix security order horder hsecurity layout) :=
  Matrix.mulVec_injective_iff_isUnit.mp (currentMatrix_injective security order horder hsecurity layout)

theorem pointIndex_card_le (order alphabet : ℕ) (halphabet : 1 ≤ alphabet)
    (hp : Fintype.card Primary ≤ alphabet) (hb : Fintype.card Body ≤ alphabet) :
    Fintype.card (PointIndex Primary Body order) ≤ (order + 1)^2 * alphabet^order := by
  rw [Fintype.card_sigma]
  calc
    _ ≤ ∑ _arity : TruncatedArity order, alphabet^order := by
      apply Finset.sum_le_sum
      intro arity _
      simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin]
      calc
        _ ≤ alphabet^arity.val.1.val * alphabet^arity.val.2.val :=
          Nat.mul_le_mul (Nat.pow_le_pow_left hp _) (Nat.pow_le_pow_left hb _)
        _ = alphabet^(arity.val.1.val + arity.val.2.val) := (pow_add _ _ _).symm
        _ ≤ alphabet^order := Nat.pow_le_pow_right halphabet arity.property
    _ = Fintype.card (TruncatedArity order) * alphabet^order := by simp
    _ ≤ (order + 1)^2 * alphabet^order := by
      apply Nat.mul_le_mul_right
      simpa only [Fintype.card_prod, Fintype.card_fin, pow_two] using
        (Fintype.card_subtype_le (fun arity : Fin (order + 1) × Fin (order + 1) =>
          arity.1.val + arity.2.val ≤ order))

theorem current_card_polynomial (security order : ℕ) :
    Fintype.card (PointIndex (ActualControls.Palette security) (SafePalette security) order) ≤
      ((order + 1)^2 * 131072^order) * Parameters.base security^(64 * order) := by
  have hcount := pointIndex_card_le (Primary := ActualControls.Palette security)
    (Body := SafePalette security) order (Parameters.modulus security)
    (Parameters.modulus_spec security).2.one_le (by simp [ActualControls.Palette])
    (by simpa only [ActualControls.Palette, Fintype.card_fin] using
      (Fintype.card_subtype_le (InwardAnchor.SafeColor security)))
  calc
    _ ≤ (order + 1)^2 * Parameters.modulus security^order := hcount
    _ ≤ (order + 1)^2 * (131072 * Parameters.base security^64)^order :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Parameters.modulus_bounds security).2 _)
    _ = _ := by rw [mul_pow, ← pow_mul]; ring

end
end CurrentAFT.CalibrationPointCoordinates
