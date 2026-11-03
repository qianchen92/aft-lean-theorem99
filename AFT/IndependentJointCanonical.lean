import AFT.IndependentJointInverse
import AFT.ReplacementCanonical

/-! # Exact canonical joint inputs for the actual independent paired coefficients -/
namespace AFT.LocalTensors
open scoped BigOperators Classical
noncomputable section
variable {Slot Color : Type*} [Fintype Slot] [DecidableEq Slot] [Fintype Color]
local instance independentJointCanonicalSubtypeDecEq (selected : Finset Slot) : DecidableEq selected := Classical.decEq _

def referenceRestrictedLinear (primary reference : Slot → FiniteDist Color) (selected : Finset Slot) :
    ((Slot → Color) → ℝ) →ₗ[ℝ] ((selected → Color) → ℝ) where
  toFun := fun mass => referenceRestrictedComponent primary reference mass selected
  map_add' first second := by
    funext values
    simp only [referenceRestrictedComponent,Pi.add_apply,add_mul,Finset.sum_add_distrib]
  map_smul' scalar mass := by
    funext values
    simp only [referenceRestrictedComponent,Pi.smul_apply,smul_eq_mul,RingHom.id_apply,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro source _
    ring

end
end AFT.LocalTensors

namespace AFT.V7Calibration
open GaussianSource BoundaryCalibration Filter MixedKernel
open scoped BigOperators Classical Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
local instance independentJointCanonicalFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _
local instance independentJointCanonicalFinSubtypeDecEq (selected : Finset (Fin 4)) : DecidableEq selected := Classical.decEq _
attribute [local instance] actualModulusNeZero
variable {Rest : Type} [Fintype Rest] [DecidableEq Rest]

def independentReferenceChannel (C : ℝ) (n : ℕ) (beta : ℝ)
    (charts : (mark : Fin (Parameters.modulus n)) → PublicChartFamily C n mark) (selected : Finset (Fin 4)) :
    (Fin (Parameters.modulus n) → ℝ) →ₗ[ℝ] ((selected → Fin (Parameters.modulus n)) → ℝ) :=
  (LocalTensors.referenceRestrictedLinear (fun _ : Fin 4 => actualPrimaryLaw C n beta)
    (fun _ : Fin 4 => actualReferenceLaw C n beta) selected).comp
    (∑ roots,(pairedRootReference n).weight roots • actualPairedDensityChannel C n beta charts roots.1 roots.2 0)

theorem independentReferenceChannel_apply (C : ℝ) (n : ℕ) (beta : ℝ)
    (charts : (mark : Fin (Parameters.modulus n)) → PublicChartFamily C n mark) (selected : Finset (Fin 4))
    (profile : Fin (Parameters.modulus n) → ℝ) :
    independentReferenceChannel C n beta charts selected profile =
      LocalTensors.referenceRestrictedComponent (fun _ : Fin 4 => actualPrimaryLaw C n beta)
        (fun _ : Fin 4 => actualReferenceLaw C n beta)
        (independentPairedNumerator C n beta charts (fun color => (actualPrimaryLaw C n beta).weight color*profile color)) selected := by
  unfold independentReferenceChannel
  simp only [LinearMap.comp_apply,LinearMap.sum_apply,LinearMap.smul_apply]
  have he : (∑ roots,(pairedRootReference n).weight roots •
      actualPairedDensityChannel C n beta charts roots.1 roots.2 0 profile) =
      independentPairedNumerator C n beta charts
        (fun color => (actualPrimaryLaw C n beta).weight color*profile color) := by
    funext word
    simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,actualPairedDensityChannel_apply,
      independentPairedNumerator,actualJointPairedNumerator]
  rw [he]
  rfl

omit [Fintype Rest] [DecidableEq Rest] in
theorem independentReferenceReplacement_eq (C : ℝ) (n : ℕ) (beta : ℝ)
    (charts : (mark : Fin (Parameters.modulus n)) → PublicChartFamily C n mark) (selected : Finset (Fin 4))
    (kernel : Fin (Parameters.modulus n) → (Rest → Fin (Parameters.modulus n)) → ℝ) :
    independentReferenceReplacement C n beta charts selected kernel =
      blockReplacement (independentReferenceChannel C n beta charts selected) kernel := by
  funext word
  unfold independentReferenceReplacement blockReplacement
  rw [independentReferenceChannel_apply]

theorem independentJointInverse_correct_uniform_eventually (C : ℝ) (hC : 1 ≤ C) (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ n in atTop, (Parameters.legs n : ℝ)/(2*Parameters.dimension n) ≤ beta n ∧
      beta n ≤ 2*(Parameters.legs n : ℝ)/Parameters.dimension n) :
    ∀ᶠ n in atTop,
    ∀ (Rest : Type) [Fintype Rest] [DecidableEq Rest],
    ∀ operator : (Fin (Parameters.modulus n) → ℝ) ≃ₗ[ℝ] (Fin (Parameters.modulus n) → ℝ),
    operator.toLinearMap=actualResponse C n →
    ∀ charts : (mark : Fin (Parameters.modulus n)) → PublicChartFamily C n mark,
    ∀ (other : Rest → FiniteDist (Fin (Parameters.modulus n)))
      (kernel : Fin (Parameters.modulus n) → (Rest → Fin (Parameters.modulus n)) → ℝ),
    Hoeffding.Canonical (Sum.elim (fun _ : Unit => actualPrimaryLaw C n (beta n)) other) Finset.univ (singletonJoin kernel) →
    ∀ selected : Finset (Fin 4),
    Hoeffding.Canonical (Sum.elim (fun _ : selected => actualPrimaryLaw C n (beta n)) other) Finset.univ
      (independentJointInverse C n (beta n) operator charts other selected kernel) ∧
    (v7Activation C n)^selected.card •
      inputIteration ((allCoordinates (Slot := selected)).map Sum.inl).reverse (fun _ => operator.toLinearMap)
        (Sum.elim (fun _ : selected => actualPrimaryLaw C n (beta n)) other)
        (independentJointInverse C n (beta n) operator charts other selected kernel) =
      independentReferenceReplacement C n (beta n) charts selected kernel := by
  filter_upwards [actual_primary_probability_eventually C hC beta hbeta,
    actual_reference_laws_eventually C hC beta hbeta,actualResponse_inverse_mass_eventually C hC,
    eventually_ge_atTop 2] with n hp hl hm hn Rest _ _ operator hop charts other kernel hkernel selected
  have hpositive (color) : 0 < (actualPrimaryLaw C n (beta n)).weight color := by rw [hl.1]; exact hp.1 color
  have hnewpositive (slot : selected ⊕ Rest) (hs : slot ∈ (allCoordinates (Slot := selected)).map Sum.inl)
      (color) : (Sum.elim (fun _ : selected => actualPrimaryLaw C n (beta n)) other slot).weight color ≠ 0 := by
    obtain ⟨left,_,rfl⟩ := List.mem_map.mp hs
    exact (hpositive color).ne'
  have hcanonical : Hoeffding.Canonical
      (Sum.elim (fun _ : selected => actualPrimaryLaw C n (beta n)) other) Finset.univ
      (independentReferenceReplacement C n (beta n) charts selected kernel) := by
    rw [independentReferenceReplacement_eq]
    apply blockReplacement_canonical (actualPrimaryLaw C n (beta n)) other _ _ _ kernel hkernel
    intro profile
    rw [independentReferenceChannel_apply]
    exact LocalTensors.referenceRestrictedComponent_canonical _ _ (fun _ => hpositive) _ _
  refine ⟨coordinateInverseKernel_canonical _ _ _ operator hnewpositive (hm operator hop) _ hcanonical,?_⟩
  have hrho : v7Activation C n ≠ 0 := (activation_positive _ _ _ _
    (legFeatureCount_positive C n hC (by omega))).ne'
  have he := coordinateInverseKernel_exact ((allCoordinates (Slot := selected)).map Sum.inl)
    (Sum.elim (fun _ : selected => actualPrimaryLaw C n (beta n)) other) (v7Activation C n) hrho operator hnewpositive
    (independentReferenceReplacement C n (beta n) charts selected kernel)
  simpa only [List.length_map,allCoordinates_length,Fintype.card_coe] using he

theorem independentJointInverse_correct_eventually (C : ℝ) (hC : 1 ≤ C) (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ n in atTop, (Parameters.legs n : ℝ)/(2*Parameters.dimension n) ≤ beta n ∧
      beta n ≤ 2*(Parameters.legs n : ℝ)/Parameters.dimension n) :
    ∀ᶠ n in atTop,
    ∀ operator : (Fin (Parameters.modulus n) → ℝ) ≃ₗ[ℝ] (Fin (Parameters.modulus n) → ℝ),
    operator.toLinearMap=actualResponse C n →
    ∀ charts : (mark : Fin (Parameters.modulus n)) → PublicChartFamily C n mark,
    ∀ (other : Rest → FiniteDist (Fin (Parameters.modulus n)))
      (kernel : Fin (Parameters.modulus n) → (Rest → Fin (Parameters.modulus n)) → ℝ),
    Hoeffding.Canonical (Sum.elim (fun _ : Unit => actualPrimaryLaw C n (beta n)) other) Finset.univ (singletonJoin kernel) →
    ∀ selected : Finset (Fin 4),
    Hoeffding.Canonical (Sum.elim (fun _ : selected => actualPrimaryLaw C n (beta n)) other) Finset.univ
      (independentJointInverse C n (beta n) operator charts other selected kernel) ∧
    (v7Activation C n)^selected.card •
      inputIteration ((allCoordinates (Slot := selected)).map Sum.inl).reverse (fun _ => operator.toLinearMap)
        (Sum.elim (fun _ : selected => actualPrimaryLaw C n (beta n)) other)
        (independentJointInverse C n (beta n) operator charts other selected kernel) =
      independentReferenceReplacement C n (beta n) charts selected kernel := by
  filter_upwards [independentJointInverse_correct_uniform_eventually C hC beta hbeta] with n h
  exact h Rest


end
end AFT.V7Calibration
