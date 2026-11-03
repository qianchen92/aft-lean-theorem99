import AFT.ActualPlacedInputTail
import AFT.CenteredPolynomial
import AFT.RootBodyStrip

/-! # The actual finite root-response operator and exact source expansion -/

namespace AFT.Hoeffding
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {Index Source : Type*} [Fintype Index] [Fintype Source]

/-- The coefficient of a singleton is exactly zero when the reference is
that coordinate's actual marginal. -/
theorem densityComponent_singleton_of_marginal (law : FiniteDist (Index → Source))
    (reference : Index → FiniteDist Source) (index : Index)
    (hmarginal : law.map (fun word => word index) = reference index)
    (hpositive : ∀ color, 0 < (reference index).weight color) (word : Index → Source) :
    densityComponent reference law.weight {index} word = 0 := by
  have hm := congrArg (fun measure : FiniteDist Source => measure.weight (word index)) hmarginal
  change (∑ sample, if sample index = word index then law.weight sample else 0) =
    (reference index).weight (word index) at hm
  simp only [densityComponent,Finset.prod_singleton,centeredAtom,mul_sub,mul_one,
    Finset.sum_sub_distrib,law.sum_one]
  have heq : (∑ sample, law.weight sample *
      (if sample index = word index then ((reference index).weight (word index))⁻¹ else 0)) =
      (∑ sample, if sample index = word index then law.weight sample else 0) *
        ((reference index).weight (word index))⁻¹ := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro sample _
    split_ifs <;> ring
  rw [heq,hm,mul_inv_cancel₀ (hpositive _).ne',sub_self]

variable [DecidableEq Index]

/-- Exact finite ANOVA expansion inside any real linear target. In
particular the target may be a generating polynomial or a literal table. -/
theorem densityComponent_expectation_expansion {Target : Type*} [AddCommMonoid Target] [Module ℝ Target]
    (reference : Index → FiniteDist Source) (law : FiniteDist (Index → Source))
    (hpositive : ∀ index color, 0 < (reference index).weight color)
    (response : (Index → Source) → Target) :
    (∑ word, law.weight word • response word) =
      ∑ selected : Finset Index, ∑ word,
        ((FiniteDist.independent reference).weight word * densityComponent reference law.weight selected word) • response word := by
  calc
    _ = ∑ word, ((FiniteDist.independent reference).weight word *
        ∑ selected : Finset Index, densityComponent reference law.weight selected word) • response word := by
      apply Finset.sum_congr rfl
      intro word _
      rw [densityComponent_sum]
      congr 1
      simp only [FiniteDist.independent]
      have hproduct : (∏ index, (reference index).weight (word index)) ≠ 0 :=
        (Finset.prod_pos (fun index _ => hpositive index (word index))).ne'
      field_simp
    _ = _ := by
      simp only [Finset.mul_sum,Finset.sum_smul]
      exact Finset.sum_comm

end
end AFT.Hoeffding

namespace AFT.RepresentedPolynomial
open scoped BigOperators Classical
noncomputable section
variable {Slot Color : Type*} [Fintype Slot] [Fintype Color]

/-- The literal centered histogram generating polynomial of an arbitrary
signed physical output mass, retaining all homogeneous degrees. -/
def centeredGeneratingLinear (reference : Color → ℝ) :
    ((Slot → Color) → ℝ) →ₗ[ℝ] MvPolynomial Color ℝ where
  toFun mass := ∑ word, mass word • ∏ slot, centeredFactor reference (word slot)
  map_add' first second := by
    simp only [Pi.add_apply,add_smul,Finset.sum_add_distrib]
  map_smul' scalar mass := by
    simp only [Pi.smul_apply,smul_eq_mul,RingHom.id_apply,Finset.smul_sum,smul_smul]

end
end AFT.RepresentedPolynomial

namespace AFT.V7Calibration
open GaussianSource Filter RepresentedPolynomial BlockProducts HistogramNormalization
open scoped BigOperators Classical Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
local instance actualRootResponseFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _
local instance actualRootResponseSumDecEq {α β : Type*} : DecidableEq (α ⊕ β) := Classical.decEq _
local instance actualRootResponseSigmaDecEq {ι : Type*} {fiber : ι → Type*} : DecidableEq (Sigma fiber) := Classical.decEq _

/-- The genuine independent-root comparison law has the actual one-root
marginal at every physical root coordinate. -/
def actualIndependentRoots (n : ℕ) : FiniteDist (actualRootWord n) :=
  FiniteDist.independent (fun _ : Fin (Parameters.bodies n) => bodyRootReference n)

/-- The genuine coefficient is computed from the full conditioned root
word, rather than from an assumed kernel with a prescribed bound. -/
def actualRootResponseCoefficient (n : ℕ) (selected : Finset (Fin (Parameters.bodies n)))
    (word : actualRootWord n) : ℝ :=
  Hoeffding.densityComponent (fun _ : Fin (Parameters.bodies n) => bodyRootReference n)
    (actualRootConditionLaw n).weight selected word

theorem bodyRootReference_positive (n : ℕ) (color : Window (v7RootCutoff n)) :
    0 < (bodyRootReference n).weight color := by
  have hleg : 1 ≤ Parameters.legs n := by
    unfold Parameters.legs
    exact one_le_pow₀ (le_trans (by decide : 1 ≤ 2) (Parameters.security_ge_two n))
  have hN : 2 ≤ Parameters.bodies n := by
    have hh := Parameters.legs_le_half_bodies n
    omega
  exact rootMarginal_positive _ _ _ hN color

theorem actualRootResponseCoefficient_empty (n : ℕ) (word : actualRootWord n) :
    actualRootResponseCoefficient n ∅ word = 1 := by
  simp only [actualRootResponseCoefficient,Hoeffding.densityComponent,Finset.prod_empty,mul_one,FiniteDist.sum_one]

theorem actualRootResponseCoefficient_singleton (n : ℕ) (index : Fin (Parameters.bodies n))
    (word : actualRootWord n) : actualRootResponseCoefficient n {index} word = 0 :=
  Hoeffding.densityComponent_singleton_of_marginal (actualRootConditionLaw n)
    (fun _ => bodyRootReference n) index (actualRootConditionLaw_coordinate n index)
    (bodyRootReference_positive n) word

/-- The actual conditioned root response in any polynomial-valued channel. -/
def actualRootResponseLinear (n : ℕ) {Color : Type*} :
    (actualRootWord n → MvPolynomial Color ℝ) →ₗ[ℝ] MvPolynomial Color ℝ where
  toFun response := ∑ word, (actualRootConditionLaw n).weight word • response word
  map_add' first second := by simp only [Pi.add_apply,smul_add,Finset.sum_add_distrib]
  map_smul' scalar response := by
    simp only [Pi.smul_apply,RingHom.id_apply,Finset.smul_sum,smul_smul]
    apply Finset.sum_congr rfl
    intro word _
    rw [mul_comm]

def independentRootResponseLinear (n : ℕ) {Color : Type*} :
    (actualRootWord n → MvPolynomial Color ℝ) →ₗ[ℝ] MvPolynomial Color ℝ where
  toFun response := ∑ word, (actualIndependentRoots n).weight word • response word
  map_add' first second := by simp only [Pi.add_apply,smul_add,Finset.sum_add_distrib]
  map_smul' scalar response := by
    simp only [Pi.smul_apply,RingHom.id_apply,Finset.smul_sum,smul_smul]
    apply Finset.sum_congr rfl
    intro word _
    rw [mul_comm]

/-- A specified source-set term, as an actual finite linear operator. -/
def rootSetResponseLinear (n : ℕ) {Color : Type*} (selected : Finset (Fin (Parameters.bodies n))) :
    (actualRootWord n → MvPolynomial Color ℝ) →ₗ[ℝ] MvPolynomial Color ℝ where
  toFun response := ∑ word,
    ((actualIndependentRoots n).weight word * actualRootResponseCoefficient n selected word) • response word
  map_add' first second := by simp only [Pi.add_apply,smul_add,Finset.sum_add_distrib]
  map_smul' scalar response := by
    simp only [Pi.smul_apply,RingHom.id_apply,Finset.smul_sum,smul_smul]
    apply Finset.sum_congr rfl
    intro word _
    rw [mul_comm]

theorem actual_root_response_expansion (n : ℕ) {Color : Type*}
    (response : actualRootWord n → MvPolynomial Color ℝ) :
    actualRootResponseLinear n response =
      ∑ selected : Finset (Fin (Parameters.bodies n)), rootSetResponseLinear n selected response :=
  Hoeffding.densityComponent_expectation_expansion (fun _ => bodyRootReference n)
    (actualRootConditionLaw n) (fun _ => bodyRootReference_positive n) response

theorem rootSetResponseLinear_empty (n : ℕ) {Color : Type*}
    (response : actualRootWord n → MvPolynomial Color ℝ) :
    rootSetResponseLinear n ∅ response = independentRootResponseLinear n response := by
  simp only [rootSetResponseLinear,LinearMap.coe_mk,AddHom.coe_mk,actualRootResponseCoefficient_empty,mul_one]
  rfl

theorem rootSetResponseLinear_singleton (n : ℕ) {Color : Type*}
    (index : Fin (Parameters.bodies n)) (response : actualRootWord n → MvPolynomial Color ℝ) :
    rootSetResponseLinear n {index} response = 0 := by
  simp only [rootSetResponseLinear,LinearMap.coe_mk,AddHom.coe_mk,actualRootResponseCoefficient_singleton,
    mul_zero,zero_smul,Finset.sum_const_zero]

/-- The entire correlated response error is a concrete finite sum over
root sets of order at least two. -/
def rootDefectResponseLinear (n : ℕ) {Color : Type*} :
    (actualRootWord n → MvPolynomial Color ℝ) →ₗ[ℝ] MvPolynomial Color ℝ :=
  ∑ selected ∈ (Finset.univ : Finset (Finset (Fin (Parameters.bodies n)))).filter (fun selected => 2 ≤ selected.card),
    rootSetResponseLinear n selected

theorem actual_root_response_defect (n : ℕ) {Color : Type*}
    (response : actualRootWord n → MvPolynomial Color ℝ) :
    actualRootResponseLinear n response = independentRootResponseLinear n response + rootDefectResponseLinear n response := by
  rw [actual_root_response_expansion]
  have hsplit := Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset (Finset (Fin (Parameters.bodies n))))
    (fun selected => 2 ≤ selected.card) (fun selected => rootSetResponseLinear n selected response)
  have hlow : (∑ selected ∈ (Finset.univ : Finset (Finset (Fin (Parameters.bodies n)))).filter (fun selected => ¬2 ≤ selected.card),
      rootSetResponseLinear n selected response) = independentRootResponseLinear n response := by
    rw [Finset.sum_eq_single ∅]
    · exact rootSetResponseLinear_empty n response
    · intro selected hs hne
      have hcard : selected.card = 1 := by
        have hh := (Finset.mem_filter.mp hs).2
        have hz := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hne)
        omega
      obtain ⟨index,rfl⟩ := Finset.card_eq_one.mp hcard
      exact rootSetResponseLinear_singleton n index response
    · simp
  rw [hlow] at hsplit
  simpa only [rootDefectResponseLinear,LinearMap.sum_apply,add_comm] using hsplit.symm

end
end AFT.V7Calibration
