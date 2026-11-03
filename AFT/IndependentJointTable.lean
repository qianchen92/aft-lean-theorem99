import AFT.IndependentJointCanonical
import AFT.GroupedFiniteSeed
import AFT.RepresentedCanonical

/-! # The literal higher-response seed table for arbitrary joint inputs -/
namespace AFT.V7Calibration
open GaussianSource BoundaryCalibration RepresentedPolynomial Filter
open scoped BigOperators Classical Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
local instance independentJointTableFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _
local instance independentJointTableSubtypeDecEq (selected : Finset (Fin 4)) : DecidableEq selected := Classical.decEq _
attribute [local instance] actualModulusNeZero
variable {Primary Body : Type} [Fintype Primary] [Fintype Body] [DecidableEq Primary] [DecidableEq Body]

def independentOriginalJointSeed {Color : Type*} [Fintype Color]
    (kernel : Color → (Primary ⊕ Body → Color) → ℝ) : InputSeed Color :=
  groupedFiniteSeed (MixedKernel.singletonJoin kernel)

def independentJointHigherSeed (C : ℝ) (n : ℕ) (beta : ℝ)
    (operator : (Fin (Parameters.modulus n) → ℝ) ≃ₗ[ℝ] (Fin (Parameters.modulus n) → ℝ))
    (charts : (mark : Fin (Parameters.modulus n)) → PublicChartFamily C n mark)
    (kernel : Fin (Parameters.modulus n) → (Primary ⊕ Body → Fin (Parameters.modulus n)) → ℝ)
    (selected : Finset (Fin 4)) : InputSeed (Fin (Parameters.modulus n)) :=
  groupedFiniteSeed (independentJointInverse C n beta operator charts
    (Sum.elim (fun _ : Primary => actualPrimaryLaw C n beta) (fun _ : Body => actualBodyLaw C n beta)) selected kernel)

def independentJointHigherTable (C : ℝ) (n : ℕ) (beta : ℝ)
    (operator : (Fin (Parameters.modulus n) → ℝ) ≃ₗ[ℝ] (Fin (Parameters.modulus n) → ℝ))
    (charts : (mark : Fin (Parameters.modulus n)) → PublicChartFamily C n mark)
    (kernel : Fin (Parameters.modulus n) → (Primary ⊕ Body → Fin (Parameters.modulus n)) → ℝ) :
    Table (InputSeed (Fin (Parameters.modulus n))) :=
  ∑ selected ∈ (Finset.univ : Finset (Finset (Fin 4))).filter (fun selected => 2 ≤ selected.card),
    MvPolynomial.X (independentJointHigherSeed C n beta operator charts kernel selected)

def independentJointHigherConstant (C : ℝ) : ℝ :=
  16*32*independentReferenceHilbertConstant*(1+8*activationConstant C)^4

theorem independentJointHigherTable_activity_uniform_eventually (C : ℝ) (hC : 1 ≤ C)
    (beta : ℕ → ℝ) (pool : ℕ → ℕ)
    (htypical : ∀ᶠ n in atTop, (Parameters.legs n : ℝ)/(2*Parameters.dimension n) ≤ beta n ∧
      beta n ≤ 2*(Parameters.legs n : ℝ)/Parameters.dimension n ∧
      Parameters.legs n ≤ 2*pool n ∧ pool n ≤ Parameters.legs n) :
    ∀ᶠ n in atTop,
    ∀ (Primary Body : Type) [Fintype Primary] [Fintype Body] [DecidableEq Primary] [DecidableEq Body],
    ∀ operator : (Fin (Parameters.modulus n) → ℝ) ≃ₗ[ℝ] (Fin (Parameters.modulus n) → ℝ),
    operator.toLinearMap=actualResponse C n →
    ∀ charts : (mark : Fin (Parameters.modulus n)) → PublicChartFamily C n mark,
    (∀ mark first second,publicChartRaw C n mark (charts mark) (fun _ => 1) first second =
      conditionalJointOutput C n mark (fun _ => 1) first second) →
    ∀ kernel : Fin (Parameters.modulus n) → (Primary ⊕ Body → Fin (Parameters.modulus n)) → ℝ,
    (∀ rest,∑ color,(actualPrimaryLaw C n (beta n)).weight color*kernel color rest=0) →
    ∀ bodyPool radius : ℝ,0 ≤ radius →
    activity (inputWeight (actualPrimaryLaw C n (beta n)) (actualBodyLaw C n (beta n)) (pool n) bodyPool radius)
      (independentJointHigherTable C n (beta n) operator charts kernel) ≤
      independentJointHigherConstant C/(n : ℝ)^(5/2 : ℝ)*
        inputWeight (actualPrimaryLaw C n (beta n)) (actualBodyLaw C n (beta n)) (pool n) bodyPool radius
          (independentOriginalJointSeed kernel) := by
  filter_upwards [independentJointInverse_activity_uniform_eventually C hC beta pool htypical,
    eventually_ge_atTop 2] with n hi hn Primary Body _ _ _ _ operator hop charts hcharts kernel hkernel bodyPool radius hradius
  obtain ⟨chosen,hchosen,hi⟩ := hi
  have hi := hi (Primary ⊕ Body)
  have heq : operator=chosen := LinearEquiv.toLinearMap_injective (hop.trans hchosen.symm)
  subst chosen
  let primary := actualPrimaryLaw C n (beta n)
  let body := actualBodyLaw C n (beta n)
  let weight := inputWeight primary body (pool n) bodyPool radius
  let old := weight (independentOriginalJointSeed kernel)
  let bound := (32*independentReferenceHilbertConstant*(1+8*activationConstant C)^4/(n : ℝ)^(5/2 : ℝ))*old
  have hx : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have ha := activationConstant_pos C hC
  have hold : 0 ≤ old := inputWeight_nonneg _ _ _ _ _ _ hradius
  have hbound : 0 ≤ bound := by dsimp [bound]; unfold independentReferenceHilbertConstant; positivity
  have hseed (selected : Finset (Fin 4)) (hdegree : 2 ≤ selected.card) :
      weight (independentJointHigherSeed C n (beta n) operator charts kernel selected) ≤ bound := by
    have hh := hi charts hcharts (Sum.elim (fun _ : Primary => primary) (fun _ : Body => body))
      (Sum.elim (fun _ : Primary => 1/Real.sqrt (pool n : ℝ)) (fun _ : Body => 1/Real.sqrt bodyPool))
      (fun slot => by cases slot <;> simp only [Sum.elim_inl,Sum.elim_inr] <;> positivity)
      kernel hkernel selected hdegree
    have hscaled := mul_le_mul_of_nonneg_left hh (pow_nonneg hradius (Fintype.card Body))
    have hweight : weight (independentJointHigherSeed C n (beta n) operator charts kernel selected) ≤
        (32*independentReferenceHilbertConstant*(8*activationConstant C)^selected.card/(n : ℝ)^(5/2 : ℝ))*old := by
      dsimp only [weight,independentJointHigherSeed,old,independentOriginalJointSeed]
      rw [groupedFiniteSeed_weight,groupedFiniteSeed_weight]
      simp only [← one_div]
      exact hscaled.trans_eq (by ring)
    have hcard : selected.card ≤ 4 := by simpa only [Fintype.card_fin] using Finset.card_le_univ selected
    have hk : (8*activationConstant C)^selected.card ≤ (1+8*activationConstant C)^4 :=
      (pow_le_pow_left₀ (by positivity) (by linarith) selected.card).trans
        (pow_le_pow_right₀ (by linarith) hcard)
    apply hweight.trans
    exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hk (by norm_num [independentReferenceHilbertConstant])) (by positivity)) hold
  unfold independentJointHigherTable
  apply (activity_sum_le weight (fun seed => inputWeight_nonneg _ _ _ _ _ seed hradius) _ _).trans
  calc
    _ ≤ ∑ _selected ∈ (Finset.univ : Finset (Finset (Fin 4))).filter (fun selected : Finset (Fin 4) => 2 ≤ selected.card),bound := by
      apply Finset.sum_le_sum
      intro selected hs
      rw [activity_X]
      exact hseed selected (Finset.mem_filter.mp hs).2
    _ ≤ 16*bound := by
      rw [Finset.sum_const,nsmul_eq_mul]
      apply mul_le_mul_of_nonneg_right _ hbound
      exact_mod_cast (Finset.card_le_univ ((Finset.univ : Finset (Finset (Fin 4))).filter
        (fun selected : Finset (Fin 4) => 2 ≤ selected.card))).trans_eq (by simp)
    _ = _ := by dsimp [bound,old,weight,primary,body,independentJointHigherConstant]; ring

theorem independentJointHigherTable_activity_eventually (C : ℝ) (hC : 1 ≤ C)
    (beta : ℕ → ℝ) (pool : ℕ → ℕ)
    (htypical : ∀ᶠ n in atTop, (Parameters.legs n : ℝ)/(2*Parameters.dimension n) ≤ beta n ∧
      beta n ≤ 2*(Parameters.legs n : ℝ)/Parameters.dimension n ∧
      Parameters.legs n ≤ 2*pool n ∧ pool n ≤ Parameters.legs n) :
    ∀ᶠ n in atTop,
    ∀ operator : (Fin (Parameters.modulus n) → ℝ) ≃ₗ[ℝ] (Fin (Parameters.modulus n) → ℝ),
    operator.toLinearMap=actualResponse C n →
    ∀ charts : (mark : Fin (Parameters.modulus n)) → PublicChartFamily C n mark,
    (∀ mark first second,publicChartRaw C n mark (charts mark) (fun _ => 1) first second =
      conditionalJointOutput C n mark (fun _ => 1) first second) →
    ∀ kernel : Fin (Parameters.modulus n) → (Primary ⊕ Body → Fin (Parameters.modulus n)) → ℝ,
    (∀ rest,∑ color,(actualPrimaryLaw C n (beta n)).weight color*kernel color rest=0) →
    ∀ bodyPool radius : ℝ,0 ≤ radius →
    activity (inputWeight (actualPrimaryLaw C n (beta n)) (actualBodyLaw C n (beta n)) (pool n) bodyPool radius)
      (independentJointHigherTable C n (beta n) operator charts kernel) ≤
      independentJointHigherConstant C/(n : ℝ)^(5/2 : ℝ)*
        inputWeight (actualPrimaryLaw C n (beta n)) (actualBodyLaw C n (beta n)) (pool n) bodyPool radius
          (independentOriginalJointSeed kernel) := by
  filter_upwards [independentJointHigherTable_activity_uniform_eventually C hC beta pool htypical] with n h
  exact h Primary Body


theorem independentJointHigherTable_hasOrder (C : ℝ) (n : ℕ) (beta : ℝ)
    (operator : (Fin (Parameters.modulus n) → ℝ) ≃ₗ[ℝ] (Fin (Parameters.modulus n) → ℝ))
    (charts : (mark : Fin (Parameters.modulus n)) → PublicChartFamily C n mark)
    (kernel : Fin (Parameters.modulus n) → (Primary ⊕ Body → Fin (Parameters.modulus n)) → ℝ) :
    HasOrder (fun seed : InputSeed (Fin (Parameters.modulus n)) => seed.primaryOrder+seed.bodyOrder)
      (2+Fintype.card Primary+Fintype.card Body) (independentJointHigherTable C n beta operator charts kernel) := by
  apply hasOrder_sum
  intro selected hs
  simpa only [map_one,one_mul] using hasOrder_C_mul_X
    (fun seed : InputSeed (Fin (Parameters.modulus n)) => seed.primaryOrder+seed.bodyOrder)
    (2+Fintype.card Primary+Fintype.card Body) (independentJointHigherSeed C n beta operator charts kernel selected) 1 (by
      have hh := (Finset.mem_filter.mp hs).2
      simp only [independentJointHigherSeed,groupedFiniteSeed,mixedFiniteSeed,Fintype.card_sum,Fintype.card_coe]
      omega)

theorem independentJointHigherTable_canonical_uniform_eventually (C : ℝ) (hC : 1 ≤ C) (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ n in atTop, (Parameters.legs n : ℝ)/(2*Parameters.dimension n) ≤ beta n ∧
      beta n ≤ 2*(Parameters.legs n : ℝ)/Parameters.dimension n) :
    ∀ᶠ n in atTop,
    ∀ (Primary Body : Type) [Fintype Primary] [Fintype Body] [DecidableEq Primary] [DecidableEq Body],
    ∀ operator : (Fin (Parameters.modulus n) → ℝ) ≃ₗ[ℝ] (Fin (Parameters.modulus n) → ℝ),
    operator.toLinearMap=actualResponse C n →
    ∀ charts : (mark : Fin (Parameters.modulus n)) → PublicChartFamily C n mark,
    ∀ kernel : Fin (Parameters.modulus n) → (Primary ⊕ Body → Fin (Parameters.modulus n)) → ℝ,
    Hoeffding.Canonical (Sum.elim (fun _ : Unit => actualPrimaryLaw C n (beta n))
      (Sum.elim (fun _ : Primary => actualPrimaryLaw C n (beta n)) (fun _ : Body => actualBodyLaw C n (beta n))))
      Finset.univ (MixedKernel.singletonJoin kernel) →
    InputTableCanonical (actualPrimaryLaw C n (beta n)) (actualBodyLaw C n (beta n))
      (independentJointHigherTable C n (beta n) operator charts kernel) := by
  filter_upwards [independentJointInverse_correct_uniform_eventually C hC beta hbeta]
    with n hi Primary Body _ _ _ _ operator hop charts kernel hkernel
  apply InputTableCanonical.sum
  intro selected _
  apply InputTableCanonical.X
  apply groupedFiniteSeed_canonical
  exact (hi (Primary ⊕ Body) operator hop charts _ kernel hkernel selected).1

theorem independentJointHigherTable_canonical_eventually (C : ℝ) (hC : 1 ≤ C) (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ n in atTop, (Parameters.legs n : ℝ)/(2*Parameters.dimension n) ≤ beta n ∧
      beta n ≤ 2*(Parameters.legs n : ℝ)/Parameters.dimension n) :
    ∀ᶠ n in atTop,
    ∀ operator : (Fin (Parameters.modulus n) → ℝ) ≃ₗ[ℝ] (Fin (Parameters.modulus n) → ℝ),
    operator.toLinearMap=actualResponse C n →
    ∀ charts : (mark : Fin (Parameters.modulus n)) → PublicChartFamily C n mark,
    ∀ kernel : Fin (Parameters.modulus n) → (Primary ⊕ Body → Fin (Parameters.modulus n)) → ℝ,
    Hoeffding.Canonical (Sum.elim (fun _ : Unit => actualPrimaryLaw C n (beta n))
      (Sum.elim (fun _ : Primary => actualPrimaryLaw C n (beta n)) (fun _ : Body => actualBodyLaw C n (beta n))))
      Finset.univ (MixedKernel.singletonJoin kernel) →
    InputTableCanonical (actualPrimaryLaw C n (beta n)) (actualBodyLaw C n (beta n))
      (independentJointHigherTable C n (beta n) operator charts kernel) := by
  filter_upwards [independentJointHigherTable_canonical_uniform_eventually C hC beta hbeta] with n h
  exact h Primary Body


end
end AFT.V7Calibration
