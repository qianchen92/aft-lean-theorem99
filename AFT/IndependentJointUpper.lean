import AFT.IndependentJointTable
import AFT.IndependentPositiveInverse
import AFT.LocalQuotientAlgebra

/-! # Sharp literal local quotient correction on every joint input seed -/
namespace AFT.V7Calibration
open GaussianSource BoundaryCalibration RepresentedPolynomial Filter
open scoped BigOperators Classical Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
local instance independentJointUpperFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _
attribute [local instance] actualModulusNeZero
variable {Primary Body : Type} [Fintype Primary] [Fintype Body] [DecidableEq Primary] [DecidableEq Body]

def independentJointUpper (C : ℝ) (n : ℕ) (beta : ℝ)
    (operator : (Fin (Parameters.modulus n) → ℝ) ≃ₗ[ℝ] (Fin (Parameters.modulus n) → ℝ))
    (charts : (mark : Fin (Parameters.modulus n)) → PublicChartFamily C n mark)
    (kernel : Fin (Parameters.modulus n) → (Primary ⊕ Body → Fin (Parameters.modulus n)) → ℝ)
    (depth : ℕ) : Table (InputSeed (Fin (Parameters.modulus n))) :=
  localUpperTable (MvPolynomial.X (independentOriginalJointSeed kernel))
    (independentJointHigherTable C n beta operator charts kernel)
    (independentPositiveInputTable C n beta operator charts) depth

def independentJointUpperConstant (C : ℝ) : ℝ :=
  2*(independentJointHigherConstant C+independentPositiveInputConstant C)

/-- Every new term has strictly larger total input order than the actual
joint seed it replaces. This is the finite triangularity needed for inversion. -/
theorem independentJointUpper_hasOrder (C : ℝ) (n : ℕ) (beta : ℝ)
    (operator : (Fin (Parameters.modulus n) → ℝ) ≃ₗ[ℝ] (Fin (Parameters.modulus n) → ℝ))
    (charts : (mark : Fin (Parameters.modulus n)) → PublicChartFamily C n mark)
    (kernel : Fin (Parameters.modulus n) → (Primary ⊕ Body → Fin (Parameters.modulus n)) → ℝ)
    (depth : ℕ) :
    HasOrder (fun seed : InputSeed (Fin (Parameters.modulus n)) => seed.primaryOrder+seed.bodyOrder)
      (2+Fintype.card Primary+Fintype.card Body) (independentJointUpper C n beta operator charts kernel depth) := by
  have hdegree : 2+Fintype.card Primary+Fintype.card Body=(1+Fintype.card Primary+Fintype.card Body)+1 := by omega
  rw [hdegree]
  apply localUpperTable_hasOrder_relative
  · simpa only [map_one,one_mul] using hasOrder_C_mul_X
      (fun seed : InputSeed (Fin (Parameters.modulus n)) => seed.primaryOrder+seed.bodyOrder)
      (1+Fintype.card Primary+Fintype.card Body) (independentOriginalJointSeed kernel) 1 (by
        simp only [independentOriginalJointSeed,groupedFiniteSeed,mixedFiniteSeed,Fintype.card_sum,Fintype.card_unique,le_refl])
  · simpa only [← hdegree] using independentJointHigherTable_hasOrder C n beta operator charts kernel
  · exact referenceInverseTable_hasOrder _ _ _ _ _ _

theorem independentJointUpper_activity_eventually (C : ℝ) (hC : 1 ≤ C)
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
    ∀ bodyPool radius : ℝ,0 ≤ radius → ∀ depth : ℕ,
    activity (inputWeight (actualPrimaryLaw C n (beta n)) (actualBodyLaw C n (beta n)) (pool n) bodyPool radius)
      (independentJointUpper C n (beta n) operator charts kernel depth) ≤
      independentJointUpperConstant C/(n : ℝ)^(5/2 : ℝ)*
        inputWeight (actualPrimaryLaw C n (beta n)) (actualBodyLaw C n (beta n)) (pool n) bodyPool radius
          (independentOriginalJointSeed kernel) := by
  have htyp := htypical.mono fun _ h => And.intro h.1 (And.intro h.2.1 h.2.2.1)
  have ht : Tendsto (fun n : ℕ => independentPositiveInputConstant C/(n : ℝ)^(43/4 : ℝ)) atTop (𝓝 0) :=
    ((tendsto_rpow_atTop (by norm_num : (0:ℝ)<43/4)).comp
      (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop)).const_div_atTop _
  have hs := Filter.Tendsto.eventually_le_const (by norm_num : (0:ℝ)<1/2) ht
  filter_upwards [independentJointHigherTable_activity_eventually (Primary := Primary) (Body := Body) C hC beta pool htypical,
    independentPositiveInputTable_activity_eventually C hC beta pool htyp,hs,eventually_ge_atTop 2]
    with n hh he hs hn operator hop charts hcharts kernel hkernel bodyPool radius hradius depth
  let weight := inputWeight (actualPrimaryLaw C n (beta n)) (actualBodyLaw C n (beta n)) (pool n) bodyPool radius
  have hw (seed) : 0 ≤ weight seed := inputWeight_nonneg _ _ _ _ _ seed hradius
  have hhigh := hh operator hop charts hcharts kernel hkernel bodyPool radius hradius
  have herror := he operator hop charts hcharts bodyPool radius hradius
  have hb := localUpperTable_activity_le weight hw (MvPolynomial.X (independentOriginalJointSeed kernel))
    (independentJointHigherTable C n (beta n) operator charts kernel)
    (independentPositiveInputTable C n (beta n) operator charts) depth (herror.trans hs)
  rw [activity_X] at hb
  have hx : (0 : ℝ) < n := by exact_mod_cast (by omega : 0<n)
  have hx1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1≤n)
  have ha := activationConstant_pos C hC
  have he0 : 0 ≤ independentPositiveInputConstant C := by unfold independentPositiveInputConstant; positivity
  have hpower := Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num : (5/2:ℝ)≤43/4)
  have herr : independentPositiveInputConstant C/(n : ℝ)^(43/4 : ℝ) ≤
      independentPositiveInputConstant C/(n : ℝ)^(5/2 : ℝ) :=
    div_le_div_of_nonneg_left he0 (Real.rpow_pos_of_pos hx _) hpower
  apply hb.trans
  have h1 := mul_le_mul_of_nonneg_left hhigh (by norm_num : (0:ℝ)≤2)
  have h2 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (herror.trans herr)
    (by norm_num : (0:ℝ)≤2)) (hw (independentOriginalJointSeed kernel))
  exact (add_le_add h1 h2).trans_eq (by dsimp [weight,independentJointUpperConstant]; ring)

theorem independentJointUpper_canonical_eventually (C : ℝ) (hC : 1 ≤ C) (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ n in atTop, (Parameters.legs n : ℝ)/(2*Parameters.dimension n) ≤ beta n ∧
      beta n ≤ 2*(Parameters.legs n : ℝ)/Parameters.dimension n) :
    ∀ᶠ n in atTop,
    ∀ operator : (Fin (Parameters.modulus n) → ℝ) ≃ₗ[ℝ] (Fin (Parameters.modulus n) → ℝ),
    operator.toLinearMap=actualResponse C n →
    ∀ charts : (mark : Fin (Parameters.modulus n)) → PublicChartFamily C n mark,
    ∀ kernel : Fin (Parameters.modulus n) → (Primary ⊕ Body → Fin (Parameters.modulus n)) → ℝ,
    Hoeffding.Canonical (Sum.elim (fun _ : Unit => actualPrimaryLaw C n (beta n))
      (Sum.elim (fun _ : Primary => actualPrimaryLaw C n (beta n)) (fun _ : Body => actualBodyLaw C n (beta n))))
      Finset.univ (MixedKernel.singletonJoin kernel) → ∀ depth : ℕ,
    InputTableCanonical (actualPrimaryLaw C n (beta n)) (actualBodyLaw C n (beta n))
      (independentJointUpper C n (beta n) operator charts kernel depth) := by
  filter_upwards [independentJointHigherTable_canonical_eventually (Primary := Primary) (Body := Body) C hC beta hbeta,
    actual_primary_probability_eventually C hC beta hbeta,actual_reference_laws_eventually C hC beta hbeta,
    actualResponse_inverse_mass_eventually C hC] with n hh hp hl hm operator hop charts kernel hkernel depth
  have hp0 (color) : 0 < (actualPrimaryLaw C n (beta n)).weight color := by rw [hl.1]; exact hp.1 color
  have horiginal := InputTableCanonical.X (independentOriginalJointSeed kernel)
    (groupedFiniteSeed_canonical _ _ _ hkernel)
  have hhigh := hh operator hop charts kernel hkernel
  have herror := referenceCoefficientTable_inverse_canonical (actualPrimaryLaw C n (beta n))
    (actualBodyLaw C n (beta n)) (actualReferenceLaw C n (beta n)) (v7Activation C n)
    operator hp0 (hm operator hop) (independentPairedPositiveMass C n (beta n) charts)
  exact ((horiginal.add hhigh).mul (herror.finiteCorrection depth)).sub horiginal

end
end AFT.V7Calibration
