import AFT.IndependentPublicBody
import AFT.IndependentPhysicalForms
import AFT.CanonicalPolynomialConstants

/-! # The exact public independent response as canonical joint channels -/
namespace AFT.V7Calibration
open GaussianSource BoundaryCalibration RepresentedPolynomial Filter
open scoped BigOperators Classical Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
local instance independentPublicFormsFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _
local instance independentPublicFormsSumDecEq {α β : Type*} : DecidableEq (α ⊕ β) := Classical.decEq _
local instance independentPublicFormsSubtypeDecEq {α : Type*} {p : α → Prop} : DecidableEq (Subtype p) := Classical.decEq _
attribute [local instance] actualModulusNeZero

def publicRoleReference (C : ℝ) (n : ℕ) (beta : ℝ) {count : ℕ} (role : Fin count → Bool) :
    Fin count → FiniteDist (Fin (Parameters.modulus n)) :=
  fun slot => if role slot=true then actualPrimaryLaw C n beta else actualBodyLaw C n beta

def publicIndependentForms (C : ℝ) (n : ℕ) (beta : ℝ)
    (charts : (mark : Fin (Parameters.modulus n)) → PublicChartFamily C n mark)
    {count : ℕ} (role : Fin count → Bool) : Fin count → Fin (Parameters.modulus n) → Table (Fin (Parameters.modulus n)) :=
  fun slot => if role slot=true then independentPairedForm C n beta charts else channelForm (actualBodyChannel n)

def publicBodyConstant (C : ℝ) (n : ℕ) (beta : ℝ) {count : ℕ} (role : Fin count → Bool) :
    Fin count → Table (Fin (Parameters.modulus n)) :=
  fun slot => if role slot=true then 0 else 1-profileForm (actualReferenceLaw C n beta).weight

theorem independentPairedForm_weighted (C : ℝ) (n : ℕ) (beta : ℝ)
    (charts : (mark : Fin (Parameters.modulus n)) → PublicChartFamily C n mark)
    (input : Fin (Parameters.modulus n)) :
    centeredGeneratingLinear (actualReferenceLaw C n beta).weight
      (independentPairedNumerator C n beta charts (fun color =>
        (actualPrimaryLaw C n beta).weight color*(Pi.single input 1 : Fin (Parameters.modulus n) → ℝ) color))=
      MvPolynomial.C ((actualPrimaryLaw C n beta).weight input)*independentPairedForm C n beta charts input := by
  rw [← independentPairedPolynomialLinear_apply]
  have he : (fun color => (actualPrimaryLaw C n beta).weight color*(Pi.single input 1 : Fin (Parameters.modulus n) → ℝ) color)=
      (actualPrimaryLaw C n beta).weight input • (Pi.single input 1 : Fin (Parameters.modulus n) → ℝ) := by
    funext color
    by_cases h : color=input <;> simp [Pi.single_apply,h]
  rw [he,map_smul]
  simp only [Algebra.smul_def,MvPolynomial.algebraMap_eq,independentPairedForm]

theorem actualLeadingOutput_body_pointMass (C : ℝ) (n : ℕ) (beta : ℝ) (input : Fin (Parameters.modulus n)) :
    actualLeadingOutput C n beta (MvPolynomial.X (bodySingletonInput (Pi.single input 1)))=
      MvPolynomial.C ((actualBodyLaw C n beta).weight input)*channelForm (actualBodyChannel n) input := by
  rw [actualLeadingOutput,outputHom_X,body_singleton_seedOutput]
  simp only [Pi.single_apply]
  simp only [mul_ite,mul_one,mul_zero,ite_mul,zero_mul,Finset.sum_ite_eq',Finset.mem_univ,if_true]
  simp only [channelForm,Finset.mul_sum,← mul_assoc,← map_mul]

theorem publicBodyRootPolynomial_average_eventually (C : ℝ) (hC : 1 ≤ C) (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ n in atTop,(Parameters.legs n : ℝ)/(2*Parameters.dimension n) ≤ beta n ∧
      beta n ≤ 2*(Parameters.legs n : ℝ)/Parameters.dimension n) :
    ∀ᶠ n in atTop,∀ input : Fin (Parameters.modulus n),
      (∑ root : Window (v7RootCutoff n),MvPolynomial.C ((bodyRootReference n).weight root)*
        publicBodyRootPolynomial C n (beta n) input root)=
      MvPolynomial.C ((actualBodyLaw C n (beta n)).weight input)*
        (channelForm (actualBodyChannel n) input+1-profileForm (actualReferenceLaw C n (beta n)).weight) := by
  filter_upwards [independent_body_generating_formula_eventually C hC beta hbeta] with n hi input
  have hh := hi (Pi.single input 1)
  rw [actualLeadingOutput_body_pointMass] at hh
  have he : (actualBodyLaw C n (beta n)).expectation (Pi.single input 1)=(actualBodyLaw C n (beta n)).weight input := by
    simp [FiniteDist.expectation,Pi.single_apply]
  rw [he] at hh
  exact hh.trans (by ring)

theorem publicInputIndependentPolynomial_forms_eventually (C : ℝ) (hC : 1 ≤ C) (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ n in atTop,(Parameters.legs n : ℝ)/(2*Parameters.dimension n) ≤ beta n ∧
      beta n ≤ 2*(Parameters.legs n : ℝ)/Parameters.dimension n) :
    ∀ᶠ n in atTop,∀ charts : (mark : Fin (Parameters.modulus n)) → PublicChartFamily C n mark,
    ∀ count : ℕ,∀ role : Fin count → Bool,∀ input : Fin count → Fin (Parameters.modulus n),
    publicInputIndependentPolynomial C n (beta n) charts role input=
      MvPolynomial.C (∏ slot,(publicRoleReference C n (beta n) role slot).weight (input slot))*
        ∏ slot,(publicIndependentForms C n (beta n) charts role slot (input slot)+publicBodyConstant C n (beta n) role slot) := by
  filter_upwards [publicBodyRootPolynomial_average_eventually C hC beta hbeta] with n hb charts count role input
  unfold publicInputIndependentPolynomial
  simp_rw [independentPairedForm_weighted,hb]
  rw [map_prod,← Finset.prod_mul_distrib,← (rolePartition role).prod_comp,Fintype.prod_sum_type]
  apply congrArg₂ (· * ·)
  · apply Finset.prod_congr (by ext; simp)
    intro index _
    simp only [rolePartition,Equiv.sumCompl_apply_inl,publicRoleReference,publicIndependentForms,publicBodyConstant,index.property,if_true,add_zero]
  · apply Finset.prod_congr (by ext; simp)
    intro index _
    simp [rolePartition,publicRoleReference,publicIndependentForms,publicBodyConstant,index.property,add_sub_assoc]

/-- The common body constant cancels against each old body variable of the
joint canonical kernel, even when every other channel is nonlinear. -/
theorem publicIndependent_joint_canonical_eventually (C : ℝ) (hC : 1 ≤ C) (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ n in atTop,(Parameters.legs n : ℝ)/(2*Parameters.dimension n) ≤ beta n ∧
      beta n ≤ 2*(Parameters.legs n : ℝ)/Parameters.dimension n) :
    ∀ᶠ n in atTop,∀ charts : (mark : Fin (Parameters.modulus n)) → PublicChartFamily C n mark,
    ∀ count : ℕ,∀ role : Fin count → Bool,∀ kernel : (Fin count → Fin (Parameters.modulus n)) → ℝ,
    Hoeffding.Canonical (publicRoleReference C n (beta n) role) Finset.univ kernel →
    (∑ input,MvPolynomial.C (kernel input)*publicInputIndependentPolynomial C n (beta n) charts role input)=
      jointChannelPolynomial (publicRoleReference C n (beta n) role)
        (publicIndependentForms C n (beta n) charts role) kernel := by
  filter_upwards [publicInputIndependentPolynomial_forms_eventually C hC beta hbeta]
    with n hi charts count role kernel hc
  simp_rw [hi charts count role,← mul_assoc,← map_mul]
  exact jointChannelPolynomial_add_constants _ _ _ kernel (fun slot => hc.2 slot (Finset.mem_univ slot))

end
end AFT.V7Calibration
