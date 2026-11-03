import AFT.JointSeedOutput
import AFT.V7BodyPairActivity
import AFT.MarkedActivity

/-! # Actual joint root convolution of literal body and mixed pair inputs -/

namespace AFT.FiniteDist

open scoped BigOperators Classical
noncomputable section
variable {A B C D : Type*} [Fintype A] [Fintype B] [Fintype C] [Fintype D]

theorem prod_map_functions (first : FiniteDist A) (second : FiniteDist B) (f : A → C) (g : B → D) :
    (first.prod second).map (fun pair => (f pair.1, g pair.2)) = (first.map f).prod (second.map g) := by
  apply FiniteDist.ext
  rintro ⟨c, d⟩
  simp only [map_weight, prod_weight, Fintype.sum_prod_type, Prod.mk.injEq,
    Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  split_ifs <;> simp_all

end
end AFT.FiniteDist

namespace AFT.SafeConvolution

open scoped BigOperators Classical
noncomputable section
variable {G : Type*} [Fintype G] [AddCommGroup G]

theorem convolution_pair_inputs (first second : FiniteDist G) (mass : G × G → ℝ) (output : G × G) :
    convolution (first.prod second).weight mass output =
      ∑ a, ∑ b, mass (a, b) * first.weight (output.1 - a) * second.weight (output.2 - b) := by
  rw [convolution_apply, ← (Equiv.subLeft output).sum_comp]
  simp only [Equiv.subLeft_apply, sub_sub_cancel, Fintype.sum_prod_type, FiniteDist.prod_weight,
    Prod.fst_sub, Prod.snd_sub]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

end
end AFT.SafeConvolution

namespace AFT.RepresentedPolynomial

open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {Color : Type*} [Fintype Color]
local instance jointPairFinDecEq (n : ℕ) : DecidableEq (Fin n) := instDecidableEqFin n

theorem body_pair_seedOutputMass (primary body : FiniteDist Color)
    (primaryChannel bodyChannel : Color → Color → ℝ) (kernel : Color → Color → ℝ)
    (output : Fin 2 → Color) :
    seedOutputMass primary body primaryChannel bodyChannel
      ⟨0, 2, fun word => kernel (word 0) (word 1)⟩ output =
      ∑ first, ∑ second, (body.weight first * body.weight second * kernel first second) *
        bodyChannel first (output 0) * bodyChannel second (output 1) := by
  unfold seedOutputMass
  calc
    _ = ∑ word : Fin 2 → Color,
      (kernel (word 0) (word 1) * (body.weight (word 0) * body.weight (word 1))) *
        (bodyChannel (word 0) (output 0) * bodyChannel (word 1) (output 1)) := by
      apply Finset.sum_congr (by ext; simp)
      intro word _
      change (kernel (word 0) (word 1) *
        (∏ slot : Fin 2, (inputReference primary body ⟨0, 2, fun w => kernel (w 0) (w 1)⟩ slot).weight (word slot))) *
        (∏ slot : Fin 2, seedChannel primaryChannel bodyChannel ⟨0, 2, fun w => kernel (w 0) (w 1)⟩ slot (word slot) (output slot)) = _
      simp only [Fin.prod_univ_two]
      rfl
    _ = _ := by
      rw [← (finTwoArrowEquiv Color).symm.sum_comp, Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro first _
      apply Finset.sum_congr rfl
      intro second _
      change (kernel first second * (body.weight first * body.weight second)) *
        (bodyChannel first (output 0) * bodyChannel second (output 1)) = _
      ring
end
end AFT.RepresentedPolynomial

namespace AFT.GaussianSource

noncomputable section

theorem actualRootPair_eq_prod (parameter : ℕ) :
    actualRootPair parameter = (actualRootLaw parameter).prod (actualRootLaw parameter) := by
  unfold actualRootPair independentRootPair actualRootLaw
  exact FiniteDist.prod_map_functions
    (rootMarginal (v7RootWidth parameter) (v7RootCutoff parameter) (Parameters.bodies parameter)
      (Parameters.bodies_positive parameter))
    (rootMarginal (v7RootWidth parameter) (v7RootCutoff parameter) (Parameters.bodies parameter)
      (Parameters.bodies_positive parameter))
    (fun sample : Window (v7RootCutoff parameter) => paletteEmbedding parameter (sample : ℤ))
    (fun sample : Window (v7RootCutoff parameter) => paletteEmbedding parameter (sample : ℤ))

end
end AFT.GaussianSource

namespace AFT.V7Calibration

open GaussianSource SafeConvolution RepresentedPolynomial Filter
open scoped BigOperators Classical Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] actualModulusNeZero

theorem actual_inactive_body_pair_outputMass_eventually (C : ℝ) (hC : 1 ≤ C) (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ n in atTop,
      (Parameters.legs n : ℝ) / (2 * Parameters.dimension n) ≤ beta n ∧
      beta n ≤ 2 * (Parameters.legs n : ℝ) / Parameters.dimension n) :
    ∀ᶠ n in atTop, ∀ output : Fin 2 → Fin (Parameters.modulus n),
      seedOutputMass (actualPrimaryLaw C n (beta n)) (actualBodyLaw C n (beta n))
        (actualPrimaryChannel C n) (actualBodyChannel n) (actualInactiveBodyPairInput C n (beta n)) output =
      convolution (actualRootPair n).weight (actualInactiveBodyPairMass C n) (output 0, output 1) := by
  filter_upwards [actual_inactive_body_pair_mass_eventually C hC beta hbeta] with n hm output
  change seedOutputMass _ _ _ _ ⟨0, 2, fun word => actualInactiveBodyPairDensity C n (beta n) (word 0) (word 1)⟩ output = _
  rw [body_pair_seedOutputMass, actualRootPair_eq_prod, convolution_pair_inputs]
  simp only [hm, actualBodyChannel]

theorem actualLeadingOutput_inactive_body_pair_eventually (C : ℝ) (hC : 1 ≤ C) (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ n in atTop,
      (Parameters.legs n : ℝ) / (2 * Parameters.dimension n) ≤ beta n ∧
      beta n ≤ 2 * (Parameters.legs n : ℝ) / Parameters.dimension n) :
    ∀ᶠ n in atTop,
      actualLeadingOutput C n (beta n) (MvPolynomial.X (actualInactiveBodyPairInput C n (beta n))) =
        ∑ output : Fin 2 → Fin (Parameters.modulus n),
          MvPolynomial.C (convolution (actualRootPair n).weight (actualInactiveBodyPairMass C n) (output 0, output 1)) *
            ∏ slot, MvPolynomial.X (output slot) := by
  filter_upwards [actual_inactive_body_pair_outputMass_eventually C hC beta hbeta] with n hm
  rw [actualLeadingOutput, outputHom_X, seedOutput_eq_mass]
  apply Finset.sum_congr rfl
  intro output _
  rw [hm]
  rfl

end
end AFT.V7Calibration
