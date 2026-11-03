import CurrentAFT.LegPolynomialEvaluation

/-!
# The complete actual independent-root background law and its physical image

The common queue is averaged after the complete product is formed. Each leg
uses its own actual scalar, shared between that leg's pair and attachment.
All generating factors are centered at the actual uniform palette law.
-/

namespace CurrentAFT.BackgroundPolynomialEvaluation

open AFT AFT.RepresentedPolynomial ControlCoordinates GradedControlAlgebra LeadingEvaluation
  DiffuseProfiles ProposalPrimary ActualControls BackgroundFamilies BackgroundEvaluation
  BackgroundAtomEvaluation BackgroundCertificates BackgroundTranslations BackgroundPopulationBounds
  LocalReferenceEnergy PairQuadraticEvaluation LegPolynomialEvaluation BodyRootAverages
open scoped BigOperators Classical

noncomputable section

set_option maxHeartbeats 1400000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.legCount ProposalPrimary.primaryLaw ActualControls.bodyReference

local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _

def finiteGenerating {State Variable : Type*} [Fintype State]
    (law : FiniteDist State) (factor : State → MvPolynomial Variable ℝ) : MvPolynomial Variable ℝ :=
  ∑ state, MvPolynomial.C (law.weight state) * factor state

theorem finiteGenerating_mix {Choice State Variable : Type*} [Fintype Choice] [Fintype State]
    (choice : FiniteDist Choice) (laws : Choice → FiniteDist State)
    (factor : State → MvPolynomial Variable ℝ) :
    finiteGenerating (choice.mix laws) factor = ∑ index, choice.weight index • finiteGenerating (laws index) factor := by
  unfold finiteGenerating
  simp only [FiniteDist.mix_weight, map_sum, map_mul, Finset.sum_mul,
    MvPolynomial.smul_eq_C_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro index _
  apply Finset.sum_congr rfl
  intro state _
  ring

theorem finiteGenerating_prod {First Second Variable : Type*} [Fintype First] [Fintype Second]
    (first : FiniteDist First) (second : FiniteDist Second)
    (firstFactor : First → MvPolynomial Variable ℝ) (secondFactor : Second → MvPolynomial Variable ℝ) :
    finiteGenerating (first.prod second) (fun state => firstFactor state.1 * secondFactor state.2) =
      finiteGenerating first firstFactor * finiteGenerating second secondFactor := by
  unfold finiteGenerating
  simp only [Fintype.sum_prod_type, FiniteDist.prod_weight, map_mul, Finset.sum_mul, Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro left _
  apply Finset.sum_congr rfl
  intro right _
  ring

theorem finiteGenerating_independent {State Variable : Type*} [Fintype State]
    (law : FiniteDist State) (factor : State → MvPolynomial Variable ℝ) (count : ℕ) :
    finiteGenerating (FiniteDist.independent (fun _ : Fin count => law))
      (fun word => ∏ index, factor (word index)) = finiteGenerating law factor ^ count := by
  unfold finiteGenerating FiniteDist.independent
  simp only [map_prod, ← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun _ : Fin count => fun state : State => MvPolynomial.C (law.weight state) * factor state)]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

def queueLaw (security : ℕ) (shift : ℤ) : FiniteDist (ActualControls.Palette security) :=
  rootAverage security (shiftedSafeLaw security shift)

theorem queueLaw_weight (security : ℕ) (shift : ℤ) (output : ActualControls.Palette security) :
    (queueLaw security shift).weight output = rootConvolutionProfile security (shiftedSafeLaw security shift).weight output := by
  rw [queueLaw, rootAverage_seed]
  simp only [FiniteDist.mix_weight, FiniteDist.map_equiv_weight, rootConvolutionProfile]

def legLaw (security : ℕ) : FiniteDist ((ActualControls.Palette security × ActualControls.Palette security) × ActualControls.Palette security) :=
  (scalarLaw security).mix (fun scalar => (conditionalPairLaw security scalar).prod (attachmentLaw security scalar))

def legFactor (security : ℕ)
    (output : (ActualControls.Palette security × ActualControls.Palette security) × ActualControls.Palette security) :
    MvPolynomial (ActualControls.Palette security) ℝ :=
  centeredFactor (FringeCertificate.uniformProfile security) output.1.1 *
    centeredFactor (FringeCertificate.uniformProfile security) output.1.2 *
    centeredFactor (FringeCertificate.uniformProfile security) output.2

theorem legLaw_generating (security : ℕ) : finiteGenerating (legLaw security) (legFactor security) = legGenerating security := by
  rw [legLaw, finiteGenerating_mix]
  unfold legGenerating
  apply Finset.sum_congr rfl
  intro scalar _
  congr 1
  unfold finiteGenerating legFactor conditionalLegGenerating tripleGenerating
  simp only [Fintype.sum_prod_type, FiniteDist.prod_weight, map_mul]
  apply Finset.sum_congr rfl
  intro first _
  apply Finset.sum_congr rfl
  intro second _
  apply Finset.sum_congr rfl
  intro attached _
  ring

def fixedQueueGenerating (security : ℕ) (queue : ℤ) : MvPolynomial (ActualControls.Palette security) ℝ :=
  singleGenerating (FringeCertificate.uniformProfile security) (convolvedCenterLaw security).weight ^ freeCount security *
    singleGenerating (FringeCertificate.uniformProfile security) (queueLaw security queue).weight ^ Parameters.modulus security *
    legGenerating security ^ Parameters.legCount security

def backgroundGenerating (security : ℕ) : MvPolynomial (ActualControls.Palette security) ℝ :=
  ∑ scalar, (scalarLaw security).weight scalar • fixedQueueGenerating security scalar.val

theorem fixedQueueBackground_image (security order : ℕ) (horder : 2 ≤ order) (queue : ℤ) :
    evaluation security order (ActualBackground.fixedQueueBackground security order horder queue) =
      TruncatedOutput.quotientMap order (fixedQueueGenerating security queue) := by
  unfold ActualBackground.fixedQueueBackground fixedQueueGenerating
  simp only [map_mul, map_pow, map_add, map_one, freeCertificate_image,
    translationCertificate_image, completeLegAtom_image security order horder]
  rw [singleGenerating_mass_one _ _ (convolvedCenterLaw security).sum_one,
    singleGenerating_mass_one _ _ (queueLaw security queue).sum_one]
  have hqueue : (queueLaw security queue).weight = rootConvolutionProfile security (shiftedSafeLaw security queue).weight :=
    funext (queueLaw_weight security queue)
  rw [hqueue]
  simp only [map_add, map_one]

theorem background_image (security order : ℕ) (horder : 2 ≤ order) :
    evaluation security order (ActualBackground.background security order horder) =
      TruncatedOutput.quotientMap order (backgroundGenerating security) := by
  unfold ActualBackground.background backgroundGenerating
  simp only [map_sum, map_smul, fixedQueueBackground_image]

abbrev FreeColors (security : ℕ) := Fin (freeCount security) → ActualControls.Palette security
abbrev QueueColors (security : ℕ) := Fin (Parameters.modulus security) → ActualControls.Palette security
abbrev LegColors (security : ℕ) := Fin (Parameters.legCount security) →
  ((ActualControls.Palette security × ActualControls.Palette security) × ActualControls.Palette security)
abbrev BackgroundColors (security : ℕ) := FreeColors security × (QueueColors security × LegColors security)

/-- This is the complete finite probability experiment, including the actual
within-leg shared scalar and one common fixed queue for all queue vertices. -/
def fixedQueueLaw (security : ℕ) (queue : ℤ) : FiniteDist (BackgroundColors security) :=
  (FiniteDist.independent (fun _ : Fin (freeCount security) => convolvedCenterLaw security)).prod
    ((FiniteDist.independent (fun _ : Fin (Parameters.modulus security) => queueLaw security queue)).prod
      (FiniteDist.independent (fun _ : Fin (Parameters.legCount security) => legLaw security)))

def backgroundLaw (security : ℕ) : FiniteDist (BackgroundColors security) :=
  (scalarLaw security).mix (fun queue => fixedQueueLaw security queue.val)

/-- Every actual output endpoint has its own uniform-centered factor. -/
def endpointFactor (security : ℕ) (output : BackgroundColors security) : MvPolynomial (ActualControls.Palette security) ℝ :=
  (∏ index, centeredFactor (FringeCertificate.uniformProfile security) (output.1 index)) *
    ((∏ index, centeredFactor (FringeCertificate.uniformProfile security) (output.2.1 index)) *
      ∏ index, legFactor security (output.2.2 index))

theorem fixedQueueLaw_generating (security : ℕ) (queue : ℤ) :
    finiteGenerating (fixedQueueLaw security queue) (endpointFactor security) = fixedQueueGenerating security queue := by
  unfold fixedQueueLaw endpointFactor
  rw [finiteGenerating_prod _ _
    (fun output : FreeColors security => ∏ index, centeredFactor (FringeCertificate.uniformProfile security) (output index))
    (fun output : QueueColors security × LegColors security =>
      (∏ index, centeredFactor (FringeCertificate.uniformProfile security) (output.1 index)) *
        ∏ index, legFactor security (output.2 index))]
  rw [finiteGenerating_prod _ _
    (fun output : QueueColors security => ∏ index, centeredFactor (FringeCertificate.uniformProfile security) (output index))
    (fun output : LegColors security => ∏ index, legFactor security (output index))]
  rw [finiteGenerating_independent,
    finiteGenerating_independent, finiteGenerating_independent, legLaw_generating]
  unfold fixedQueueGenerating finiteGenerating singleGenerating
  ring

theorem backgroundLaw_generating (security : ℕ) :
    finiteGenerating (backgroundLaw security) (endpointFactor security) = backgroundGenerating security := by
  unfold backgroundLaw backgroundGenerating
  rw [finiteGenerating_mix]
  simp only [fixedQueueLaw_generating]

/-- The concrete background coefficient family evaluates to the exact
centered PGF of its actual full finite law, with no factor-independence
assumption on endpoints inside a leg or between the common queue slots. -/
theorem background_image_law (security order : ℕ) (horder : 2 ≤ order) :
    evaluation security order (ActualBackground.background security order horder) =
      TruncatedOutput.quotientMap order
        (finiteGenerating (backgroundLaw security) (endpointFactor security)) := by
  rw [backgroundLaw_generating]
  exact background_image security order horder

theorem inverse_physical_background (security order : ℕ) (horder : 2 ≤ order) :
    evaluation security order (ActualBackgroundInverse.inverse security order horder) *
      TruncatedOutput.quotientMap order
        (finiteGenerating (backgroundLaw security) (endpointFactor security)) = 1 := by
  rw [← background_image_law security order horder, ← map_mul,
    ActualBackgroundInverse.inverse_mul, map_one]

end

end CurrentAFT.BackgroundPolynomialEvaluation
