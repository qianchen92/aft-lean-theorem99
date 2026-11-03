import AFT.ActualPairEnergy
import AFT.AttachedBodyDifference
import AFT.FirstCoefficient

/-! # The genuine physical triple at a fixed root coordinate and common queue -/

namespace AFT.V7Calibration

open Filter GaussianSource
open scoped BigOperators Classical Topology

noncomputable section

local instance (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _

/-- The literal conditional triple mass before averaging the constrained
root word. The inactive endpoints and body retain their common source. -/
def actualFixedRootTriple (cutoffScale : ℝ) (parameter : ℕ) (beta : ℝ) (root queue : ℤ)
    (first second attached : Fin (Parameters.modulus parameter)) : ℝ :=
  (1 - v7Activation cutoffScale parameter) *
    (∑ source, (inactiveLegSource cutoffScale parameter).weight source *
      inactivePairAtSource cutoffScale parameter source first second *
      integerShiftProfile parameter (actualBodyCenter cutoffScale parameter beta) (root + source + queue) attached) +
    v7Activation cutoffScale parameter * actualMarkedPair cutoffScale parameter beta first second *
      integerShiftProfile parameter (actualBodyCenter cutoffScale parameter beta) (root + queue) attached

/-- The root-marginal triple used by the finite logarithm is exactly the
marginal of the physical triple used by the complete conditional tail. -/
theorem actualFixedRootTriple_root_average (cutoffScale : ℝ) (parameter : ℕ) (beta : ℝ) (queue : ℤ)
    (first second attached : Fin (Parameters.modulus parameter)) :
    (∑ root : Window (v7RootCutoff parameter),
      (rootMarginal (v7RootWidth parameter) (v7RootCutoff parameter) (Parameters.bodies parameter)
        (Parameters.bodies_positive parameter)).weight root *
        actualFixedRootTriple cutoffScale parameter beta root queue first second attached) =
      actualLocalTriple cutoffScale parameter beta queue first second attached := by
  unfold actualFixedRootTriple actualLocalTriple attachedBodyAtSource
  simp only [mul_add, Finset.sum_add_distrib, add_zero, Finset.mul_sum]
  apply congrArg₂ (· + ·)
  · rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro source _
    apply Finset.sum_congr rfl
    intro root _
    ring
  · apply Finset.sum_congr rfl
    intro root _
    ring

def actualInactivePairLaw (cutoffScale : ℝ) (parameter : ℕ)
    (source : Window (legCutoff cutoffScale parameter - 1)) :
    FiniteDist (Fin (Parameters.modulus parameter) × Fin (Parameters.modulus parameter)) :=
  probabilityOr (fun point : Fin (Parameters.modulus parameter) × Fin (Parameters.modulus parameter) => inactivePairAtSource cutoffScale parameter source point.1 point.2)
    ((actualCoreLaw parameter).prod (actualCoreLaw parameter))

def actualCompanionLawOr (cutoffScale : ℝ) (parameter : ℕ) (first : Fin (Parameters.modulus parameter)) :
    FiniteDist (Fin (Parameters.modulus parameter)) :=
  probabilityOr (fun second => blurredAnchorKernel (Parameters.modulus parameter) (Parameters.anchorWidth parameter)
    (bodyShift cutoffScale parameter) (bodyBlur cutoffScale parameter) first second.val) (actualCoreLaw parameter)

def actualShiftedBodyLaw (cutoffScale : ℝ) (parameter : ℕ) (beta : ℝ) (shift : ℤ) :
    FiniteDist (Fin (Parameters.modulus parameter)) :=
  probabilityOr (integerShiftProfile parameter (actualBodyCenter cutoffScale parameter beta) shift) (actualCoreLaw parameter)

def actualActivatedSource (cutoffScale : ℝ) (parameter : ℕ) :
    FiniteDist (Unit ⊕ Window (legCutoff cutoffScale parameter - 1)) :=
  BlockDensity.activatedSource (windowGaussian (10 * parameter) (legCutoff cutoffScale parameter - 1))
    (windowZero (legCutoff cutoffScale parameter - 1)) (v7Activation cutoffScale parameter)
    (by unfold v7Activation GaussianSource.activation; exact mul_nonneg (by positivity) (FiniteDist.nonneg _ _))
    (activation_le_second_atom _ _ _ _)

def actualPairBranch (cutoffScale : ℝ) (parameter : ℕ) (beta : ℝ) :
    Unit ⊕ Window (legCutoff cutoffScale parameter - 1) →
      FiniteDist (Fin (Parameters.modulus parameter) × Fin (Parameters.modulus parameter)) :=
  Sum.elim (fun _ => BlockDensity.markedPairLaw (actualPrimaryLaw cutoffScale parameter beta)
    (actualCompanionLawOr cutoffScale parameter)) (actualInactivePairLaw cutoffScale parameter)

def actualSourceShift (cutoffScale : ℝ) (parameter : ℕ)
    (sample : Unit ⊕ Window (legCutoff cutoffScale parameter - 1)) : ℤ :=
  match sample with
  | .inl _ => 0
  | .inr source => source

def actualBodyBranch (cutoffScale : ℝ) (parameter : ℕ) (beta : ℝ) (root queue : ℤ) :
    Unit ⊕ Window (legCutoff cutoffScale parameter - 1) →
      Fin (Parameters.modulus parameter) → Fin (Parameters.modulus parameter) → FiniteDist (Fin (Parameters.modulus parameter)) :=
  fun sample _ _ => actualShiftedBodyLaw cutoffScale parameter beta
    (root + actualSourceShift cutoffScale parameter sample + queue)

/-- A genuine probability sampler on its three physical outputs for every
parameter; the fallbacks disappear on the proven legal V7 range. -/
def actualFixedRootTripleLaw (cutoffScale : ℝ) (parameter : ℕ) (beta : ℝ) (root queue : ℤ) :
    FiniteDist (Fin 3 → Fin (Parameters.modulus parameter)) :=
  PhysicalBlockTensors.sharedSourceTriple (actualActivatedSource cutoffScale parameter)
    (actualPairBranch cutoffScale parameter beta) (actualBodyBranch cutoffScale parameter beta root queue)

theorem actualActivatedSource_weights (cutoffScale : ℝ) (parameter : ℕ) :
    (∀ point : Unit, (actualActivatedSource cutoffScale parameter).weight (.inl point) = v7Activation cutoffScale parameter) ∧
    (∀ source, (actualActivatedSource cutoffScale parameter).weight (.inr source) =
      (1 - v7Activation cutoffScale parameter) * (inactiveLegSource cutoffScale parameter).weight source) := by
  refine ⟨fun _ => rfl, ?_⟩
  intro source
  have hh := inactiveLegSource_mixture cutoffScale parameter source
  simp only [actualActivatedSource, BlockDensity.activatedSource, Sum.elim_inr, BlockDensity.unmarkedSourceWeight]
  by_cases hs : source = windowZero (legCutoff cutoffScale parameter - 1)
  · simp only [if_pos hs] at hh ⊢
    linarith
  · simp only [if_neg hs] at hh ⊢
    linarith

theorem actual_pair_branch_weights_eventually (cutoffScale : ℝ) (hscale : 1 ≤ cutoffScale) (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ parameter in atTop,
      (Parameters.legs parameter : ℝ) / (2 * Parameters.dimension parameter) ≤ beta parameter ∧
      beta parameter ≤ 2 * (Parameters.legs parameter : ℝ) / Parameters.dimension parameter) :
    ∀ᶠ parameter in atTop,
      (∀ source first second, (actualPairBranch cutoffScale parameter (beta parameter) (.inr source)).weight (first, second) =
        inactivePairAtSource cutoffScale parameter source first second) ∧
      (∀ point : Unit, ∀ first second, (actualPairBranch cutoffScale parameter (beta parameter) (.inl point)).weight (first, second) =
        actualMarkedPair cutoffScale parameter (beta parameter) first second) := by
  filter_upwards [actual_inactive_pair_bounds_eventually cutoffScale hscale,
    actual_full_anchor_safe_eventually cutoffScale hscale,
    actual_reference_laws_eventually cutoffScale hscale beta hbeta] with parameter hi hc hp
  refine ⟨?_, ?_⟩
  · intro source first second
    have hmass : (∑ point : Fin (Parameters.modulus parameter) × Fin (Parameters.modulus parameter),
        inactivePairAtSource cutoffScale parameter source point.1 point.2) = 1 := by
      calc
        _ = ∑ first, ∑ second, inactivePairAtSource cutoffScale parameter source first second :=
          Fintype.sum_prod_type _
        _ = 1 := (hi source).2.1
    have hw := probabilityOr_weight
      (fun point : Fin (Parameters.modulus parameter) × Fin (Parameters.modulus parameter) => inactivePairAtSource cutoffScale parameter source point.1 point.2)
      ((actualCoreLaw parameter).prod (actualCoreLaw parameter))
      ⟨fun point => (hi source).1 point.1 point.2, hmass⟩
    exact congrFun hw (first, second)
  · intro point first second
    have hw := probabilityOr_weight
      (fun second : Fin (Parameters.modulus parameter) => blurredAnchorKernel (Parameters.modulus parameter) (Parameters.anchorWidth parameter)
        (bodyShift cutoffScale parameter) (bodyBlur cutoffScale parameter) first second.val) (actualCoreLaw parameter)
      ⟨fun _ => blurredAnchorKernel_nonneg _ _ _ _ _ _, (hc first).1⟩
    change (actualPrimaryLaw cutoffScale parameter (beta parameter)).weight first *
      (actualCompanionLawOr cutoffScale parameter first).weight second = _
    rw [hp.1]
    exact congrArg (fun value => actualPrimary cutoffScale parameter (beta parameter) first * value) (congrFun hw second)

theorem actual_pair_branch_mixture_eventually (cutoffScale : ℝ) (hscale : 1 ≤ cutoffScale) (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ parameter in atTop,
      (Parameters.legs parameter : ℝ) / (2 * Parameters.dimension parameter) ≤ beta parameter ∧
      beta parameter ≤ 2 * (Parameters.legs parameter : ℝ) / Parameters.dimension parameter) :
    ∀ᶠ parameter in atTop, ∀ first second,
      ((actualActivatedSource cutoffScale parameter).mix (actualPairBranch cutoffScale parameter (beta parameter))).weight (first, second) =
        localPairMixture cutoffScale parameter (beta parameter) first second := by
  filter_upwards [actual_pair_branch_weights_eventually cutoffScale hscale beta hbeta] with parameter hp first second
  simp only [FiniteDist.mix_weight, Fintype.sum_sum_type, (actualActivatedSource_weights cutoffScale parameter).1,
    (actualActivatedSource_weights cutoffScale parameter).2, hp.1, hp.2, Fintype.sum_unique]
  simp only [localPairMixture, averagedInactivePair, Finset.mul_sum, mul_assoc]
  ring

theorem actual_shifted_body_law_eventually (cutoffScale : ℝ) (hscale : 1 ≤ cutoffScale) (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ parameter in atTop,
      (Parameters.legs parameter : ℝ) / (2 * Parameters.dimension parameter) ≤ beta parameter ∧
      beta parameter ≤ 2 * (Parameters.legs parameter : ℝ) / Parameters.dimension parameter) :
    ∀ᶠ parameter in atTop, ∀ shift : ℤ, |shift| ≤ (maxBodyShift cutoffScale parameter : ℤ) →
      (actualShiftedBodyLaw cutoffScale parameter (beta parameter) shift).weight =
        integerShiftProfile parameter (actualBodyCenter cutoffScale parameter (beta parameter)) shift ∧
      (∀ output, (actualShiftedBodyLaw cutoffScale parameter (beta parameter) shift).weight output ≤
        4 / (Parameters.modulus parameter : ℝ)) := by
  filter_upwards [actual_body_center_probability_eventually cutoffScale hscale beta hbeta,
    body_support_scales_eventually cutoffScale hscale] with parameter hb hs shift hshift
  have hn (color) : 0 ≤ actualBodyCenter cutoffScale parameter (beta parameter) color :=
    (div_nonneg ((actualCoreLaw parameter).nonneg color) (by norm_num)).trans (hb.2.1 color).1
  have hw := probabilityOr_weight
    (integerShiftProfile parameter (actualBodyCenter cutoffScale parameter (beta parameter)) shift) (actualCoreLaw parameter)
    ⟨integerShiftProfile_nonneg _ _ hn shift, by
      rw [integerShiftProfile_mass parameter _ hb.2.2 shift (hshift.trans (by exact_mod_cast hs.1)), hb.1]⟩
  refine ⟨hw, ?_⟩
  intro output
  change (probabilityOr _ _).weight output ≤ _
  rw [hw]
  apply integerShiftProfile_bound parameter _ _ (by positivity) _ shift output
  intro color
  have hh := mul_le_mul_of_nonneg_left ((actualCoreLaw_bounds parameter).1 color) (by norm_num : (0 : ℝ) ≤ 2)
  exact (hb.2.1 color).2.trans (hh.trans_eq (by ring))

theorem actualBodyBranch_shift_bound (cutoffScale : ℝ) (parameter : ℕ) (root queue : ℤ)
    (hroot : |root| ≤ (v7RootCutoff parameter : ℤ)) (hqueue : |queue| ≤ (queueCutoff parameter : ℤ))
    (sample : Unit ⊕ Window (legCutoff cutoffScale parameter - 1)) :
    |root + actualSourceShift cutoffScale parameter sample + queue| ≤
      (maxBodyShift cutoffScale parameter : ℤ) := by
  have hs : |actualSourceShift cutoffScale parameter sample| ≤
      ((legCutoff cutoffScale parameter - 1 : ℕ) : ℤ) := by
    cases sample with
    | inl point => change (0 : ℤ) ≤ _; positivity
    | inr source => exact abs_le.mpr (Finset.mem_Icc.mp source.property)
  have hh := (abs_add_le (root + actualSourceShift cutoffScale parameter sample) queue).trans
    (add_le_add ((abs_add_le _ _).trans (add_le_add hroot hs)) hqueue)
  simpa only [maxBodyShift, Nat.cast_add] using hh

theorem actual_fixed_root_triple_weights_eventually (cutoffScale : ℝ) (hscale : 1 ≤ cutoffScale) (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ parameter in atTop,
      (Parameters.legs parameter : ℝ) / (2 * Parameters.dimension parameter) ≤ beta parameter ∧
      beta parameter ≤ 2 * (Parameters.legs parameter : ℝ) / Parameters.dimension parameter) :
    ∀ᶠ parameter in atTop, ∀ root queue : ℤ,
      |root| ≤ (v7RootCutoff parameter : ℤ) → |queue| ≤ (queueCutoff parameter : ℤ) →
      (actualFixedRootTripleLaw cutoffScale parameter (beta parameter) root queue).weight =
        PhysicalBlockTensors.tripleMass (actualFixedRootTriple cutoffScale parameter (beta parameter) root queue) := by
  filter_upwards [actual_pair_branch_weights_eventually cutoffScale hscale beta hbeta,
    actual_shifted_body_law_eventually cutoffScale hscale beta hbeta] with parameter hp hb root queue hr hq
  funext word
  rw [actualFixedRootTripleLaw, PhysicalBlockTensors.sharedSourceTriple_weight]
  unfold PhysicalBlockTensors.tripleMass BlockDensity.attachedMass
  have hbody (sample) (first second attached : Fin (Parameters.modulus parameter)) :
      (actualBodyBranch cutoffScale parameter (beta parameter) root queue sample first second).weight attached =
        integerShiftProfile parameter (actualBodyCenter cutoffScale parameter (beta parameter))
          (root + actualSourceShift cutoffScale parameter sample + queue) attached :=
    congrFun (hb _ (actualBodyBranch_shift_bound cutoffScale parameter root queue hr hq sample)).1 attached
  simp only [Fintype.sum_sum_type, hbody, (actualActivatedSource_weights cutoffScale parameter).1,
    (actualActivatedSource_weights cutoffScale parameter).2, hp.1, hp.2, Fintype.sum_unique,
    actualSourceShift, add_zero, actualFixedRootTriple, Finset.mul_sum, mul_assoc]
  ring

/-- The complete genuine fixed-root local triple has every degree bounded
by the proved V7 pair energy, uniformly over the common queue. -/
theorem actual_fixed_root_triple_degree_power_eventually (cutoffScale : ℝ) (hscale : 1 ≤ cutoffScale) (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ parameter in atTop,
      (Parameters.legs parameter : ℝ) / (2 * Parameters.dimension parameter) ≤ beta parameter ∧
      beta parameter ≤ 2 * (Parameters.legs parameter : ℝ) / Parameters.dimension parameter) :
    ∀ᶠ parameter in atTop, ∀ root queue : ℤ,
      |root| ≤ (v7RootCutoff parameter : ℤ) → |queue| ≤ (queueCutoff parameter : ℤ) → ∀ degree : ℕ,
      BlockFock.tensorEnergy (LocalTensors.degreeTensor
        (fun _ : Fin 3 => actualReferenceLaw cutoffScale parameter (beta parameter))
        (actualFixedRootTripleLaw cutoffScale parameter (beta parameter) root queue).weight degree) ≤
          1576960 * (parameter : ℝ) ^ 30 := by
  filter_upwards [actual_pair_branch_mixture_eventually cutoffScale hscale beta hbeta,
    actual_shifted_body_law_eventually cutoffScale hscale beta hbeta,
    actual_pair_energy_power_eventually cutoffScale hscale beta hbeta,
    actual_reference_laws_eventually cutoffScale hscale beta hbeta,
    actual_reference_lower_eventually cutoffScale hscale beta hbeta] with parameter hp hb he hl hr root queue hroot hqueue degree
  have hq : (0 : ℝ) < Parameters.modulus parameter := by exact_mod_cast (Parameters.modulus_prime parameter).pos
  have hreference (color) : 1 / (2 * (Parameters.modulus parameter : ℝ)) ≤
      (actualReferenceLaw cutoffScale parameter (beta parameter)).weight color := by rw [hl.2.2]; exact hr color
  have hbody (sample first second attached) :
      (actualBodyBranch cutoffScale parameter (beta parameter) root queue sample first second).weight attached ≤
        4 / (Parameters.modulus parameter : ℝ) :=
    (hb _ (actualBodyBranch_shift_bound cutoffScale parameter root queue hroot hqueue sample)).2 attached
  have hh := PhysicalBlockTensors.shared_source_degree_energy_le
    (actualActivatedSource cutoffScale parameter) (actualPairBranch cutoffScale parameter (beta parameter))
    (actualBodyBranch cutoffScale parameter (beta parameter) root queue)
    (actualReferenceLaw cutoffScale parameter (beta parameter))
    (1 / (2 * (Parameters.modulus parameter : ℝ))) (4 / (Parameters.modulus parameter : ℝ))
    (by positivity) (by positivity) hreference hbody degree
  have hratio : 8 * ((4 / (Parameters.modulus parameter : ℝ)) / (1 / (2 * (Parameters.modulus parameter : ℝ)))) = 64 := by field_simp; ring
  simp only [hp, hl.2.2, hratio] at hh
  calc
    _ ≤ 64 * BlockDensity.pairEnergy (actualReferenceMean cutoffScale parameter (beta parameter))
      (actualReferenceMean cutoffScale parameter (beta parameter)) (localPairMixture cutoffScale parameter (beta parameter)) := hh
    _ ≤ 64 * (24640 * (parameter : ℝ) ^ 30) := mul_le_mul_of_nonneg_left he (by norm_num)
    _ = _ := by ring

end

end AFT.V7Calibration
