import CurrentAFT.LocalRaisingNorm
import CurrentAFT.OrdinaryRaising
import AFT.SignedFirstCoefficient

/-! # Exact first and higher parts of a general centered local signed mass -/
namespace CurrentAFT.CompleteFirstCoefficient

open AFT DiffuseProfiles ProposalPrimary ActualControls ControlCoordinates ControlProduct ControlNorm
  GradedControlAlgebra GradedControlNorm GradedControlStability LocalCoefficientFamily LocalCoefficientNorm
  NormalizedLocalPolynomial LocalRaisingFirst LocalRaisingNorm BackgroundFamilies LocalReferenceEnergy
open scoped BigOperators Classical
noncomputable section
local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
set_option maxHeartbeats 1400000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base primaryLaw
abbrev Palette (security : ℕ) := ActualControls.Palette security

def firstScore (security order : ℕ) (horder : 1 ≤ order) (mass : (Fin 4 → Palette security) → ℝ) : Palette security → ℝ :=
  primaryCoefficient (primaryLaw security) (bodyReference security) order horder (completeFamily security order mass)

theorem firstScore_centered (security order : ℕ) (horder : 1 ≤ order) (mass : (Fin 4 → Palette security) → ℝ) :
    (primaryLaw security).expectation (firstScore security order horder mass) = 0 := by
  let color : Palette security := ⟨0, (Parameters.modulus_spec security).2.pos⟩
  let kernel : canonicalKernels (primaryLaw security) (bodyReference security) 1 0 :=
    completeFamily security order mass (primaryArity order horder)
  have h := kernel.property.1 (0 : Fin 1) (fun _ => color) Fin.elim0
  have hupdate (input : Palette security) : Function.update (fun _ : Fin 1 => color) 0 input = (fun _ => input) := by
    funext index
    have hi := Fin.eq_zero index
    subst index
    exact Function.update_self _ _ _
  simp only [hupdate] at h
  exact h

def firstFamily (security order : ℕ) (horder : 1 ≤ order) (mass : (Fin 4 → Palette security) → ℝ) : Family security order :=
  primaryFamily (primaryLaw security) (bodyReference security) order horder (firstScore security order horder mass)
    (firstScore_centered security order horder mass)

theorem complete_sub_first_raises (security order : ℕ) (horder : 1 ≤ order)
    (mass : (Fin 4 → Palette security) → ℝ) (hmass : ∑ word, mass word = 0) :
    GradedInverse.VanishesBelow (primaryLaw security) (bodyReference security) order 2
      (completeFamily security order mass - firstFamily security order horder mass) := by
  intro arity hsmall
  change completeFamily security order mass arity - firstFamily security order horder mass arity = 0
  by_cases hb : 0 < arity.val.2.val
  · rw [completeFamily_no_body security order mass arity hb]
    unfold firstFamily primaryFamily
    rw [Pi.single_eq_of_ne, sub_zero]
    intro hequal
    have h := congrArg (fun item : TruncatedArity order => item.val.2.val) hequal
    change arity.val.2.val = 0 at h
    omega
  · have hs : arity.val.2.val = 0 := by omega
    by_cases hr : arity.val.1.val = 0
    · have harity : arity = zeroArity order := by
        apply Subtype.ext
        exact Prod.ext (Fin.ext hr) (Fin.ext hs)
      subst arity
      rw [completeFamily_zeroArity, hmass, zero_smul]
      unfold firstFamily primaryFamily
      rw [Pi.single_eq_of_ne, sub_zero]
      intro hequal
      have h := congrArg (fun item : TruncatedArity order => item.val.1.val) hequal
      change 0 = 1 at h
      omega
    · have hrone : arity.val.1.val = 1 := by omega
      have harity : arity = primaryArity order horder := by
        apply Subtype.ext
        exact Prod.ext (Fin.ext hrone) (Fin.ext hs)
      subst arity
      apply sub_eq_zero.mpr
      unfold firstFamily primaryFamily
      rw [Pi.single_eq_same]
      apply Subtype.ext
      funext (colors : Fin 1 → Palette security) (centers : Fin 0 → SafePalette security)
      have hcolors : colors = (fun _ => colors 0) := by
        funext index
        have hi := Fin.eq_zero index
        subst index
        rfl
      have hcenters : centers = Fin.elim0 := Subsingleton.elim _ _
      rw [hcolors, hcenters]
      rfl

theorem complete_eq_first_add_higher (security order : ℕ) (horder : 1 ≤ order)
    (mass : (Fin 4 → Palette security) → ℝ) (hmass : ∑ word, mass word = 0) :
    completeFamily security order mass = firstFamily security order horder mass + higherFamily security order mass := by
  funext arity
  change completeFamily security order mass arity = firstFamily security order horder mass arity + higherFamily security order mass arity
  by_cases hsmall : arity.val.1.val + arity.val.2.val < 2
  · rw [higherFamily_vanishesBelow security order mass arity hsmall, add_zero]
    exact sub_eq_zero.mp (complete_sub_first_raises security order horder mass hmass arity hsmall)
  · have hfirst : firstFamily security order horder mass arity = 0 := by
      unfold firstFamily primaryFamily
      rw [Pi.single_eq_of_ne]
      intro hequal
      have h := congrArg (fun item : TruncatedArity order => item.val.1.val + item.val.2.val) hequal
      change arity.val.1.val + arity.val.2.val = 1 + 0 at h
      omega
    rw [hfirst, zero_add]
    unfold completeFamily higherFamily
    simp only [hmass, zero_smul, zero_add, Finset.sum_apply]
    symm
    apply Finset.sum_subset
    · intro selected hselected
      apply Finset.mem_erase.mpr
      constructor
      · intro hequal
        have hcard := (Finset.mem_filter.mp hselected).2
        rw [hequal, Finset.card_empty] at hcard
        omega
      · exact Finset.mem_univ _
    · intro selected _ hnot
      have hcard : selected.card < 2 := by
        by_contra! hcard
        exact hnot (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcard⟩)
      unfold selectedFamily
      split_ifs with hdegree
      · rw [Pi.single_eq_of_ne]
        intro hequal
        have h := congrArg (fun item : TruncatedArity order => item.val.1.val + item.val.2.val) hequal
        change arity.val.1.val + arity.val.2.val = selected.card + 0 at h
        omega
      · rfl

theorem firstFamily_norm (security order : ℕ) (horder : 1 ≤ order)
    (mass : (Fin 4 → Palette security) → ℝ) (hmass : ∑ word, mass word = 0)
    (primaryFactor bodyFactor : ℝ) (hprimary : 0 ≤ primaryFactor) :
    familyNorm (primaryLaw security) (bodyReference security) order primaryFactor bodyFactor
      (firstFamily security order horder mass) ≤
        primaryFactor * (2 / activation security) * Real.sqrt 2 *
          Real.sqrt (BlockFock.tensorEnergy (LocalTensors.degreeTensor
            (fun _ : Fin 4 => uniformReference security) mass 1)) := by
  let profile := LocalTensors.signedColorCount mass
  have hscore : firstScore security order horder mass =
      PrimaryTensorInverse.densityInverse security (fun color => profile color / (primaryLaw security).weight color) :=
    completeFamily_primary_centered security order horder mass hmass
  have hraw : (primaryLaw security).l2Sq (fun color => profile color / (primaryLaw security).weight color) =
      profileSquareNorm (primaryLaw security).weight profile := by
    change densitySquareNorm (primaryLaw security).weight _ = _
    exact densityScore_square _ _
  have henergy := PrimaryTensorInverse.densityInverse_energy security
    (fun color => profile color / (primaryLaw security).weight color)
  rw [hraw] at henergy
  have hcount := OrdinaryRaising.profile_primary_energy_le_uniform security profile
  have hfock := LocalTensors.degreeTensor_one_energy_zero_mass (uniformReference security)
    (fun color => by rw [uniformReference_weight]; exact one_div_pos.mpr (FirstResponse.modulus_pos security)) mass hmass
  have htotal : (primaryLaw security).l2Sq (firstScore security order horder mass) ≤
      (2 / activation security) ^ 2 * (2 * BlockFock.tensorEnergy
        (LocalTensors.degreeTensor (fun _ : Fin 4 => uniformReference security) mass 1)) := by
    rw [hscore]
    exact henergy.trans (mul_le_mul_of_nonneg_left (hcount.trans_eq (by rw [hfock])) (sq_nonneg _))
  unfold firstFamily
  rw [primaryFamily_norm]
  apply (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt htotal) hprimary).trans_eq
  rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (div_nonneg (by norm_num) (activation_pos security).le),
    Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
  ring

end
end CurrentAFT.CompleteFirstCoefficient
