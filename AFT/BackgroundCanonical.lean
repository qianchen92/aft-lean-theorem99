import AFT.GlobalBackgroundLog
import AFT.MeanSeedCanonical
import AFT.RepresentedCanonical
import AFT.JointSeedOutput

/-! # Canonical seed support of the actual background mean and covariance tables -/
namespace AFT.RepresentedPolynomial
open scoped BigOperators Classical
noncomputable section
variable {Color : Type*} [Fintype Color]

theorem inversePrimaryTable_canonical (primary body : FiniteDist Color) (rho : ℝ)
    (operator : (Color → ℝ) ≃ₗ[ℝ] (Color → ℝ)) (table : Table (InputSeed Color))
    (hc : InputTableCanonical primary body table)
    (hinverse : ∀ seed, Hoeffding.Canonical (inputReference primary body seed) Finset.univ seed.kernel →
      Hoeffding.Canonical (inputReference primary body (inversePrimarySeed primary body rho operator seed))
        Finset.univ (inversePrimarySeed primary body rho operator seed).kernel) :
    InputTableCanonical primary body (inversePrimaryTable primary body rho operator table) := by
  change InputTableCanonical primary body (MvPolynomial.rename (inversePrimarySeed primary body rho operator) table)
  exact InputTableCanonical.rename _ (fun seed hs => hinverse seed ((inputTableCanonical_iff_vars _ _ _).mp hc seed hs))

end
end AFT.RepresentedPolynomial

namespace AFT.V7Calibration
open GaussianSource Filter RepresentedPolynomial
open scoped BigOperators Classical Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
local instance backgroundCanonicalFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _
local instance backgroundCanonicalSumDecEq {α β : Type*} : DecidableEq (α ⊕ β) := Classical.decEq _

theorem actual_mean_tables_canonical_eventually (C : ℝ) (hC : 1 ≤ C) (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ n in atTop, (Parameters.legs n : ℝ)/(2*Parameters.dimension n) ≤ beta n ∧
      beta n ≤ 2*(Parameters.legs n : ℝ)/Parameters.dimension n) :
    ∀ᶠ n in atTop,
      let p := actualPrimaryLaw C n (beta n)
      let b := actualBodyLaw C n (beta n)
      InputTableCanonical p b (pairMeanTable C n (beta n)) ∧
      (∀ shift : ℤ, |shift| ≤ maxBodyShift C n → InputTableCanonical p b (bodyMeanTable C n (beta n) shift)) ∧
      (∀ queue : ℤ, |queue| ≤ queueCutoff n → InputTableCanonical p b (attachedMeanTable C n (beta n) queue)) ∧
      (∀ sample,InputTableCanonical p b (globalMeanTable C n (beta n) sample)) := by
  filter_upwards [actual_mean_seeds_canonical_eventually C hC beta hbeta] with n hs
  dsimp only at hs ⊢
  obtain ⟨hroot,hfull,hextra,hshift⟩ := hs
  have hb (shift : ℤ) (hh : |shift| ≤ maxBodyShift C n) :
      InputTableCanonical (actualPrimaryLaw C n (beta n)) (actualBodyLaw C n (beta n)) (bodyMeanTable C n (beta n) shift) := by
    obtain ⟨hs,ho⟩ := hshift shift hh
    exact ((InputTableCanonical.X _ hs).add (InputTableCanonical.X _ ho)).add
      ((InputTableCanonical.C _).mul (InputTableCanonical.X _ hroot))
  have ha (queue : ℤ) (hq : |queue| ≤ queueCutoff n) :
      InputTableCanonical (actualPrimaryLaw C n (beta n)) (actualBodyLaw C n (beta n)) (attachedMeanTable C n (beta n) queue) :=
    InputTableCanonical.queueAverage _ _ (fun source => hb _ (attached_mean_shift_bound C n queue hq source))
  refine ⟨?_,hb,ha,?_⟩
  · exact (((InputTableCanonical.C _).mul (InputTableCanonical.X _ hextra)).add
      ((InputTableCanonical.C _).mul (InputTableCanonical.X _ hroot))).add
      ((InputTableCanonical.C _).mul (InputTableCanonical.X _ hfull))
  · have hblock (index : blockIndex n) (queue : ℤ) (hq : |queue| ≤ queueCutoff n) :
        InputTableCanonical (actualPrimaryLaw C n (beta n)) (actualBodyLaw C n (beta n))
          (blockBodyMeanTable C n (beta n) index queue) := by
      cases index with
      | inl _ => exact ha queue hq
      | inr _ => exact hb queue (by unfold maxBodyShift; omega)
    have hc (sample) : InputTableCanonical (actualPrimaryLaw C n (beta n)) (actualBodyLaw C n (beta n))
        (globalMeanChangeTable C n (beta n) sample) :=
      InputTableCanonical.sum _ _ (fun index _ => (hblock index _ (actualQueueShifts_bound n sample index)).sub
        (hblock index 0 (by simp)))
    intro sample
    exact (hc sample).sub (InputTableCanonical.queueAverage _ _ hc)

theorem actual_covariance_table_canonical_eventually (C : ℝ) (hC : 1 ≤ C) (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ n in atTop, (Parameters.legs n : ℝ)/(2*Parameters.dimension n) ≤ beta n ∧
      beta n ≤ 2*(Parameters.legs n : ℝ)/Parameters.dimension n) :
    ∀ᶠ n in atTop, ∀ queue : ℤ, |queue| ≤ queueCutoff n →
      InputTableCanonical (actualPrimaryLaw C n (beta n)) (actualBodyLaw C n (beta n))
        (actualCovarianceTable C n (beta n) queue) := by
  filter_upwards [actual_covariance_inputs_canonical_eventually C hC beta hbeta,
    actual_reference_laws_eventually C hC beta hbeta] with n hc hl queue hq
  have hc := hc queue hq _ hl.1
  apply InputTableCanonical.sum
  intro index _
  apply (InputTableCanonical.C _).mul
  apply InputTableCanonical.X
  have hbody : (actualCovarianceSeed C n (beta n) queue index).bodyOrder = 0 := by
    fin_cases index <;> rfl
  rw [show inputReference (actualPrimaryLaw C n (beta n)) (actualBodyLaw C n (beta n))
      (actualCovarianceSeed C n (beta n) queue index) = fun _ => actualPrimaryLaw C n (beta n) from
    funext (all_primary_reference _ _ _ hbody)]
  fin_cases index
  · exact hc.1
  · exact hc.2.1
  · exact hc.2.2.1
  · exact hc.2.2.2 false
  · exact hc.2.2.2 true

end
end AFT.V7Calibration
