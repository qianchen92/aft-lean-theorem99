import AFT.BetaGridError
import AFT.SafeBetaGridPoint
import AFT.FiniteKernelVariation

/-! # Finite fair-bit beta mixing of the actual V7 reference histogram -/
namespace AFT.V7Calibration
open GaussianSource BetaReference HistogramGenerating Filter MeasureTheory
open scoped BigOperators Classical Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] actualModulusNeZero
local instance actualFiniteBetaReferenceFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _

def actualFiniteBetaSource (n : ℕ) : FiniteDist (Fin (2^n)) :=
  finiteLaw (Parameters.legs n) (Parameters.dimension n-Parameters.legs n-1) n (n+n)

def actualFiniteBetaValue (n : ℕ) (j : Fin (2^n)) : ℝ :=
  safeGridValue (Parameters.dimension n) (Parameters.legs n) (2^n) j

def actualFiniteBetaHistogram (C : ℝ) (n : ℕ) :
    FiniteDist (Histogram (Parameters.dimension n) (Fin (Parameters.modulus n))) :=
  (actualFiniteBetaSource n).mix fun j => actualPositiveReferenceHistogram C n (actualFiniteBetaValue n j)

def actualBetaSamplingError (C : ℝ) (n : ℕ) : ℝ :=
  betaGridMesh n+actualBetaBufferedTail n+2*betaGridRejectedMass n+actualBetaGridError C n

/-- Every output of the actual finite beta routine satisfies the exact
calibration interval, including its deterministic exceptional-value fallback. -/
theorem actualFiniteBetaValue_typical (n : ℕ) (j : Fin (2^n)) :
    (Parameters.legs n : ℝ)/(2*Parameters.dimension n) ≤ actualFiniteBetaValue n j ∧
      actualFiniteBetaValue n j ≤ 2*(Parameters.legs n : ℝ)/Parameters.dimension n :=
  safeGridValue_real_typical _ _ _ _

theorem actualFiniteBetaSource_tv (n : ℕ) :
    FiniteDist.TVBound (actualFiniteBetaSource n)
      (gridLaw (Parameters.legs n) (Parameters.dimension n-Parameters.legs n-1) (2^n) (by positivity))
      (betaGridMesh n) := by
  have hh := finiteLaw_tv (Parameters.legs n) (Parameters.dimension n-Parameters.legs n-1) n (n+n)
  have he : (((2^n : ℕ) : ℝ)/(2^(n+n) : ℕ))=betaGridMesh n := by
    unfold betaGridMesh
    simp only [Nat.cast_pow,Nat.cast_ofNat,pow_add,Nat.cast_mul]
    field_simp
  simpa only [he] using hh

theorem actual_grid_typical_rejection_eventually :
    ∀ᶠ n in atTop,
      (gridLaw (Parameters.legs n) (Parameters.dimension n-Parameters.legs n-1) (2^n) (by positivity)).eventMass
        (fun j => ¬((Parameters.legs n : ℝ)/(2*Parameters.dimension n) ≤ ((j.val+1 : ℕ) : ℝ)/(2^n : ℕ) ∧
          ((j.val+1 : ℕ) : ℝ)/(2^n : ℕ) ≤ 2*(Parameters.legs n : ℝ)/Parameters.dimension n)) ≤ actualBetaBufferedTail n := by
  filter_upwards [actual_beta_mesh_typical_eventually] with n hm
  have hi := Parameters.population_identity n
  have hb := Parameters.bodies_positive n
  have hpop : Parameters.legs n+(Parameters.dimension n-Parameters.legs n-1)+1=Parameters.dimension n := by omega
  have hh := gridLaw_typical_rejection_le (Parameters.legs n) (Parameters.dimension n-Parameters.legs n-1) (2^n)
    (by positivity) (by omega) (by simpa only [hpop] using hm)
  simpa only [hpop,actualBetaBufferedTail] using hh

/-- The finite routine uses `2n` fair bits, a depth-`n` rational CDF search,
and a rational typical-interval test. Its complete reference histogram is
within the displayed negligible error of the true uniform histogram. -/
theorem actual_finite_beta_uniform_histogram_eventually (C : ℝ) (hC : 1 ≤ C) :
    ∀ᶠ n in atTop,FiniteDist.TVBound (actualFiniteBetaHistogram C n)
      ((FiniteDist.independent fun _ : Fin (Parameters.dimension n) => FiniteDist.uniform (Fin (Parameters.modulus n))).map histogram)
      (actualBetaSamplingError C n) := by
  filter_upwards [beta_grid_legal_eventually C hC,actual_beta_cutoff_eventually C hC,
    actual_boundary_fraction_eventually C hC,actual_reference_histogram_eventually C hC,
    actual_reference_uniform_eventually C hC,actual_grid_typical_rejection_eventually]
    with n hg hc hb href hu htyp
  let grid := gridLaw (Parameters.legs n) (Parameters.dimension n-Parameters.legs n-1) (2^n) (by positivity)
  let retained := gridTailLaw (Parameters.legs n) (Parameters.dimension n-Parameters.legs n-1)
    (2^n) (betaGridStart n) (by positivity) hg.2.1
  let raw := fun j : Fin (2^n) => actualPositiveReferenceHistogram C n (((j.val+1 : ℕ) : ℝ)/(2^n : ℕ))
  let safe := fun j : Fin (2^n) => actualPositiveReferenceHistogram C n (actualFiniteBetaValue n j)
  have hfinite : FiniteDist.TVBound (actualFiniteBetaHistogram C n) (grid.mix safe) (betaGridMesh n) :=
    (actualFiniteBetaSource_tv n).mix safe
  have hsafe : FiniteDist.TVBound (grid.mix safe) (grid.mix raw) (actualBetaBufferedTail n) := by
    apply (FiniteDist.mix_exception_tv grid safe raw
      (fun j => (Parameters.legs n : ℝ)/(2*Parameters.dimension n) ≤ ((j.val+1 : ℕ) : ℝ)/(2^n : ℕ) ∧
        ((j.val+1 : ℕ) : ℝ)/(2^n : ℕ) ≤ 2*(Parameters.legs n : ℝ)/Parameters.dimension n)
      (fun j hj => by dsimp only [safe,raw,actualFiniteBetaValue]; rw [safeGridValue_real_eq _ _ _ _ hj])).mono htyp
  have hretain : FiniteDist.TVBound (grid.mix raw) (retained.mix raw) (betaGridRejectedMass n) := by
    have ht := FiniteDist.condition_self_tv grid (fun j => betaGridStart n ≤ j.val)
      (gridLaw_tail_positive _ _ _ _ (by positivity) hg.2.1)
    have he : grid.eventMass (fun j => ¬betaGridStart n ≤ j.val)=betaGridRejectedMass n := by
      simpa only [not_le,betaGridRejectedMass,betaGridCutoff,grid] using
        gridLaw_head_mass (Parameters.legs n) (Parameters.dimension n-Parameters.legs n-1)
          (2^n) (betaGridStart n) (by positivity) hg.2.1.le
    rw [he] at ht
    exact ht.symm.mix raw
  have hpop : Parameters.legs n+(Parameters.dimension n-Parameters.legs n-1)+1=Parameters.dimension n := by
    have hi := Parameters.population_identity n
    have hbp := Parameters.bodies_positive n
    omega
  have hbc : actualBoundaryFraction C n ≤ (betaGridStart n : ℝ)/(2^n : ℕ) := hc.2.1.trans hg.2.2.1
  have habstract := grid_histogram_tv_dimension (Parameters.dimension n) (Parameters.legs n)
    (Parameters.dimension n-Parameters.legs n-1) (2^n) (betaGridStart n) hpop (by positivity) hg.1 hg.2.1
    (actualReferenceInteriorLaw C n) (actualReferenceBoundaryLaw C n) (actualBoundaryFraction C n) hb.1 hbc
  have hmix : retained.mix raw=retained.mix (fun j => referenceHistogram (Parameters.dimension n) (Parameters.legs n)
      (by omega) (actualReferenceInteriorLaw C n) (actualReferenceBoundaryLaw C n)
      (actualBoundaryFraction C n/(((j.val+1 : ℕ) : ℝ)/(2^n : ℕ)))) := by
    ext hist
    simp only [FiniteDist.mix_weight]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : betaGridStart n ≤ j.val
    · have hbeta : actualBetaCutoff C n ≤ ((j.val+1 : ℕ) : ℝ)/(2^n : ℕ) := hg.2.2.1.trans
        (div_le_div_of_nonneg_right (by exact_mod_cast (by omega : betaGridStart n ≤ j.val+1)) (by positivity))
      simp only [raw,href _ hbeta]
    · have hz : retained.weight j=0 := by
        dsimp only [retained,gridTailLaw,FiniteDist.condition]
        simp only [hj,if_false,zero_div]
      simp only [hz,zero_mul]
  have huniform : FiniteDist.TVBound (retained.mix raw)
      ((FiniteDist.independent fun _ : Fin (Parameters.dimension n) => FiniteDist.uniform (Fin (Parameters.modulus n))).map histogram)
      (betaGridRejectedMass n+actualBetaGridError C n) := by
    rw [hmix]
    simpa only [hu,betaGridRejectedMass,betaGridCutoff,actualBetaGridError,retained] using habstract
  have htotal := ((hfinite.triangle hsafe).triangle hretain).triangle huniform
  exact htotal.mono (by unfold actualBetaSamplingError; ring_nf; rfl)

theorem actualBetaSamplingError_negligible (C : ℝ) (hC : 1 ≤ C) : Negligible (actualBetaSamplingError C) := by
  exact ((betaGridMesh_negligible.add actual_beta_buffered_tail_negligible).add
    (betaGridRejectedMass_negligible.const_mul 2)).add (actualBetaGridError_negligible C hC)

end
end AFT.V7Calibration
