import AFT.IndependentRootHilbert
import AFT.ReferenceHilbertFibers
import AFT.ReferencePrimaryDensity

/-! # Sharp actual selected coefficients on arbitrary remaining fibers -/
namespace AFT.V7Calibration
open GaussianSource BoundaryCalibration Filter
open scoped BigOperators Classical Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
local instance independentReferenceHilbertFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _
local instance independentReferenceHilbertSubtypeDecEq (selected : Finset (Fin 4)) : DecidableEq selected := Classical.decEq _
attribute [local instance] actualModulusNeZero

def independentReferenceHilbertConstant : ℝ := 65536*100000000

theorem independentPaired_reference_hilbert_eventually (C : ℝ) (hC : 1 ≤ C)
    (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ n in atTop, (Parameters.legs n : ℝ)/(2*Parameters.dimension n) ≤ beta n ∧
      beta n ≤ 2*(Parameters.legs n : ℝ)/Parameters.dimension n) :
    ∀ᶠ n in atTop,
    ∀ charts : (mark : Fin (Parameters.modulus n)) → PublicChartFamily C n mark,
    (∀ mark first second,publicChartRaw C n mark (charts mark) (fun _ => 1) first second =
      conditionalJointOutput C n mark (fun _ => 1) first second) →
    ∀ (Fiber : Type) [Fintype Fiber], ∀ fiber : FiniteDist Fiber,
    ∀ kernel : Fin (Parameters.modulus n) → Fiber → ℝ,
      (∀ rest,∑ color,(actualPrimaryLaw C n (beta n)).weight color*kernel color rest=0) →
    ∀ full fixed : ℝ,0 ≤ full → 0 ≤ fixed →
      fiber.expectation (fun rest => (actualPrimaryLaw C n (beta n)).l2Sq (fun color => kernel color rest)) ≤ full^2 →
      (∀ color,fiber.l2Sq (kernel color) ≤ fixed^2) →
    ∀ selected : Finset (Fin 4),
    let coefficient := fun rest => LocalTensors.referenceRestrictedComponent
      (fun _ : Fin 4 => actualPrimaryLaw C n (beta n)) (fun _ : Fin 4 => actualReferenceLaw C n (beta n))
      (independentPairedNumerator C n (beta n) charts
        (fun color => (actualPrimaryLaw C n (beta n)).weight color*kernel color rest)) selected
    (fiber.expectation (fun rest =>
      (FiniteDist.independent (fun _ : selected => actualPrimaryLaw C n (beta n))).l2Sq (coefficient rest)) ≤
      (independentReferenceHilbertConstant*(n : ℝ)^4*full)^2) ∧
    (∀ (slot : selected) values,fiber.expectation (fun rest => MixedKernel.fiberSq
      (fun _ : selected => actualPrimaryLaw C n (beta n)) (coefficient rest) {slot} values) ≤
      (independentReferenceHilbertConstant*(n : ℝ)^4*(full+fixed))^2) ∧
    (∀ word,fiber.l2Sq (fun rest => coefficient rest word) ≤
      (independentReferenceHilbertConstant*(n : ℝ)^8*fixed)^2) := by
  filter_upwards [independentPairedDensity_hilbert_eventually C hC beta hbeta,
    actual_reference_laws_eventually C hC beta hbeta,
    actual_primary_probability_eventually C hC beta hbeta,
    actual_reference_primary_density_eventually C hC beta hbeta]
    with n hh hl hp hc charts hcharts Fiber inst fiber kernel hcanonical full fixed hfull hfixed hF hG selected
  let primary := actualPrimaryLaw C n (beta n)
  let reference := actualReferenceLaw C n (beta n)
  let mass := fun rest => independentPairedNumerator C n (beta n) charts
    (fun color => primary.weight color*kernel color rest)
  have hpositive (slot : Fin 4) (color) : 0 < primary.weight color := by
    change 0 < (actualPrimaryLaw C n (beta n)).weight color
    rw [hl.1]
    exact hp.1 color
  have hcompare (slot : Fin 4) (color) : reference.weight color ≤ 8*primary.weight color := by
    have hh := (div_le_iff₀ (hp.1 color)).mp ((le_abs_self _).trans (hc.1 color))
    simpa only [primary,reference,hl.1,hl.2.2] using hh
  have hraw := hh charts hcharts Fiber fiber kernel hcanonical (fixed^2) (sq_nonneg fixed) hG
  have hrawF : fiber.expectation (fun rest => (FiniteDist.independent (fun _ : Fin 4 => primary)).l2Sq
      (fun word => mass rest word/(FiniteDist.independent (fun _ : Fin 4 => primary)).weight word)) ≤
        (100000000*(n : ℝ)^4*full)^2 := by
    apply hraw.1.trans
    apply (mul_le_mul_of_nonneg_left hF (by positivity : 0 ≤ (26912768 : ℝ)*(n : ℝ)^8)).trans
    calc
      _ ≤ (100000000 : ℝ)^2*(n : ℝ)^8*full^2 := by gcongr; norm_num
      _ = _ := by ring
  have hrawG (slot : Fin 4) values : fiber.expectation (fun rest => MixedKernel.fiberSq
      (fun _ : Fin 4 => primary)
      (fun word => mass rest word/(FiniteDist.independent (fun _ : Fin 4 => primary)).weight word) {slot} values) ≤
        (100000000*(n : ℝ)^4*fixed)^2 := by
    apply (hraw.2.1 slot values).trans
    calc
      _ ≤ (100000000 : ℝ)^2*(n : ℝ)^8*fixed^2 := by gcongr; norm_num
      _ = _ := by ring
  have hrawH (word) : fiber.l2Sq (fun rest => mass rest word/
      (FiniteDist.independent (fun _ : Fin 4 => primary)).weight word) ≤ (100000000*(n : ℝ)^8*fixed)^2 := by
    apply (hraw.2.2 word).trans
    calc
      _ ≤ (100000000 : ℝ)^2*(n : ℝ)^16*fixed^2 := by gcongr; norm_num
      _ = _ := by ring
  have hcard : selected.card ≤ 4 := by simpa only [Fintype.card_fin] using Finset.card_le_univ selected
  have hfactor : (16:ℝ)^selected.card ≤ 65536 :=
    (pow_le_pow_right₀ (by norm_num : (1:ℝ)≤16) hcard).trans_eq (by norm_num)
  have hfactorSq : ((2*(8:ℝ))^selected.card)^2 ≤ (65536:ℝ)^2 := by
    simpa only [show (2:ℝ)*8=16 by norm_num] using
      (sq_le_sq₀ (by positivity) (by norm_num)).mpr hfactor
  refine ⟨?_,?_,?_⟩
  · apply (LocalTensors.referenceRestrictedComponent_hilbert_square_le (fun _ : Fin 4 => primary)
      (fun _ : Fin 4 => reference) hpositive fiber mass selected 8 (by norm_num) hcompare).trans
    have he := mul_le_mul hfactorSq hrawF (Finset.sum_nonneg fun rest _ => mul_nonneg (fiber.nonneg rest) (FiniteDist.l2Sq_nonneg _ _))
      (sq_nonneg (65536:ℝ))
    exact he.trans_eq (by dsimp [independentReferenceHilbertConstant]; ring)
  · intro slot values
    apply (LocalTensors.referenceRestrictedComponent_singleton_hilbert_square_le
      (fun _ : Fin 4 => primary) (fun _ : Fin 4 => reference) hpositive fiber mass selected 8
      ((100000000*(n : ℝ)^4*full)^2) ((100000000*(n : ℝ)^4*fixed)^2)
      (by norm_num) hcompare hrawF hrawG slot values).trans
    have hsum : (100000000*(n : ℝ)^4*full)^2+(100000000*(n : ℝ)^4*fixed)^2 ≤
        (100000000*(n : ℝ)^4*(full+fixed))^2 := by
      nlinarith [mul_nonneg (show 0 ≤ 100000000*(n : ℝ)^4*full by positivity)
        (show 0 ≤ 100000000*(n : ℝ)^4*fixed by positivity)]
    exact (mul_le_mul hfactorSq hsum (by positivity) (sq_nonneg (65536:ℝ))).trans_eq
      (by dsimp [independentReferenceHilbertConstant]; ring)
  · intro word
    apply (LocalTensors.referenceRestrictedComponent_fixed_hilbert_square_le
      (fun _ : Fin 4 => primary) (fun _ : Fin 4 => reference) hpositive fiber mass selected 8
      ((100000000*(n : ℝ)^8*fixed)^2) (by norm_num) hcompare hrawH word).trans
    exact (mul_le_mul_of_nonneg_right hfactorSq (sq_nonneg _)).trans_eq
      (by dsimp [independentReferenceHilbertConstant]; ring)

end
end AFT.V7Calibration
