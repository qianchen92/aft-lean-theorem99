import AFT.CountedCenteredSampling
import AFT.ActualBodyBlurProgram

/-! # Counted cached queries for the actual unshifted Gaussian windows

Every raw weight and the normalization sum are materialized once. Ticket
rounding stores its complete floor table before computing the deficit.
-/
namespace AFT.RationalNumerics
open GaussianSource FiniteConvolutionProgram
open scoped BigOperators

/-- This uses precisely `windowApproxPrecision`, including its guard bits. -/
def countedWindowWeights (squaredWidth : ℚ) (cutoff bits : ℕ) :
    CountedGaussianWeights (2*cutoff+1) :=
  let raw := Vector.ofFn (fun i : Fin (2*cutoff+1) =>
    GaussianArithmetic.gaussian squaredWidth (windowIndexEquiv cutoff i) (windowApproxPrecision cutoff bits))
  let normalizer := ∑ i,(raw.get i).value
  ⟨Vector.ofFn (fun i => (raw.get i).value/normalizer),
    (∑ i,(raw.get i).work)+2*(2*cutoff+1)⟩

theorem countedWindowWeights_value (squaredWidth : ℚ) (cutoff bits : ℕ) (i : Fin (2*cutoff+1)) :
    (countedWindowWeights squaredWidth cutoff bits).value.get i=windowGaussianWeights squaredWidth cutoff bits i := by
  simp only [countedWindowWeights,Vector.get_ofFn,GaussianArithmetic.gaussian_value,
    windowGaussianWeights,windowApproxWeight]
  congr 1
  change (∑ i : Fin (2*cutoff+1),windowApproxRaw squaredWidth cutoff bits (windowIndexEquiv cutoff i))=_
  exact (windowIndexEquiv cutoff).sum_comp _

structure CountedWindowTickets (size : ℕ) where
  value : Vector ℕ size
  work : ℕ

def countedWindowTickets (squaredWidth : ℚ) (cutoff bits : ℕ) : CountedWindowTickets (2*cutoff+1) :=
  let weights := countedWindowWeights squaredWidth cutoff (bits+1)
  let tickets := PermutationProgram.powerTwo (windowTicketBits cutoff bits)
  let floors := Vector.ofFn (fun i : Fin (2*cutoff+1) => ⌊(tickets.value : ℚ)*weights.value.get i⌋₊)
  let total := ∑ i,floors.get i
  let deficit := tickets.value-total
  ⟨Vector.ofFn (fun i => floors.get i+if i=0 then deficit else 0),
    weights.work+tickets.work+5*(2*cutoff+1)+1⟩

theorem countedWindowTickets_value (squaredWidth : ℚ) (cutoff bits : ℕ) (i : Fin (2*cutoff+1)) :
    (countedWindowTickets squaredWidth cutoff bits).value.get i=windowTicketCounts squaredWidth cutoff bits i := by
  simp only [countedWindowTickets,Vector.get_ofFn,countedWindowWeights_value,PermutationProgram.powerTwo_value]
  rfl

def countedWindowTicketWeight (squaredWidth : ℚ) (cutoff bits : ℕ) (point : Window cutoff) : GaussianArithmetic :=
  let counts := countedWindowTickets squaredWidth cutoff bits
  let denominator := GaussianArithmetic.power 2 (windowTicketBits cutoff bits)
  ⟨(counts.value.get ((windowIndexEquiv cutoff).symm point) : ℚ)/denominator.value,
    counts.work+denominator.work+2⟩

theorem countedWindowTicketWeight_value (squaredWidth : ℚ) (cutoff bits : ℕ) (point : Window cutoff) :
    (countedWindowTicketWeight squaredWidth cutoff bits point).value=
      V7Calibration.windowTicketWeightProgram squaredWidth cutoff bits point := by
  simp only [countedWindowTicketWeight,countedWindowTickets_value,GaussianArithmetic.power_value]
  rfl

def windowQueryWork (cutoff bits : ℕ) : ℕ :=
  (2*cutoff+1)*(2000*(cutoff+bits+(cutoff+1)^2+4)^2+7)+2*windowTicketBits cutoff bits+3

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000

private theorem gaussian_work_budget (squaredWidth : ℚ) (point : ℤ) (precision budget : ℕ)
    (hb : 2≤budget) (hp : precision≤4*budget)
    (hr0 : 0≤gaussianRatio squaredWidth point) (hr : gaussianRatio squaredWidth point≤budget) :
    (GaussianArithmetic.gaussian squaredWidth point precision).work≤2000*budget^2 := by
  have hg : gaussianGuard squaredWidth point≤budget := Nat.ceil_le.mpr hr
  have hpi : gaussianPiPrecision squaredWidth point precision+4≤8*budget := by
    unfold gaussianPiPrecision;omega
  have harg : max (piApprox (gaussianPiPrecision squaredWidth point precision)*gaussianRatio squaredWidth point) 0≤(5*budget : ℕ) := by
    apply max_le
    · have hh := mul_le_mul_of_nonneg_right (piApprox_le_five (gaussianPiPrecision squaredWidth point precision)) hr0
      have hh' := mul_le_mul_of_nonneg_left hr (by norm_num : (0 : ℚ)≤5)
      push_cast
      linarith
    · positivity
  have hs : gaussianExpScale squaredWidth point precision≤11*budget := by
    have hh := Nat.ceil_le.mpr harg
    unfold gaussianExpScale expScale
    omega
  have ht : gaussianTaylorTerms squaredWidth point precision≤16*budget := by
    unfold gaussianTaylorTerms;omega
  apply (GaussianArithmetic.gaussian_work squaredWidth point precision).trans
  calc
    _ ≤ 8*(8*budget)^2+(16*budget)*(2*(16*budget)+2)+11*budget+16 := by gcongr
    _ ≤ _ := by nlinarith

theorem countedWindowWeights_work (squaredWidth : ℚ) (cutoff bits : ℕ) (hw : 1≤squaredWidth) :
    (countedWindowWeights squaredWidth cutoff bits).work≤
      (2*cutoff+1)*(2000*(cutoff+bits+(cutoff+1)^2+3)^2+2) := by
  let budget := cutoff+bits+(cutoff+1)^2+3
  have hs (point : Window cutoff) :
      (GaussianArithmetic.gaussian squaredWidth point (windowApproxPrecision cutoff bits)).work≤2000*budget^2 := by
    apply gaussian_work_budget _ _ _ budget (by dsimp [budget];omega)
      (by dsimp [budget,windowApproxPrecision];omega)
    · unfold gaussianRatio;positivity
    · have hp := Finset.mem_Icc.mp point.property
      have ha : |((point : ℤ) : ℚ)|≤cutoff := by rw [abs_le];constructor <;> exact_mod_cast (by omega : _)
      have hh : ((point : ℤ) : ℚ)^2≤(cutoff : ℚ)^2 := by
        simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) (Nat.cast_nonneg cutoff)).mpr ha
      apply (div_le_self (sq_nonneg _) hw).trans
      apply hh.trans
      dsimp [budget]
      push_cast
      nlinarith
  simp only [countedWindowWeights,Vector.get_ofFn]
  have hh := Finset.sum_le_sum (s:=Finset.univ) (fun i _ => hs (windowIndexEquiv cutoff i))
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul] at hh
  change _≤(2*cutoff+1)*(2000*budget^2+2)
  nlinarith

theorem countedWindowTicketWeight_work (squaredWidth : ℚ) (cutoff bits : ℕ)
    (hw : 1≤squaredWidth) (point : Window cutoff) :
    (countedWindowTicketWeight squaredWidth cutoff bits point).work≤windowQueryWork cutoff bits := by
  have hh := countedWindowWeights_work squaredWidth cutoff (bits+1) hw
  simp only [countedWindowTicketWeight,countedWindowTickets,GaussianArithmetic.power_work,PermutationProgram.powerTwo_work]
  unfold windowQueryWork
  have he : cutoff+(bits+1)+(cutoff+1)^2+3=cutoff+bits+(cutoff+1)^2+4 := by omega
  rw [he] at hh
  nlinarith

end
end AFT.RationalNumerics
