import CurrentAFT.RationalPackedRootUntaggedBounds
import CurrentAFT.RationalPackedRootControl

/-! # Scalar errors for the original joint root and control coefficient -/
namespace CurrentAFT.RationalPackedRootProgram
open AFT TaggedSelection PairedRootPlacement CycleRootExpansion ActualControls
open ActualBlockFock (BlockIndex)
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1600000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
local instance packedScalarFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
local instance packedScalarSafeDecidableEq (security : ℕ) : DecidableEq (SafePalette security) := Classical.decEq _
local instance packedScalarSumDecidableEq {Left Right : Type*} : DecidableEq (Left ⊕ Right) := Classical.decEq _
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.legCount rootReference

def scalarError (security r s count tags : ℕ) : ℝ :=
  (WeightedPointKernelProgram.errorConstant security r s + 4*count)*(1+4*tags)+4*tags

def scalarBound (security r s tags : ℕ) : ℝ :=
  (1+WeightedPointKernelProgram.errorConstant security r s)*(1+4*tags)

def sourceScalar {security r s : ℕ} (bits : ℕ) (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) (sourcePrimary : Fin r → Palette security)
    (sourceBody : Fin s → SafePalette security) (source : PairedRootInput.GroupInput selection tagged) : ℚ :=
  let word := sourceWord security (groupCount selection tagged) (sourceIndex selection tagged source)
  control security bits (actualMetadata selection tagged) (fun index => (sourcePrimary index).val)
    (fun index => (sourceBody index).val.val) word * untagged security bits (actualMetadata selection tagged) word *
      signed security bits (actualMetadata selection tagged) word

def actualScalar {security r s : ℕ} (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) (layout : BlockIndex security ≃ Vertex security)
    (sourcePrimary : Fin r → Palette security) (sourceBody : Fin s → SafePalette security)
    (source : PairedRootInput.GroupInput selection tagged) : ℝ :=
  PairedRootInput.controlKernel selection tagged (WeightedPointKernelProgram.actualKernel security sourcePrimary sourceBody)
    (fun group => (source group).2) * RootWeightedSynthesis.untaggedWeight selection tagged source *
      RootWeightedSynthesis.weightedCoefficient selection tagged layout source

theorem pointKernelError_nonneg (security r s : ℕ) :
    0 ≤ WeightedPointKernelProgram.errorConstant security r s := by
  unfold WeightedPointKernelProgram.errorConstant RationalRootMassProgram.primaryErrorConstant
  positivity

theorem scalarError_nonneg (security r s count tags : ℕ) : 0 ≤ scalarError security r s count tags := by
  unfold scalarError
  have h := pointKernelError_nonneg security r s
  positivity

theorem scalarBound_nonneg (security r s tags : ℕ) : 0 ≤ scalarBound security r s tags := by
  unfold scalarBound
  have h := pointKernelError_nonneg security r s
  positivity

theorem two_factor_error (a b x y A B e f : ℝ) (hA : 0 ≤ A) (_hB : 0 ≤ B)
    (he : 0 ≤ e) (_hf : 0 ≤ f) (hx : |x| ≤ A) (hb : |b| ≤ B)
    (ha : |a-x| ≤ e) (hy : |b-y| ≤ f) :
    |a*b-x*y| ≤ e*B+A*f := by
  calc
    _ = |(a-x)*b+x*(b-y)| := by congr 1; ring
    _ ≤ |a-x| * |b| + |x| * |b-y| := by simpa only [abs_mul] using abs_add_le ((a-x)*b) (x*(b-y))
    _ ≤ e*B+A*f := add_le_add (mul_le_mul ha hb (abs_nonneg _) he)
      (mul_le_mul hx hy (abs_nonneg _) hA)

theorem scalar_error {security r s : ℕ} (bits : ℕ) (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) (layout : BlockIndex security ≃ Vertex security)
    (hroom : tagged.card ≤ Parameters.bodySize security)
    (sourcePrimary : Fin r → Palette security) (sourceBody : Fin s → SafePalette security)
    (source : PairedRootInput.GroupInput selection tagged)
    (hprecision : 1 / (2 : ℝ)^bits ≤ 1 / (4 * (Parameters.base security : ℝ)))
    (hbudget : 64 * (Parameters.base security : ℝ) * Parameters.dimension security * (1 / (2 : ℝ)^bits) ≤
      1 / (4 * (Parameters.modulus security : ℝ))) :
    |(sourceScalar bits selection tagged sourcePrimary sourceBody source : ℝ) -
      actualScalar selection tagged layout sourcePrimary sourceBody source| ≤
      scalarError security r s (groupCount selection tagged) tagged.card * (1/(2:ℝ)^bits) := by
  let word := sourceWord security (groupCount selection tagged) (sourceIndex selection tagged source)
  let a : ℝ := control security bits (actualMetadata selection tagged) (fun index => (sourcePrimary index).val)
    (fun index => (sourceBody index).val.val) word
  let b : ℝ := untagged security bits (actualMetadata selection tagged) word
  let c : ℝ := signed security bits (actualMetadata selection tagged) word
  let x := PairedRootInput.controlKernel selection tagged (WeightedPointKernelProgram.actualKernel security sourcePrimary sourceBody)
    (fun group => (source group).2)
  let y := RootWeightedSynthesis.untaggedWeight selection tagged source
  let z := RootWeightedSynthesis.weightedCoefficient selection tagged layout source
  let epsilon : ℝ := 1/(2:ℝ)^bits
  let E := WeightedPointKernelProgram.errorConstant security r s
  have hE : 0 ≤ E := pointKernelError_nonneg security r s
  have he : 0 ≤ epsilon := by positivity
  have he1 : epsilon ≤ 1 := RationalCoefficientExtraction.epsilon_le_one bits
  have ha : |a-x| ≤ E*epsilon := control_error bits selection tagged sourcePrimary sourceBody source hprecision hbudget
  have hb : |b-y| ≤ (4*groupCount selection tagged:ℝ)*epsilon := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using untagged_error bits selection tagged source
  have hc : |c-z| ≤ (4*tagged.card:ℝ)*epsilon := by
    simpa only [c, z, word, epsilon, Nat.cast_mul, Nat.cast_ofNat, div_eq_mul_inv, one_div, one_mul] using
      signed_error bits selection tagged layout hroom source
  have hbb : |b| ≤ 1 := by rw [abs_of_nonneg (untagged_bounds bits selection tagged source).1]; exact (untagged_bounds bits selection tagged source).2
  have hxb : |x| ≤ 1 := control_bound selection tagged sourcePrimary sourceBody source
  have hyb : |y| ≤ 1 := by rw [abs_of_nonneg (untaggedWeight_bounds selection tagged source).1]; exact (untaggedWeight_bounds selection tagged source).2
  have hzb : |z| ≤ 1 := weightedCoefficient_bound selection tagged layout source
  have hcb : |c| ≤ 1+4*tagged.card := by
    calc
      _ ≤ |c-z|+|z| := by simpa only [sub_add_cancel] using abs_add_le (c-z) z
      _ ≤ (4*tagged.card:ℝ)*epsilon+1 := add_le_add hc hzb
      _ ≤ _ := by nlinarith
  have hab := two_factor_error a b x y 1 1 (E*epsilon) ((4*groupCount selection tagged:ℝ)*epsilon)
    (by norm_num) (by norm_num) (mul_nonneg (pointKernelError_nonneg security r s) he) (by positivity)
    hxb hbb ha hb
  have hxy : |x*y| ≤ 1 := by rw [abs_mul]; exact (mul_le_mul hxb hyb (abs_nonneg _) (by norm_num)).trans_eq (by norm_num)
  have hall := two_factor_error (a*b) c (x*y) z 1 (1+4*tagged.card)
    (E*epsilon*1+1*((4*groupCount selection tagged:ℝ)*epsilon)) ((4*tagged.card:ℝ)*epsilon)
    (by norm_num) (by positivity) (by positivity) (by positivity) hxy hcb hab hc
  unfold sourceScalar
  push_cast
  change |a*b*c-x*y*z| ≤ _
  exact hall.trans_eq (by unfold scalarError; dsimp only [E, epsilon]; ring)

theorem sourceScalar_bound {security r s : ℕ} (bits : ℕ) (selection : Selection security r s)
    (tagged : Finset (BlockIndex security)) (layout : BlockIndex security ≃ Vertex security)
    (hroom : tagged.card ≤ Parameters.bodySize security)
    (sourcePrimary : Fin r → Palette security) (sourceBody : Fin s → SafePalette security)
    (source : PairedRootInput.GroupInput selection tagged)
    (hprecision : 1 / (2 : ℝ)^bits ≤ 1 / (4 * (Parameters.base security : ℝ)))
    (hbudget : 64 * (Parameters.base security : ℝ) * Parameters.dimension security * (1 / (2 : ℝ)^bits) ≤
      1 / (4 * (Parameters.modulus security : ℝ))) :
    |(sourceScalar bits selection tagged sourcePrimary sourceBody source : ℝ)| ≤ scalarBound security r s tagged.card := by
  let word := sourceWord security (groupCount selection tagged) (sourceIndex selection tagged source)
  have he := RationalCoefficientExtraction.epsilon_le_one bits
  have hE := pointKernelError_nonneg security r s
  have ha := control_error bits selection tagged sourcePrimary sourceBody source hprecision hbudget
  have hx := control_bound selection tagged sourcePrimary sourceBody source
  have hb := untagged_bounds bits selection tagged source
  have hc := signed_error bits selection tagged layout hroom source
  have hz := weightedCoefficient_bound selection tagged layout source
  have hcontrol : |(control security bits (actualMetadata selection tagged) (fun index => (sourcePrimary index).val)
      (fun index => (sourceBody index).val.val) word : ℝ)| ≤ 1+WeightedPointKernelProgram.errorConstant security r s := by
    calc
      _ ≤ |(control security bits (actualMetadata selection tagged) (fun index => (sourcePrimary index).val)
        (fun index => (sourceBody index).val.val) word : ℝ) -
        PairedRootInput.controlKernel selection tagged (WeightedPointKernelProgram.actualKernel security sourcePrimary sourceBody)
          (fun group => (source group).2)| +
        |PairedRootInput.controlKernel selection tagged (WeightedPointKernelProgram.actualKernel security sourcePrimary sourceBody)
          (fun group => (source group).2)| := by
        simpa only [sub_add_cancel] using abs_add_le
          ((control security bits (actualMetadata selection tagged) (fun index => (sourcePrimary index).val)
            (fun index => (sourceBody index).val.val) word : ℝ) -
            PairedRootInput.controlKernel selection tagged (WeightedPointKernelProgram.actualKernel security sourcePrimary sourceBody)
              (fun group => (source group).2))
          (PairedRootInput.controlKernel selection tagged (WeightedPointKernelProgram.actualKernel security sourcePrimary sourceBody)
              (fun group => (source group).2))
      _ ≤ WeightedPointKernelProgram.errorConstant security r s * (1/(2:ℝ)^bits)+1 := add_le_add ha hx
      _ ≤ _ := by nlinarith
  have hsigned : |(signed security bits (actualMetadata selection tagged) word : ℝ)| ≤ 1+4*tagged.card := by
    have hc' : |(signed security bits (actualMetadata selection tagged) word : ℝ)-
        RootWeightedSynthesis.weightedCoefficient selection tagged layout source| ≤
        (4*tagged.card:ℝ)*(1/(2:ℝ)^bits) := by
      simpa only [word, Nat.cast_mul, Nat.cast_ofNat, div_eq_mul_inv, one_div, one_mul] using hc
    calc
      _ ≤ |(signed security bits (actualMetadata selection tagged) word : ℝ)-
        RootWeightedSynthesis.weightedCoefficient selection tagged layout source|+
        |RootWeightedSynthesis.weightedCoefficient selection tagged layout source| := by
        simpa only [sub_add_cancel] using abs_add_le
          ((signed security bits (actualMetadata selection tagged) word : ℝ)-
            RootWeightedSynthesis.weightedCoefficient selection tagged layout source)
          (RootWeightedSynthesis.weightedCoefficient selection tagged layout source)
      _ ≤ (4*tagged.card:ℝ)*(1/(2:ℝ)^bits)+1 := add_le_add hc' hz
      _ ≤ _ := by nlinarith
  unfold sourceScalar
  push_cast
  rw [abs_mul, abs_mul, abs_of_nonneg hb.1]
  exact (mul_le_mul (mul_le_mul hcontrol hb.2 hb.1 (by positivity)) hsigned (abs_nonneg _) (by positivity)).trans_eq
    (by unfold scalarBound; ring)

end
end CurrentAFT.RationalPackedRootProgram
