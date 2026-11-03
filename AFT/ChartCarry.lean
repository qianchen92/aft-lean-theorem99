import AFT.PublicChartSupport
import AFT.BodyPhysicalSupport

/-! # Integer carry cancellation for the actual protected affine charts -/
namespace AFT.BoundaryCalibration
open GaussianSource Filter
open scoped BigOperators Classical Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
attribute [local instance] actualModulusNeZero

/-- Integer lifts of the three public affine-chart parameters. -/
def chartIntegerLoad {q : ℕ} (chart : Chart (ZMod q)) (first second : ℤ) : ℤ :=
  chart.1.val + (chart.2.1.val : ℤ)*first+(chart.2.2.val : ℤ)*second

theorem chartIntegerLoad_cast {q : ℕ} [NeZero q] [Fact q.Prime] (chart : Chart (ZMod q)) (first second : ℤ) :
    (chartIntegerLoad chart first second : ZMod q)=feature (first : ZMod q) (second : ZMod q) chart := by
  simp only [chartIntegerLoad,Int.cast_add,Int.cast_mul,Int.cast_natCast,ZMod.natCast_zmod_val,feature]

theorem finEquiv_symm_val {q : ℕ} [NeZero q] (color : ZMod q) :
    ((ZMod.finEquiv q).symm color).val=color.val := by
  cases q with
  | zero => exact False.elim (NeZero.ne 0 rfl)
  | succ q => rfl

theorem chartIntegerLoad_remainder (C : ℝ) (n : ℕ) (input : V7Input C n)
    (chart : Chart (ZMod (Parameters.modulus n))) :
    chartIntegerLoad chart input.1 input.2 % (Parameters.modulus n : ℤ)=
      ((chartPaletteFeature C n input chart).val : ℤ) := by
  rw [← ZMod.val_intCast,chartIntegerLoad_cast]
  simp only [chartPaletteFeature,finEquiv_symm_val]

/-- The second load complements the first load. Once its reduced
companion lies in the palette, the two integer carries cancel exactly. -/
theorem complementary_carries (modulus load total : ℤ) (hq : modulus ≠ 0)
    (hlow : 0 ≤ total-load%modulus) (hhigh : total-load%modulus < modulus) :
    load/modulus+(total-load)/modulus=0 := by
  have he : total-load=(total-load%modulus)+modulus*(-(load/modulus)) := by
    have hh := Int.emod_add_mul_ediv load modulus
    nlinarith
  rw [he,Int.add_mul_ediv_left _ _ hq,Int.ediv_eq_zero_of_lt hlow hhigh]
  ring

/-- The chart's field support is precisely the corresponding integer
slice after choosing the canonical palette representative. -/
theorem chartPaletteFeature_mem_slice (C : ℝ) (n : ℕ) (boundary baseline : ℤ)
    (input : V7Input C n) (chart : Chart (ZMod (Parameters.modulus n)))
    (hmem : feature ((input.1 : ℤ) : ZMod (Parameters.modulus n))
      ((input.2 : ℤ) : ZMod (Parameters.modulus n)) chart ∈ v7ProtectedPalettes C n boundary baseline input) :
    ((chartPaletteFeature C n input chart).val : ℤ) ∈
      TrimmedSlice.slice (Parameters.modulus n) boundary (baseline-input.2) := by
  obtain ⟨color,hcolor,he⟩ := Finset.mem_map.mp hmem
  have hc : chartPaletteFeature C n input chart=color := by
    unfold chartPaletteFeature
    rw [← he]
    exact (ZMod.finEquiv (Parameters.modulus n)).symm_apply_apply color
  rw [hc]
  exact (Finset.mem_filter.mp hcolor).2

theorem protected_chart_carry (C : ℝ) (n : ℕ) (boundary baseline : ℤ)
    (hboundary : 0 ≤ boundary) (mark : Fin (Parameters.modulus n))
    (law : FiniteDist (Chart (ZMod (Parameters.modulus n))))
    (hsupport : ProtectedChartSupport C n boundary baseline mark law)
    (hmark : 0 ≤ (Parameters.modulus n : ℤ)-1+baseline-mark.val ∧
      (Parameters.modulus n : ℤ)-1+baseline-mark.val < Parameters.modulus n)
    (chart : Chart (ZMod (Parameters.modulus n))) (hchart : law.weight chart ≠ 0) :
    chart.2.1 ≠ 0 ∧ ∀ input : V7Input C n,
      chartIntegerLoad chart input.1 input.2/(Parameters.modulus n : ℤ)+
        ((Parameters.modulus n : ℤ)-1+baseline-input.2-chartIntegerLoad chart input.1 input.2)/
          (Parameters.modulus n : ℤ)=0 := by
  obtain ⟨hscale,hs⟩ := hsupport chart hchart
  refine ⟨hscale,fun input => ?_⟩
  have hcomp : 0 ≤ (Parameters.modulus n : ℤ)-1+baseline-input.2-
        chartIntegerLoad chart input.1 input.2 % (Parameters.modulus n : ℤ) ∧
      (Parameters.modulus n : ℤ)-1+baseline-input.2-
        chartIntegerLoad chart input.1 input.2 % (Parameters.modulus n : ℤ) < Parameters.modulus n := by
    rw [chartIntegerLoad_remainder]
    rcases hs input with hi|⟨hz,he⟩
    · have hh := (TrimmedSlice.mem_slice _ _ _ _).mp (chartPaletteFeature_mem_slice C n boundary baseline input chart hi)
      constructor <;> omega
    · have hc : chartPaletteFeature C n input chart=mark := by
        unfold chartPaletteFeature
        rw [he]
        exact (ZMod.finEquiv (Parameters.modulus n)).symm_apply_apply mark
      rw [hc,hz]
      simpa only [windowZero,sub_zero] using hmark
  exact complementary_carries _ _ _ (by exact_mod_cast (Parameters.modulus_prime n).ne_zero) hcomp.1 hcomp.2

end
end AFT.BoundaryCalibration
