import AFT.ReferenceCharge

/-! # Conditioning the actual beta-reference histogram on total charge -/
namespace AFT
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace FiniteDist
variable {State : Type*} [Fintype State] [Nonempty State]

theorem independent_uniform {Slot : Type*} [Fintype Slot] [DecidableEq Slot] :
    independent (fun _ : Slot => uniform State)=uniform (Slot → State) := by
  ext word
  simp only [independent,uniform_weight,Finset.prod_const,Finset.card_univ,Fintype.card_fun,
    Nat.cast_pow,inv_pow]

theorem uniform_eventMass (event : State → Prop) :
    (uniform State).eventMass event=(Fintype.card {point // event point} : ℝ)/Fintype.card State := by
  simp only [eventMass,uniform_weight]
  calc
    _ = (∑ point,if event point then (1 : ℝ) else 0)*(Fintype.card State : ℝ)⁻¹ := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro point _
      split_ifs <;> simp
    _ = _ := by simp [← Fintype.card_subtype,div_eq_mul_inv]

/-- Restriction of the exact uniform law is the exact uniform law of the
nonempty event, pushed back to the original finite state space. -/
theorem uniform_condition (event : State → Prop) [Nonempty {point // event point}] :
    (uniform State).condition event
      (by rw [uniform_eventMass]; exact div_pos (Nat.cast_pos.mpr Fintype.card_pos) (Nat.cast_pos.mpr Fintype.card_pos))=
      (uniform {point // event point}).map Subtype.val := by
  ext point
  rw [map_weight]
  simp only [condition,uniform_weight,uniform_eventMass]
  by_cases he : event point
  · have hsub : (∑ x : {point // event point},if (x : State)=point then
        (Fintype.card {point // event point} : ℝ)⁻¹ else 0)=(Fintype.card {point // event point} : ℝ)⁻¹ := by
      have hh : ∀ x : {point // event point},(x : State)=point ↔ x=⟨point,he⟩ := fun x => ⟨fun h => Subtype.ext h,fun h => congrArg Subtype.val h⟩
      simp only [hh,Finset.sum_ite_eq',Finset.mem_univ,if_true]
    rw [if_pos he,hsub]
    have hcard : (Fintype.card State : ℝ)≠0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    field_simp
  · rw [if_neg he,zero_div]
    symm
    apply Finset.sum_eq_zero
    intro x _
    have hne : (x : State)≠point := fun h => he (h ▸ x.property)
    simp only [hne,if_false]

end FiniteDist

namespace HistogramGenerating
variable {G : Type*} [Fintype G] [AddCommGroup G]

/-- An actual iid uniform histogram has each total charge with probability
exactly `1/q`, before or after the histogram pushforward. -/
theorem uniform_histogram_charge (N : ℕ) (hN : 0<N) (required : G) :
    ((FiniteDist.independent (fun _ : Fin N => FiniteDist.uniform G)).map histogram).eventMass
      (fun hist => histogramCharge N hist=required)=(Fintype.card G : ℝ)⁻¹ := by
  rw [FiniteDist.eventMass_map]
  simp only [histogramCharge_histogram]
  have hu : (FiniteDist.uniform G).uniformDeviation=0 := by
    simp [FiniteDist.uniformDeviation,FiniteDist.uniform_weight]
  have hh := FiniteDist.sumLaw_deviation_le (FiniteDist.uniform G) N required
  rw [hu,zero_pow (Nat.ne_of_gt hN)] at hh
  have he := sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm hh (abs_nonneg _)))
  change ((FiniteDist.independent (fun _ : Fin N => FiniteDist.uniform G)).map (fun word => ∑ i,word i)).weight required=_
  rw [FiniteDist.independent_sum_map,he]

/-- The charge-zero uniform histogram is precisely the histogram of the
uniform zero-sum vector, not an auxiliary conditional reference. -/
theorem uniform_histogram_condition_zero (N : ℕ) (hN : 0<N) :
    (((FiniteDist.independent (fun _ : Fin N => FiniteDist.uniform G)).map histogram).condition
      (fun hist => histogramCharge N hist=0)
      (by rw [uniform_histogram_charge N hN]; positivity))=(uniformZeroSum N G).map histogram := by
  have hevent : (fun word : Fin N → G => histogramCharge N (histogram word)=0)=
      fun word => (∑ i,word i)=0 := by funext word; rw [histogramCharge_histogram]
  have hp : 0<(FiniteDist.independent (fun _ : Fin N => FiniteDist.uniform G)).eventMass
      (fun word => histogramCharge N (histogram word)=0) := by
    rw [← FiniteDist.eventMass_map (FiniteDist.independent (fun _ : Fin N => FiniteDist.uniform G)) histogram (fun hist => histogramCharge N hist=0),uniform_histogram_charge N hN]
    positivity
  rw [← FiniteDist.condition_map _ histogram _ hp]
  simp only [hevent,FiniteDist.independent_uniform,FiniteDist.uniform_condition,uniformZeroSum]
end HistogramGenerating

namespace V7Calibration
open GaussianSource HistogramGenerating Filter
open scoped Topology
attribute [local instance] actualModulusNeZero
local instance referenceChargeConditionFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _

/-- Any finite beta sampler inherits the charge/mixture interchange bound.
The source may depend on the security parameter and may have arbitrarily
many atoms; the estimate loses no source-cardinality factor. -/
theorem actual_reference_mix_charge_eventually (C : ℝ) (hC : 1≤C) :
    ∀ᶠ n in atTop,∀ (Source : Type*) [Fintype Source] (source : FiniteDist Source)
      (beta : Source → ℝ) (required : Fin (Parameters.modulus n)),
      let law := fun index => actualPositiveReferenceHistogram C n (beta index)
      let event := fun hist => histogramCharge (Parameters.dimension n) hist=required
      ∃ hpos : 0<(source.mix law).eventMass event,∃ hlaw : ∀ index,0<(law index).eventMass event,
        (∑ hist,|((source.mix (fun index => (law index).condition event (hlaw index))).weight hist)-
          ((source.mix law).condition event hpos).weight hist|)≤4*actualReferenceChargeError C n := by
  filter_upwards [actual_reference_charge_eventually C hC,(actual_reference_charge_error_negligible C hC) 1,
    eventually_ge_atTop 2] with n hcharge hsmall hn Source _ source beta required
  have hn2 : (2 : ℝ)≤n := by exact_mod_cast hn
  have herr : 0≤actualReferenceChargeError C n := by unfold actualReferenceChargeError actualBoundaryFraction; positivity
  apply FiniteDist.mix_condition_l1 source (fun index => actualPositiveReferenceHistogram C n (beta index))
    (fun hist => histogramCharge (Parameters.dimension n) hist=required) (Parameters.modulus n : ℝ)⁻¹
    (actualReferenceChargeError C n) (inv_pos.mpr (by exact_mod_cast (Parameters.modulus_prime n).pos)) herr
  · rw [abs_of_nonneg herr,pow_one] at hsmall
    exact hsmall.trans (one_div_le_one_div_of_le (by norm_num) hn2)
  · intro index
    simpa only [div_inv_eq_mul,mul_comm] using hcharge (beta index) required

end V7Calibration
end
end AFT
