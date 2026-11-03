import CurrentAFT.FourierCoordinates
import CurrentAFT.FrequencySupport
import AFT.HistogramNormalization
import CurrentAFT.SupportTail

/-!
# Exact support energy of the actual ordered homogeneous coefficient tensors

The coordinate characters diagonalize the actual finite Hoeffding
components. Complete Parseval on each selected coordinate space therefore
identifies every support-energy layer with the real color-frame tensor
energy already used by the physical local response bounds.
-/

namespace CurrentAFT.FourierSupportIsometry

open AFT FourierCoordinates FrequencySupport
open scoped BigOperators Classical

noncomputable section

set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

variable {Color Index : Type*} [Fintype Color] [Nonempty Color] [Fintype Index]
  {modulus : ℕ} [NeZero modulus]

/-- Actual Fourier transform of a selected canonical density component. -/
def componentFourier (palette : Color ≃ ZMod modulus) (mass : (Index → Color) → ℝ)
    (selected : Finset Index) (frequency : selected → ZMod modulus) : ℂ :=
  fourier palette (fun output =>
    (((FiniteDist.independent (fun _ : selected => uniformReference (Color := Color))).weight output *
      LocalTensors.restrictedComponent (fun _ : Index => uniformReference (Color := Color)) mass selected output : ℝ) : ℂ)) frequency

/-- The true selected component transforms one centered atom per slot;
all remaining dependencies of the signed mass are retained in its sum. -/
theorem componentFourier_product (palette : Color ≃ ZMod modulus) (mass : (Index → Color) → ℝ)
    (selected : Finset Index) (frequency : selected → ZMod modulus) :
    componentFourier palette mass selected frequency =
      ∑ input, (mass input : ℂ) * ∏ slot : selected,
        (if frequency slot = 0 then 0 else scalarCharacter palette (frequency slot) (input slot)) := by
  unfold componentFourier FourierCoordinates.fourier LocalTensors.restrictedComponent
  simp only [Complex.ofReal_mul, Complex.ofReal_sum, Complex.ofReal_prod,
    Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro input _
  have hproduct := complex_product_expectation
    (fun _ : selected => uniformReference (Color := Color))
    (fun slot output => (Hoeffding.centeredAtom (uniformReference (Color := Color)) (input slot) output : ℂ) *
      scalarCharacter palette (frequency slot) output)
  simp_rw [← mul_assoc, centeredAtom_fourier palette] at hproduct
  apply Eq.trans _ (congrArg ((mass input : ℂ) * ·) hproduct)
  dsimp only
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro output _
  simp only [Finset.prod_mul_distrib]
  ring

omit [Fintype Color] [Nonempty Color] in
/-- Extending a selected frequency by zero adds only trivial characters. -/
theorem character_extend (palette : Color ≃ ZMod modulus) (selected : Finset Index)
    (frequency : selected → ZMod modulus) (input : Index → Color) :
    (∏ index, scalarCharacter palette (extend selected frequency index) (input index)) =
      ∏ slot : selected, scalarCharacter palette (frequency slot) (input slot) := by
  rw [← Fintype.prod_subtype_mul_prod_subtype (fun index => index ∈ selected)]
  have hselected (slot : selected) : scalarCharacter palette (extend selected frequency slot) (input slot) =
      scalarCharacter palette (frequency slot) (input slot) := by
    unfold extend
    rw [dif_pos slot.property]
  have hrest (slot : {index // index ∉ selected}) :
      scalarCharacter palette (extend selected frequency slot.val) (input slot.val) = 1 := by
    unfold extend
    rw [dif_neg slot.property]
    simp only [scalarCharacter, map_zero, AddChar.zero_apply]
  simp_rw [hselected, hrest]
  simp only [Finset.prod_const_one, mul_one]
  apply Finset.prod_congr (by ext; simp)
  intro slot _
  rfl

/-- Its transform is precisely the actual marginal coefficient on full
selected support and zero at every frequency omitting a selected slot. -/
theorem componentFourier_formula (palette : Color ≃ ZMod modulus) (mass : (Index → Color) → ℝ)
    (selected : Finset Index) (frequency : selected → ZMod modulus) :
    componentFourier palette mass selected frequency =
      if ∀ slot, frequency slot ≠ 0 then
        fourier palette (fun input => (mass input : ℂ)) (extend selected frequency) else 0 := by
  rw [componentFourier_product]
  by_cases hnonzero : ∀ slot, frequency slot ≠ 0
  · rw [if_pos hnonzero]
    unfold FourierCoordinates.fourier
    apply Finset.sum_congr rfl
    intro input _
    rw [character_extend]
    congr 1
    apply Finset.prod_congr rfl
    intro slot _
    rw [if_neg (hnonzero slot)]
  · rw [if_neg hnonzero]
    obtain ⟨slot, hslot⟩ := not_forall.mp hnonzero
    have hzero : frequency slot = 0 := not_not.mp hslot
    apply Finset.sum_eq_zero
    intro input _
    have hproduct : (∏ other : selected,
        if frequency other = 0 then (0 : ℂ) else scalarCharacter palette (frequency other) (input other)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ slot) (by rw [if_pos hzero])
    rw [hproduct, mul_zero]

/-- Exact selected-support spectral energy equals the actual canonical
component's complete Hilbert energy. This is finite Parseval, not a norm
definition or a per-frequency estimate. -/
theorem selected_support_energy (palette : Color ≃ ZMod modulus) (mass : (Index → Color) → ℝ)
    (selected : Finset Index) :
    (∑ frequency : selected → NonzeroFrequency modulus,
      ‖fourier palette (fun input => (mass input : ℂ)) (packed selected frequency)‖ ^ 2) =
      (FiniteDist.independent (fun _ : Index => uniformReference (Color := Color))).l2Sq
        (Hoeffding.densityComponent (fun _ : Index => uniformReference (Color := Color)) mass selected) := by
  have hparseval := uniform_density_parseval palette
    (LocalTensors.restrictedComponent (fun _ : Index => uniformReference (Color := Color)) mass selected)
  change (∑ frequency : selected → ZMod modulus, ‖componentFourier palette mass selected frequency‖ ^ 2) = _ at hparseval
  simp_rw [componentFourier_formula, apply_ite (fun value : ℂ => ‖value‖ ^ 2), norm_zero, zero_pow (by decide : 2 ≠ 0)] at hparseval
  rw [← Finset.sum_filter] at hparseval
  have hreindex := (Equiv.subtypePiEquivPi (p := fun _ : selected => fun frequency : ZMod modulus => frequency ≠ 0)).sum_comp
    (fun frequency : selected → NonzeroFrequency modulus =>
      ‖fourier palette (fun input => (mass input : ℂ)) (packed selected frequency)‖ ^ 2)
  have hfiltered : (∑ frequency : selected → ZMod modulus,
      if ∀ slot, frequency slot ≠ 0 then
        ‖fourier palette (fun input => (mass input : ℂ)) (extend selected frequency)‖ ^ 2 else 0) =
      ∑ frequency : selected → NonzeroFrequency modulus,
        ‖fourier palette (fun input => (mass input : ℂ)) (packed selected frequency)‖ ^ 2 := by
    rw [← Finset.sum_filter]
    rw [Finset.sum_subtype (p := fun frequency : selected → ZMod modulus => ∀ slot, frequency slot ≠ 0)
      (Finset.univ.filter (fun frequency : selected → ZMod modulus => ∀ slot, frequency slot ≠ 0))
      (by intro frequency; simp)]
    exact hreindex
  have henergy :
      (FiniteDist.independent (fun _ : selected => uniformReference (Color := Color))).l2Sq
        (LocalTensors.restrictedComponent (fun _ : Index => uniformReference (Color := Color)) mass selected) =
      (FiniteDist.independent (fun _ : Index => uniformReference (Color := Color))).l2Sq
        (Hoeffding.densityComponent (fun _ : Index => uniformReference (Color := Color)) mass selected) := by
    unfold FiniteDist.l2Sq
    have h := LocalTensors.independent_restriction_expectation
      (fun _ : Index => uniformReference (Color := Color)) selected
      (fun output => LocalTensors.restrictedComponent (fun _ : Index => uniformReference (Color := Color)) mass selected output ^ 2)
    simp_rw [LocalTensors.restrictedComponent_eq] at h
    convert h.symm using 1
  rw [← henergy]
  rw [← hparseval]
  rw [← Finset.sum_filter] at hfiltered
  exact hfiltered.symm

/-- Exact ordered-tensor normalization at each actual Fourier support
size, including degree zero and the full output population. -/
theorem degree_support_energy (palette : Color ≃ ZMod modulus) (mass : (Index → Color) → ℝ)
    (hexchangeable : HistogramNormalization.ExchangeableMass mass)
    (degree : ℕ) (hdegree : degree ≤ Fintype.card Index) :
    (∑ frequency : Index → ZMod modulus,
      if (support frequency).card = degree then
        ‖fourier palette (fun input => (mass input : ℂ)) frequency‖ ^ 2 else 0) =
      (degree.factorial : ℝ) * BlockFock.tensorEnergy
        (LocalTensors.degreeTensor (fun _ : Index => uniformReference (Color := Color)) mass degree) /
          ((Fintype.card Index).descFactorial degree : ℝ) := by
  rw [FrequencySupport.sum_exact_support]
  simp_rw [selected_support_energy]
  exact HistogramNormalization.degree_energy_identity
    (uniformReference (Color := Color)) mass hexchangeable degree hdegree

/-- Complete actual ordered-color-tensor Fock energy. Its coefficients
are extracted from the physical signed-law polynomial by `degreeTensor`. -/
def colorFockEnergy (mass : (Index → Color) → ℝ) (radius : ℝ) : ℝ :=
  HistogramTail.fockEnergy (Fintype.card Index) radius
    (fun degree => BlockFock.tensorEnergy
      (LocalTensors.degreeTensor (fun _ : Index => uniformReference (Color := Color)) mass degree))

omit [Nonempty Color] in
/-- Regrouping all frequencies is exact and includes the highest support. -/
theorem complete_weighted_energy_by_degree (palette : Color ≃ ZMod modulus)
    (mass : (Index → Color) → ℝ) (radius : ℝ) :
    weightedSupportEnergy Finset.univ (fun frequency : Index → ZMod modulus => (support frequency).card)
      (fun frequency => ‖fourier palette (fun input => (mass input : ℂ)) frequency‖ ^ 2) radius =
      ∑ degree ∈ Finset.range (Fintype.card Index + 1), radius ^ (2 * degree) *
        ∑ frequency : Index → ZMod modulus,
          if (support frequency).card = degree then
            ‖fourier palette (fun input => (mass input : ℂ)) frequency‖ ^ 2 else 0 := by
  unfold weightedSupportEnergy
  calc
    _ = ∑ frequency : Index → ZMod modulus,
        ∑ degree ∈ Finset.range (Fintype.card Index + 1),
          if (support frequency).card = degree then
            radius ^ (2 * degree) * ‖fourier palette (fun input => (mass input : ℂ)) frequency‖ ^ 2 else 0 := by
      apply Finset.sum_congr rfl
      intro frequency _
      have hmem : (support frequency).card ∈ Finset.range (Fintype.card Index + 1) :=
        Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.card_le_univ _))
      simp only [Finset.sum_ite_eq, hmem, if_true]
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro degree _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro frequency _
      split_ifs <;> simp

/-- The all-degree comparison from the real physical ordered coefficient
norm to the actual complete weighted Fourier energy. The population
normalization is exactly `degree! * radius^(2 degree) / d^degree`. -/
theorem complete_weighted_energy_le_fock (palette : Color ≃ ZMod modulus)
    (mass : (Index → Color) → ℝ) (hexchangeable : HistogramNormalization.ExchangeableMass mass)
    (hpopulation : 0 < Fintype.card Index) (radius : ℝ) :
    weightedSupportEnergy Finset.univ (fun frequency : Index → ZMod modulus => (support frequency).card)
      (fun frequency => ‖fourier palette (fun input => (mass input : ℂ)) frequency‖ ^ 2)
      (radius / Real.sqrt (Real.exp 1)) ≤ colorFockEnergy mass radius := by
  rw [complete_weighted_energy_by_degree]
  unfold colorFockEnergy HistogramTail.fockEnergy
  apply Finset.sum_le_sum
  intro degree hdegree
  have hdegreeBound : degree ≤ Fintype.card Index := by
    exact Nat.lt_succ_iff.mp (Finset.mem_range.mp hdegree)
  rw [degree_support_energy palette mass hexchangeable degree hdegreeBound]
  let energy := BlockFock.tensorEnergy
    (LocalTensors.degreeTensor (fun _ : Index => uniformReference (Color := Color)) mass degree)
  have henergy : 0 ≤ energy := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hweight := HistogramTail.reciprocal_descFactorial_le (Fintype.card Index) degree hpopulation hdegreeBound
  have hscale : 0 ≤ (radius / Real.sqrt (Real.exp 1)) ^ (2 * degree) := by
    rw [pow_mul]
    exact pow_nonneg (sq_nonneg _) _
  have hfactor : 0 ≤ (degree.factorial : ℝ) * energy := mul_nonneg (Nat.cast_nonneg _) henergy
  have hcharge : (radius / Real.sqrt (Real.exp 1)) ^ (2 * degree) * Real.exp 1 ^ degree = radius ^ (2 * degree) := by
    simp only [pow_mul, div_pow, Real.sq_sqrt (Real.exp_pos 1).le]
    have hnonzero : Real.exp 1 ≠ 0 := (Real.exp_pos 1).ne'
    field_simp
  calc
    _ = ((radius / Real.sqrt (Real.exp 1)) ^ (2 * degree) * ((degree.factorial : ℝ) * energy)) *
        (1 / ((Fintype.card Index).descFactorial degree : ℝ)) := by ring
    _ ≤ ((radius / Real.sqrt (Real.exp 1)) ^ (2 * degree) * ((degree.factorial : ℝ) * energy)) *
        (Real.exp 1 ^ degree / (Fintype.card Index : ℝ) ^ degree) :=
      mul_le_mul_of_nonneg_left hweight (mul_nonneg hscale hfactor)
    _ = ((degree.factorial : ℝ) * energy / (Fintype.card Index : ℝ) ^ degree) *
        ((radius / Real.sqrt (Real.exp 1)) ^ (2 * degree) * Real.exp 1 ^ degree) := by ring
    _ = _ := by rw [hcharge]; ring

end

end CurrentAFT.FourierSupportIsometry
