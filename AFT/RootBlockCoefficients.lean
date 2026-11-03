import AFT.AttachedRootBackgroundChannel
import AFT.GroupedRootInput
import AFT.PhysicalRootFactorization

/-! # Actual centered coefficients of every physical root block -/
namespace AFT.V7Calibration
open GaussianSource PhysicalBlockTensors RepresentedPolynomial Filter
open scoped BigOperators Classical Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
local instance rootBlockCoefficientFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _
local instance rootBlockCoefficientSumDecEq {α β : Type*} : DecidableEq (α ⊕ β) := Classical.decEq _
local instance rootBlockCoefficientSubtypeDecEq {α : Type*} (selected : Finset α) : DecidableEq selected := Classical.decEq _

def actualCenteredRootBlock (C : ℝ) (n : ℕ) (beta : ℝ) (index : blockIndex n)
    (queue : ℤ) (root : Window (v7RootCutoff n)) : (blockSlots n index → Fin (Parameters.modulus n)) → ℝ :=
  match index with
  | .inl _ => actualCenteredRootTriple C n beta queue root
  | .inr _ => fun word => centeredRootBodyProfile C n beta queue root (word 0)

def rootBlockFullCost (n : ℕ) (index : blockIndex n) (queue : ℤ) : ℝ :=
  match index with
  | .inl _ => Real.sqrt (64*24640*175104)/(n : ℝ)^4
  | .inr _ => rootBodyFullCost n queue

theorem rootBlockFullCost_nonneg (n : ℕ) (index : blockIndex n) (queue : ℤ) :
    0 ≤ rootBlockFullCost n index queue := by
  cases index with
  | inl _ => exact div_nonneg (Real.sqrt_nonneg _) (by positivity)
  | inr _ => exact rootBodyFullCost_nonneg _ _

/-- The centered mass is exactly the original block with its own root
centered under the genuine one-root marginal. -/
theorem actual_centered_root_block_eq_eventually (C : ℝ) (hC : 1 ≤ C) (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ n in atTop,(Parameters.legs n : ℝ)/(2*Parameters.dimension n)≤beta n ∧
      beta n≤2*(Parameters.legs n : ℝ)/Parameters.dimension n) :
    ∀ᶠ n in atTop,∀ index : blockIndex n,∀ queue : ℤ,|queue|≤(queueCutoff n : ℤ) →
    ∀ root : Window (v7RootCutoff n),∀ word : blockSlots n index → Fin (Parameters.modulus n),
      actualCenteredRootBlock C n (beta n) index queue root word =
        (actualBlockFamily C n (beta n) (fun _ => root) (fun _ => queue) index).weight word-
          ∑ other : Window (v7RootCutoff n),(bodyRootReference n).weight other*
            (actualBlockFamily C n (beta n) (fun _ => other) (fun _ => queue) index).weight word := by
  filter_upwards [actual_shifted_body_law_eventually C hC beta hbeta] with n hb index queue hq root word
  cases index with
  | inl leg => exact actualCenteredRootTriple_eq C n (beta n) queue root word
  | inr body =>
    have hm (other : Window (v7RootCutoff n)) :
        (actualBlockFamily C n (beta n) (fun _ => other) (fun _ => queue) (.inr body)).weight word =
          (actualShiftedBodyLaw C n (beta n) (other+queue)).weight (word 0) := by
      exact FiniteDist.map_equiv_weight (actualShiftedBodyLaw C n (beta n) (other+queue))
        (Equiv.funUnique (Fin 1) (Fin (Parameters.modulus n))).symm word
    simp only [hm,actualCenteredRootBlock,centeredRootBodyProfile]

/-- Uniform full Hilbert budgets include the ordinary root variance, the
few shifted bodies, and the genuine shared-source attached triple. -/
theorem actual_centered_root_block_energy_eventually (C : ℝ) (hC : 1 ≤ C) (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ n in atTop,(Parameters.legs n : ℝ)/(2*Parameters.dimension n)≤beta n ∧
      beta n≤2*(Parameters.legs n : ℝ)/Parameters.dimension n) :
    ∀ᶠ n in atTop,∀ index : blockIndex n,∀ queue : ℤ,|queue|≤(queueCutoff n : ℤ) →
      (bodyRootReference n).expectation (fun root =>
        (FiniteDist.independent (fun _ : blockSlots n index => actualPrimaryLaw C n (beta n))).l2Sq
          (fun word => actualCenteredRootBlock C n (beta n) index queue root word/
            (FiniteDist.independent (fun _ : blockSlots n index => actualPrimaryLaw C n (beta n))).weight word)) ≤
        rootBlockFullCost n index queue^2 := by
  filter_upwards [actual_centered_root_triple_energy_eventually C hC beta hbeta,
    actual_root_body_density_variance_eventually C hC beta hbeta,eventually_ge_atTop 1]
    with n ht hb hn index queue hq
  cases index with
  | inl leg =>
    change (bodyRootReference n).expectation (fun root =>
      (FiniteDist.independent (fun _ : Fin 3 => actualPrimaryLaw C n (beta n))).l2Sq
        (fun word => actualCenteredRootTriple C n (beta n) queue root word/
          (FiniteDist.independent (fun _ : Fin 3 => actualPrimaryLaw C n (beta n))).weight word)) ≤ _
    calc
      _ ≤ (bodyRootReference n).expectation (fun _ => (64*24640*175104)/(n : ℝ)^8) :=
        Finset.sum_le_sum fun root _ => mul_le_mul_of_nonneg_left (ht queue hq root) (FiniteDist.nonneg _ _)
      _ = _ := by
        rw [FiniteDist.expectation_const]
        simp only [rootBlockFullCost,div_pow,Real.sq_sqrt (by norm_num : (0 : ℝ)≤64*24640*175104)]
        ring
  | inr body =>
    have hoff (root : Window (v7RootCutoff n)) : |(root : ℤ)+queue| ≤ maxBodyShift C n := by
      have hh := actualBodyBranch_shift_bound C n (root : ℤ) queue
        (abs_le.mpr (Finset.mem_Icc.mp root.property)) hq (.inl ())
      simpa only [actualSourceShift,add_zero] using hh
    have he (root : Window (v7RootCutoff n)) :
        (FiniteDist.independent (fun _ : blockSlots n (.inr body) => actualPrimaryLaw C n (beta n))).l2Sq
          (fun word => actualCenteredRootBlock C n (beta n) (.inr body) queue root word/
            (FiniteDist.independent (fun _ : blockSlots n (.inr body) => actualPrimaryLaw C n (beta n))).weight word) =
        (actualPrimaryLaw C n (beta n)).l2Sq (rootBodyDensityMatrix C n (beta n) queue root) := by
      unfold FiniteDist.l2Sq FiniteDist.expectation FiniteDist.independent
      simp only [blockSlots,actualCenteredRootBlock,Fin.prod_univ_one]
      exact (Equiv.funUnique (Fin 1) (Fin (Parameters.modulus n))).sum_comp
        (fun color => (actualPrimaryLaw C n (beta n)).weight color*
          (centeredRootBodyProfile C n (beta n) queue root color/(actualPrimaryLaw C n (beta n)).weight color)^2)
    simp_rw [he]
    change (bodyRootReference n).expectation (fun root =>
      (actualPrimaryLaw C n (beta n)).expectation (fun color =>
        rootBodyDensityMatrix C n (beta n) queue root color ^ 2)) ≤ _
    rw [FiniteDist.expectation_comm]
    exact (hb queue hoff).1

def actualRootBlockCoefficient (C : ℝ) (n : ℕ) (beta : ℝ) (index : blockIndex n)
    (queue : ℤ) (selected : Finset (blockSlots n index)) (root : Window (v7RootCutoff n)) :
    (selected → Fin (Parameters.modulus n)) → ℝ :=
  LocalTensors.referenceRestrictedComponent (fun _ : blockSlots n index => actualPrimaryLaw C n beta)
    (fun _ => actualReferenceLaw C n beta) (actualCenteredRootBlock C n beta index queue root) selected

/-- Every actual selected coefficient has the local Hilbert bound used by
the grouped tensor construction, with no extra alphabet factor. -/
theorem actual_root_block_coefficient_eventually (C : ℝ) (hC : 1 ≤ C) (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ n in atTop,(Parameters.legs n : ℝ)/(2*Parameters.dimension n)≤beta n ∧
      beta n≤2*(Parameters.legs n : ℝ)/Parameters.dimension n) :
    ∀ᶠ n in atTop,∀ index : blockIndex n,∀ queue : ℤ,|queue|≤(queueCutoff n : ℤ) →
    ∀ selected : Finset (blockSlots n index),
      (FiniteDist.independent (fun _ : selected => actualPrimaryLaw C n (beta n))).expectation
        (fun word => (bodyRootReference n).l2Sq (fun root => actualRootBlockCoefficient C n (beta n) index queue selected root word)) ≤
        ((16 : ℝ)^selected.card*rootBlockFullCost n index queue)^2 ∧
      ∀ root,Hoeffding.Canonical (fun _ : selected => actualPrimaryLaw C n (beta n)) Finset.univ
        (actualRootBlockCoefficient C n (beta n) index queue selected root) := by
  filter_upwards [actual_centered_root_block_energy_eventually C hC beta hbeta,
    actual_reference_laws_eventually C hC beta hbeta,
    actual_reference_probability_eventually C hC beta hbeta,
    actual_primary_law_quarter_lower_eventually C hC beta hbeta] with n he hl hr hp index queue hq selected
  have hmod : (0 : ℝ)<Parameters.modulus n := Nat.cast_pos.mpr (Parameters.modulus_prime n).pos
  have hp0 (color) : 0<(actualPrimaryLaw C n (beta n)).weight color := lt_of_lt_of_le (by positivity) (hp color)
  have hcompare (color) : (actualReferenceLaw C n (beta n)).weight color≤8*(actualPrimaryLaw C n (beta n)).weight color := by
    rw [hl.2.2]
    have ht := (hr.1 color).2
    have hh := hp color
    change 1/(4*(Parameters.modulus n : ℝ)) ≤ _ at hh
    calc
      _ ≤ 2/(Parameters.modulus n : ℝ) := ht
      _ = 8*(1/(4*(Parameters.modulus n : ℝ))) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hh (by norm_num)
  refine ⟨?_,fun root => LocalTensors.referenceRestrictedComponent_canonical _ _ (fun _ => hp0) _ _⟩
  unfold actualRootBlockCoefficient
  change (FiniteDist.independent (fun _ : selected => actualPrimaryLaw C n (beta n))).expectation
    (fun word => (bodyRootReference n).expectation (fun root =>
      LocalTensors.referenceRestrictedComponent (fun _ : blockSlots n index => actualPrimaryLaw C n (beta n))
        (fun _ => actualReferenceLaw C n (beta n))
        (actualCenteredRootBlock C n (beta n) index queue root) selected word ^ 2)) ≤ _
  rw [FiniteDist.expectation_comm]
  have hh := LocalTensors.referenceRestrictedComponent_hilbert_square_le
    (fun _ : blockSlots n index => actualPrimaryLaw C n (beta n)) (fun _ => actualReferenceLaw C n (beta n))
    (fun _ => hp0) (bodyRootReference n) (actualCenteredRootBlock C n (beta n) index queue)
    selected 8 (by norm_num) (fun _ => hcompare)
  apply hh.trans
  norm_num only [show (2 : ℝ)*8=16 by norm_num]
  exact (mul_le_mul_of_nonneg_left (he index queue hq) (sq_nonneg _)).trans_eq (by rw [mul_pow])

end
end AFT.V7Calibration
