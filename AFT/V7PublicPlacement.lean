import AFT.PublicPlacement
import AFT.V7Blocks

/-! # Actual public placement of the shared V7 queue -/

namespace AFT.GaussianSource

open scoped BigOperators Classical
open V7Calibration FiniteDist

noncomputable section

set_option backward.isDefEq.respectTransparency false

theorem modulus_le_bodies (parameter : ℕ) : Parameters.modulus parameter ≤ Parameters.bodies parameter := by
  have hb : (0 : ℝ) < Parameters.bodies parameter := by exact_mod_cast Parameters.bodies_positive parameter
  have hh := (body_rates_le_quarter parameter).2.trans (by norm_num : (1 : ℝ) / 4 ≤ 1)
  unfold queueRate at hh
  exact_mod_cast (div_le_one hb).mp hh

/-- A fixed mask of exactly q body indices, subsequently moved by a uniform
public permutation independently of the single hidden queue draw. -/
def actualQueueSelection (parameter : ℕ) : Finset (blockIndex parameter) :=
  Finset.univ.map ((Fin.castLEEmb (modulus_le_bodies parameter)).trans
    (blockIndexNumbering parameter).symm.toEmbedding)

@[simp] theorem actualQueueSelection_card (parameter : ℕ) :
    (actualQueueSelection parameter).card = Parameters.modulus parameter := by
  simp only [actualQueueSelection, Finset.card_map, Finset.card_univ, Fintype.card_fin]

def actualQueuePlacementLaw (parameter : ℕ) :
    FiniteDist (Window (queueCutoff parameter) × Equiv.Perm (blockIndex parameter)) :=
  (windowGaussian parameter (queueCutoff parameter)).prod (uniform (Equiv.Perm (blockIndex parameter)))

def actualQueueShifts (parameter : ℕ)
    (sample : Window (queueCutoff parameter) × Equiv.Perm (blockIndex parameter)) : blockIndex parameter → ℤ :=
  sharedQueueShift (actualQueueSelection parameter) sample.1 sample.2

/-- The common queue satisfies every physical block's deterministic cutoff. -/
theorem actualQueueShifts_bound (parameter : ℕ)
    (sample : Window (queueCutoff parameter) × Equiv.Perm (blockIndex parameter)) (index : blockIndex parameter) :
    |actualQueueShifts parameter sample index| ≤ (queueCutoff parameter : ℤ) :=
  (sharedQueueShift_bound _ _ _ _).trans (abs_le.mpr (Finset.mem_Icc.mp sample.1.property))

/-- The complete queue field has sum q times its one shared realized value. -/
theorem actualQueueShifts_sum (parameter : ℕ)
    (sample : Window (queueCutoff parameter) × Equiv.Perm (blockIndex parameter)) :
    (∑ index, actualQueueShifts parameter sample index) = Parameters.modulus parameter * (sample.1 : ℤ) := by
  unfold actualQueueShifts sharedQueueShift
  rw [Equiv.sum_comp sample.2 (fun index => if index ∈ actualQueueSelection parameter then (sample.1 : ℤ) else 0)]
  simp only [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul, actualQueueSelection_card]

/-- Each body index has exactly the optional queue marginal appearing in
`extraBlur`. This says nothing about independence between different indices. -/
theorem actualQueueShifts_expectation (parameter : ℕ) (index : blockIndex parameter) (value : ℤ → ℝ) :
    (actualQueuePlacementLaw parameter).expectation (fun sample => value (actualQueueShifts parameter sample index)) =
      (optional (windowGaussian parameter (queueCutoff parameter)) (queueRate parameter)
        (by unfold queueRate; positivity)
        ((body_rates_le_quarter parameter).2.trans (by norm_num))).expectation
          (fun sample => value (optionalShift sample)) := by
  haveI : Nonempty (blockIndex parameter) := Fintype.card_pos_iff.mp (by
    simpa only [blockIndex_card] using Parameters.bodies_positive parameter)
  have hh := sharedQueue_optional_expectation (actualQueueSelection parameter)
    (windowGaussian parameter (queueCutoff parameter)) (fun sample => (sample : ℤ)) index value
  have hshift (sample : Option (Window (queueCutoff parameter))) :
      sample.elim 0 (fun sample => (sample : ℤ)) = optionalShift sample := by
    cases sample <;> rfl
  simp_rw [hshift] at hh
  simpa only [actualQueueSelection_card, blockIndex_card, queueRate,
    actualQueuePlacementLaw, actualQueueShifts] using hh

end
end AFT.GaussianSource
