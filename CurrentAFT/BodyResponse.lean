import AFT.FiniteProbability

/-!
# The actual cyclic body channel on joint root/control inputs

For a root draw `r`, the ordinary body output is the center plus the
cyclic shift `shift r`. The signed profile below is obtained by summing
the actual joint input over that channel. The input function can depend
arbitrarily on the root draw and the center, and can take values in any
real normed space, including a Hilbert space of retained coordinates.

The proof derives the operator estimate from elementary center-height
and primary-atom bounds. It never assumes the desired norm estimate,
factors the joint input, or divides by a root probability. In particular,
zero-probability root atoms cause no loss. This supplies the ordinary-body
local estimate used in `lem:df-actual-cycle-defect`; the selected paired
leg channel and its global pattern assembly remain separate obligations.
-/

namespace CurrentAFT

namespace BodyResponse

open AFT
open scoped BigOperators

noncomputable section

variable {Root Value : Type*} [Fintype Root]
  [NormedAddCommGroup Value] [NormedSpace ℝ Value]

private theorem weighted_norm_sum_sq_le (weight : Root → ℝ) (value : Root → Value)
    (hweight : ∀ root, 0 ≤ weight root) :
    ‖∑ root, weight root • value root‖ ^ 2 ≤
      (∑ root, weight root) * ∑ root, weight root * ‖value root‖ ^ 2 := by
  have hnorm : ‖∑ root, weight root • value root‖ ≤ ∑ root, weight root * ‖value root‖ := by
    calc
      _ ≤ ∑ root, ‖weight root • value root‖ := norm_sum_le _ _
      _ = _ := by simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hweight _)]
  have hcauchy : (∑ root, weight root * ‖value root‖) ^ 2 ≤
      (∑ root, weight root) * ∑ root, weight root * ‖value root‖ ^ 2 := by
    apply Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul
    · intro root _
      exact hweight root
    · intro root _
      exact mul_nonneg (hweight root) (sq_nonneg _)
    · intro root _
      ring
  exact (pow_le_pow_left₀ (norm_nonneg _) hnorm 2).trans hcauchy

variable {modulus : ℕ} [NeZero modulus]

/-- Actual root averaging of the cyclically translated center profile.
All remaining root coordinates may be retained in the single index `Root`. -/
def jointBodyProfile (rootLaw : FiniteDist Root) (shift : Root → ZMod modulus)
    (centerLaw : FiniteDist (ZMod modulus)) (jointInput : Root → ZMod modulus → Value)
    (output : ZMod modulus) : Value :=
  ∑ root, (rootLaw.weight root * centerLaw.weight (output - shift root)) •
    jointInput root (output - shift root)

/-- The full joint input norm is taken once under the product reference;
the function itself is not required to be a product. -/
def jointBodyInputEnergy (rootLaw : FiniteDist Root) (centerLaw : FiniteDist (ZMod modulus))
    (jointInput : Root → ZMod modulus → Value) : ℝ :=
  ∑ root, rootLaw.weight root *
    ∑ center, centerLaw.weight center * ‖jointInput root center‖ ^ 2

theorem jointBodyProfile_norm_sq_le (rootLaw : FiniteDist Root) (shift : Root → ZMod modulus)
    (centerLaw : FiniteDist (ZMod modulus)) (jointInput : Root → ZMod modulus → Value)
    (upper : ℝ) (hupper : ∀ center, centerLaw.weight center ≤ upper)
    (output : ZMod modulus) :
    ‖jointBodyProfile rootLaw shift centerLaw jointInput output‖ ^ 2 ≤
      upper * ∑ root, rootLaw.weight root * centerLaw.weight (output - shift root) *
        ‖jointInput root (output - shift root)‖ ^ 2 := by
  have hweights (root) : 0 ≤ rootLaw.weight root * centerLaw.weight (output - shift root) :=
    mul_nonneg (rootLaw.nonneg root) (centerLaw.nonneg _)
  have hcauchy := weighted_norm_sum_sq_le
    (fun root => rootLaw.weight root * centerLaw.weight (output - shift root))
    (fun root => jointInput root (output - shift root)) hweights
  have hmass : (∑ root, rootLaw.weight root * centerLaw.weight (output - shift root)) ≤ upper := by
    calc
      _ ≤ ∑ root, rootLaw.weight root * upper :=
        Finset.sum_le_sum (fun root _ => mul_le_mul_of_nonneg_left (hupper _) (rootLaw.nonneg root))
      _ = upper := by rw [← Finset.sum_mul, rootLaw.sum_one, one_mul]
  exact hcauchy.trans (mul_le_mul_of_nonneg_right hmass
    (Finset.sum_nonneg (fun root _ => mul_nonneg (hweights root) (sq_nonneg _))))

/-- The cyclic channel has squared norm at most `upper / lower` from
the genuine joint input norm to the output profile norm. This includes
arbitrary retained Hilbert-valued inputs without an extra dimension factor. -/
theorem joint_body_profile_energy_le (rootLaw : FiniteDist Root) (shift : Root → ZMod modulus)
    (centerLaw primaryLaw : FiniteDist (ZMod modulus))
    (jointInput : Root → ZMod modulus → Value) (upper lower : ℝ)
    (hupperNonneg : 0 ≤ upper) (hlowerPositive : 0 < lower)
    (hupper : ∀ center, centerLaw.weight center ≤ upper)
    (hlower : ∀ output, lower ≤ primaryLaw.weight output) :
    (∑ output, ‖jointBodyProfile rootLaw shift centerLaw jointInput output‖ ^ 2 /
      primaryLaw.weight output) ≤
        (upper / lower) * jointBodyInputEnergy rootLaw centerLaw jointInput := by
  have hpoint (output : ZMod modulus) :
      ‖jointBodyProfile rootLaw shift centerLaw jointInput output‖ ^ 2 /
        primaryLaw.weight output ≤
      (upper / lower) * ∑ root, rootLaw.weight root * centerLaw.weight (output - shift root) *
        ‖jointInput root (output - shift root)‖ ^ 2 := by
    have hprimary : 0 < primaryLaw.weight output := hlowerPositive.trans_le (hlower output)
    have hinputNonneg : 0 ≤ ∑ root, rootLaw.weight root * centerLaw.weight (output - shift root) *
        ‖jointInput root (output - shift root)‖ ^ 2 :=
      Finset.sum_nonneg (fun root _ =>
        mul_nonneg (mul_nonneg (rootLaw.nonneg root) (centerLaw.nonneg _)) (sq_nonneg _))
    calc
      _ ≤ (upper * ∑ root, rootLaw.weight root * centerLaw.weight (output - shift root) *
          ‖jointInput root (output - shift root)‖ ^ 2) / primaryLaw.weight output :=
        div_le_div_of_nonneg_right
          (jointBodyProfile_norm_sq_le rootLaw shift centerLaw jointInput upper hupper output) hprimary.le
      _ ≤ (upper * ∑ root, rootLaw.weight root * centerLaw.weight (output - shift root) *
          ‖jointInput root (output - shift root)‖ ^ 2) / lower :=
        div_le_div_of_nonneg_left (mul_nonneg hupperNonneg hinputNonneg) hlowerPositive (hlower output)
      _ = _ := by ring
  calc
    _ ≤ ∑ output, (upper / lower) *
        ∑ root, rootLaw.weight root * centerLaw.weight (output - shift root) *
          ‖jointInput root (output - shift root)‖ ^ 2 :=
      Finset.sum_le_sum (fun output _ => hpoint output)
    _ = _ := by
      rw [← Finset.mul_sum, Finset.sum_comm]
      simp only [mul_assoc, ← Finset.mul_sum]
      have htranslation (root : Root) :
          (∑ output : ZMod modulus, centerLaw.weight (output - shift root) *
            ‖jointInput root (output - shift root)‖ ^ 2) =
          ∑ center, centerLaw.weight center * ‖jointInput root center‖ ^ 2 :=
        (Equiv.subRight (shift root)).sum_comp
          (fun center => centerLaw.weight center * ‖jointInput root center‖ ^ 2)
      simp only [htranslation, jointBodyInputEnergy]

/-- Instantiating the current proposal's elementary atom bounds gives
the exact constant eight, independently of the modulus and root atoms. -/
theorem joint_body_profile_energy_eight (rootLaw : FiniteDist Root) (shift : Root → ZMod modulus)
    (centerLaw primaryLaw : FiniteDist (ZMod modulus))
    (jointInput : Root → ZMod modulus → Value)
    (hcenter : ∀ center, centerLaw.weight center ≤ 4 / (modulus : ℝ))
    (hprimary : ∀ output, 1 / (2 * (modulus : ℝ)) ≤ primaryLaw.weight output) :
    (∑ output, ‖jointBodyProfile rootLaw shift centerLaw jointInput output‖ ^ 2 /
      primaryLaw.weight output) ≤
        8 * jointBodyInputEnergy rootLaw centerLaw jointInput := by
  have hmodulus : (0 : ℝ) < modulus := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne modulus))
  have hbound := joint_body_profile_energy_le rootLaw shift centerLaw primaryLaw jointInput
    (4 / (modulus : ℝ)) (1 / (2 * (modulus : ℝ))) (by positivity) (by positivity) hcenter hprimary
  have hratio : (4 / (modulus : ℝ)) / (1 / (2 * (modulus : ℝ))) = 8 := by
    field_simp
    norm_num
  simpa only [hratio] using hbound

/-- The fixed-root ordinary-body score is the same actual cyclic
translation, without any root averaging. -/
theorem fixed_root_body_energy_eight (root : ZMod modulus)
    (centerLaw primaryLaw : FiniteDist (ZMod modulus)) (input : ZMod modulus → Value)
    (hcenter : ∀ center, centerLaw.weight center ≤ 4 / (modulus : ℝ))
    (hprimary : ∀ output, 1 / (2 * (modulus : ℝ)) ≤ primaryLaw.weight output) :
    (∑ output, ‖centerLaw.weight (output - root) • input (output - root)‖ ^ 2 /
      primaryLaw.weight output) ≤
        8 * ∑ center, centerLaw.weight center * ‖input center‖ ^ 2 := by
  simpa only [jointBodyProfile, jointBodyInputEnergy, FiniteDist.uniform_weight,
    Fintype.sum_unique, Fintype.card_unique, Nat.cast_one, inv_one, one_mul] using
    joint_body_profile_energy_eight (FiniteDist.uniform Unit) (fun _ => root)
      centerLaw primaryLaw (fun _ => input) hcenter hprimary

end

end BodyResponse

end CurrentAFT
