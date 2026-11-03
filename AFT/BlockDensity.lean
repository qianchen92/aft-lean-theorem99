import AFT.SelectionBound
import AFT.LocalResponse
import AFT.Hoeffding

/-! # Concrete endpoint and shared-source attachment L2 estimates -/

namespace AFT
namespace BlockDensity

open scoped BigOperators Classical

variable {First Second Body Source Coordinate Slot : Type*}
variable [Fintype First] [Fintype Second] [Fintype Body] [Fintype Source]

/-- A positive finite mass has L2 energy at most its actual maximum density
ratio times its total mass. -/
theorem profile_energy_le_ratio (reference mass : First → ℝ) (bound : ℝ)
    (href : ∀ point, 0 < reference point) (hmass : ∀ point, 0 ≤ mass point)
    (hratio : ∀ point, mass point ≤ bound * reference point) :
    profileSquareNorm reference mass ≤ bound * ∑ point, mass point := by
  unfold profileSquareNorm
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro point _
  apply (div_le_iff₀ (href point)).mpr
  nlinarith [mul_le_mul_of_nonneg_left (hratio point) (hmass point)]

/-- Squared profile norm of an actual ordered endpoint pair. -/
noncomputable def pairEnergy (firstReference : First → ℝ) (secondReference : Second → ℝ)
    (mass : First → Second → ℝ) : ℝ :=
  ∑ first, ∑ second, mass first second ^ 2 / (firstReference first * secondReference second)

/-- A diffuse endpoint sublaw has its full finite joint norm controlled by
its point mass and the actual target reference lower bounds. -/
theorem diffuse_pair_energy_le (firstReference : First → ℝ) (secondReference : Second → ℝ)
    (mass : First → Second → ℝ) (firstLower secondLower upper : ℝ)
    (hfirst : 0 < firstLower) (hsecond : 0 < secondLower) (hu : 0 ≤ upper)
    (hrefFirst : ∀ first, firstLower ≤ firstReference first)
    (hrefSecond : ∀ second, secondLower ≤ secondReference second)
    (hmass : ∀ first second, 0 ≤ mass first second)
    (hupper : ∀ first second, mass first second ≤ upper)
    (htotal : (∑ first, ∑ second, mass first second) ≤ 1) :
    pairEnergy firstReference secondReference mass ≤ upper / (firstLower * secondLower) := by
  have hpoint (first : First) (second : Second) :
      mass first second ^ 2 / (firstReference first * secondReference second) ≤
        (upper / (firstLower * secondLower)) * mass first second := by
    have href : 0 < firstReference first * secondReference second :=
      mul_pos (hfirst.trans_le (hrefFirst first)) (hsecond.trans_le (hrefSecond second))
    have hden : firstLower * secondLower ≤ firstReference first * secondReference second :=
      mul_le_mul (hrefFirst first) (hrefSecond second) hsecond.le (hfirst.trans_le (hrefFirst first)).le
    calc
      _ ≤ mass first second ^ 2 / (firstLower * secondLower) :=
        div_le_div_of_nonneg_left (sq_nonneg _) (mul_pos hfirst hsecond) hden
      _ ≤ _ := by
        apply (div_le_iff₀ (mul_pos hfirst hsecond)).mpr
        have h := mul_le_mul_of_nonneg_left (hupper first second) (hmass first second)
        field_simp
        nlinarith
  calc
    _ ≤ ∑ first, ∑ second, (upper / (firstLower * secondLower)) * mass first second :=
      Finset.sum_le_sum fun first _ => Finset.sum_le_sum fun second _ => hpoint first second
    _ = (upper / (firstLower * secondLower)) * ∑ first, ∑ second, mass first second := by
      simp only [← Finset.mul_sum]
    _ ≤ _ := by nlinarith [div_nonneg hu (mul_nonneg hfirst.le hsecond.le)]

/-- A conditional finite companion law has counting-square mass bounded by
its actual pointwise height. -/
theorem companion_square_le (companion : FiniteDist Second) (upper : ℝ)
    (hupper : ∀ second, companion.weight second ≤ upper) :
    (∑ second, companion.weight second ^ 2) ≤ upper := by
  calc
    _ ≤ ∑ second, upper * companion.weight second := by
      apply Finset.sum_le_sum
      intro second _
      nlinarith [mul_le_mul_of_nonneg_right (hupper second) (companion.nonneg second)]
    _ = _ := by rw [← Finset.mul_sum, companion.sum_one, mul_one]

/-- The marked endpoint pair is bounded using the actual primary/profile
square sum and conditional companion height. -/
theorem marked_pair_energy_le (firstReference : First → ℝ) (secondReference : Second → ℝ)
    (profile : First → ℝ) (companion : First → FiniteDist Second)
    (activation firstLower secondLower companionUpper : ℝ)
    (hfirst : 0 < firstLower) (hsecond : 0 < secondLower)
    (hrefFirst : ∀ first, firstLower ≤ firstReference first)
    (hrefSecond : ∀ second, secondLower ≤ secondReference second)
    (hcompanion : ∀ first second, (companion first).weight second ≤ companionUpper) :
    pairEnergy firstReference secondReference
      (fun first second => activation * profile first * (companion first).weight second) ≤
      (activation ^ 2 * companionUpper / (firstLower * secondLower)) * ∑ first, profile first ^ 2 := by
  have hden (first : First) (second : Second) : firstLower * secondLower ≤
      firstReference first * secondReference second :=
    mul_le_mul (hrefFirst first) (hrefSecond second) hsecond.le (hfirst.trans_le (hrefFirst first)).le
  calc
    _ ≤ ∑ first, ∑ second,
        (activation * profile first * (companion first).weight second) ^ 2 / (firstLower * secondLower) := by
      exact Finset.sum_le_sum fun first _ => Finset.sum_le_sum fun second _ =>
        div_le_div_of_nonneg_left (sq_nonneg _) (mul_pos hfirst hsecond) (hden first second)
    _ = ∑ first, activation ^ 2 * profile first ^ 2 / (firstLower * secondLower) *
        ∑ second, (companion first).weight second ^ 2 := by
      apply Finset.sum_congr rfl
      intro first _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro second _
      ring
    _ ≤ ∑ first, activation ^ 2 * profile first ^ 2 / (firstLower * secondLower) * companionUpper := by
      apply Finset.sum_le_sum
      intro first _
      exact mul_le_mul_of_nonneg_left (companion_square_le _ _ (hcompanion first)) (by positivity)
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro first _
      ring

/-- In the primary-weighted norm the marked pair uses the profile norm
exactly, with no maximum-primary loss. -/
theorem marked_pair_primary_energy_le (primary profile : First → ℝ)
    (secondReference : Second → ℝ) (companion : First → FiniteDist Second)
    (activation secondLower companionUpper : ℝ)
    (hprimary : ∀ first, 0 < primary first) (hsecond : 0 < secondLower)
    (hrefSecond : ∀ second, secondLower ≤ secondReference second)
    (hcompanion : ∀ first second, (companion first).weight second ≤ companionUpper) :
    pairEnergy primary secondReference
      (fun first second => activation * profile first * (companion first).weight second) ≤
      (activation ^ 2 * companionUpper / secondLower) * profileSquareNorm primary profile := by
  unfold pairEnergy profileSquareNorm
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro first _
  calc
    _ ≤ ∑ second,
        (activation * profile first * (companion first).weight second) ^ 2 /
          (primary first * secondLower) := by
      apply Finset.sum_le_sum
      intro second _
      exact div_le_div_of_nonneg_left (sq_nonneg _) (mul_pos (hprimary first) hsecond)
        (mul_le_mul_of_nonneg_left (hrefSecond second) (hprimary first).le)
    _ = (activation ^ 2 * profile first ^ 2 / (primary first * secondLower)) *
        ∑ second, (companion first).weight second ^ 2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro second _
      ring
    _ ≤ (activation ^ 2 * profile first ^ 2 / (primary first * secondLower)) * companionUpper :=
      mul_le_mul_of_nonneg_left (companion_square_le _ _ (hcompanion first))
        (div_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) (mul_pos (hprimary first) hsecond).le)
    _ = _ := by ring

/-- Exact tensorization of weighted signed profile energies, including the
independent compensating-center factor in the fourth-degree response. -/
theorem independent_profile_energy (firstReference firstMass : First → ℝ)
    (secondReference secondMass : Second → ℝ) :
    profileSquareNorm (fun point : First × Second => firstReference point.1 * secondReference point.2)
      (fun point => firstMass point.1 * secondMass point.2) =
      profileSquareNorm firstReference firstMass * profileSquareNorm secondReference secondMass := by
  unfold profileSquareNorm
  rw [Fintype.sum_prod_type, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro first _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro second _
  ring

/-- Comparing an actual input profile's counting energy with its weighted
profile norm introduces only the true maximum primary probability. -/
theorem counting_profile_energy_le (primary profile : First → ℝ) (maximum : ℝ)
    (hprimary : ∀ first, 0 < primary first) (hmaximum : ∀ first, primary first ≤ maximum) :
    (∑ first, profile first ^ 2) ≤ maximum * profileSquareNorm primary profile := by
  unfold profileSquareNorm
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro first _
  rw [← mul_div_assoc]
  apply (le_div_iff₀ (hprimary first)).mpr
  nlinarith [mul_le_mul_of_nonneg_left (hmaximum first) (sq_nonneg (profile first))]

/-- The genuine marked endpoint response as a weighted L2 operator; this is
the term carrying the sharper maximum-primary factor in V7. -/
theorem marked_pair_operator_energy_le (firstReference : First → ℝ) (secondReference : Second → ℝ)
    (primary profile : First → ℝ) (companion : First → FiniteDist Second)
    (activation firstLower secondLower companionUpper primaryMaximum : ℝ)
    (hfirst : 0 < firstLower) (hsecond : 0 < secondLower) (hcompanion0 : 0 ≤ companionUpper)
    (hrefFirst : ∀ first, firstLower ≤ firstReference first)
    (hrefSecond : ∀ second, secondLower ≤ secondReference second)
    (hcompanion : ∀ first second, (companion first).weight second ≤ companionUpper)
    (hprimary : ∀ first, 0 < primary first) (hmaximum : ∀ first, primary first ≤ primaryMaximum) :
    pairEnergy firstReference secondReference
      (fun first second => activation * profile first * (companion first).weight second) ≤
      (activation ^ 2 * companionUpper * primaryMaximum / (firstLower * secondLower)) *
        profileSquareNorm primary profile := by
  apply (marked_pair_energy_le firstReference secondReference profile companion activation firstLower
    secondLower companionUpper hfirst hsecond hrefFirst hrefSecond hcompanion).trans
  have h := mul_le_mul_of_nonneg_left (counting_profile_energy_le primary profile primaryMaximum hprimary hmaximum)
    (show 0 ≤ activation ^ 2 * companionUpper / (firstLower * secondLower) by positivity)
  convert h using 1
  ring

/-- Actual endpoint/attachment mass, retaining the shared sample source. -/
noncomputable def attachedMass (source : FiniteDist Source)
    (pair : Source → FiniteDist (First × Second))
    (body : Source → First → Second → FiniteDist Body)
    (first : First) (second : Second) (attached : Body) : ℝ :=
  ∑ sample, source.weight sample * (pair sample).weight (first, second) * (body sample first second).weight attached

/-- Averaging endpoints does not duplicate or independently resample the source. -/
theorem attachedMass_marginal (source : FiniteDist Source)
    (pair : Source → FiniteDist (First × Second))
    (body : Source → First → Second → FiniteDist Body) (first : First) (second : Second) :
    (∑ attached, attachedMass source pair body first second attached) =
      (source.mix pair).weight (first, second) := by
  unfold attachedMass
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum, FiniteDist.sum_one, mul_one, FiniteDist.mix_weight]

/-- The complete actual law for one endpoint pair and its fresh attached
body, retaining their common source in its probability mass. -/
noncomputable def attachedLaw (source : FiniteDist Source)
    (pair : Source → FiniteDist (First × Second))
    (body : Source → First → Second → FiniteDist Body) : FiniteDist ((First × Second) × Body) where
  weight point := attachedMass source pair body point.1.1 point.1.2 point.2
  nonneg point := Finset.sum_nonneg fun sample _ => mul_nonneg
    (mul_nonneg (source.nonneg _) ((pair sample).nonneg _))
      ((body sample point.1.1 point.1.2).nonneg _)
  sum_one := by
    rw [Fintype.sum_prod_type]
    simp_rw [attachedMass_marginal]
    exact (source.mix pair).sum_one

/-- The sampler's exact joint mass is the shared-source mass used in its
energy estimates. -/
theorem attachedLaw_weight (source : FiniteDist Source)
    (pair : Source → FiniteDist (First × Second))
    (body : Source → First → Second → FiniteDist Body) (first : First) (second : Second) (attached : Body) :
    (attachedLaw source pair body).weight ((first, second), attached) =
      attachedMass source pair body first second attached := rfl

/-- A uniformly diffuse fresh body center remains diffuse jointly with its
own endpoint/source variables, without an independence replacement. -/
theorem attachedMass_upper (source : FiniteDist Source)
    (pair : Source → FiniteDist (First × Second))
    (body : Source → First → Second → FiniteDist Body) (upper : ℝ)
    (hbody : ∀ sample first second attached, (body sample first second).weight attached ≤ upper)
    (first : First) (second : Second) (attached : Body) :
    attachedMass source pair body first second attached ≤ upper * (source.mix pair).weight (first, second) := by
  unfold attachedMass
  calc
    _ ≤ ∑ sample, source.weight sample * (pair sample).weight (first, second) * upper := by
      apply Finset.sum_le_sum
      intro sample _
      exact mul_le_mul_of_nonneg_left (hbody sample first second attached)
        (mul_nonneg (source.nonneg _) ((pair sample).nonneg _))
    _ = _ := by simp only [FiniteDist.mix_weight, ← Finset.sum_mul]; ring

/-- Full weighted square norm of an actual endpoint/attached-body triple. -/
noncomputable def tripleEnergy (firstReference : First → ℝ) (secondReference : Second → ℝ)
    (bodyReference : Body → ℝ) (mass : First → Second → Body → ℝ) : ℝ :=
  ∑ first, ∑ second, ∑ attached,
    mass first second attached ^ 2 / (firstReference first * secondReference second * bodyReference attached)

/-- Exact shared-source triple estimate: the full triple density costs at
most the ratio of its fresh-center height to the target reference lower bound,
times the actual averaged endpoint-pair energy. -/
theorem attached_triple_energy_le (source : FiniteDist Source)
    (pair : Source → FiniteDist (First × Second))
    (body : Source → First → Second → FiniteDist Body)
    (firstReference : First → ℝ) (secondReference : Second → ℝ) (bodyReference : Body → ℝ)
    (bodyLower bodyUpper : ℝ) (hlower : 0 < bodyLower) (hupper : 0 ≤ bodyUpper)
    (hfirst : ∀ first, 0 < firstReference first) (hsecond : ∀ second, 0 < secondReference second)
    (hbodyReference : ∀ attached, bodyLower ≤ bodyReference attached)
    (hbody : ∀ sample first second attached, (body sample first second).weight attached ≤ bodyUpper) :
    tripleEnergy firstReference secondReference bodyReference (attachedMass source pair body) ≤
      (bodyUpper / bodyLower) * pairEnergy firstReference secondReference
        (fun first second => (source.mix pair).weight (first, second)) := by
  have hnonneg (first : First) (second : Second) (attached : Body) :
      0 ≤ attachedMass source pair body first second attached :=
    Finset.sum_nonneg fun sample _ => mul_nonneg
      (mul_nonneg (source.nonneg _) ((pair sample).nonneg _)) ((body sample first second).nonneg _)
  have hrow (first : First) (second : Second) :
      profileSquareNorm bodyReference (attachedMass source pair body first second) ≤
        (bodyUpper / bodyLower) * (source.mix pair).weight (first, second) ^ 2 := by
    have h := profile_energy_le_ratio bodyReference (attachedMass source pair body first second)
      ((bodyUpper / bodyLower) * (source.mix pair).weight (first, second))
      (fun attached => hlower.trans_le (hbodyReference attached)) (hnonneg first second) (by
        intro attached
        apply (attachedMass_upper source pair body bodyUpper hbody first second attached).trans
        have hm := mul_le_mul_of_nonneg_left (hbodyReference attached)
          (mul_nonneg (div_nonneg hupper hlower.le) ((source.mix pair).nonneg (first, second)))
        have heq : (bodyUpper / bodyLower) * (source.mix pair).weight (first, second) * bodyLower =
            bodyUpper * (source.mix pair).weight (first, second) := by field_simp
        rwa [heq] at hm)
    rw [attachedMass_marginal] at h
    nlinarith only [h]
  unfold tripleEnergy pairEnergy
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro first _
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro second _
  calc
    _ = profileSquareNorm bodyReference (attachedMass source pair body first second) /
        (firstReference first * secondReference second) := by
      unfold profileSquareNorm
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro attached _
      ring
    _ ≤ ((bodyUpper / bodyLower) * (source.mix pair).weight (first, second) ^ 2) /
        (firstReference first * secondReference second) :=
      div_le_div_of_nonneg_right (hrow first second) (mul_pos (hfirst first) (hsecond second)).le
    _ = _ := by ring

/-- Multiplying a shared-source positive triple by an arbitrary signed
endpoint profile retains the same fresh-center cost. The sign may depend
jointly on both endpoints. -/
theorem signed_attached_triple_energy_le (source : FiniteDist Source)
    (pair : Source → FiniteDist (First × Second))
    (body : Source → First → Second → FiniteDist Body) (profile : First → Second → ℝ)
    (firstReference : First → ℝ) (secondReference : Second → ℝ) (bodyReference : Body → ℝ)
    (bodyLower bodyUpper : ℝ) (hlower : 0 < bodyLower) (hupper : 0 ≤ bodyUpper)
    (hfirst : ∀ first, 0 < firstReference first) (hsecond : ∀ second, 0 < secondReference second)
    (hbodyReference : ∀ attached, bodyLower ≤ bodyReference attached)
    (hbody : ∀ sample first second attached, (body sample first second).weight attached ≤ bodyUpper) :
    tripleEnergy firstReference secondReference bodyReference
      (fun first second attached => profile first second * attachedMass source pair body first second attached) ≤
      (bodyUpper / bodyLower) * pairEnergy firstReference secondReference
        (fun first second => profile first second * (source.mix pair).weight (first, second)) := by
  have hrow (first : First) (second : Second) :
      profileSquareNorm bodyReference (attachedMass source pair body first second) ≤
        (bodyUpper / bodyLower) * (source.mix pair).weight (first, second) ^ 2 := by
    have h := profile_energy_le_ratio bodyReference (attachedMass source pair body first second)
      ((bodyUpper / bodyLower) * (source.mix pair).weight (first, second))
      (fun attached => hlower.trans_le (hbodyReference attached))
      (fun attached => Finset.sum_nonneg fun sample _ => mul_nonneg
        (mul_nonneg (source.nonneg _) ((pair sample).nonneg _)) ((body sample first second).nonneg _)) (by
        intro attached
        apply (attachedMass_upper source pair body bodyUpper hbody first second attached).trans
        have hm := mul_le_mul_of_nonneg_left (hbodyReference attached)
          (mul_nonneg (div_nonneg hupper hlower.le) ((source.mix pair).nonneg (first, second)))
        have heq : (bodyUpper / bodyLower) * (source.mix pair).weight (first, second) * bodyLower =
            bodyUpper * (source.mix pair).weight (first, second) := by field_simp
        rwa [heq] at hm)
    rw [attachedMass_marginal] at h
    nlinarith only [h]
  unfold tripleEnergy pairEnergy
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro first _
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro second _
  calc
    _ = (profile first second ^ 2 / (firstReference first * secondReference second)) *
        profileSquareNorm bodyReference (attachedMass source pair body first second) := by
      unfold profileSquareNorm
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro attached _
      ring
    _ ≤ (profile first second ^ 2 / (firstReference first * secondReference second)) *
        ((bodyUpper / bodyLower) * (source.mix pair).weight (first, second) ^ 2) :=
      mul_le_mul_of_nonneg_left (hrow first second)
        (div_nonneg (sq_nonneg _) (mul_pos (hfirst first) (hsecond second)).le)
    _ = _ := by ring

omit [Fintype First] [Fintype Second] [Fintype Body] [Fintype Source] in
/-- Every actual canonical sample coefficient is contracted by the full
Hoeffding projection, as a consequence of the proved exact finite Parseval identity. -/
theorem canonical_component_energy_le [Fintype Slot] [Fintype Coordinate]
    (reference : Slot → FiniteDist Coordinate) (hreference : ∀ slot color, 0 < (reference slot).weight color)
    (mass : (Slot → Coordinate) → ℝ) (selected : Finset Slot) :
    (FiniteDist.independent reference).l2Sq (Hoeffding.densityComponent reference mass selected) ≤
      (FiniteDist.independent reference).l2Sq (fun value => mass value / (FiniteDist.independent reference).weight value) := by
  rw [Hoeffding.densityComponent_parseval reference hreference mass]
  exact Finset.single_le_sum (fun _ _ => FiniteDist.l2Sq_nonneg _ _) (Finset.mem_univ selected)

end BlockDensity
end AFT
