import AFT.RootBodyTensor
import AFT.SignedChannelFibers
import AFT.ReferenceHilbertFibers

/-! # The actual root-centered shared-source triple channel -/
namespace AFT.BlockDensity
open scoped BigOperators Classical
noncomputable section
variable {Source Color : Type*} [Fintype Source] [Fintype Color]

def signedAttachedMass (source : FiniteDist Source) (pair : Source → FiniteDist (Color × Color))
    (body : Source → Color → ℝ) (first second attached : Color) : ℝ :=
  ∑ sample,source.weight sample*(pair sample).weight (first,second)*body sample attached

/-- The same-source signed body channel is bounded by the genuine averaged
pair energy. The source is averaged before the pair energy is taken. -/
theorem signedAttachedMass_energy_le (source : FiniteDist Source)
    (pair : Source → FiniteDist (Color × Color)) (body : Source → Color → ℝ)
    (reference : FiniteDist Color) (hp : ∀ color,0<reference.weight color)
    (bound : ℝ) (hbody : ∀ sample,profileSquareNorm reference.weight (body sample) ≤ bound) :
    tripleEnergy reference.weight reference.weight reference.weight (signedAttachedMass source pair body) ≤
      bound*pairEnergy reference.weight reference.weight (fun first second => (source.mix pair).weight (first,second)) := by
  have hrow (first second : Color) :
      profileSquareNorm reference.weight (signedAttachedMass source pair body first second) ≤
        (source.mix pair).weight (first,second)^2*bound := by
    have hh := positiveCombination_l2Sq_le reference
      (fun sample => source.weight sample*(pair sample).weight (first,second))
      (fun sample color => body sample color/reference.weight color) bound
      (fun sample => mul_nonneg (source.nonneg _) ((pair sample).nonneg _)) (fun sample => by
        change densitySquareNorm reference.weight (fun color => body sample color/reference.weight color) ≤ _
        rw [densityScore_square]
        exact hbody sample)
    have he : (fun color => ∑ sample,source.weight sample*(pair sample).weight (first,second)*
        (body sample color/reference.weight color)) =
        fun color => signedAttachedMass source pair body first second color/reference.weight color := by
      funext color
      simp only [signedAttachedMass,Finset.sum_div,mul_div_assoc]
    rw [he] at hh
    change densitySquareNorm reference.weight _ ≤ _ at hh
    rw [densityScore_square] at hh
    exact hh
  unfold tripleEnergy pairEnergy
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro first _
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro second _
  calc
    _ = profileSquareNorm reference.weight (signedAttachedMass source pair body first second)/
        (reference.weight first*reference.weight second) := by
      unfold profileSquareNorm
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro attached _
      ring
    _ ≤ ((source.mix pair).weight (first,second)^2*bound)/(reference.weight first*reference.weight second) :=
      div_le_div_of_nonneg_right (hrow first second) (mul_nonneg (hp first).le (hp second).le)
    _ = _ := by ring

theorem pairEnergy_reference_domination (first second : FiniteDist Color)
    (hp : ∀ color,0<first.weight color) (hq : ∀ color,0<second.weight color)
    (comparison : ℝ) (hc : 0≤comparison)
    (hcompare : ∀ color,second.weight color≤comparison*first.weight color)
    (mass : Color → Color → ℝ) :
    pairEnergy first.weight first.weight mass ≤ comparison^2*pairEnergy second.weight second.weight mass := by
  unfold pairEnergy
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro color _
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro other _
  apply (div_le_iff₀ (mul_pos (hp color) (hp other))).mpr
  have hh := mul_le_mul (hcompare color) (hcompare other) (hq other).le (mul_nonneg hc (hp color).le)
  have hi := mul_le_mul_of_nonneg_left hh (div_nonneg (sq_nonneg (mass color other)) (mul_nonneg (hq color).le (hq other).le))
  have hz : mass color other^2/(second.weight color*second.weight other)*(second.weight color*second.weight other)=mass color other^2 := by field_simp [(hq color).ne', (hq other).ne']
  rw [hz] at hi
  exact hi.trans_eq (by ring)

end
end AFT.BlockDensity

namespace AFT.V7Calibration
open GaussianSource PhysicalBlockTensors Filter
open scoped BigOperators Classical Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
local instance attachedRootBackgroundFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _

/-- The genuine shared-source triple with only its own root centered.
The activated/inactive source and both endpoint coordinates remain joint. -/
def actualCenteredRootTriple (C : ℝ) (n : ℕ) (beta : ℝ) (queue : ℤ)
    (root : Window (v7RootCutoff n)) : (Fin 3 → Fin (Parameters.modulus n)) → ℝ :=
  tripleMass (BlockDensity.signedAttachedMass (actualActivatedSource C n) (actualPairBranch C n beta)
    (fun source => centeredRootBodyProfile C n beta (actualSourceShift C n source+queue) root))

/-- This is precisely the centered law of the original conditional triple
sampler, including its common source, rather than a surrogate channel. -/
theorem actualCenteredRootTriple_eq (C : ℝ) (n : ℕ) (beta : ℝ) (queue : ℤ)
    (root : Window (v7RootCutoff n)) (word : Fin 3 → Fin (Parameters.modulus n)) :
    actualCenteredRootTriple C n beta queue root word =
      (actualFixedRootTripleLaw C n beta root queue).weight word-
        ∑ other,(bodyRootReference n).weight other*(actualFixedRootTripleLaw C n beta other queue).weight word := by
  simp only [actualCenteredRootTriple,actualFixedRootTripleLaw,sharedSourceTriple_weight,
    tripleMass,BlockDensity.signedAttachedMass,BlockDensity.attachedMass,actualBodyBranch,
    centeredRootBodyProfile,add_assoc,mul_sub,Finset.sum_sub_distrib,Finset.mul_sum]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro source _
  apply Finset.sum_congr rfl
  intro other _
  ring

/-- The complete actual root-centered triple density has squared Hilbert
size O(lambda^-8), uniformly over its legal root and common queue. -/
theorem actual_centered_root_triple_energy_eventually (C : ℝ) (hC : 1≤C)
    (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ n in atTop,(Parameters.legs n : ℝ)/(2*Parameters.dimension n)≤beta n ∧
      beta n≤2*(Parameters.legs n : ℝ)/Parameters.dimension n) :
    ∀ᶠ n in atTop, ∀ queue : ℤ,|queue|≤(queueCutoff n : ℤ) →
    ∀ root : Window (v7RootCutoff n),
      (FiniteDist.independent (fun _ : Fin 3 => actualPrimaryLaw C n (beta n))).l2Sq
        (fun word => actualCenteredRootTriple C n (beta n) queue root word/
          (FiniteDist.independent (fun _ : Fin 3 => actualPrimaryLaw C n (beta n))).weight word) ≤
      (64*24640*175104)/(n : ℝ)^8 := by
  filter_upwards [actual_centered_root_body_strip_eventually C hC beta hbeta,
    actual_pair_branch_mixture_eventually C hC beta hbeta,
    actual_pair_energy_power_eventually C hC beta hbeta,
    actual_reference_laws_eventually C hC beta hbeta,
    actual_reference_probability_eventually C hC beta hbeta,
    actual_reference_lower_eventually C hC beta hbeta,
    actual_primary_law_quarter_lower_eventually C hC beta hbeta,eventually_ge_atTop 1]
    with n hs hm he hl hr hrl hp hn queue hqueue root
  have hx : (0 : ℝ)<n := by exact_mod_cast (by omega : 0<n)
  have hq : (0 : ℝ)<Parameters.modulus n := Nat.cast_pos.mpr (Parameters.modulus_prime n).pos
  have hp0 (color) : 0<(actualPrimaryLaw C n (beta n)).weight color := lt_of_lt_of_le (by positivity) (hp color)
  have hr0 (color) : 0<(actualReferenceLaw C n (beta n)).weight color := by
    rw [hl.2.2]
    exact lt_of_lt_of_le (by positivity) (hrl color)
  have hcompare (color) : (actualReferenceLaw C n (beta n)).weight color ≤ 8*(actualPrimaryLaw C n (beta n)).weight color := by
    rw [hl.2.2]
    have ht := (hr.1 color).2
    have hh := hp color
    change 1/(4*(Parameters.modulus n : ℝ)) ≤ _ at hh
    calc
      _ ≤ 2/(Parameters.modulus n : ℝ) := ht
      _ = 8*(1/(4*(Parameters.modulus n : ℝ))) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hh (by norm_num)
  have hpair := BlockDensity.pairEnergy_reference_domination
    (actualPrimaryLaw C n (beta n)) (actualReferenceLaw C n (beta n)) hp0 hr0 8 (by norm_num) hcompare
    (fun first second => ((actualActivatedSource C n).mix (actualPairBranch C n (beta n))).weight (first,second))
  simp only [hm,hl.2.2] at hpair
  have hpairbound := hpair.trans (mul_le_mul_of_nonneg_left he (by norm_num : (0 : ℝ)≤8^2))
  have hb := BlockDensity.signedAttachedMass_energy_le (actualActivatedSource C n)
    (actualPairBranch C n (beta n))
    (fun source => centeredRootBodyProfile C n (beta n) (actualSourceShift C n source+queue) root)
    (actualPrimaryLaw C n (beta n)) hp0 (175104/(n : ℝ)^38) (fun source =>
      (hs (actualSourceShift C n source+queue) (fun other : Window (v7RootCutoff n) => by
        simpa only [add_assoc] using actualBodyBranch_shift_bound C n (other : ℤ) queue
          (abs_le.mpr (Finset.mem_Icc.mp other.property)) hqueue source) root).1)
  rw [actualCenteredRootTriple,triple_density_energy]
  apply hb.trans
  simp only [hm] at ⊢
  apply (mul_le_mul_of_nonneg_left hpairbound (by positivity : (0 : ℝ)≤175104/(n : ℝ)^38)).trans_eq
  field_simp
  norm_num

end
end AFT.V7Calibration
