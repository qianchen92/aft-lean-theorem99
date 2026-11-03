import AFT.LeadingPolynomial
import AFT.MixedMonomialSeed

/-! # Genuine joint leading coefficients controlled by literal mixed activity -/
namespace AFT.RepresentedPolynomial
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {Color : Type*} [Fintype Color]

/-- The integrated tensor norm is paid for by the actual mixed activity,
with every input coordinate and its original pool normalization retained. -/
theorem leadingSeedTensor_energy_activity (primary body : FiniteDist Color) (reference : Color → ℝ)
    (primaryChannel bodyChannel : Color → Color → ℝ) (seed : InputSeed Color)
    (primaryPool bodyPool radius factor : ℝ) (hradius : 1 ≤ radius) (_hfactor : 0 ≤ factor)
    (href : ∀ output,0 ≤ reference output)
    (hp : ∀ kernel,profileSquareNorm reference (fun output => ∑ point,
      primary.weight point*kernel point*primaryChannel point output) ≤
        (factor*(Real.sqrt primaryPool)⁻¹)^2*primary.l2Sq kernel)
    (hb : ∀ kernel,profileSquareNorm reference (fun output => ∑ point,
      body.weight point*kernel point*bodyChannel point output) ≤
        (factor*(Real.sqrt bodyPool)⁻¹)^2*body.l2Sq kernel) :
    BlockFock.tensorEnergy (leadingSeedTensor primary body reference primaryChannel bodyChannel seed) ≤
      (factor^(seed.primaryOrder+seed.bodyOrder)*inputWeight primary body primaryPool bodyPool radius seed)^2 := by
  let rate := inputRate primaryPool bodyPool seed
  let ref := inputReference primary body seed
  let act := MixedKernel.activity rate ref seed.kernel
  have hr (slot) : 0 ≤ rate slot := by
    dsimp only [rate,inputRate]
    cases slot using Fin.addCases <;> simp only [Fin.addCases_left,Fin.addCases_right] <;> positivity
  have ha : 0 ≤ act := MixedKernel.activity_nonneg rate ref seed.kernel hr
  have hnorm := MixedKernel.integrated_norm_le_activity rate ref seed.kernel hr
  have hi := (sq_le_sq₀ (mul_nonneg (Finset.prod_nonneg fun slot _ => hr slot) (Real.sqrt_nonneg _)) ha).mpr hnorm
  simp only [mul_pow,← Finset.prod_pow,Real.sq_sqrt (FiniteDist.l2Sq_nonneg _ _)] at hi
  have hh := leadingSeedTensor_energy primary body reference primaryChannel bodyChannel seed
    (factor*(Real.sqrt primaryPool)⁻¹) (factor*(Real.sqrt bodyPool)⁻¹) href hp hb
  have hprod : ((factor*(Real.sqrt primaryPool)⁻¹)^2)^seed.primaryOrder*
      ((factor*(Real.sqrt bodyPool)⁻¹)^2)^seed.bodyOrder=
      (factor^(seed.primaryOrder+seed.bodyOrder))^2*(∏ slot,rate slot^2) := by
    simp only [rate,inputRate,Fin.prod_univ_add,Fin.addCases_left,Fin.addCases_right,
      Finset.prod_const,Finset.card_univ,Fintype.card_fin,mul_pow,pow_add]
    ring
  rw [hprod,mul_assoc] at hh
  have hw : act ≤ inputWeight primary body primaryPool bodyPool radius seed := by
    change act ≤ radius^seed.bodyOrder*act
    exact le_mul_of_one_le_left ha (one_le_pow₀ hradius)
  calc
    _ ≤ (factor^(seed.primaryOrder+seed.bodyOrder))^2*act^2 :=
      hh.trans (mul_le_mul_of_nonneg_left hi (sq_nonneg _))
    _ ≤ _ := by
      rw [mul_pow]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ha hw 2) (sq_nonneg _)

end
end AFT.RepresentedPolynomial

namespace AFT.V7Calibration
open GaussianSource RepresentedPolynomial Filter
open scoped BigOperators Classical Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false

def leadingEnergyConstant : ℝ := responseEnergyConstant+4

def leadingActivityFactor (n : ℕ) : ℝ := 2*Real.sqrt leadingEnergyConstant*(n : ℝ)^50

theorem leadingEnergyConstant_pos : 0 < leadingEnergyConstant := by
  unfold leadingEnergyConstant responseEnergyConstant
  positivity

theorem leadingActivityFactor_nonneg (n : ℕ) : 0 ≤ leadingActivityFactor n := by
  unfold leadingActivityFactor
  positivity

theorem actual_pool_sqrt_le (n : ℕ) (hn : 2 ≤ n) (pool : ℕ)
    (hpool : pool ≤ Parameters.dimension n) : Real.sqrt (pool : ℝ) ≤ 2*(n : ℝ)^30 := by
  have hd : (pool : ℝ) ≤ 2*(n : ℝ)^60 := by
    exact_mod_cast hpool.trans (by simpa only [Parameters.security_eq n hn] using (Parameters.dimension_bounds n).2)
  apply Real.sqrt_le_iff.mpr ⟨by positivity,?_⟩
  have hp : (0 : ℝ) ≤ n^60 := by positivity
  nlinarith [show ((n : ℝ)^30)^2=(n : ℝ)^60 by ring]

/-- A fixed polynomial loss is sufficient for the low-degree residual.
All channel and pool bounds here are instantiated from the actual V7 laws. -/
theorem actual_leading_seed_activity_eventually (C : ℝ) (hC : 1 ≤ C) (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ n in atTop,(Parameters.legs n : ℝ)/(2*Parameters.dimension n) ≤ beta n ∧
      beta n ≤ 2*(Parameters.legs n : ℝ)/Parameters.dimension n) :
    ∀ᶠ n in atTop,∀ primaryPool bodyPool : ℕ,0<primaryPool →0<bodyPool →
    primaryPool ≤ Parameters.dimension n →bodyPool ≤ Parameters.dimension n →
    ∀ seed : InputSeed (Fin (Parameters.modulus n)),
    BlockFock.tensorEnergy (leadingSeedTensor (actualPrimaryLaw C n (beta n)) (actualBodyLaw C n (beta n))
      (actualReferenceLaw C n (beta n)).weight (actualPrimaryChannel C n) (actualBodyChannel n) seed) ≤
      (leadingActivityFactor n^(seed.primaryOrder+seed.bodyOrder)*
        inputWeight (actualPrimaryLaw C n (beta n)) (actualBodyLaw C n (beta n)) primaryPool bodyPool ((n : ℝ)^2) seed)^2 := by
  filter_upwards [actual_leading_channels_energy_eventually C hC beta hbeta,eventually_ge_atTop 2]
    with n he hn primaryPool bodyPool hp hb hpN hbN seed
  have hx : (1 : ℝ) ≤ n := by exact_mod_cast (show 1≤n by omega)
  have hK := leadingEnergyConstant_pos
  have hR : 0 ≤ responseEnergyConstant := by unfold responseEnergyConstant; positivity
  have hcommon (pool : ℕ) (hpool : 0<pool) (hcapacity : pool≤Parameters.dimension n) :
      leadingEnergyConstant*(n : ℝ)^40 ≤ (leadingActivityFactor n*(Real.sqrt (pool : ℝ))⁻¹)^2 := by
    have hroot : 0<Real.sqrt (pool : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hpool)
    have hm : Real.sqrt leadingEnergyConstant*(n : ℝ)^20 ≤ leadingActivityFactor n/Real.sqrt (pool : ℝ) := by
      apply (le_div_iff₀ hroot).mpr
      calc
        _ ≤ (Real.sqrt leadingEnergyConstant*(n : ℝ)^20)*(2*(n : ℝ)^30) :=
          mul_le_mul_of_nonneg_left (actual_pool_sqrt_le n hn pool hcapacity) (by positivity)
        _ = _ := by unfold leadingActivityFactor; ring
    have hs := pow_le_pow_left₀ (by positivity : (0 : ℝ)≤Real.sqrt leadingEnergyConstant*(n : ℝ)^20) hm 2
    simpa only [mul_pow,Real.sq_sqrt hK.le,← pow_mul,div_eq_mul_inv] using hs
  apply leadingSeedTensor_energy_activity _ _ _ _ _ seed primaryPool bodyPool ((n : ℝ)^2)
    (leadingActivityFactor n) (one_le_pow₀ hx) (leadingActivityFactor_nonneg n) (FiniteDist.nonneg _) ?_ ?_
  · intro kernel
    apply (he.1 kernel).trans
    apply mul_le_mul_of_nonneg_right _ (FiniteDist.l2Sq_nonneg _ _)
    apply le_trans _ (hcommon primaryPool hp hpN)
    calc
      _ ≤ responseEnergyConstant*(n : ℝ)^40 := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hx (by decide : 26≤40)) hR
      _ ≤ _ := mul_le_mul_of_nonneg_right (by unfold leadingEnergyConstant; linarith) (by positivity)
  · intro kernel
    apply (he.2 kernel).trans
    apply mul_le_mul_of_nonneg_right _ (FiniteDist.l2Sq_nonneg _ _)
    apply le_trans _ (hcommon bodyPool hb hbN)
    have hq : (Parameters.modulus n : ℝ) ≤ 2*(n : ℝ)^40 := by
      exact_mod_cast (by simpa only [Parameters.security_eq n hn] using (Parameters.modulus_bounds n).2 : Parameters.modulus n≤2*n^40)
    calc
      _ ≤ 4*(n : ℝ)^40 := by linarith
      _ ≤ _ := mul_le_mul_of_nonneg_right (by unfold leadingEnergyConstant; linarith) (by positivity)

end
end AFT.V7Calibration
