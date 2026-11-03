import CurrentAFT.RaisingChannels
import CurrentAFT.GroupedKernelCanonical

/-! # Current-parameter budgets for every mixed-role raising pattern -/
namespace CurrentAFT.RaisingPatternBudget

open AFT DiffuseProfiles ProposalPrimary ActualControls ControlCoordinates ControlProduct ControlNorm
  GradedControlAlgebra GradedControlNorm LocalCoefficientFamily LocalRaisingBounds RaisingChannels
open Filter
open scoped BigOperators Classical Topology
noncomputable section
local instance classicalFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _
local instance classicalSumDecidableEq {Left Right : Type*} : DecidableEq (Left ⊕ Right) := Classical.decEq _
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base primaryLaw
abbrev Palette (security : ℕ) := ActualControls.Palette security
abbrev Role (r s : ℕ) := Fin r ⊕ Fin s

abbrev RoleInput (security r s : ℕ) : Role r s → Type :=
  Sum.elim (fun _ => Palette security) (fun _ => SafePalette security)

instance roleInputFintype (security r s : ℕ) (role : Role r s) : Fintype (RoleInput security r s role) := by
  cases role <;> dsimp only [RoleInput, Sum.elim_inl, Sum.elim_inr] <;> infer_instance

def roleReference (security r s : ℕ) : (role : Role r s) → FiniteDist (RoleInput security r s role)
  | .inl _ => primaryLaw security
  | .inr _ => bodyReference security

def roleFactor (security r s : ℕ) : Role r s → ℝ :=
  Sum.elim (fun _ => BackgroundRates.primaryFactor security) (fun _ => BackgroundRates.bodyFactor security)

def roleCost (security : ℕ) {r s : ℕ} (selected : Finset (Role r s)) : Role r s → ℝ
  | .inl index => if Sum.inl index ∈ selected then raisingConstant / (Parameters.base security : ℝ) ^ 102
      else BackgroundRates.primaryFactor security
  | .inr index => if Sum.inr index ∈ selected then (80 / (Parameters.base security : ℝ) ^ 63) * BackgroundRates.bodyFactor security
      else BackgroundRates.bodyFactor security

def roleChannel (security order : ℕ) (horder : 1 ≤ order) {r s : ℕ} (selected : Finset (Role r s)) :
    (role : Role r s) → (RoleInput security r s role → ℝ) →ₗ[ℝ] Family security order
  | .inl index => if Sum.inl index ∈ selected then primaryRaised security order horder else primaryLeading security order horder
  | .inr index => if Sum.inr index ∈ selected then bodyRaised security order horder else bodyLeading security order horder

def rolePoint (security order : ℕ) (horder : 1 ≤ order) {r s : ℕ} (selected : Finset (Role r s)) :
    (role : Role r s) → RoleInput security r s role → Family security order
  | .inl index, source => if Sum.inl index ∈ selected then GlobalRaising.raisedPoint security order horder source
      else GlobalRaising.primaryPoint security order horder source
  | .inr index, source => if Sum.inr index ∈ selected then CompleteRaising.ordinaryRaisedPoint security order horder source
      else GlobalRaising.bodyPoint security order horder source

theorem roleChannel_single (security order : ℕ) (horder : 1 ≤ order) {r s : ℕ}
    (selected : Finset (Role r s)) (role : Role r s) (source : RoleInput security r s role) :
    roleChannel security order horder selected role (Pi.single source 1) =
      (roleReference security r s role).weight source • rolePoint security order horder selected role source := by
  cases role with
  | inl index =>
    dsimp only [roleChannel, roleReference, rolePoint]
    split_ifs
    · exact primaryRaised_single security order horder source
    · exact primaryLeading_single security order horder source
  | inr index =>
    dsimp only [roleChannel, roleReference, rolePoint]
    split_ifs
    · exact bodyRaised_single security order horder source
    · exact bodyLeading_single security order horder source

theorem roleChannel_norm (security order : ℕ) (horder : 1 ≤ order)
    (hlarge : 2 * positiveConstant ≤ (Parameters.base security : ℝ)) {r s : ℕ}
    (selected : Finset (Role r s)) (role : Role r s) (score : RoleInput security r s role → ℝ) :
    LocalRaisingBounds.coefficientNorm security order (roleChannel security order horder selected role score) ≤
      roleCost security selected role * Real.sqrt ((roleReference security r s role).l2Sq score) := by
  cases role with
  | inl index =>
    dsimp only [roleChannel, roleReference, roleCost]
    split_ifs
    · exact primaryRaised_norm security order horder hlarge score
    · exact primaryLeading_norm security order horder score
  | inr index =>
    dsimp only [roleChannel, roleReference, roleCost]
    split_ifs
    · exact bodyRaised_norm security order horder score
    · exact bodyLeading_norm security order horder score

theorem primaryFactor_pos (security : ℕ) : 0 < BackgroundRates.primaryFactor security := by
  rw [BackgroundRates.primaryFactor_eq]
  exact one_div_pos.mpr (pow_pos (FirstResponse.base_pos security) _)

theorem bodyFactor_pos (security : ℕ) : 0 < BackgroundRates.bodyFactor security := by
  have hpool : (0 : ℝ) < BackgroundRates.ordinaryPool security := by exact_mod_cast BackgroundRates.ordinaryPool_pos security
  have hradius : 0 < BackgroundRates.radius security := by
    unfold BackgroundRates.radius
    exact Real.rpow_pos_of_pos (FirstResponse.base_pos security) _
  unfold BackgroundRates.bodyFactor
  exact mul_pos hradius (inv_pos.mpr (Real.sqrt_pos.mpr hpool))

theorem raisingConstant_nonneg : 0 ≤ raisingConstant :=
  mul_nonneg (by norm_num) (add_nonneg higherConstant_nonneg positiveConstant_nonneg)

theorem roleCost_nonneg (security : ℕ) {r s : ℕ} (selected : Finset (Role r s)) (role : Role r s) :
    0 ≤ roleCost security selected role := by
  cases role <;> dsimp only [roleCost] <;> split_ifs
  · exact div_nonneg raisingConstant_nonneg (pow_nonneg (FirstResponse.base_pos security).le _)
  · exact (primaryFactor_pos security).le
  · exact mul_nonneg (by positivity) (bodyFactor_pos security).le
  · exact (bodyFactor_pos security).le

def relativeBudget (security : ℕ) : ℝ := (raisingConstant + 80) / (Parameters.base security : ℝ) ^ 38

theorem relativeBudget_nonneg (security : ℕ) : 0 ≤ relativeBudget security :=
  div_nonneg (add_nonneg raisingConstant_nonneg (by norm_num)) (pow_nonneg (FirstResponse.base_pos security).le _)

theorem roleCost_le (security : ℕ) {r s : ℕ} (selected : Finset (Role r s)) (role : Role r s) :
    roleCost security selected role ≤ roleFactor security r s role *
      (if role ∈ selected then relativeBudget security else 1) := by
  have hb := FirstResponse.base_pos security
  have hb1 : (1 : ℝ) ≤ Parameters.base security := by
    exact_mod_cast (show 1 ≤ Parameters.base security by have := Parameters.base_ge_two security; omega)
  cases role with
  | inl index =>
    dsimp only [roleCost, roleFactor, Sum.elim_inl]
    split_ifs
    · have hequal : raisingConstant / (Parameters.base security : ℝ) ^ 102 =
          BackgroundRates.primaryFactor security * (raisingConstant / (Parameters.base security : ℝ) ^ 38) := by
        rw [BackgroundRates.primaryFactor_eq, show (102 : ℕ) = 64 + 38 by omega, pow_add]
        ring
      rw [hequal]
      apply mul_le_mul_of_nonneg_left _ (primaryFactor_pos security).le
      apply div_le_div_of_nonneg_right _ (pow_nonneg hb.le _)
      linarith
    · rw [mul_one]
  | inr index =>
    dsimp only [roleCost, roleFactor, Sum.elim_inr]
    split_ifs
    · have hdiv : 80 / (Parameters.base security : ℝ) ^ 63 ≤ relativeBudget security := by
        calc
          _ ≤ 80 / (Parameters.base security : ℝ) ^ 38 :=
            div_le_div_of_nonneg_left (by norm_num) (pow_pos hb _)
              (pow_le_pow_right₀ hb1 (show 38 ≤ 63 by omega))
          _ ≤ _ := div_le_div_of_nonneg_right (by linarith [raisingConstant_nonneg]) (pow_nonneg hb.le _)
      exact (mul_le_mul_of_nonneg_right hdiv (bodyFactor_pos security).le).trans_eq (mul_comm _ _)
    · rw [mul_one]

theorem roleCost_product (security : ℕ) {r s : ℕ} (selected : Finset (Role r s)) :
    (∏ role : Role r s, roleCost security selected role) ≤
      gradeWeight (BackgroundRates.primaryFactor security) (BackgroundRates.bodyFactor security) r s *
        relativeBudget security ^ selected.card := by
  apply (Finset.prod_le_prod (fun role _ => roleCost_nonneg security selected role)
    (fun role _ => roleCost_le security selected role)).trans_eq
  rw [Finset.prod_mul_distrib]
  have hfactor : (∏ role : Role r s, roleFactor security r s role) =
      gradeWeight (BackgroundRates.primaryFactor security) (BackgroundRates.bodyFactor security) r s := by
    simp [roleFactor, gradeWeight, Fintype.prod_sum_type]
  rw [hfactor]
  congr 1
  simp

theorem nonempty_roleCost_product (security : ℕ) {r s : ℕ} (selected : Finset (Role r s))
    (hnonempty : selected.Nonempty) (hsmall : relativeBudget security ≤ 1) :
    (∏ role : Role r s, roleCost security selected role) ≤
      gradeWeight (BackgroundRates.primaryFactor security) (BackgroundRates.bodyFactor security) r s * relativeBudget security := by
  apply (roleCost_product security selected).trans
  apply mul_le_mul_of_nonneg_left _
    (gradeWeight_nonneg _ _ (primaryFactor_pos security).le (bodyFactor_pos security).le _ _)
  simpa only [pow_one] using pow_le_pow_of_le_one (relativeBudget_nonneg security) hsmall
    (Finset.card_pos.mpr hnonempty)

theorem relativeBudget_small_eventually : ∀ᶠ security : ℕ in atTop, relativeBudget security ≤ 1 := by
  obtain ⟨threshold, hthreshold⟩ := exists_nat_ge (raisingConstant + 80)
  filter_upwards [eventually_ge_atTop threshold] with security hsecurity
  have hb := FirstResponse.base_pos security
  have hb1 : (1 : ℝ) ≤ Parameters.base security := by
    exact_mod_cast (show 1 ≤ Parameters.base security by have := Parameters.base_ge_two security; omega)
  have hlarge : raisingConstant + 80 ≤ (Parameters.base security : ℝ) :=
    hthreshold.trans (Nat.cast_le.mpr (show threshold ≤ Parameters.base security by unfold Parameters.base; omega))
  apply (div_le_one (pow_pos hb _)).mpr
  exact hlarge.trans (by simpa only [pow_one] using pow_le_pow_right₀ hb1 (show 1 ≤ 38 by omega))

end
end CurrentAFT.RaisingPatternBudget
