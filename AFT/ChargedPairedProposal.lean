import AFT.ActualPairedChargeMoment
import AFT.ActualPairedTableMoment
import AFT.FinitePairedPools
import AFT.ActualChargeEnvelope

/-! # The actual full-charge proposal for complete paired public weights -/
namespace AFT.V7Calibration
open GaussianSource Filter FiniteDist RepresentedPolynomial
open scoped BigOperators Classical Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
local instance chargedPairedProposalFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _
local instance chargedPairedProposalSumDecEq {α β : Type*} : DecidableEq (α ⊕ β) := Classical.decEq _
attribute [local instance] actualModulusNeZero

/-- Dummy primary marks at ordinary-body slots are ignored by the public
kernel. Including them gives one common alphabet for the two actual pools. -/
def chargedPairedProposal (C : ℝ) (n : ℕ) (beta : ℝ) (primaryPool bodyPool : ℕ)
    (markLaw : FiniteDist ((Fin primaryPool ⊕ Fin bodyPool) → Fin (Parameters.modulus n)))
    (required : ((Fin primaryPool ⊕ Fin bodyPool) → Fin (Parameters.modulus n)) → Fin (Parameters.modulus n))
    (hpos : ∀ residue, 0 < ((actualBodyLaw C n beta).sumLaw (Parameters.bodies n)).weight residue) :=
  joint markLaw (fun marks => chargeWordLaw (Slot := Fin (Parameters.bodies n))
    (actualBodyLaw C n beta) (required marks) (by simpa only [Fintype.card_fin] using hpos (required marks)))

def productPairedProposal (C : ℝ) (n : ℕ) (beta : ℝ) (primaryPool bodyPool : ℕ)
    (markLaw : FiniteDist ((Fin primaryPool ⊕ Fin bodyPool) → Fin (Parameters.modulus n))) :=
  joint markLaw (fun _ => independent (fun _ : Fin (Parameters.bodies n) => actualBodyLaw C n beta))

def retainedPairedValue (C : ℝ) (n : ℕ) (beta : ℝ) (primaryPool bodyPool : ℕ)
    (table : Table (InputSeed (Fin (Parameters.modulus n))))
    (embedding : (Fin primaryPool ⊕ Fin bodyPool) ↪ Fin (Parameters.bodies n))
    (pair : ((Fin primaryPool ⊕ Fin bodyPool) → Fin (Parameters.modulus n)) ×
      (Fin (Parameters.bodies n) → Fin (Parameters.modulus n))) : ℝ :=
  tablePairedStatistic (actualPrimaryLaw C n beta) (actualBodyLaw C n beta)
    (fun color center => publicAnchorKernel (Parameters.modulus n) (Parameters.anchorWidth n) color center.val)
    (v7Activation C n) primaryPool bodyPool table
    (pairedRetainedWord primaryPool bodyPool embedding pair.1 pair.2)

/-- A residue depending on the entire retained public word is allowed;
the same full body charge contains every paired compensator. -/
theorem actual_charged_paired_proposal_power_transfer_eventually (C : ℝ) (hC : 1 ≤ C) (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ n in atTop,
      (Parameters.legs n : ℝ)/(2*Parameters.dimension n) ≤ beta n ∧
      beta n ≤ 2*(Parameters.legs n : ℝ)/Parameters.dimension n) (order power : ℕ) :
    ∀ᶠ n in atTop,
      ∃ hpos : ∀ residue, 0 < ((actualBodyLaw C n (beta n)).sumLaw (Parameters.bodies n)).weight residue,
      ∀ primaryPool bodyPool : ℕ, 0 < primaryPool → 0 < bodyPool → order ≤ primaryPool → order ≤ bodyPool →
      ∀ table : Table (InputSeed (Fin (Parameters.modulus n))),
      (∀ powers ∈ table.support, finiteControlCount (monomialOccurrences powers) ≤ order) →
      ∀ embedding : (Fin primaryPool ⊕ Fin bodyPool) ↪ Fin (Parameters.bodies n),
      ∀ markLaw : FiniteDist ((Fin primaryPool ⊕ Fin bodyPool) → Fin (Parameters.modulus n)),
      ∀ required : ((Fin primaryPool ⊕ Fin bodyPool) → Fin (Parameters.modulus n)) → Fin (Parameters.modulus n),
      |(chargedPairedProposal C n (beta n) primaryPool bodyPool markLaw required hpos).expectation
          (fun point => retainedPairedValue C n (beta n) primaryPool bodyPool table embedding point ^ power) -
        (productPairedProposal C n (beta n) primaryPool bodyPool markLaw).expectation
          (fun point => retainedPairedValue C n (beta n) primaryPool bodyPool table embedding point ^ power)| ≤
        actualChargeError C n (beta n) (power*order) *
          tablePairedEnvelope 772 (actualPrimaryLaw C n (beta n)) (actualBodyLaw C n (beta n))
            primaryPool bodyPool ((n : ℝ)^2) table order ^ power := by
  filter_upwards [actual_paired_table_charge_power_transfer_eventually C hC beta hbeta order power] with n ht
  let hpos (residue) := (ht residue).choose
  refine ⟨hpos, ?_⟩
  intro primaryPool bodyPool hp hb hpl hbl table ho embedding markLaw required
  have hh := joint_expectation_difference_le markLaw
    (fun marks => chargeWordLaw (Slot := Fin (Parameters.bodies n)) (actualBodyLaw C n (beta n))
      (required marks) (by simpa only [Fintype.card_fin] using hpos (required marks)))
    (fun _ => independent (fun _ : Fin (Parameters.bodies n) => actualBodyLaw C n (beta n)))
    (fun point => retainedPairedValue C n (beta n) primaryPool bodyPool table embedding point ^ power)
    (fun _ => actualChargeError C n (beta n) (power*order) *
      tablePairedEnvelope 772 (actualPrimaryLaw C n (beta n)) (actualBodyLaw C n (beta n))
        primaryPool bodyPool ((n : ℝ)^2) table order ^ power)
    (fun marks => (ht (required marks)).choose_spec primaryPool bodyPool hp hb hpl hbl table ho embedding marks)
  rw [expectation_const] at hh
  exact hh

/-- Exact distributional bridge from the actual uncharged full body word
to the paired product law, for every test function of the complete score. -/
theorem productPairedProposal_expectation (C : ℝ) (n : ℕ) (beta : ℝ) (primaryPool bodyPool : ℕ)
    (table : Table (InputSeed (Fin (Parameters.modulus n))))
    (embedding : (Fin primaryPool ⊕ Fin bodyPool) ↪ Fin (Parameters.bodies n)) (test : ℝ → ℝ) :
    (productPairedProposal C n beta primaryPool bodyPool
      (independent (fun _ => actualPrimaryLaw C n beta))).expectation
      (fun point => test (retainedPairedValue C n beta primaryPool bodyPool table embedding point)) =
    (independent (Sum.elim (fun _ : Fin primaryPool => (actualPrimaryLaw C n beta).prod (actualBodyLaw C n beta))
      (fun _ : Fin bodyPool => (actualPrimaryLaw C n beta).prod (actualBodyLaw C n beta)))).expectation
      (fun word => test (tablePairedStatistic (actualPrimaryLaw C n beta) (actualBodyLaw C n beta)
        (fun color center => publicAnchorKernel (Parameters.modulus n) (Parameters.anchorWidth n) color center.val)
        (v7Activation C n) primaryPool bodyPool table word)) := by
  have hh := joint_paired_embedding_expectation (fun _ => actualPrimaryLaw C n beta) (actualBodyLaw C n beta)
    embedding (fun word => test (tablePairedStatistic (actualPrimaryLaw C n beta) (actualBodyLaw C n beta)
      (fun color center => publicAnchorKernel (Parameters.modulus n) (Parameters.anchorWidth n) color center.val)
      (v7Activation C n) primaryPool bodyPool table word))
  apply hh.trans
  congr 2
  funext slot
  cases slot <;> rfl

theorem actual_product_paired_proposal_moments_eventually (C : ℝ) (hC : 1 ≤ C) (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ n in atTop,
      (Parameters.legs n : ℝ)/(2*Parameters.dimension n) ≤ beta n ∧
      beta n ≤ 2*(Parameters.legs n : ℝ)/Parameters.dimension n) :
    ∀ᶠ n in atTop,
      ∀ primaryPool bodyPool : ℕ, 0 < primaryPool → 0 < bodyPool →
      ∀ radius : ℝ, 1 ≤ radius →
      ∀ table : Table (InputSeed (Fin (Parameters.modulus n))),
      InputTableCanonical (actualPrimaryLaw C n (beta n)) (actualBodyLaw C n (beta n)) table →
      ∀ order : ℕ, (∀ powers ∈ table.support, finiteControlCount (monomialOccurrences powers) ≤ order) →
      2*order ≤ primaryPool → 2*order ≤ bodyPool →
      ∀ embedding : (Fin primaryPool ⊕ Fin bodyPool) ↪ Fin (Parameters.bodies n),
      ∀ moment : ℕ, 0 < moment →
      (productPairedProposal C n (beta n) primaryPool bodyPool
        (independent (fun _ => actualPrimaryLaw C n (beta n)))).expectation
        (fun point => |retainedPairedValue C n (beta n) primaryPool bodyPool table embedding point|^(2*moment)) ≤
      (representedPairedMomentConstant 772 order moment * activity
        (inputWeight (actualPrimaryLaw C n (beta n)) (actualBodyLaw C n (beta n)) primaryPool bodyPool radius) table)^(2*moment) := by
  filter_upwards [actual_paired_table_moments_eventually C hC beta hbeta] with n ht
  intro primaryPool bodyPool hp hb radius hr table hc order ho hpl hbl embedding moment hm
  rw [productPairedProposal_expectation C n (beta n) primaryPool bodyPool table embedding (fun value => |value|^(2*moment))]
  exact ht primaryPool bodyPool hp hb radius hr table hc order ho hpl hbl moment hm

/-- The charge cost remains negligible for the complete paired public
weight; its extra fixed-order Schur factor is independent of the dimension. -/
theorem actual_paired_charge_envelope_negligible (C : ℝ) (hC : 1 ≤ C) (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ n in atTop, (Parameters.legs n : ℝ)/(2*Parameters.dimension n) ≤ beta n ∧
      beta n ≤ 2*(Parameters.legs n : ℝ)/Parameters.dimension n)
    (primaryPool bodyPool : ℕ → ℕ)
    (hcaps : ∀ᶠ n in atTop, primaryPool n ≤ Parameters.legs n ∧ bodyPool n ≤ Parameters.bodies n)
    (table : (n : ℕ) → Table (InputSeed (Fin (Parameters.modulus n))))
    (order cutoff power : ℕ) (bound : ℝ) (hbound : 0 ≤ bound)
    (hactivity : ∀ᶠ n in atTop, activity
      (inputWeight (actualPrimaryLaw C n (beta n)) (actualBodyLaw C n (beta n))
        (primaryPool n) (bodyPool n) ((n : ℝ)^2)) (table n) ≤ bound) :
    Negligible (fun n => actualChargeError C n (beta n) cutoff *
      tablePairedEnvelope 772 (actualPrimaryLaw C n (beta n)) (actualBodyLaw C n (beta n))
        (primaryPool n) (bodyPool n) ((n : ℝ)^2) (table n) order ^ power) := by
  have hh := (actual_table_charge_envelope_negligible C hC beta hbeta primaryPool bodyPool hcaps
    table order cutoff power bound hbound hactivity).const_mul ((((772 : ℝ)+2)^(2*order))^power)
  simpa only [tablePairedEnvelope, mul_pow, mul_left_comm] using hh
/-- The actual conditional-mean floor eventually follows from the same
bounded input activity used in the fixed-order inverse construction. -/
theorem actual_paired_charge_mean_small_eventually (C : ℝ) (hC : 1 ≤ C) (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ n in atTop, (Parameters.legs n : ℝ)/(2*Parameters.dimension n) ≤ beta n ∧
      beta n ≤ 2*(Parameters.legs n : ℝ)/Parameters.dimension n)
    (primaryPool bodyPool : ℕ → ℕ)
    (hcaps : ∀ᶠ n in atTop, primaryPool n ≤ Parameters.legs n ∧ bodyPool n ≤ Parameters.bodies n)
    (table : (n : ℕ) → Table (InputSeed (Fin (Parameters.modulus n))))
    (order : ℕ) (bound : ℝ) (hbound : 0 ≤ bound)
    (hactivity : ∀ᶠ n in atTop, activity
      (inputWeight (actualPrimaryLaw C n (beta n)) (actualBodyLaw C n (beta n))
        (primaryPool n) (bodyPool n) ((n : ℝ)^2)) (table n) ≤ bound) :
    ∀ᶠ n in atTop, actualChargeError C n (beta n) order *
      tablePairedEnvelope 772 (actualPrimaryLaw C n (beta n)) (actualBodyLaw C n (beta n))
        (primaryPool n) (bodyPool n) ((n : ℝ)^2) (table n) order ≤ 1/2 := by
  have hn := actual_paired_charge_envelope_negligible C hC beta hbeta primaryPool bodyPool hcaps
    table order order 1 bound hbound hactivity
  filter_upwards [hn 1, eventually_ge_atTop 2] with n he hn
  simp only [pow_one] at he
  exact (le_abs_self _).trans (he.trans (one_div_le_one_div_of_le (by norm_num : (0 : ℝ)<2)
    (by exact_mod_cast hn)))

/-- Correcting the signed conditional mean to one is also negligible,
even after paying the full pointwise paired rejection envelope. -/
theorem actual_paired_charge_normalization_negligible (C : ℝ) (hC : 1 ≤ C) (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ n in atTop, (Parameters.legs n : ℝ)/(2*Parameters.dimension n) ≤ beta n ∧
      beta n ≤ 2*(Parameters.legs n : ℝ)/Parameters.dimension n)
    (primaryPool bodyPool : ℕ → ℕ)
    (hcaps : ∀ᶠ n in atTop, primaryPool n ≤ Parameters.legs n ∧ bodyPool n ≤ Parameters.bodies n)
    (table : (n : ℕ) → Table (InputSeed (Fin (Parameters.modulus n))))
    (order : ℕ) (bound : ℝ) (hbound : 0 ≤ bound)
    (hactivity : ∀ᶠ n in atTop, activity
      (inputWeight (actualPrimaryLaw C n (beta n)) (actualBodyLaw C n (beta n))
        (primaryPool n) (bodyPool n) ((n : ℝ)^2)) (table n) ≤ bound) :
    Negligible (fun n =>
      let envelope := tablePairedEnvelope 772 (actualPrimaryLaw C n (beta n)) (actualBodyLaw C n (beta n))
        (primaryPool n) (bodyPool n) ((n : ℝ)^2) (table n) order
      2*(actualChargeError C n (beta n) order * envelope)*(1+envelope)) := by
  have h1 := actual_paired_charge_envelope_negligible C hC beta hbeta primaryPool bodyPool hcaps
    table order order 1 bound hbound hactivity
  have h2 := actual_paired_charge_envelope_negligible C hC beta hbeta primaryPool bodyPool hcaps
    table order order 2 bound hbound hactivity
  convert (h1.add h2).const_mul 2 using 1
  funext n
  dsimp only
  ring

/-- The full paired score has a deterministic envelope, including every
anchor compensation, uniformly over the actual complete body word. -/
theorem actual_retained_paired_envelope_eventually (C : ℝ) (hC : 1 ≤ C) (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ n in atTop, (Parameters.legs n : ℝ)/(2*Parameters.dimension n) ≤ beta n ∧
      beta n ≤ 2*(Parameters.legs n : ℝ)/Parameters.dimension n) :
    ∀ᶠ n in atTop, ∀ primaryPool bodyPool : ℕ, 0 < primaryPool → 0 < bodyPool →
    ∀ table : Table (InputSeed (Fin (Parameters.modulus n))), ∀ order : ℕ,
    (∀ powers ∈ table.support, finiteControlCount (monomialOccurrences powers) ≤ order) →
    order ≤ primaryPool → order ≤ bodyPool →
    ∀ embedding : (Fin primaryPool ⊕ Fin bodyPool) ↪ Fin (Parameters.bodies n), ∀ point,
      |retainedPairedValue C n (beta n) primaryPool bodyPool table embedding point| ≤
        tablePairedEnvelope 772 (actualPrimaryLaw C n (beta n)) (actualBodyLaw C n (beta n))
          primaryPool bodyPool ((n : ℝ)^2) table order := by
  filter_upwards [actual_public_anchor_comparison_eventually C hC beta hbeta, eventually_ge_atTop 2]
    with n hcompare hn primaryPool bodyPool hp hb table order ho hpl hbl embedding point
  have hr : (1 : ℝ) ≤ (n : ℝ)^2 := one_le_pow₀ (by exact_mod_cast (show 1 ≤ n by omega))
  exact tablePairedStatistic_abs_le_envelope (actualPrimaryLaw C n (beta n)) (actualBodyLaw C n (beta n))
    (fun color center => publicAnchorKernel (Parameters.modulus n) (Parameters.anchorWidth n) color center.val)
    (v7Activation C n) 772
    (activation_positive _ _ _ _ (legFeatureCount_positive C n hC (by omega))).le
    (activation_le_one _ _ _ _) (by norm_num) (fun color center => publicAnchorKernel_nonneg _ _ _ _)
    (fun color => (actual_anchor_safe_mass n color).1) hcompare primaryPool bodyPool hp hb _ hr table order ho hpl hbl _

end
end AFT.V7Calibration
