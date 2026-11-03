import AFT.ChargedPairedProposal
import AFT.ConditionalRepair

/-! # Exact charge and safe-center support survive positive repair -/
namespace AFT.FiniteDist
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {State Skeleton Slot G : Type*} [Fintype State] [Fintype Skeleton]
  [Fintype Slot] [Fintype G] [AddCommGroup G]

omit [Fintype Skeleton] [Fintype Slot] [Fintype G] [AddCommGroup G] in
theorem condition_nonzero_support (law : FiniteDist State) (event : State → Prop)
    (hpos : 0 < law.eventMass event) (point : State)
    (hne : (law.condition event hpos).weight point ≠ 0) : event point ∧ law.weight point ≠ 0 := by
  constructor
  · by_contra hh
    exact hne (by simp [condition, hh])
  · intro hh
    exact hne (by simp [condition, hh])

omit [Fintype State] [Fintype Skeleton] in
theorem chargeWordLaw_nonzero_support (center : FiniteDist G) (required : G)
    (hpos : 0 < (center.sumLaw (Fintype.card Slot)).weight required) (word : Slot → G)
    (hne : (chargeWordLaw center required hpos).weight word ≠ 0) :
    (∑ slot, word slot) = required ∧ ∀ slot, center.weight (word slot) ≠ 0 := by
  have hh := condition_nonzero_support (independent (fun _ : Slot => center))
    (fun word => ∑ slot, word slot = required) _ word hne
  refine ⟨hh.1, ?_⟩
  intro slot hz
  apply hh.2
  exact Finset.prod_eq_zero (Finset.mem_univ slot) hz

omit [Fintype Slot] [Fintype G] [AddCommGroup G] in
theorem conditionalRepair_nonzero_support (skeleton : FiniteDist Skeleton)
    (proposal : Skeleton → FiniteDist State) (weight : Skeleton → State → ℝ)
    (hmean : ∀ cell, 0 < signedMass (weightedMass (proposal cell) (weight cell)))
    (pair : Skeleton × State)
    (hne : (conditionalRepair skeleton proposal weight hmean).weight pair ≠ 0) :
    skeleton.weight pair.1 ≠ 0 ∧ (proposal pair.1).weight pair.2 ≠ 0 := by
  constructor
  · intro hz
    apply hne
    change skeleton.weight pair.1 * _ = 0
    rw [hz, zero_mul]
  · intro hz
    apply hne
    change skeleton.weight pair.1 * (positiveRepairLaw _ _ _).weight pair.2 = 0
    rw [positiveRepairLaw_support _ _ _ _ hz, mul_zero]
end
end AFT.FiniteDist

namespace AFT.V7Calibration
open GaussianSource Filter FiniteDist RepresentedPolynomial
open scoped BigOperators Classical Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
local instance chargedPairedSupportFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _
local instance chargedPairedSupportSumDecEq {α β : Type*} : DecidableEq (α ⊕ β) := Classical.decEq _
attribute [local instance] actualModulusNeZero

/-- Every retained word obeys the single complete body charge, including
all paired compensators, and remains inside the original product support. -/
theorem chargedPairedProposal_nonzero_support (C : ℝ) (n : ℕ) (beta : ℝ) (primaryPool bodyPool : ℕ)
    (markLaw : FiniteDist ((Fin primaryPool ⊕ Fin bodyPool) → Fin (Parameters.modulus n)))
    (required : ((Fin primaryPool ⊕ Fin bodyPool) → Fin (Parameters.modulus n)) → Fin (Parameters.modulus n))
    (hpos : ∀ residue, 0 < ((actualBodyLaw C n beta).sumLaw (Parameters.bodies n)).weight residue)
    (point : ((Fin primaryPool ⊕ Fin bodyPool) → Fin (Parameters.modulus n)) ×
      (Fin (Parameters.bodies n) → Fin (Parameters.modulus n)))
    (hne : (chargedPairedProposal C n beta primaryPool bodyPool markLaw required hpos).weight point ≠ 0) :
    markLaw.weight point.1 ≠ 0 ∧ (∑ slot, point.2 slot) = required point.1 ∧
      ∀ slot, (actualBodyLaw C n beta).weight (point.2 slot) ≠ 0 := by
  have hp : markLaw.weight point.1 ≠ 0 ∧
      (chargeWordLaw (Slot := Fin (Parameters.bodies n)) (actualBodyLaw C n beta) (required point.1)
        (by simpa only [Fintype.card_fin] using hpos (required point.1))).weight point.2 ≠ 0 :=
    mul_ne_zero_iff.mp hne
  exact ⟨hp.1, chargeWordLaw_nonzero_support _ _ _ _ hp.2⟩

/-- A repaired proposal cannot introduce an unsafe center or a wrong
charge. This is a support statement, so no probability lower bound on a
retained public record is used. -/
theorem actual_repaired_charged_support_eventually (C : ℝ) (hC : 1 ≤ C) (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ n in atTop, (Parameters.legs n : ℝ)/(2*Parameters.dimension n) ≤ beta n ∧
      beta n ≤ 2*(Parameters.legs n : ℝ)/Parameters.dimension n) :
    ∀ᶠ n in atTop, ∀ primaryPool bodyPool : ℕ, ∀ (Skeleton : Type) [Fintype Skeleton],
    ∀ skeleton : FiniteDist Skeleton,
    ∀ markLaw : Skeleton → FiniteDist ((Fin primaryPool ⊕ Fin bodyPool) → Fin (Parameters.modulus n)),
    ∀ required : Skeleton → ((Fin primaryPool ⊕ Fin bodyPool) → Fin (Parameters.modulus n)) → Fin (Parameters.modulus n),
    ∀ hpos : ∀ residue, 0 < ((actualBodyLaw C n (beta n)).sumLaw (Parameters.bodies n)).weight residue,
    let proposal := fun cell => chargedPairedProposal C n (beta n) primaryPool bodyPool (markLaw cell) (required cell) hpos
    ∀ weight, ∀ hmean : ∀ cell, 0 < signedMass (weightedMass (proposal cell) (weight cell)),
    ∀ point, (conditionalRepair skeleton proposal weight hmean).weight point ≠ 0 →
      skeleton.weight point.1 ≠ 0 ∧ (markLaw point.1).weight point.2.1 ≠ 0 ∧
        (∑ slot, point.2.2 slot) = required point.1 point.2.1 ∧
        ∀ slot, point.2.2 slot ∈ safePalette n := by
  filter_upwards [actual_reference_laws_eventually C hC beta hbeta,
    actual_body_center_probability_eventually C hC beta hbeta] with n hl hb
  intro primaryPool bodyPool Skeleton _ skeleton markLaw required hpos
  dsimp only
  intro weight hmean point hne
  have hs := conditionalRepair_nonzero_support skeleton _ weight hmean point hne
  have hp := chargedPairedProposal_nonzero_support C n (beta n) primaryPool bodyPool
    (markLaw point.1) (required point.1) hpos point.2 hs.2
  refine ⟨hs.1, hp.1, hp.2.1, ?_⟩
  intro slot
  by_contra hout
  have hh := hp.2.2 slot
  rw [hl.2.1, hb.2.2 _ hout] at hh
  exact hh rfl
end
end AFT.V7Calibration
