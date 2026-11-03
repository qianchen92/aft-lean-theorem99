import AFT.RepresentedControlOrder
import AFT.RepresentedCanonical
import AFT.TwoPoolMomentBound

/-! # Literal seed products in the actual two-pool input statistic -/
namespace AFT.RepresentedPolynomial
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
local instance representedTwoPoolSumDecEq {α β : Type*} : DecidableEq (α ⊕ β) := Classical.decEq _
variable {Color : Type*} [Fintype Color]

abbrev ControlPrimarySlot (seeds : List (InputSeed Color)) := {slot : ControlProductSlot seeds // controlProductRole seeds slot = true}
abbrev ControlBodySlot (seeds : List (InputSeed Color)) := {slot : ControlProductSlot seeds // ¬ controlProductRole seeds slot = true}

def controlPoolEquiv (seeds : List (InputSeed Color)) :
    ControlPrimarySlot seeds ⊕ ControlBodySlot seeds ≃ ControlProductSlot seeds :=
  Equiv.sumCompl (fun slot => controlProductRole seeds slot = true)

def twoPoolControlKernel (seeds : List (InputSeed Color)) :
    ((ControlPrimarySlot seeds ⊕ ControlBodySlot seeds) → Color) → ℝ :=
  fun word => controlProductKernel seeds (word ∘ (controlPoolEquiv seeds).symm)

theorem controlPool_reference (primary body : FiniteDist Color) (seeds : List (InputSeed Color)) :
    (fun slot => controlProductReference primary body seeds (controlPoolEquiv seeds slot)) =
      Sum.elim (fun _ : ControlPrimarySlot seeds => primary) (fun _ : ControlBodySlot seeds => body) := by
  funext slot
  cases slot with
  | inl slot => simp [controlPoolEquiv, controlProductReference_role, slot.property]
  | inr slot => simp [controlPoolEquiv, controlProductReference_role, slot.property]

omit [Fintype Color] in
theorem controlPool_rate (primaryPool bodyPool : ℝ) (seeds : List (InputSeed Color)) :
    (fun slot => controlProductRate primaryPool bodyPool seeds (controlPoolEquiv seeds slot)) =
      Sum.elim (fun _ : ControlPrimarySlot seeds => 1 / Real.sqrt primaryPool)
        (fun _ : ControlBodySlot seeds => 1 / Real.sqrt bodyPool) := by
  funext slot
  cases slot with
  | inl slot => simp [controlPoolEquiv, controlProductRate_role, slot.property]
  | inr slot => simp [controlPoolEquiv, controlProductRate_role, slot.property]

theorem twoPoolControlKernel_canonical (primary body : FiniteDist Color) (seeds : List (InputSeed Color))
    (hc : ∀ seed ∈ seeds, Hoeffding.Canonical (inputReference primary body seed) Finset.univ seed.kernel) :
    Hoeffding.Canonical (Sum.elim (fun _ : ControlPrimarySlot seeds => primary) (fun _ : ControlBodySlot seeds => body))
      Finset.univ (twoPoolControlKernel seeds) := by
  have he := MixedKernel.CoordinateTransport.canonical_equiv (controlPoolEquiv seeds).symm
    (controlProductReference primary body seeds) (controlProductKernel seeds)
    (controlProductKernel_canonical primary body seeds hc)
  simpa only [Equiv.symm_symm, controlPool_reference, twoPoolControlKernel] using he

theorem twoPoolControlKernel_activity_le (primary body : FiniteDist Color) (primaryPool bodyPool radius : ℝ)
    (hradius : 1 ≤ radius) (seeds : List (InputSeed Color)) :
    MixedKernel.activity (Sum.elim (fun _ : ControlPrimarySlot seeds => 1 / Real.sqrt primaryPool)
      (fun _ : ControlBodySlot seeds => 1 / Real.sqrt bodyPool))
      (Sum.elim (fun _ : ControlPrimarySlot seeds => primary) (fun _ : ControlBodySlot seeds => body))
      (twoPoolControlKernel seeds) ≤ (seeds.map (inputWeight primary body primaryPool bodyPool radius)).prod := by
  have he := MixedKernel.CoordinateTransport.activity_equiv (controlPoolEquiv seeds).symm
    (controlProductRate primaryPool bodyPool seeds) (controlProductReference primary body seeds) (controlProductKernel seeds)
  simp only [Equiv.symm_symm, controlPool_rate, controlPool_reference] at he
  change MixedKernel.activity _ _ (fun word => controlProductKernel seeds (word ∘ (controlPoolEquiv seeds).symm)) ≤ _
  rw [he]
  apply le_trans _ (controlProductActivity_le primary body primaryPool bodyPool radius (le_trans zero_le_one hradius) seeds)
  unfold controlProductActivity
  exact le_mul_of_one_le_left (MixedKernel.activity_nonneg _ _ _ (controlProductRate_nonneg _ _ _))
    (one_le_pow₀ hradius)

omit [Fintype Color] in
theorem controlPrimarySlot_card_le (seeds : List (InputSeed Color)) :
    Fintype.card (ControlPrimarySlot seeds) ≤ finiteControlCount seeds := Fintype.card_subtype_le _

omit [Fintype Color] in
theorem controlBodySlot_card_le (seeds : List (InputSeed Color)) :
    Fintype.card (ControlBodySlot seeds) ≤ finiteControlCount seeds := Fintype.card_subtype_le _

/-- The exact ordered, without-replacement statistic of the full joint
kernel, averaging separately over the retained primary and body pools. -/
def monomialInputStatistic (primaryPool bodyPool : ℕ) (powers : InputSeed Color →₀ ℕ) :
    ((Fin primaryPool ⊕ Fin bodyPool) → Color) → ℝ :=
  CanonicalMoments.twoPoolStatistic (twoPoolControlKernel (monomialOccurrences powers))

end
end AFT.RepresentedPolynomial
