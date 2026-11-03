import AFT.TaggedBlockTail
import AFT.JointChannelMass

/-! # Exact mass preservation for physical signed-law operations -/
namespace AFT.HistogramNormalization
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {Slot OtherSlot Color Source : Type*}
  [Fintype Slot] [Fintype OtherSlot] [Fintype Color] [Fintype Source]

omit [Fintype Source] in
theorem renamedMass_total (equiv : Slot ≃ OtherSlot) (mass : (Slot → Color) → ℝ) :
    (∑ output, renamedMass equiv mass output) = ∑ input, mass input :=
  (renameWord (Color := Color) equiv).symm.sum_comp mass

omit [Fintype OtherSlot] in
theorem mixtureMass_total (source : FiniteDist Source) (mass : Source → (Slot → Color) → ℝ) :
    (∑ word, mixtureMass source mass word) = source.expectation (fun sample => ∑ word, mass sample word) :=
  (FiniteDist.expectation_sum source (fun word sample => mass sample word)).symm

end
end AFT.HistogramNormalization

namespace AFT.BlockProducts
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {Index Color TaggedSlot : Type*} [Fintype Index] [Fintype Color] [Fintype TaggedSlot]
variable (Slots : Index → Type*) [∀ index, Fintype (Slots index)]
local instance signedMassOperationsSumDecEq {α β : Type*} : DecidableEq (α ⊕ β) := Classical.decEq _
local instance signedMassOperationsSigmaDecEq : DecidableEq (Sigma Slots) := Classical.decEq _

/-- Tensoring a signed marked response with the actual independent
physical complement preserves its total mass exactly. -/
theorem taggedBlockMass_total (tagged : (TaggedSlot → Color) → ℝ)
    (law : (index : Index) → FiniteDist (Slots index → Color)) :
    (∑ word, taggedBlockMass Slots tagged law word) = ∑ word, tagged word := by
  have he := (Equiv.sumArrowEquivProdArrow TaggedSlot (Sigma Slots) Color).sum_comp
    (fun point => tagged point.1 * blockMass Slots law point.2)
  change (∑ word, tagged (word ∘ Sum.inl) * blockMass Slots law (word ∘ Sum.inr)) = _
  calc
    _ = ∑ point : (TaggedSlot → Color) × (Sigma Slots → Color),
        tagged point.1 * blockMass Slots law point.2 := he
    _ = _ := by
      rw [Fintype.sum_prod_type]
      have hm : (∑ word : Sigma Slots → Color, blockMass Slots law word) = 1 := by
        change (∑ word : Sigma Slots → Color, ∏ index, (law index).weight (fun slot => word ⟨index, slot⟩)) = 1
        rw [JointPhysicalChannel.product_total]
        simp only [FiniteDist.sum_one, Finset.prod_const_one]
      simp only [← Finset.mul_sum, hm, mul_one]

end
end AFT.BlockProducts
