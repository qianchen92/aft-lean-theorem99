import CurrentAFT.BinaryCoefficientExtraction
import CurrentAFT.RationalLegCoefficientExtraction

/-! # The executed joint extractor for the three actual leg endpoints -/
namespace CurrentAFT.BinaryLegCoefficientExtraction
open AFT RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits
open scoped BigOperators
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
abbrev colors (security : ℕ) := BinaryFirstInverseProgram.colors security

theorem density_value (security bits : ℕ) (selected : Finset (Fin 3)) (slots : Vector (Fin 3) selected.card)
    (hslots : ∀ index, slots.get index=((Finset.orderIsoOfFin selected rfl) index).val)
    (output : Vector (Fin (colors security)) selected.card) (mass : Vector (Fin (colors security)) 3 → RationalResult)
    (value : (Fin 3 → ℕ) → ℚ) (hmass : ∀ source, (mass source).data.decode=value (fun index => (source.get index).val)) :
    (BinaryCoefficientDensity.current security bits slots output mass).data.decode=
      RationalLegCoefficientExtraction.density security bits value selected (fun index => (output.get index).val) := by
  rw [BinaryCoefficientDensity.sum_value security bits slots output mass value hmass]
  unfold RationalLegCoefficientExtraction.density
  apply Finset.sum_congr rfl
  intro source _
  congr 1
  rw [← Equiv.prod_comp (Finset.orderIsoOfFin selected rfl).toEquiv]
  apply Finset.prod_congr rfl
  intro index _
  simp only [hslots,RationalLegCoefficientExtraction.slotNumber]
  change RationalCoefficientExtraction.atom security bits (source ((Finset.orderIsoOfFin selected rfl) index).val).val (output.get index).val=
    RationalLegCoefficientExtraction.atom security bits (source ((Finset.orderIsoOfFin selected rfl) index).val).val
      (output.get ((Finset.orderIsoOfFin selected rfl).symm ((Finset.orderIsoOfFin selected rfl) index))).val
  rw [OrderIso.symm_apply_apply]
  rfl

theorem normalized_value (security bits : ℕ) (selected : Finset (Fin 3)) (slots : Vector (Fin 3) selected.card)
    (hslots : ∀ index, slots.get index=((Finset.orderIsoOfFin selected rfl) index).val)
    (output : Vector (Fin (colors security)) selected.card) (mass : Vector (Fin (colors security)) 3 → RationalResult)
    (value : (Fin 3 → ℕ) → ℚ) (hmass : ∀ source, (mass source).data.decode=value (fun index => (source.get index).val)) :
    (BinaryCoefficientExtraction.normalized security bits slots output mass).data.decode=
      RationalLegCoefficientExtraction.normalized security bits value selected (fun index => (output.get index).val) :=
  BinaryDensityInverseTensor.current_value security bits selected.card output _ _
    (fun source => density_value security bits selected slots hslots source mass value hmass)

noncomputable section
open scoped Classical

theorem current_value (security bits : ℕ) (selected : Finset (Fin 3)) (slots : Vector (Fin 3) selected.card)
    (hslots : ∀ index, slots.get index=((Finset.orderIsoOfFin selected rfl) index).val)
    (program : BinaryStoredSymmetrization.Program selected.card)
    (hprogram : program.meaning RationalBits.decode=BinaryStoredSymmetrization.meanSyntax selected.card)
    (output : Vector (Fin (colors security)) selected.card) (mass : Vector (Fin (colors security)) 3 → RationalResult)
    (value : (Fin 3 → ℕ) → ℚ) (hmass : ∀ source, (mass source).data.decode=value (fun index => (source.get index).val)) :
    (BinaryCoefficientExtraction.current security bits slots program output mass).data.decode=
      RationalLegCoefficientExtraction.selectedKernel security bits value selected (fun index => (output.get index).val) :=
  BinaryStoredSymmetrization.current_value security program hprogram output _ _
    (fun source => normalized_value security bits selected slots hslots source mass value hmass)

end
end CurrentAFT.BinaryLegCoefficientExtraction
