import CurrentAFT.RationalBackgroundTable
import CurrentAFT.RationalMassLiftProgram

/-! # Literal one-slot primary mass-certificate data -/
namespace CurrentAFT.RationalMassCertificateTable
open AFT GradedControlAlgebra BackgroundFamilies PrimaryMassFamilies ActualControls
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
local instance massFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _

theorem data (security order : ℕ) (horder : 1 ≤ order) (profile : FirstHistogram.Palette security → ℝ)
    (hcenter : PrimaryTensorInverse.MassCentered 1 (PrimaryMassFamilies.oneWordProfile profile))
    (hsymm : ∀ (permutation : Equiv.Perm (Fin 1)) word,
      PrimaryMassFamilies.oneWordProfile profile (word ∘ permutation) = PrimaryMassFamilies.oneWordProfile profile word) :
    RationalBackgroundTable.firstTable order (RationalMassLiftProgram.actual security profile) (fun _ : SafePalette security => (0:ℝ)) =
      fun arity => (PrimaryMassFamilies.massCertificateFamily security order 1 horder
        (PrimaryMassFamilies.oneWordProfile profile) hcenter hsymm arity).val := by
  funext arity colors centers
  by_cases hp : arity = BackgroundFamilies.primaryArity order horder
  · subst arity
    simp only [RationalBackgroundTable.firstTable, BackgroundFamilies.primaryArity, Fin.val_zero, and_self,
      PrimaryMassFamilies.massCertificateFamily, PrimaryMassFamilies.primaryArity, Pi.single_eq_same,
      PrimaryMassFamilies.massLiftKernel]
    exact (RationalMassLiftProgram.massLift_one security profile colors).symm
  · have hshape : ¬(arity.val.1.val=1 ∧ arity.val.2.val=0) := by
      intro hs
      apply hp
      apply Subtype.ext
      exact Prod.ext (Fin.ext hs.1) (Fin.ext hs.2)
    have hmass : arity ≠ PrimaryMassFamilies.primaryArity order 1 horder := hp
    simp only [RationalBackgroundTable.firstTable, dif_neg hshape, PrimaryMassFamilies.massCertificateFamily,
      Pi.single_eq_of_ne hmass, Submodule.coe_zero, Pi.zero_apply]
    split_ifs <;> rfl

end
end CurrentAFT.RationalMassCertificateTable
