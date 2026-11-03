import AFT.FixedOrderNumberingProgram
import AFT.PendingHigherColumns
import AFT.IndependentInverseProgram

/-! # Exact executable local U replacement using stored fixed-order numbering -/
namespace AFT.RationalNumerics
open scoped BigOperators

/-- Only finite stored indices, a finite palette sum, and the supplied old
joint kernel and new-coordinate columns are used at runtime. -/
def storedHigherKernel {Value : Type*} [AddCommMonoid Value] [Mul Value] {bound colors : ℕ}
    (code : FixedOrderNumberingCode bound) (primary body : ℕ) (hp : primary ≤ bound) (hb : body ≤ bound)
    (point : Fin primary) (mask : Fin 16)
    (kernel : (Fin (primary+body) → Fin colors) → Value)
    (column : Fin colors → (pendingMask mask → Fin colors) → Value) (word : ℕ → Fin colors) : Value :=
  ∑ color,kernel (Fin.addCases
    (fun old => if old=point then color else
      word (code.primaryLookup ⟨primary,by omega⟩ ⟨point.val,by omega⟩ mask ⟨old.val+4,by omega⟩))
    (fun old => word ((pendingMask mask).card+(primary-1)+
      code.bodyLookup ⟨body,by omega⟩ ⟨old.val,by omega⟩)))*
    column color (fun new => word
      (code.primaryLookup ⟨primary,by omega⟩ ⟨point.val,by omega⟩ mask ⟨new.val.val,by omega⟩))

def pendingHigherProgram {bound colors : ℕ} (code : FixedOrderNumberingCode bound)
    (constant n : ℕ) (beta : ℚ) (primary body : ℕ) (hp : primary ≤ bound) (hb : body ≤ bound)
    (point : Fin primary) (mask : Fin 16) (kernel : (Fin (primary+body) → Fin colors) → ℚ)
    (word : ℕ → Fin colors) : ℚ :=
  storedHigherKernel code primary body hp hb point mask kernel
    (fun color => V7Calibration.independentInverseProgram constant n beta color.val (pendingMask mask)) word

noncomputable section
open RepresentedPolynomial V7Calibration GaussianSource
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 450000
local instance storedPendingHigherFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _

private theorem pending_primary_count (primary : ℕ) (point : Fin primary) (selected : Finset (Fin 4)) :
    Fintype.card (selected ⊕ {other : Fin primary // other≠point})=selected.card+(primary-1) := by
  have hh := Fintype.card_congr (primarySplitEquiv point)
  simp only [Fintype.card_sum,Fintype.card_unique,Fintype.card_fin] at hh
  simp only [Fintype.card_sum,Fintype.card_coe]
  omega

/-- The stored-coordinate program has exactly the same literal kernel as
the proved analytic pending replacement. -/
theorem storedHigherKernel_exact {bound : ℕ} (code : FixedOrderNumberingCode bound)
    (hprimary : ∀ order point mask slot,code.primaryLookup order point mask slot=pendingNumberingMeaning order point mask slot)
    (hbody : ∀ order slot,code.bodyLookup order slot=bodyNumberingMeaning order slot)
    (C : ℝ) (n : ℕ) (beta : ℝ)
    (operator : (Fin (Parameters.modulus n) → ℝ) ≃ₗ[ℝ] (Fin (Parameters.modulus n) → ℝ))
    (charts : (mark : Fin (Parameters.modulus n)) → PublicChartFamily C n mark)
    (seed : InputSeed (Fin (Parameters.modulus n))) (hp : seed.primaryOrder ≤ bound) (hb : seed.bodyOrder ≤ bound)
    (point : Fin seed.primaryOrder) (mask : Fin 16) (word : ℕ → Fin (Parameters.modulus n)) :
    storedHigherKernel code seed.primaryOrder seed.bodyOrder hp hb point mask seed.kernel
      (independentInverseColumn C n beta operator charts (pendingMask mask)) word=
      (pendingPrimaryHigherSeed C n beta operator charts seed point (pendingMask mask)).kernel (fun slot => word slot.val) := by
  rw [pendingPrimaryHigherSeed_columns]
  unfold storedHigherKernel
  apply Finset.sum_congr rfl
  intro color _
  congr 1
  · congr 1
    funext slot
    refine Fin.addCases ?_ ?_ slot
    · intro old
      simp only [Fin.addCases_left]
      by_cases ho : old=point
      · simp only [ho,if_true,dif_pos]
      · simp only [if_neg ho,dif_neg ho]
        rw [hprimary]
        exact congrArg word (pendingNumberingMeaning_old ⟨seed.primaryOrder,by omega⟩
          ⟨point.val,by omega⟩ point.isLt mask ⟨old,ho⟩)
    · intro old
      simp only [Fin.addCases_right]
      rw [hbody,bodyNumberingMeaning_exact,pending_primary_count]
  · congr 1
    funext new
    rw [hprimary]
    exact congrArg word (pendingNumberingMeaning_new ⟨seed.primaryOrder,by omega⟩
      ⟨point.val,by omega⟩ point.isLt mask new)

end
end AFT.RationalNumerics
