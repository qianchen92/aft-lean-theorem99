import CurrentAFT.RationalFamilyProductProgram
import CurrentAFT.BackgroundFamilies

/-! # Literal degree-one data of a mixed primary/body certificate -/
namespace CurrentAFT.RationalBackgroundTable
open AFT ControlCoordinates ControlProduct GradedControlAlgebra BackgroundFamilies
open scoped BigOperators
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

def firstTable {Scalar Primary Body : Type*} [Zero Scalar] (order : ℕ)
    (primary : Primary → Scalar) (body : Body → Scalar) : RationalFamilyProductProgram.Table Scalar Primary Body order :=
  fun arity colors centers =>
    if h : arity.val.1.val = 1 ∧ arity.val.2.val = 0 then primary (colors ⟨0, by omega⟩)
    else if h : arity.val.1.val = 0 ∧ arity.val.2.val = 1 then body (centers ⟨0, by omega⟩) else 0

noncomputable section
open scoped Classical
local instance tableFinDecidableEq (count : ℕ) : DecidableEq (Fin count) := Classical.decEq _

private theorem primaryShape (order : ℕ) (horder : 1 ≤ order) (arity : TruncatedArity order) :
    arity = primaryArity order horder ↔ arity.val.1.val = 1 ∧ arity.val.2.val = 0 := by
  constructor
  · rintro rfl; exact ⟨rfl, rfl⟩
  · intro h
    apply Subtype.ext
    exact Prod.ext (Fin.ext h.1) (Fin.ext h.2)

private theorem bodyShape (order : ℕ) (horder : 1 ≤ order) (arity : TruncatedArity order) :
    arity = bodyArity order horder ↔ arity.val.1.val = 0 ∧ arity.val.2.val = 1 := by
  constructor
  · rintro rfl; exact ⟨rfl, rfl⟩
  · intro h
    apply Subtype.ext
    exact Prod.ext (Fin.ext h.1) (Fin.ext h.2)

theorem firstTable_actual {Primary Body : Type*} [Fintype Primary] [Fintype Body]
    (primary : FiniteDist Primary) (body : FiniteDist Body) (order : ℕ) (horder : 1 ≤ order)
    (first : Primary → ℝ) (second : Body → ℝ)
    (hf : ∑ color, primary.weight color*first color = 0) (hs : ∑ color, body.weight color*second color = 0) :
    firstTable order first second = fun arity =>
      ((primaryFamily primary body order horder first hf+bodyFamily primary body order horder second hs) arity).val := by
  funext arity colors centers
  by_cases hp : arity = primaryArity order horder
  · subst arity
    simp [firstTable, primaryFamily, bodyFamily, primaryArity, bodyArity, primaryKernel, bodyKernel]
  · by_cases hb : arity = bodyArity order horder
    · subst arity
      simp [firstTable, primaryFamily, bodyFamily, primaryArity, bodyArity, primaryKernel, bodyKernel]
    · have hfirst := mt (primaryShape order horder arity).mpr hp
      have hsecond := mt (bodyShape order horder arity).mpr hb
      simp only [firstTable, dif_neg hfirst, dif_neg hsecond, Pi.add_apply, primaryFamily, bodyFamily,
        Pi.single_eq_of_ne hp, Pi.single_eq_of_ne hb, Submodule.coe_zero, Pi.zero_apply, add_zero]

theorem primaryFamily_add {Primary Body : Type*} [Fintype Primary] [Fintype Body]
    (primary : FiniteDist Primary) (body : FiniteDist Body) (order : ℕ) (horder : 1 ≤ order)
    (first second : Primary → ℝ)
    (hf : ∑ color, primary.weight color*first color=0) (hs : ∑ color, primary.weight color*second color=0)
    (ht : ∑ color, primary.weight color*(first color+second color)=0) :
    primaryFamily primary body order horder (fun color => first color+second color) ht =
      primaryFamily primary body order horder first hf+primaryFamily primary body order horder second hs := by
  unfold primaryFamily
  rw [← Pi.single_add]
  congr 1

theorem firstTable_error {Primary Body : Type*} (order : ℕ) (firstQ secondQ : ℕ → ℚ)
    (first : Primary → ℝ) (second : Body → ℝ) (primaryCode : Primary → ℕ) (bodyCode : Body → ℕ)
    (firstError secondError : ℝ) (hf : 0 ≤ firstError) (hs : 0 ≤ secondError)
    (hfirst : ∀ color, |(firstQ (primaryCode color):ℝ)-first color| ≤ firstError)
    (hsecond : ∀ color, |(secondQ (bodyCode color):ℝ)-second color| ≤ secondError)
    (arity : TruncatedArity order) (colors : Fin arity.val.1.val → Primary) (centers : Fin arity.val.2.val → Body) :
    |(firstTable order firstQ secondQ arity (fun index => primaryCode (colors index)) (fun index => bodyCode (centers index)):ℝ)-
      firstTable order first second arity colors centers| ≤ firstError+secondError := by
  unfold firstTable
  split_ifs
  · exact (hfirst _).trans (le_add_of_nonneg_right hs)
  · exact (hsecond _).trans (le_add_of_nonneg_left hf)
  · simpa only [Rat.cast_zero, sub_self, abs_zero] using add_nonneg hf hs

end
end CurrentAFT.RationalBackgroundTable
