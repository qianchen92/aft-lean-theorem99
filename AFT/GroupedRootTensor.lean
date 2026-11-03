import AFT.RootTensorActivity
import AFT.MixedFiberLower

/-! # Joint root channels with variable-size physical output groups -/
namespace AFT.RootTensor
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {Index Source Color : Type*} [Fintype Index] [DecidableEq Index]
  [Fintype Source] [Fintype Color]
variable (Slots : Index → Type*) [∀ index,Fintype (Slots index)]
local instance groupedRootSigmaDecEq : DecidableEq (Sigma Slots) := Classical.decEq _
local instance groupedRootLocalDecEq (index : Index) : DecidableEq (Slots index) := Classical.decEq _

/-- The whole input root coefficient is integrated against the product of
actual local channels; output groups need not have the same size. -/
def groupedDensity (source : Index → FiniteDist Source)
    (matrix : (index : Index) → Source → (Slots index → Color) → ℝ)
    (kernel : (Index → Source) → ℝ) (output : Sigma Slots → Color) : ℝ :=
  (FiniteDist.independent source).expectation (fun roots => kernel roots*
    ∏ index,matrix index (roots index) (fun slot => output ⟨index,slot⟩))

theorem expectation_sigma_product (reference : Sigma Slots → FiniteDist Color)
    (functions : (index : Index) → (Slots index → Color) → ℝ) :
    (FiniteDist.independent reference).expectation
      (fun output => ∏ index,functions index (fun slot => output ⟨index,slot⟩)) =
      ∏ index,(FiniteDist.independent (fun slot : Slots index => reference ⟨index,slot⟩)).expectation
        (functions index) := by
  have he := (Equiv.piCurry (fun index (_ : Slots index) => Color)).sum_comp
    (fun output => ∏ index,((∏ slot,(reference ⟨index,slot⟩).weight (output index slot))*functions index (output index)))
  unfold FiniteDist.expectation FiniteDist.independent
  simp only [Fintype.prod_sigma,← Finset.prod_mul_distrib]
  apply Eq.trans ?_ (he.trans (Fintype.prod_sum (fun index (output : Slots index → Color) => (∏ slot,(reference ⟨index,slot⟩).weight (output slot))*functions index output)).symm)
  apply Finset.sum_congr (by ext; simp)
  intro output _
  rfl

/-- Finite Fubini and one joint Cauchy--Schwarz give the full density
energy, without a rank-one decomposition of the root coefficient. -/
theorem groupedDensity_energy_le (source : Index → FiniteDist Source)
    (reference : Sigma Slots → FiniteDist Color)
    (matrix : (index : Index) → Source → (Slots index → Color) → ℝ)
    (bound : Index → ℝ)
    (hlocal : ∀ index,(FiniteDist.independent (fun slot : Slots index => reference ⟨index,slot⟩)).expectation
      (fun output => (source index).l2Sq (fun root => matrix index root output)) ≤ bound index^2)
    (kernel : (Index → Source) → ℝ) :
    (FiniteDist.independent reference).l2Sq (groupedDensity Slots source matrix kernel) ≤
      (∏ index,bound index^2)*(FiniteDist.independent source).l2Sq kernel := by
  have hpoint (output : Sigma Slots → Color) : groupedDensity Slots source matrix kernel output^2 ≤
      (FiniteDist.independent source).l2Sq kernel*
        ∏ index,(source index).l2Sq (fun root => matrix index root (fun slot => output ⟨index,slot⟩)) := by
    have hh : groupedDensity Slots source matrix kernel output^2 ≤
        (FiniteDist.independent source).l2Sq kernel*
          (FiniteDist.independent source).l2Sq (fun roots =>
            ∏ index,matrix index (roots index) (fun slot => output ⟨index,slot⟩)) := by
      unfold groupedDensity FiniteDist.l2Sq FiniteDist.expectation
      apply Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul
      · intro roots _; exact mul_nonneg (FiniteDist.nonneg _ _) (sq_nonneg _)
      · intro roots _; exact mul_nonneg (FiniteDist.nonneg _ _) (sq_nonneg _)
      · intro roots _; ring
    apply hh.trans_eq
    congr 1
    simp only [FiniteDist.l2Sq,← Finset.prod_pow]
    exact expectation_product source (fun index root => matrix index root (fun slot => output ⟨index,slot⟩)^2)
  calc
    _ ≤ (FiniteDist.independent reference).expectation (fun output =>
        (FiniteDist.independent source).l2Sq kernel*
          ∏ index,(source index).l2Sq (fun root => matrix index root (fun slot => output ⟨index,slot⟩))) :=
      Finset.sum_le_sum fun output _ => mul_le_mul_of_nonneg_left (hpoint output) (FiniteDist.nonneg _ _)
    _ = (FiniteDist.independent source).l2Sq kernel*
        ∏ index,(FiniteDist.independent (fun slot : Slots index => reference ⟨index,slot⟩)).expectation
          (fun output => (source index).l2Sq (fun root => matrix index root output)) := by
      rw [FiniteDist.expectation_const_mul]
      congr 1
      exact expectation_sigma_product Slots reference
        (fun index output => (source index).l2Sq (fun root => matrix index root output))
    _ ≤ _ := by
      rw [mul_comm (∏ index,bound index^2)]
      apply mul_le_mul_of_nonneg_left _ (FiniteDist.l2Sq_nonneg _ _)
      exact Finset.prod_le_prod (fun index _ => Finset.sum_nonneg fun output _ =>
        mul_nonneg (FiniteDist.nonneg _ _) (FiniteDist.l2Sq_nonneg _ _)) (fun index _ => hlocal index)

/-- The actual reference lower bound supplies every fixed-output fiber
simultaneously. This version works for arbitrary variable-sized groups. -/
theorem groupedDensity_activity_le (source : Index → FiniteDist Source)
    (reference : Sigma Slots → FiniteDist Color)
    (matrix : (index : Index) → Source → (Slots index → Color) → ℝ)
    (bound : Index → ℝ) (hb : ∀ index,0≤bound index)
    (hlocal : ∀ index,(FiniteDist.independent (fun slot : Slots index => reference ⟨index,slot⟩)).expectation
      (fun output => (source index).l2Sq (fun root => matrix index root output)) ≤ bound index^2)
    (lower rate : ℝ) (hlower : 0<lower) (hrate : 0≤rate)
    (href : ∀ slot color,lower≤(reference slot).weight color)
    (kernel : (Index → Source) → ℝ) :
    MixedKernel.activity (fun _ : Sigma Slots => rate) reference (groupedDensity Slots source matrix kernel) ≤
      (rate*(1+rate/Real.sqrt lower))^Fintype.card (Sigma Slots)*
        (∏ index,bound index)*Real.sqrt ((FiniteDist.independent source).l2Sq kernel) := by
  have hh := MixedKernel.activity_le_lower reference lower hlower href rate hrate
    (groupedDensity Slots source matrix kernel)
  apply hh.trans
  have he := Real.sqrt_le_sqrt (groupedDensity_energy_le Slots source reference matrix bound hlocal kernel)
  have hp : 0≤∏ index,bound index := Finset.prod_nonneg fun index _ => hb index
  rw [Finset.prod_pow,Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq hp] at he
  have hi := mul_le_mul_of_nonneg_left he
    (show 0≤rate^Fintype.card (Sigma Slots)*(1+rate/Real.sqrt lower)^Fintype.card (Sigma Slots) by positivity)
  exact hi.trans_eq (by rw [mul_pow]; ring)


/-- A separately canonical coefficient in every physical group remains
canonical after integration against one arbitrary joint root kernel. -/
theorem groupedDensity_canonical (source : Index → FiniteDist Source)
    (reference : Sigma Slots → FiniteDist Color)
    (matrix : (index : Index) → Source → (Slots index → Color) → ℝ)
    (hcanonical : ∀ index root,Hoeffding.Canonical
      (fun slot : Slots index => reference ⟨index,slot⟩) Finset.univ (matrix index root))
    (kernel : (Index → Source) → ℝ) :
    Hoeffding.Canonical reference Finset.univ (groupedDensity Slots source matrix kernel) := by
  constructor
  · intro first second h
    have he : first=second := funext fun slot => h slot (Finset.mem_univ _)
    rw [he]
  · intro selected _ word
    rcases selected with ⟨index,slot⟩
    unfold groupedDensity FiniteDist.expectation
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro roots _
    have hsame (color : Color) :
        (fun part : Slots index => Function.update word ⟨index,slot⟩ color ⟨index,part⟩) =
          Function.update (fun part : Slots index => word ⟨index,part⟩) slot color := by
      funext part
      by_cases he : part=slot
      · subst part; simp
      · simp [Function.update_of_ne he,show (⟨index,part⟩ : Sigma Slots) ≠ ⟨index,slot⟩ by
          intro hh; exact he (eq_of_heq (Sigma.mk.inj_iff.mp hh).2)]
    have hother (other : Index) (hne : other ≠ index) (color : Color) :
        (fun part : Slots other => Function.update word ⟨index,slot⟩ color ⟨other,part⟩) =
          fun part : Slots other => word ⟨other,part⟩ := by
      funext part
      apply Function.update_of_ne
      intro hh
      exact hne (congrArg Sigma.fst hh)
    have hprod (color : Color) :
        (∏ other,matrix other (roots other)
          (fun part => Function.update word ⟨index,slot⟩ color ⟨other,part⟩)) =
        matrix index (roots index) (Function.update (fun part => word ⟨index,part⟩) slot color)*
          ∏ other ∈ (Finset.univ : Finset Index).erase index,
            matrix other (roots other) (fun part => word ⟨other,part⟩) := by
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ index),hsame]
      congr 1
      apply Finset.prod_congr rfl
      intro other ho
      rw [hother other (Finset.mem_erase.mp ho).1]
    simp only [hprod]
    calc
      _ = ((FiniteDist.independent source).weight roots*kernel roots*
          ∏ other ∈ (Finset.univ : Finset Index).erase index,
            matrix other (roots other) (fun part => word ⟨other,part⟩))*
          ∑ color,(reference ⟨index,slot⟩).weight color*
            matrix index (roots index) (Function.update (fun part => word ⟨index,part⟩) slot color) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro color _
        ring
      _ = 0 := by rw [(hcanonical index (roots index)).2 slot (Finset.mem_univ _) _,mul_zero]

end
end AFT.RootTensor
