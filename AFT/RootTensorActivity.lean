import AFT.RootProfileChannel
import AFT.MixedKernel
import AFT.FiniteExpectationAlgebra

/-! # Mixed fibers of genuinely joint root tensors

The root coefficient is retained as one arbitrary joint function.  Only the
actual independent root reference is factored; the coefficient itself is not.
-/
namespace AFT.RootTensor
open scoped BigOperators Classical
noncomputable section
variable {Slot Source Color : Type*} [Fintype Slot] [DecidableEq Slot]
  [Fintype Source] [Fintype Color]

/-- A signed joint root coefficient passed through all its actual local
centered output density channels. -/
def density (source : Slot → FiniteDist Source) (matrix : Slot → Source → Color → ℝ)
    (kernel : (Slot → Source) → ℝ) (word : Slot → Color) : ℝ :=
  (FiniteDist.independent source).expectation
    (fun roots => kernel roots * ∏ slot, matrix slot (roots slot) (word slot))

theorem expectation_product (source : Slot → FiniteDist Source)
    (functions : Slot → Source → ℝ) :
    (FiniteDist.independent source).expectation (fun roots => ∏ slot,functions slot (roots slot)) =
      ∏ slot,(source slot).expectation (functions slot) := by
  unfold FiniteDist.expectation FiniteDist.independent
  simp only [← Finset.prod_mul_distrib]
  rw [Fintype.prod_sum]

omit [Fintype Color] in
/-- The pointwise square estimate uses Cauchy--Schwarz once on the entire
joint root input, including every dependence among the active sources. -/
theorem density_square_le (source : Slot → FiniteDist Source)
    (matrix : Slot → Source → Color → ℝ) (kernel : (Slot → Source) → ℝ)
    (word : Slot → Color) :
    density source matrix kernel word ^ 2 ≤
      (FiniteDist.independent source).l2Sq kernel *
        ∏ slot,(source slot).l2Sq (fun root => matrix slot root (word slot)) := by
  have hcs : density source matrix kernel word ^ 2 ≤
      (FiniteDist.independent source).l2Sq kernel *
        (FiniteDist.independent source).l2Sq (fun roots => ∏ slot,matrix slot (roots slot) (word slot)) := by
    unfold density FiniteDist.expectation FiniteDist.l2Sq
    apply Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul
    · intro roots _; exact mul_nonneg (FiniteDist.nonneg _ _) (sq_nonneg _)
    · intro roots _; exact mul_nonneg (FiniteDist.nonneg _ _) (sq_nonneg _)
    · intro roots _; ring
  apply hcs.trans_eq
  congr 1
  simp only [FiniteDist.l2Sq,← Finset.prod_pow]
  exact expectation_product source (fun slot root => matrix slot root (word slot)^2)

/-- A fixed fiber has exactly one local row factor at each frozen output,
and one integrated local factor at every remaining output. -/
theorem density_fiberSq_le (source : Slot → FiniteDist Source)
    (reference : Slot → FiniteDist Color) (matrix : Slot → Source → Color → ℝ)
    (full row : Slot → ℝ)
    (hfull : ∀ slot,(reference slot).expectation
      (fun color => (source slot).l2Sq (fun root => matrix slot root color)) ≤ full slot ^ 2)
    (hrow : ∀ slot color,(source slot).l2Sq (fun root => matrix slot root color) ≤ row slot ^ 2)
    (kernel : (Slot → Source) → ℝ) (fixed : Finset Slot) (values : Slot → Color) :
    MixedKernel.fiberSq reference (density source matrix kernel) fixed values ≤
      (FiniteDist.independent source).l2Sq kernel *
        ∏ slot,(if slot ∈ fixed then row slot else full slot)^2 := by
  let localEnergy := fun slot color => (source slot).l2Sq (fun root => matrix slot root color)
  have hfactor : (FiniteDist.independent reference).expectation
      (fun integrated => ∏ slot,localEnergy slot (MixedKernel.freeze fixed values integrated slot)) =
      ∏ slot,(reference slot).expectation (fun color =>
        localEnergy slot (if slot ∈ fixed then values slot else color)) := by
    exact expectation_product reference (fun slot color => localEnergy slot (if slot ∈ fixed then values slot else color))
  calc
    _ ≤ (FiniteDist.independent reference).expectation (fun integrated =>
        (FiniteDist.independent source).l2Sq kernel *
          ∏ slot,localEnergy slot (MixedKernel.freeze fixed values integrated slot)) := by
      apply Finset.sum_le_sum
      intro integrated _
      exact mul_le_mul_of_nonneg_left (density_square_le source matrix kernel _) (FiniteDist.nonneg _ _)
    _ = (FiniteDist.independent source).l2Sq kernel *
        ∏ slot,(reference slot).expectation (fun color =>
          localEnergy slot (if slot ∈ fixed then values slot else color)) := by
      rw [FiniteDist.expectation_const_mul,hfactor]
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (FiniteDist.l2Sq_nonneg _ _)
      apply Finset.prod_le_prod
      · intro slot _
        exact Finset.sum_nonneg fun color _ => mul_nonneg (FiniteDist.nonneg _ _) (FiniteDist.l2Sq_nonneg _ _)
      · intro slot _
        by_cases hs : slot ∈ fixed
        · simp only [if_pos hs,FiniteDist.expectation_const]
          exact hrow slot (values slot)
        · simp only [if_neg hs]
          exact hfull slot

theorem density_fiberNorm_le (source : Slot → FiniteDist Source)
    (reference : Slot → FiniteDist Color) (matrix : Slot → Source → Color → ℝ)
    (full row : Slot → ℝ) (hfull0 : ∀ slot,0 ≤ full slot) (hrow0 : ∀ slot,0 ≤ row slot)
    (hfull : ∀ slot,(reference slot).expectation
      (fun color => (source slot).l2Sq (fun root => matrix slot root color)) ≤ full slot ^ 2)
    (hrow : ∀ slot color,(source slot).l2Sq (fun root => matrix slot root color) ≤ row slot ^ 2)
    (kernel : (Slot → Source) → ℝ) (fixed : Finset Slot) :
    MixedKernel.fiberNorm reference (density source matrix kernel) fixed ≤
      Real.sqrt ((FiniteDist.independent source).l2Sq kernel) *
        ∏ slot,if slot ∈ fixed then row slot else full slot := by
  have hp0 : 0 ≤ ∏ slot,if slot ∈ fixed then row slot else full slot :=
    Finset.prod_nonneg fun slot _ => by split_ifs; exact hrow0 slot; exact hfull0 slot
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg (Real.sqrt_nonneg _) hp0)).mpr
  intro values
  rw [Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _)]
  apply (Real.sqrt_le_sqrt (density_fiberSq_le source reference matrix full row hfull hrow kernel fixed values)).trans_eq
  rw [Finset.prod_pow,Real.sqrt_mul (FiniteDist.l2Sq_nonneg _ _),Real.sqrt_sq hp0]

/-- Summing all genuine fixed-output fibers yields a product of local
Hilbert-plus-row costs, without a palette-size or root-alphabet factor. -/
theorem density_activity_le (source : Slot → FiniteDist Source)
    (reference : Slot → FiniteDist Color) (matrix : Slot → Source → Color → ℝ)
    (rate full row : Slot → ℝ) (hrate : ∀ slot,0 ≤ rate slot)
    (hfull0 : ∀ slot,0 ≤ full slot) (hrow0 : ∀ slot,0 ≤ row slot)
    (hfull : ∀ slot,(reference slot).expectation
      (fun color => (source slot).l2Sq (fun root => matrix slot root color)) ≤ full slot ^ 2)
    (hrow : ∀ slot color,(source slot).l2Sq (fun root => matrix slot root color) ≤ row slot ^ 2)
    (kernel : (Slot → Source) → ℝ) :
    MixedKernel.activity rate reference (density source matrix kernel) ≤
      (∏ slot,rate slot*(full slot+rate slot*row slot)) *
        Real.sqrt ((FiniteDist.independent source).l2Sq kernel) := by
  have hf (fixed : Finset Slot) :
      (∏ slot ∈ fixed,rate slot)*(∏ slot,if slot ∈ fixed then row slot else full slot) =
        (∏ slot ∈ fixed,rate slot*row slot)*(∏ slot ∈ fixedᶜ,full slot) := by
    rw [← Fintype.prod_ite_mem fixed (fun slot => rate slot*row slot),
      ← Fintype.prod_ite_mem fixedᶜ full,← Finset.prod_mul_distrib,
      ← Fintype.prod_ite_mem fixed rate,← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro slot _
    by_cases hs : slot ∈ fixed <;> simp [hs]
  have hsum : (∑ fixed : Finset Slot,(∏ slot ∈ fixed,rate slot)*
      (∏ slot,if slot ∈ fixed then row slot else full slot)) =
      ∏ slot,(full slot+rate slot*row slot) := by
    simp_rw [hf]
    simpa only [add_comm] using (Fintype.prod_add (fun slot => rate slot*row slot) full).symm
  unfold MixedKernel.activity
  calc
    _ ≤ (∏ slot,rate slot)*∑ fixed : Finset Slot,(∏ slot ∈ fixed,rate slot)*
        (Real.sqrt ((FiniteDist.independent source).l2Sq kernel)*
          ∏ slot,if slot ∈ fixed then row slot else full slot) := by
      apply mul_le_mul_of_nonneg_left _ (Finset.prod_nonneg fun slot _ => hrate slot)
      apply Finset.sum_le_sum
      intro fixed _
      exact mul_le_mul_of_nonneg_left
        (density_fiberNorm_le source reference matrix full row hfull0 hrow0 hfull hrow kernel fixed)
        (Finset.prod_nonneg fun slot _ => hrate slot)
    _ = _ := by
      rw [Finset.prod_mul_distrib]
      rw [← hsum,mul_assoc,Finset.sum_mul]
      congr 1
      apply Finset.sum_congr rfl
      intro fixed _
      ring


/-- Centering each local output channel makes the complete joint output
canonical, even for a nonseparable root coefficient. -/
theorem density_canonical (source : Slot → FiniteDist Source)
    (reference : Slot → FiniteDist Color) (matrix : Slot → Source → Color → ℝ)
    (hcenter : ∀ slot root,(reference slot).expectation (matrix slot root)=0)
    (kernel : (Slot → Source) → ℝ) :
    Hoeffding.Canonical reference Finset.univ (density source matrix kernel) := by
  have hd : (inferInstance : DecidableEq Slot)=Classical.decEq Slot := Subsingleton.elim _ _
  cases hd
  constructor
  · intro first second h
    have he : first=second := funext fun slot => h slot (Finset.mem_univ _)
    rw [he]
  · intro slot _ word
    unfold density FiniteDist.expectation
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro roots _
    have hprod (color : Color) :
        (∏ other,matrix other (roots other) (Function.update word slot color other)) =
          matrix slot (roots slot) color * ∏ other ∈ (Finset.univ : Finset Slot).erase slot,
            matrix other (roots other) (word other) := by
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ slot)]
      simp only [Function.update_self]
      congr 1
      apply Finset.prod_congr rfl
      intro other ho
      rw [Function.update_of_ne (Finset.mem_erase.mp ho).1]
    simp only [hprod]
    calc
      _ = ((FiniteDist.independent source).weight roots*kernel roots*
          ∏ other ∈ (Finset.univ : Finset Slot).erase slot,matrix other (roots other) (word other))*
          (reference slot).expectation (matrix slot (roots slot)) := by
        unfold FiniteDist.expectation
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro color _
        ring
      _ = 0 := by rw [hcenter,mul_zero]

end
end AFT.RootTensor
