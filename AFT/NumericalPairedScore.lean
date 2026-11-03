import AFT.PairedTableMoment
import AFT.ActualPairedPublic

/-! # Stability of complete joint paired scores under numerical perturbation

The estimates compare actual finite tensors and actual sampling without
replacement. They retain arbitrary joint kernels and signed coefficients.
-/
namespace AFT.RationalNumerics
open CanonicalMoments
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false

 theorem abs_prod_le_power {Index : Type*} (set : Finset Index) (value : Index → ℝ)
    (bound : ℝ) (_hb : 0 ≤ bound) (hv : ∀ i∈set,|value i| ≤ bound) :
    |∏ i∈set,value i| ≤ bound^set.card := by
  rw [Finset.abs_prod]
  calc
    _  ≤  ∏ _i∈set,bound := Finset.prod_le_prod (fun _ _ => abs_nonneg _) hv
    _ = _ := by simp

/-- A uniform product perturbation bound valid also in degree zero. -/
theorem abs_prod_sub_prod_le {Index : Type*} (set : Finset Index) (first second : Index → ℝ)
    (bound error : ℝ) (hb : 1 ≤ bound) (he : 0 ≤ error)
    (hf : ∀ i∈set,|first i| ≤ bound) (hg : ∀ i∈set,|second i| ≤ bound)
    (hd : ∀ i∈set,|first i-second i| ≤ error) :
    |(∏ i∈set,first i)-(∏ i∈set,second i)| ≤ (set.card : ℝ)*error*bound^set.card := by
  classical
  induction set using Finset.induction_on with
  | empty => simp
  | @insert index set hn ih =>
    have hfs := fun i hi => hf i (Finset.mem_insert_of_mem hi)
    have hgs := fun i hi => hg i (Finset.mem_insert_of_mem hi)
    have hds := fun i hi => hd i (Finset.mem_insert_of_mem hi)
    have hp := abs_prod_le_power set first bound (by linarith) hfs
    have hi := ih hfs hgs hds
    simp only [Finset.prod_insert hn,Finset.card_insert_of_notMem hn,Nat.cast_add,Nat.cast_one]
    rw [show first index*(∏ i∈set,first i)-second index*(∏ i∈set,second i)=
      (first index-second index)*(∏ i∈set,first i)+
        second index*((∏ i∈set,first i)-(∏ i∈set,second i)) by ring]
    calc
      _  ≤  |first index-second index| *|∏ i∈set,first i|+
          |second index| *|(∏ i∈set,first i)-(∏ i∈set,second i)| := by
        simpa only [abs_mul] using abs_add_le ((first index-second index)*(∏ i∈set,first i))
          (second index*((∏ i∈set,first i)-(∏ i∈set,second i)))
      _  ≤  error*bound^set.card+bound*((set.card : ℝ)*error*bound^set.card) := by
        exact add_le_add (mul_le_mul (hd index (Finset.mem_insert_self _ _)) hp (abs_nonneg _) he)
          (mul_le_mul (hg index (Finset.mem_insert_self _ _)) hi (abs_nonneg _) (by linarith))
      _  ≤  error*bound^(set.card+1)+bound*((set.card : ℝ)*error*bound^set.card) := by
        exact add_le_add (mul_le_mul_of_nonneg_left
          (pow_le_pow_right₀ hb (Nat.le_succ set.card)) he) (le_refl _)
      _ = _ := by rw [pow_succ]; ring

/-- Simultaneous errors in every scalar matrix and in an arbitrary joint
kernel give an explicit fixed-degree bound on the actual public score. -/
theorem matrixApply_perturbation {Slot Input Output : Type*}
    [Fintype Slot] [DecidableEq Slot] [Fintype Input] [Fintype Output]
    (matrix approximateMatrix : Slot → Input → Output → ℝ)
    (kernel approximateKernel : (Slot → Input) → ℝ)
    (bound kernelBound matrixError kernelError : ℝ)
    (hb : 1 ≤ bound) (hk : 0 ≤ kernelBound) (he : 0 ≤ matrixError) (hf : 0 ≤ kernelError)
    (hm : ∀ slot input output,|matrix slot input output| ≤ bound)
    (ha : ∀ slot input output,|approximateMatrix slot input output| ≤ bound)
    (hd : ∀ slot input output,|approximateMatrix slot input output-matrix slot input output| ≤ matrixError)
    (hkernel : ∀ word,|kernel word| ≤ kernelBound)
    (happrox : ∀ word,|approximateKernel word-kernel word| ≤ kernelError)
    (output : Slot → Output) :
    |MixedKernel.matrixApply approximateMatrix approximateKernel output-
      MixedKernel.matrixApply matrix kernel output| ≤ 
    (Fintype.card Input : ℝ)^Fintype.card Slot*
      (kernelError+kernelBound*(Fintype.card Slot : ℝ)*matrixError)*bound^Fintype.card Slot := by
  have hword (word : Slot → Input) :
      |approximateKernel word*(∏ slot,approximateMatrix slot (word slot) (output slot))-
        kernel word*(∏ slot,matrix slot (word slot) (output slot))| ≤ 
      (kernelError+kernelBound*(Fintype.card Slot : ℝ)*matrixError)*bound^Fintype.card Slot := by
    have hp := abs_prod_le_power Finset.univ (fun slot => approximateMatrix slot (word slot) (output slot))
      bound (by linarith) (fun slot _ => ha slot _ _)
    have he' := abs_prod_sub_prod_le Finset.univ
      (fun slot => approximateMatrix slot (word slot) (output slot)) (fun slot => matrix slot (word slot) (output slot))
      bound matrixError hb he (fun slot _ => ha slot _ _) (fun slot _ => hm slot _ _) (fun slot _ => hd slot _ _)
    simp only [Finset.card_univ] at hp he'
    rw [show approximateKernel word*(∏ slot,approximateMatrix slot (word slot) (output slot))-
        kernel word*(∏ slot,matrix slot (word slot) (output slot))=
        (approximateKernel word-kernel word)*(∏ slot,approximateMatrix slot (word slot) (output slot))+
        kernel word*((∏ slot,approximateMatrix slot (word slot) (output slot))-(∏ slot,matrix slot (word slot) (output slot))) by ring]
    apply (abs_add_le _ _).trans
    simp only [abs_mul]
    have hh := add_le_add (mul_le_mul (happrox word) hp (abs_nonneg _) hf)
      (mul_le_mul (hkernel word) he' (abs_nonneg _) hk)
    exact hh.trans_eq (by ring)
  unfold MixedKernel.matrixApply
  rw [← Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  have hh := Finset.sum_le_sum (s:=Finset.univ) (fun word _ => hword word)
  simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Fintype.card_fun,Nat.cast_pow,mul_assoc] using hh

/-- Actual two-pool sampling without replacement is a contraction for
uniform kernel error, including the empty set of admissible placements. -/
theorem twoPoolStatistic_perturbation {PS BS PP BP Color : Type*}
    [Fintype PS] [Fintype BS] [Fintype PP] [Fintype BP] [Fintype Color]
    (first second : ((PS ⊕ BS) → Color) → ℝ) (error : ℝ) (he : 0 ≤ error)
    (herror : ∀ word,|first word-second word| ≤ error) (word : (PP ⊕ BP) → Color) :
    |twoPoolStatistic first word-twoPoolStatistic second word| ≤ error := by
  have hcard : (Fintype.card ((PS ↪ PP) × (BS ↪ BP)) : ℝ)=
      ((Fintype.card PP).descFactorial (Fintype.card PS) : ℝ)*
        ((Fintype.card BP).descFactorial (Fintype.card BS) : ℝ) := by
    simp [Fintype.card_prod,Fintype.card_embedding_eq]
  unfold twoPoolStatistic
  rw [←hcard,←sub_div,←Finset.sum_sub_distrib,abs_div,abs_of_nonneg (show (0 : ℝ) ≤ (Fintype.card ((PS ↪ PP) × (BS ↪ BP)) : ℝ) from Nat.cast_nonneg _)]
  by_cases hz : Fintype.card ((PS ↪ PP) × (BS ↪ BP))=0
  · simp only [hz,Nat.cast_zero,div_zero]
    exact he
  · have hp : 0<(Fintype.card ((PS ↪ PP) × (BS ↪ BP)) : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hz
    apply (div_le_iff₀ hp).mpr
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    have hh := Finset.sum_le_sum (s:=Finset.univ) (fun placement : (PS ↪ PP) × (BS ↪ BP) =>
      fun _ => herror (word ∘ placement.1.sumMap placement.2))
    simpa only [placedKernel,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_comm] using hh

/-- Signed coefficient cancellation is retained; numerical errors are paid
by the coefficient absolute sum, with no extra term-count multiplier. -/
theorem finiteScore_perturbation {Term State : Type*} [Fintype Term]
    (coefficient approximateCoefficient : Term → ℝ) (value approximateValue : Term → State → ℝ)
    (valueBound valueError coefficientError : Term → ℝ)
    (_hv : ∀ term,0 ≤ valueBound term) (_he : ∀ term,0 ≤ valueError term) (hc : ∀ term,0 ≤ coefficientError term)
    (hvalue : ∀ term state,|value term state| ≤ valueBound term)
    (herror : ∀ term state,|approximateValue term state-value term state| ≤ valueError term)
    (hcoefficient : ∀ term,|approximateCoefficient term-coefficient term| ≤ coefficientError term)
    (state : State) :
    |(∑ term,approximateCoefficient term*approximateValue term state)-
      (∑ term,coefficient term*value term state)| ≤ 
      ∑ term,(|approximateCoefficient term| *valueError term+coefficientError term*valueBound term) := by
  rw [←Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro term _
  rw [show approximateCoefficient term*approximateValue term state-coefficient term*value term state=
    approximateCoefficient term*(approximateValue term state-value term state)+
      (approximateCoefficient term-coefficient term)*value term state by ring]
  apply (abs_add_le _ _).trans
  simp only [abs_mul]
  exact add_le_add (mul_le_mul_of_nonneg_left (herror term state) (abs_nonneg _))
    (mul_le_mul (hcoefficient term) (hvalue term state) (abs_nonneg _) (hc term))

end
end AFT.RationalNumerics
