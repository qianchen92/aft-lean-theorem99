import AFT.CountedActivationProgram

/-! # Materialized actual scalar source tables for primary calibration

The public modulus, population ratios and three scalar probability arrays
are prepared before any body or pair expectation is evaluated.
-/
namespace AFT.V7Calibration
open GaussianSource RationalNumerics FiniteConvolutionProgram
open scoped BigOperators

structure PrimarySourceTable (constant n : ℕ) where
  modulus : ℕ
  population : ℕ
  dimension : ℕ
  legs : ℕ
  margin : ℕ
  width : ℕ
  boundary : ℤ
  legRate : ℚ
  queueRate : ℚ
  root : Vector ℚ (2*(3*n^2-1)+1)
  leg : Vector ℚ (2*(actualLegCutoffProgram constant n-1)+1)
  queue : Vector ℚ (2*(n^2-1)+1)
  work : ℕ

def countedPrimarySources (constant n : ℕ) : PrimarySourceTable constant n :=
  let modulus := ParameterProgram.modulus n
  let cutoff := countedLegCutoff constant n
  let legs := (max 2 n)^30
  let dimension := modulus.value*(max 2 n)^20
  let population := dimension-2*legs
  let root := Vector.ofFn (fun index : Fin (2*(3*n^2-1)+1) =>
    countedRootTicketMarginal n population (windowIndexEquiv _ index))
  let leg := Vector.ofFn (fun index : Fin (2*(actualLegCutoffProgram constant n-1)+1) =>
    countedWindowTicketWeight (actualAuxiliarySquaredWidth 10 n)
      (actualLegCutoffProgram constant n-1) n (windowIndexEquiv _ index))
  let queue := Vector.ofFn (fun index : Fin (2*(n^2-1)+1) =>
    countedWindowTicketWeight (actualAuxiliarySquaredWidth 1 n) (n^2-1) n (windowIndexEquiv _ index))
  ⟨modulus.value,population,dimension,legs,20*(max 2 n)^2,(max 2 n)^32,
    (20*(max 2 n)^2 : ℕ)-((3*n^2-1)+(cutoff.value-1)+(n^2-1) : ℕ),
    (legs : ℚ)/population,(modulus.value : ℚ)/population,
    Vector.ofFn (fun i => (root.get i).value),Vector.ofFn (fun i => (leg.get i).value),
    Vector.ofFn (fun i => (queue.get i).value),
    modulus.work+2*cutoff.work+(∑ i,(root.get i).work)+(∑ i,(leg.get i).work)+(∑ i,(queue.get i).work)+1000⟩

def primaryTableBodyWeight {constant n : ℕ} (table : PrimarySourceTable constant n)
    (point : ActualBodyProgramSample constant n) : GaussianArithmetic :=
  let root := table.root.get ((windowIndexEquiv _).symm point.1)
  let leg := match point.2.1 with
    | none => GaussianArithmetic.sub (.literal 1) (.literal table.legRate)
    | some value => GaussianArithmetic.mul (.literal table.legRate)
        (.literal (table.leg.get ((windowIndexEquiv _).symm value)))
  let queue := match point.2.2 with
    | none => GaussianArithmetic.sub (.literal 1) (.literal table.queueRate)
    | some value => GaussianArithmetic.mul (.literal table.queueRate)
        (.literal (table.queue.get ((windowIndexEquiv _).symm value)))
  let result := GaussianArithmetic.mul (.literal root) (leg.mul queue)
  ⟨result.value,result.work+12⟩

def primaryTablePairWeight {constant n : ℕ} (table : PrimarySourceTable constant n)
    (point : ActualPairProgramSample constant n) : GaussianArithmetic :=
  let body := primaryTableBodyWeight table point.1
  let result := body.mul (.literal (table.leg.get ((windowIndexEquiv _).symm point.2)))
  ⟨result.value,result.work+2⟩

theorem primaryTableBodyWeight_work {constant n : ℕ} (table : PrimarySourceTable constant n)
    (point : ActualBodyProgramSample constant n) : (primaryTableBodyWeight table point).work=16 := by
  rcases point with ⟨root,leg,queue⟩
  cases leg <;> cases queue <;> rfl

theorem primaryTablePairWeight_work {constant n : ℕ} (table : PrimarySourceTable constant n)
    (point : ActualPairProgramSample constant n) : (primaryTablePairWeight table point).work=19 := by
  simp only [primaryTablePairWeight,GaussianArithmetic.mul,GaussianArithmetic.literal,primaryTableBodyWeight_work]

@[simp] theorem countedPrimarySources_modulus (constant n : ℕ) :
    (countedPrimarySources constant n).modulus=(ParameterProgram.modulus n).value := rfl
@[simp] theorem countedPrimarySources_population (constant n : ℕ) :
    (countedPrimarySources constant n).population=actualRootPopulationProgram n := rfl
@[simp] theorem countedPrimarySources_dimension (constant n : ℕ) :
    (countedPrimarySources constant n).dimension=actualDimensionProgram n := rfl
@[simp] theorem countedPrimarySources_legs (constant n : ℕ) :
    (countedPrimarySources constant n).legs=actualLegPopulationProgram n := rfl
@[simp] theorem countedPrimarySources_margin (constant n : ℕ) :
    (countedPrimarySources constant n).margin=actualSafeMarginProgram n := rfl
@[simp] theorem countedPrimarySources_width (constant n : ℕ) :
    (countedPrimarySources constant n).width=actualAnchorWidthProgram n := rfl
@[simp] theorem countedPrimarySources_boundary (constant n : ℕ) :
    (countedPrimarySources constant n).boundary=actualBoundaryHalfProgram constant n := by
  simp only [countedPrimarySources,countedLegCutoff_value,actualBoundaryHalfProgram,actualSafeMarginProgram]
@[simp] theorem countedPrimarySources_root (constant n : ℕ) (point : Window (3*n^2-1)) :
    (countedPrimarySources constant n).root.get ((windowIndexEquiv _).symm point)=actualRootMarginalProgram n point := by
  simp only [countedPrimarySources,Vector.get_ofFn,countedRootTicketMarginal_value,Equiv.apply_symm_apply]
  rfl
@[simp] theorem countedPrimarySources_leg (constant n : ℕ) (point : Window (actualLegCutoffProgram constant n-1)) :
    (countedPrimarySources constant n).leg.get ((windowIndexEquiv _).symm point)=
      windowTicketWeightProgram (actualAuxiliarySquaredWidth 10 n) (actualLegCutoffProgram constant n-1) n point := by
  simp only [countedPrimarySources,Vector.get_ofFn,countedWindowTicketWeight_value,Equiv.apply_symm_apply]
@[simp] theorem countedPrimarySources_queue (constant n : ℕ) (point : Window (n^2-1)) :
    (countedPrimarySources constant n).queue.get ((windowIndexEquiv _).symm point)=
      windowTicketWeightProgram (actualAuxiliarySquaredWidth 1 n) (n^2-1) n point := by
  simp only [countedPrimarySources,Vector.get_ofFn,countedWindowTicketWeight_value,Equiv.apply_symm_apply]

theorem primaryTableBodyWeight_value (constant n : ℕ) (point : ActualBodyProgramSample constant n) :
    (primaryTableBodyWeight (countedPrimarySources constant n) point).value=actualBodyBlurProgram constant n point := by
  rcases point with ⟨root,leg,queue⟩
  cases leg <;> cases queue <;>
    simp only [primaryTableBodyWeight,GaussianArithmetic.mul,GaussianArithmetic.sub,GaussianArithmetic.literal,
      countedPrimarySources_root,countedPrimarySources_leg,countedPrimarySources_queue,
      actualBodyBlurProgram,optionalWeightProgram]
  all_goals simp only [countedPrimarySources,actualLegRateProgram,actualQueueRateProgram,
    actualRootPopulationProgram,Nat.cast_pow]

theorem primaryTablePairWeight_value (constant n : ℕ) (point : ActualPairProgramSample constant n) :
    (primaryTablePairWeight (countedPrimarySources constant n) point).value=actualPairSourceProgram constant n point := by
  simp only [primaryTablePairWeight,GaussianArithmetic.mul,GaussianArithmetic.literal,
    primaryTableBodyWeight_value,countedPrimarySources_leg,actualPairSourceProgram]

def primarySourcesWork (constant n : ℕ) : ℕ :=
  100*n^80+24*(constant*n^2+1)+(6*n^2+1)*rootMarginalQueryWork n+
    (2*constant*n^2+1)*windowQueryWork (constant*n^2) n+
    (2*n^2+1)*windowQueryWork (n^2) n+1050

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

theorem countedPrimarySources_work (constant n : ℕ) (hn : 2≤n) :
    (countedPrimarySources constant n).work≤primarySourcesWork constant n := by
  have hq := ParameterProgram.modulus_work_le n
  rw [Parameters.security_eq n hn] at hq
  have hr := Finset.sum_le_sum (s:=Finset.univ) (fun index _ =>
    countedRootTicketMarginal_work n (actualRootPopulationProgram n) hn le_rfl (windowIndexEquiv _ index))
  have hl := Finset.sum_le_sum (s:=Finset.univ) (fun index _ =>
    (countedWindowTicketWeight_work (actualAuxiliarySquaredWidth 10 n) (actualLegCutoffProgram constant n-1) n
      (actualAuxiliarySquaredWidth_ge_one 10 n (by decide) (by omega)) (windowIndexEquiv _ index)).trans
      (windowQueryWork_mono ((Nat.sub_le _ _).trans (actualLegCutoffProgram_le constant n)) (le_refl n)))
  have hqueue := Finset.sum_le_sum (s:=Finset.univ) (fun index _ =>
    (countedWindowTicketWeight_work (actualAuxiliarySquaredWidth 1 n) (n^2-1) n
      (actualAuxiliarySquaredWidth_ge_one 1 n (by decide) (by omega)) (windowIndexEquiv _ index)).trans
      (windowQueryWork_mono (Nat.sub_le _ _) (le_refl n)))
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul] at hr hl hqueue
  have hr' : (2*(3*n^2-1)+1)*rootMarginalQueryWork n≤(6*n^2+1)*rootMarginalQueryWork n := by
    apply Nat.mul_le_mul_right
    omega
  have hl' : (2*(actualLegCutoffProgram constant n-1)+1)*windowQueryWork (constant*n^2) n≤
      (2*constant*n^2+1)*windowQueryWork (constant*n^2) n := by
    apply Nat.mul_le_mul_right
    have hh := actualLegCutoffProgram_le constant n
    have hs := Nat.sub_le (actualLegCutoffProgram constant n) 1
    nlinarith
  have hqueue' : (2*(n^2-1)+1)*windowQueryWork (n^2) n≤(2*n^2+1)*windowQueryWork (n^2) n := by
    apply Nat.mul_le_mul_right
    omega
  simp only [countedPrimarySources,Vector.get_ofFn,countedLegCutoff]
  change (ParameterProgram.modulus n).work+2*(12*(constant*n^2+1)+25)+
    (∑ i : Fin (2*(3*n^2-1)+1),(countedRootTicketMarginal n (actualRootPopulationProgram n) (windowIndexEquiv _ i)).work)+
    (∑ i : Fin (2*(actualLegCutoffProgram constant n-1)+1),
      (countedWindowTicketWeight (actualAuxiliarySquaredWidth 10 n) (actualLegCutoffProgram constant n-1) n (windowIndexEquiv _ i)).work)+
    (∑ i : Fin (2*(n^2-1)+1),
      (countedWindowTicketWeight (actualAuxiliarySquaredWidth 1 n) (n^2-1) n (windowIndexEquiv _ i)).work)+1000≤_
  unfold primarySourcesWork
  omega

end
end AFT.V7Calibration
