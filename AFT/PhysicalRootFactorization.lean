import AFT.ActualNormalizedResponse
import AFT.BackgroundQueueCertificate

/-! # Exact independent-root factorization of the physical background -/
namespace AFT.RepresentedPolynomial
open BlockProducts HistogramNormalization PhysicalBlockTensors
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {Index Source Color : Type*} [Fintype Index] [Fintype Source] [Fintype Color]
variable (Slots : Index → Type*) [∀ index, Fintype (Slots index)]
local instance physicalRootFactorizationIndexDecEq : DecidableEq Index := Classical.decEq _
local instance physicalRootFactorizationGenericFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _
local instance physicalRootFactorizationSigmaDecEq : DecidableEq (Sigma Slots) := Classical.decEq _

omit [Fintype Source] in
theorem centeredGeneratingLinear_product (reference : Color → ℝ)
    (law : (index : Index) → FiniteDist (Slots index → Color)) :
    centeredGeneratingLinear reference (blockMass Slots law) =
      ∏ index, centeredGeneratingLinear reference (law index).weight := by
  change (∑ word : Sigma Slots → Color,
    (∏ index, (law index).weight (fun slot => word ⟨index,slot⟩)) •
      ∏ coordinate : Sigma Slots, centeredFactor reference (word coordinate)) = _
  simp only [Algebra.smul_def,MvPolynomial.algebraMap_eq,map_prod,Fintype.prod_sigma]
  calc
    _ = ∑ word : Sigma Slots → Color, ∏ index,
        (MvPolynomial.C ((law index).weight (fun slot => word ⟨index,slot⟩)) *
          ∏ slot, centeredFactor reference (word ⟨index,slot⟩)) := by
      simp only [Finset.prod_mul_distrib]
    _ = ∑ word : (index : Index) → Slots index → Color, ∏ index,
        (MvPolynomial.C ((law index).weight (word index)) *
          ∏ slot, centeredFactor reference (word index slot)) :=
      by
      exact (Equiv.piCurry (fun index (_ : Slots index) => Color)).sum_comp
        (fun word => ∏ index, (MvPolynomial.C ((law index).weight (word index)) *
          ∏ slot, centeredFactor reference (word index slot)))
    _ = _ := by
      simpa only [centeredGeneratingLinear,LinearMap.coe_mk,AddHom.coe_mk,Algebra.smul_def,
        MvPolynomial.algebraMap_eq] using (Fintype.prod_sum fun index (word : Slots index → Color) =>
        MvPolynomial.C ((law index).weight word) * ∏ slot, centeredFactor reference (word slot)).symm

omit Slots [Fintype Color] in
theorem independent_polynomial_product (source : Index → FiniteDist Source)
    (polynomial : Index → Source → Table Color) :
    (∑ word : Index → Source, (FiniteDist.independent source).weight word • ∏ index, polynomial index (word index)) =
      ∏ index, ∑ value, (source index).weight value • polynomial index value := by
  simp only [FiniteDist.independent,Algebra.smul_def,MvPolynomial.algebraMap_eq,map_prod,
    ← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum fun index value => MvPolynomial.C ((source index).weight value)*polynomial index value).symm

omit [Fintype Index] [Fintype Source] Slots in
theorem centeredGeneratingLinear_triple (reference : Color → ℝ) (mass : Color → Color → Color → ℝ) :
    centeredGeneratingLinear reference (tripleMass mass) = tripleGenerating reference mass := by
  unfold centeredGeneratingLinear
  simp only [LinearMap.coe_mk,AddHom.coe_mk]
  rw [← tripleEquiv.symm.sum_comp]
  simp only [Fintype.sum_prod_type,Fin.prod_univ_three]
  change (∑ first, ∑ second, ∑ third,
    mass first second third • (centeredFactor reference first*centeredFactor reference second*centeredFactor reference third)) = _
  simp only [Algebra.smul_def,MvPolynomial.algebraMap_eq,mul_assoc,tripleGenerating]

omit [Fintype Index] [Fintype Source] Slots in
theorem centeredGeneratingLinear_singleton (reference : Color → ℝ) (law : FiniteDist Color) :
    centeredGeneratingLinear reference (V7Calibration.singletonBlockLaw law).weight = singleGenerating reference law.weight := by
  unfold centeredGeneratingLinear
  simp only [LinearMap.coe_mk,AddHom.coe_mk]
  rw [← (Equiv.funUnique (Fin 1) Color).symm.sum_comp]
  have hm (color : Color) : (V7Calibration.singletonBlockLaw law).weight
      ((Equiv.funUnique (Fin 1) Color).symm color) = law.weight color := by
    exact (FiniteDist.map_equiv_weight law (Equiv.funUnique (Fin 1) Color).symm _).trans
      (congrArg law.weight ((Equiv.funUnique (Fin 1) Color).apply_symm_apply color))
  simp only [Equiv.funUnique_symm_apply] at hm
  simp only [Fin.prod_univ_one,Equiv.funUnique_symm_apply,uniqueElim_const,
    Algebra.smul_def,MvPolynomial.algebraMap_eq]
  simp only [hm,singleGenerating]

end
end AFT.RepresentedPolynomial

namespace AFT.V7Calibration
open GaussianSource RepresentedPolynomial BlockProducts Filter
open scoped BigOperators Classical Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
local instance physicalRootFactorizationFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _
local instance physicalRootFactorizationSumDecEq {α β : Type*} : DecidableEq (α ⊕ β) := Classical.decEq _
local instance physicalRootFactorizationV7SigmaDecEq {ι : Type*} {fiber : ι → Type*} : DecidableEq (Sigma fiber) := Classical.decEq _

/-- A block's genuine full polynomial, with precisely its own root fixed. -/
def actualBlockConditionalPolynomial (C : ℝ) (n : ℕ) (beta : ℝ) (index : blockIndex n)
    (root queue : ℤ) : Table (Fin (Parameters.modulus n)) :=
  centeredGeneratingLinear (actualReferenceLaw C n beta).weight
    (actualBlockFamily C n beta (fun _ => root) (fun _ => queue) index).weight

theorem actualConditionalForwardPolynomial_factor (C : ℝ) (n : ℕ) (beta : ℝ)
    (roots : actualRootWord n) (sample : Window (queueCutoff n) × Equiv.Perm (blockIndex n)) :
    actualConditionalForwardPolynomial C n beta roots sample =
      ∏ index, actualBlockConditionalPolynomial C n beta index
        (actualRootField n roots index) (actualQueueShifts n sample index) := by
  rw [actualConditionalForwardPolynomial,centeredGeneratingLinear_product]
  apply Finset.prod_congr rfl
  intro index _
  cases index <;> rfl

theorem actual_independent_forward_at_queue (C : ℝ) (n : ℕ) (beta : ℝ)
    (sample : Window (queueCutoff n) × Equiv.Perm (blockIndex n)) :
    independentRootResponseLinear n (fun roots => actualConditionalForwardPolynomial C n beta roots sample) =
      ∏ index, ∑ root : Window (v7RootCutoff n), (bodyRootReference n).weight root •
        actualBlockConditionalPolynomial C n beta index root (actualQueueShifts n sample index) := by
  change (∑ roots : actualRootWord n, (actualIndependentRoots n).weight roots •
    actualConditionalForwardPolynomial C n beta roots sample) = _
  simp_rw [actualConditionalForwardPolynomial_factor]
  have hprod (roots : actualRootWord n) : (∏ index, actualBlockConditionalPolynomial C n beta index
      (actualRootField n roots index) (actualQueueShifts n sample index)) =
      ∏ index : Fin (Parameters.bodies n), actualBlockConditionalPolynomial C n beta ((actualRootIndex n).symm index)
        (roots index) (actualQueueShifts n sample ((actualRootIndex n).symm index)) := by
    have hh := (actualRootIndex n).symm.prod_comp (fun index => actualBlockConditionalPolynomial C n beta index
      (actualRootField n roots index) (actualQueueShifts n sample index))
    simpa only [actualRootField,Equiv.apply_symm_apply] using hh.symm
  simp_rw [hprod]
  unfold actualIndependentRoots
  have hh := independent_polynomial_product (fun _ : Fin (Parameters.bodies n) => bodyRootReference n)
    (fun index root => actualBlockConditionalPolynomial C n beta ((actualRootIndex n).symm index)
      root (actualQueueShifts n sample ((actualRootIndex n).symm index)))
  trans (∏ index : Fin (Parameters.bodies n), ∑ root : Window (v7RootCutoff n),
    (bodyRootReference n).weight root • actualBlockConditionalPolynomial C n beta ((actualRootIndex n).symm index) root
      (actualQueueShifts n sample ((actualRootIndex n).symm index)))
  · exact hh
  exact (actualRootIndex n).symm.prod_comp (fun index => ∑ root : Window (v7RootCutoff n),
    (bodyRootReference n).weight root • actualBlockConditionalPolynomial C n beta index root (actualQueueShifts n sample index))


/-- Root averaging of each genuine physical block is exactly the block
used by the already certified background logarithm. -/
theorem actual_block_root_polynomial_eventually (C : ℝ) (hC : 1 ≤ C) (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ n in atTop, (Parameters.legs n : ℝ)/(2*Parameters.dimension n) ≤ beta n ∧
      beta n ≤ 2*(Parameters.legs n : ℝ)/Parameters.dimension n) :
    ∀ᶠ n in atTop, ∀ index : blockIndex n, ∀ queue : ℤ, |queue| ≤ (queueCutoff n : ℤ) →
      (∑ root : Window (v7RootCutoff n), (bodyRootReference n).weight root •
        actualBlockConditionalPolynomial C n (beta n) index root queue) =
        blockPhysicalPolynomial C n (beta n) index queue := by
  filter_upwards [actual_fixed_root_triple_weights_eventually C hC beta hbeta,
    actual_shifted_body_law_eventually C hC beta hbeta,
    actual_reference_laws_eventually C hC beta hbeta] with n ht hb href index queue hq
  have hr (root : Window (v7RootCutoff n)) : |(root : ℤ)| ≤ (v7RootCutoff n : ℤ) :=
    abs_le.mpr (Finset.mem_Icc.mp root.property)
  cases index with
  | inl leg =>
    have he (root : Window (v7RootCutoff n)) :
        actualBlockConditionalPolynomial C n (beta n) (.inl leg) root queue =
          tripleGenerating (actualReferenceMean C n (beta n)) (actualFixedRootTriple C n (beta n) root queue) := by
      change centeredGeneratingLinear (actualReferenceLaw C n (beta n)).weight
        (actualFixedRootTripleLaw C n (beta n) root queue).weight = _
      rw [ht root queue (hr root) hq,centeredGeneratingLinear_triple,href.2.2]
    simp_rw [he]
    have hav : (∑ root : Window (v7RootCutoff n), (bodyRootReference n).weight root •
        actualFixedRootTriple C n (beta n) root queue) = actualLocalTriple C n (beta n) queue := by
      funext first second attached
      simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
      exact actualFixedRootTriple_root_average C n (beta n) queue first second attached
    change (∑ root : Window (v7RootCutoff n), (bodyRootReference n).weight root •
      covarianceTripleGeneratingLinear (actualReferenceMean C n (beta n))
        (actualFixedRootTriple C n (beta n) root queue)) =
      covarianceTripleGeneratingLinear (actualReferenceMean C n (beta n)) (actualLocalTriple C n (beta n) queue)
    have hh := congrArg (covarianceTripleGeneratingLinear (actualReferenceMean C n (beta n))) hav
    simpa only [map_sum,map_smul] using hh
  | inr body =>
    have he (root : Window (v7RootCutoff n)) :
        actualBlockConditionalPolynomial C n (beta n) (.inr body) root queue =
          singleGenerating (actualReferenceMean C n (beta n))
            (integerShiftProfile n (actualBodyCenter C n (beta n)) (root+queue)) := by
      change centeredGeneratingLinear (actualReferenceLaw C n (beta n)).weight
        (singletonBlockLaw (actualShiftedBodyLaw C n (beta n) (root+queue))).weight = _
      rw [centeredGeneratingLinear_singleton,href.2.2]
      have hs := actualBodyBranch_shift_bound C n root queue (hr root) hq (.inl ())
      simp only [actualSourceShift,add_zero] at hs
      rw [(hb (root+queue) hs).1]
    simp_rw [he]
    change (∑ root : Window (v7RootCutoff n), (bodyRootReference n).weight root •
      singleGenerating (actualReferenceMean C n (beta n))
        (integerShiftProfile n (actualBodyCenter C n (beta n)) (root+queue))) =
      singleGenerating (actualReferenceMean C n (beta n)) (attachedBodyAtSource C n (beta n) queue 0)
    simp only [singleGenerating,Algebra.smul_def,MvPolynomial.algebraMap_eq,
      Finset.mul_sum,attachedBodyAtSource,add_zero,map_sum,map_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro color _
    simp only [Finset.sum_mul,mul_assoc]
    rfl

/-- All independent roots are integrated before the common queue. This is
the literal whole-sampler background certified by the finite logarithm. -/
theorem actual_independent_forward_background_eventually (C : ℝ) (hC : 1 ≤ C) (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ n in atTop, (Parameters.legs n : ℝ)/(2*Parameters.dimension n) ≤ beta n ∧
      beta n ≤ 2*(Parameters.legs n : ℝ)/Parameters.dimension n) :
    ∀ᶠ n in atTop, actualIndependentForwardPolynomial C n (beta n) =
      actualBackgroundPolynomial C n (beta n) := by
  filter_upwards [actual_block_root_polynomial_eventually C hC beta hbeta] with n hb
  unfold actualIndependentForwardPolynomial actualBackgroundPolynomial queueAverage
  simp only [actual_independent_forward_at_queue,Algebra.smul_def,MvPolynomial.algebraMap_eq]
  apply Finset.sum_congr rfl
  intro sample _
  congr 1
  apply Finset.prod_congr rfl
  intro index _
  simpa only [Algebra.smul_def,MvPolynomial.algebraMap_eq] using
    hb index _ (actualQueueShifts_bound n sample index)

end
end AFT.V7Calibration
