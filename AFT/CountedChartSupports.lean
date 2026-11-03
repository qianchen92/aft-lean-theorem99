import AFT.CachedPublicChartProgram
import AFT.CountedLegalChart

/-! # Building both chart supports by explicit stored-table scans

Every palette test reads a stored Boolean entry. The feature coordinates,
palette Boolean table and scale coordinates are supplied as materialized
arrays; their construction is accounted for separately.
-/
namespace AFT.BoundaryCalibration
open RationalRejectionProgram
open scoped BigOperators

def countedSafeChartTest {charts colors features : ℕ} [NeZero colors]
    (feature : Vector (Vector (Fin colors) charts) features)
    (allowed : Vector (Vector Bool colors) features) (scale : Vector (Fin colors) charts)
    (chart : Fin charts) : CountedValue Bool :=
  let all := countedFinAll features (fun index =>
    ⟨(allowed.get index).get ((feature.get index).get chart),4⟩)
  ⟨decide (scale.get chart≠0) && all.value,all.work+3⟩

def countedFiberChartTest {charts colors features : ℕ} [NeZero colors]
    (feature : Vector (Vector (Fin colors) charts) features)
    (allowed : Vector (Vector Bool colors) features) (scale : Vector (Fin colors) charts)
    (marked : Fin features) (mark : Fin colors) (chart : Fin charts) : CountedValue Bool :=
  let all := countedFinAll features (fun index =>
    ⟨decide (index=marked) || (allowed.get index).get ((feature.get index).get chart),6⟩)
  ⟨decide ((feature.get marked).get chart=mark) && decide (scale.get chart≠0) && all.value,
    all.work+7⟩

theorem countedSafeChartTest_value {charts colors features : ℕ} [NeZero colors]
    (feature : Vector (Vector (Fin colors) charts) features)
    (allowed : Vector (Vector Bool colors) features) (scale : Vector (Fin colors) charts)
    (chart : Fin charts) :
    (countedSafeChartTest feature allowed scale chart).value=true ↔
      scale.get chart≠0 ∧ ∀ index,(allowed.get index).get ((feature.get index).get chart)=true := by
  simp only [countedSafeChartTest,Bool.and_eq_true,decide_eq_true_eq,countedFinAll_value]

theorem countedFiberChartTest_value {charts colors features : ℕ} [NeZero colors]
    (feature : Vector (Vector (Fin colors) charts) features)
    (allowed : Vector (Vector Bool colors) features) (scale : Vector (Fin colors) charts)
    (marked : Fin features) (mark : Fin colors) (chart : Fin charts) :
    (countedFiberChartTest feature allowed scale marked mark chart).value=true ↔
      (feature.get marked).get chart=mark ∧ scale.get chart≠0 ∧
        ∀ index,index≠marked → (allowed.get index).get ((feature.get index).get chart)=true := by
  simp only [countedFiberChartTest,Bool.and_eq_true,decide_eq_true_eq,countedFinAll_value,
    Bool.or_eq_true,or_iff_not_imp_left,and_assoc]

theorem countedSafeChartTest_work {charts colors features : ℕ} [NeZero colors]
    (feature : Vector (Vector (Fin colors) charts) features)
    (allowed : Vector (Vector Bool colors) features) (scale : Vector (Fin colors) charts)
    (chart : Fin charts) : (countedSafeChartTest feature allowed scale chart).work≤ 6*features+3 := by
  have hh := countedFinAll_work features (fun index =>
    (⟨(allowed.get index).get ((feature.get index).get chart),4⟩ : CountedValue Bool)) 4
    (fun _ => le_rfl)
  simp only [countedSafeChartTest]
  omega

theorem countedFiberChartTest_work {charts colors features : ℕ} [NeZero colors]
    (feature : Vector (Vector (Fin colors) charts) features)
    (allowed : Vector (Vector Bool colors) features) (scale : Vector (Fin colors) charts)
    (marked : Fin features) (mark : Fin colors) (chart : Fin charts) :
    (countedFiberChartTest feature allowed scale marked mark chart).work≤ 8*features+7 := by
  have hh := countedFinAll_work features (fun index =>
    (⟨decide (index=marked) || (allowed.get index).get ((feature.get index).get chart),6⟩ : CountedValue Bool)) 6
    (fun _ => le_rfl)
  simp only [countedFiberChartTest]
  omega

structure StoredChartSupports (charts : ℕ) where
  safe : Finset (Fin charts)
  fiber : Finset (Fin charts)
  legal : Vector Bool charts

def countedChartSupports {charts colors features : ℕ} [NeZero colors]
    (feature : Vector (Vector (Fin colors) charts) features)
    (allowed : Vector (Vector Bool colors) features) (scale : Vector (Fin colors) charts)
    (marked : Fin features) (mark : Fin colors) : CountedValue (StoredChartSupports charts) :=
  let safe := Vector.ofFn (countedSafeChartTest feature allowed scale)
  let fiber := Vector.ofFn (countedFiberChartTest feature allowed scale marked mark)
  let safeSet := countedFinFilter charts (fun index => ⟨(safe.get index).value,1⟩)
  let fiberSet := countedFinFilter charts (fun index => ⟨(fiber.get index).value,1⟩)
  ⟨⟨safeSet.value,fiberSet.value,
      Vector.ofFn (fun index => (safe.get index).value || (fiber.get index).value)⟩,
    (∑ index,(safe.get index).work)+(∑ index,(fiber.get index).work)+
      safeSet.work+fiberSet.work+5*charts⟩

theorem countedChartSupports_safe {charts colors features : ℕ} [NeZero colors]
    (feature : Vector (Vector (Fin colors) charts) features)
    (allowed : Vector (Vector Bool colors) features) (scale : Vector (Fin colors) charts)
    (marked : Fin features) (mark : Fin colors) (palette : Fin features → Finset (Fin colors))
    (hallowed : ∀ index color,(allowed.get index).get color=true ↔ color∈palette index) :
    (countedChartSupports feature allowed scale marked mark).value.safe=
      finiteMarkedSafe (fun index chart => (feature.get index).get chart) scale.get palette := by
  ext chart
  simp only [countedChartSupports,countedFinFilter_value,Finset.mem_filter,Finset.mem_univ,
    true_and,Vector.get_ofFn,countedSafeChartTest_value,finiteMarkedSafe]
  exact and_congr Iff.rfl (forall_congr' (fun index => hallowed index _))

theorem countedChartSupports_fiber {charts colors features : ℕ} [NeZero colors]
    (feature : Vector (Vector (Fin colors) charts) features)
    (allowed : Vector (Vector Bool colors) features) (scale : Vector (Fin colors) charts)
    (marked : Fin features) (mark : Fin colors) (palette : Fin features → Finset (Fin colors))
    (hallowed : ∀ index color,(allowed.get index).get color=true ↔ color∈palette index) :
    (countedChartSupports feature allowed scale marked mark).value.fiber=
      finiteMarkedFiber (fun index chart => (feature.get index).get chart) scale.get palette marked mark := by
  ext chart
  simp only [countedChartSupports,countedFinFilter_value,Finset.mem_filter,Finset.mem_univ,
    true_and,Vector.get_ofFn,countedFiberChartTest_value,finiteMarkedFiber]
  exact and_congr Iff.rfl (and_congr Iff.rfl
    (forall_congr' (fun index => imp_congr_right (fun _ => hallowed index _))))

theorem countedChartSupports_legal {charts colors features : ℕ} [NeZero colors]
    (feature : Vector (Vector (Fin colors) charts) features)
    (allowed : Vector (Vector Bool colors) features) (scale : Vector (Fin colors) charts)
    (marked : Fin features) (mark : Fin colors) (chart : Fin charts) :
    (countedChartSupports feature allowed scale marked mark).value.legal.get chart=true ↔
      chart∈(countedChartSupports feature allowed scale marked mark).value.safe∪
        (countedChartSupports feature allowed scale marked mark).value.fiber := by
  simp only [countedChartSupports,Vector.get_ofFn,Bool.or_eq_true,countedFinFilter_value,
    Finset.mem_union,Finset.mem_filter,Finset.mem_univ,true_and]

theorem countedChartSupports_work {charts colors features : ℕ} [NeZero colors]
    (feature : Vector (Vector (Fin colors) charts) features)
    (allowed : Vector (Vector Bool colors) features) (scale : Vector (Fin colors) charts)
    (marked : Fin features) (mark : Fin colors) :
    (countedChartSupports feature allowed scale marked mark).work≤ charts*(14*features+23) := by
  have hs := Finset.sum_le_sum (s:=Finset.univ) (fun chart _ =>
    countedSafeChartTest_work feature allowed scale chart)
  have hf := Finset.sum_le_sum (s:=Finset.univ) (fun chart _ =>
    countedFiberChartTest_work feature allowed scale marked mark chart)
  have hss := countedFinFilter_work charts (fun index =>
    (⟨(Vector.ofFn (countedSafeChartTest feature allowed scale)).get index |>.value,1⟩ : CountedValue Bool))
    1 (fun _ => le_rfl)
  have hfs := countedFinFilter_work charts (fun index =>
    (⟨(Vector.ofFn (countedFiberChartTest feature allowed scale marked mark)).get index |>.value,1⟩ : CountedValue Bool))
    1 (fun _ => le_rfl)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul] at hs hf
  simp only [Vector.get_ofFn] at hss hfs
  simp only [countedChartSupports,Vector.get_ofFn]
  nlinarith

end AFT.BoundaryCalibration
