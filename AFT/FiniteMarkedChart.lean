import AFT.MarkedChartLaw
import AFT.ExplicitSurvivingFiber

/-! # Positive marked-chart laws on the explicitly indexed array -/
namespace AFT.BoundaryCalibration
open scoped BigOperators

def finiteMarkedSafe {charts colors features : ℕ} [NeZero colors]
    (feature : Fin features → Fin charts → Fin colors) (auxiliary : Fin charts → Fin colors)
    (allowed : Fin features → Finset (Fin colors)) : Finset (Fin charts) :=
  Finset.univ.filter (fun x => auxiliary x≠0 ∧ ∀ i, feature i x∈allowed i)

def finiteMarkedFiber {charts colors features : ℕ} [NeZero colors]
    (feature : Fin features → Fin charts → Fin colors) (auxiliary : Fin charts → Fin colors)
    (allowed : Fin features → Finset (Fin colors)) (marked : Fin features) (mark : Fin colors) : Finset (Fin charts) :=
  Finset.univ.filter (fun x => feature marked x=mark ∧ auxiliary x≠0 ∧ ∀ i, i≠marked → feature i x∈allowed i)

noncomputable section
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

 theorem finite_marked_chart
    (charts colors features : ℕ) [NeZero charts] [NeZero colors]
    (feature : Fin features → Fin charts → Fin colors) (auxiliary : Fin charts → Fin colors)
    (allowed : Fin features → Finset (Fin colors)) (marked : Fin features) (mark : Fin colors)
    (hfeature : ∀ i, (FiniteDist.uniform (Fin charts)).map (feature i)=FiniteDist.uniform (Fin colors))
    (hpair : ∀ i j, i≠j → (FiniteDist.uniform (Fin charts)).map (fun x => (feature i x,feature j x))=
      (FiniteDist.uniform (Fin colors)).prod (FiniteDist.uniform (Fin colors)))
    (haux : (FiniteDist.uniform (Fin charts)).map auxiliary=FiniteDist.uniform (Fin colors))
    (hauxpair : ∀ i, (FiniteDist.uniform (Fin charts)).map (fun x => (feature i x,auxiliary x))=
      (FiniteDist.uniform (Fin colors)).prod (FiniteDist.uniform (Fin colors)))
    (hsmall : (2*features+1 : ℝ)*affineDeletionBudget allowed≤1/4)
    (atom : ℝ) (ha : 0≤atom) (ha100 : atom≤1/100) (hsize : 4*atom*features≤1/25) :
    let safe := finiteMarkedSafe feature auxiliary allowed
    let survivingFiber := finiteMarkedFiber feature auxiliary allowed marked mark
    ∃ hD : ‖deletion (chartProjection (FiniteDist.uniform (Fin charts)) feature allowed) (fun x => x∈safe)‖<1,
      ‖deletion (chartProjection (FiniteDist.uniform (Fin charts)) feature allowed) (fun x => x∈safe)‖≤1/4 ∧
      ‖spikeDefect (FiniteDist.uniform (Fin charts)) feature allowed marked atom
        (restrictedDensity (FiniteDist.uniform (Fin charts)) (fun x => x∈survivingFiber))‖≤1/25 ∧
      ∃ law : FiniteDist (Fin charts),
        (∀ point, law.weight point=explicitMarkedChartDensity charts colors features feature allowed safe survivingFiber marked atom hD point/charts) ∧
        (∀ point, point∉safe → point∉survivingFiber → law.weight point=0) ∧
        (∀ c, (law.map (feature marked)).weight c=
          (1-atom)*(if c∈allowed marked then ((allowed marked).card : ℝ)⁻¹ else 0)+atom*(if c=mark then 1 else 0)) ∧
        (∀ i, i≠marked → ∀ c, (law.map (feature i)).weight c=if c∈allowed i then ((allowed i).card : ℝ)⁻¹ else 0) := by
  let p := FiniteDist.uniform (Fin charts)
  let safe := finiteMarkedSafe feature auxiliary allowed
  let fiber := finiteMarkedFiber feature auxiliary allowed marked mark
  let auxAllowed := Finset.univ.erase (0 : Fin colors)
  let otherAllowed := fun i => if i=marked then Finset.univ else allowed i
  let otherSafe := legalChart auxiliary auxAllowed feature otherAllowed
  have hsafe : (fun x => x∈safe)=legalChart auxiliary auxAllowed feature allowed := by
    funext x
    simp [safe,finiteMarkedSafe,legalChart,auxAllowed]
  have hfiber : (fun x => x∈fiber)=(fun x => feature marked x=mark ∧ otherSafe x) := by
    funext x
    simp only [fiber,finiteMarkedFiber,Finset.mem_filter,Finset.mem_univ,true_and,otherSafe,legalChart,auxAllowed,
      Finset.mem_erase,ne_eq,Finset.mem_univ,and_true]
    congr 2
    apply propext
    constructor
    · intro hh i
      by_cases hi : i=marked
      · simp [otherAllowed,hi]
      · simpa [otherAllowed,hi] using hh i hi
    · intro hh i hi
      simpa [otherAllowed,hi] using hh i
  have hbudget : expectation (FiniteDist.uniform (Fin colors)) (paletteFailure auxAllowed)+
      ∑ i,expectation (FiniteDist.uniform (Fin colors)) (paletteFailure (allowed i))=affineDeletionBudget allowed := by
    have hz : expectation (FiniteDist.uniform (Fin colors)) (paletteFailure auxAllowed)=(colors : ℝ)⁻¹ := by
      simp [expectation_apply,FiniteDist.uniform_weight,paletteFailure,auxAllowed,mul_ite,ite_not]
    rw [hz]
    simp only [uniform_palette_failure,affineDeletionBudget,Fintype.card_fin]
  have hglobal : expectation p (badIndicator (fun x => x∈safe))≤affineDeletionBudget allowed := by
    rw [hsafe,←hbudget]
    exact legalChart_global_budget p auxiliary auxAllowed feature allowed haux hfeature
  have hconditional : ∀ i c, c∈allowed i → conditional p (feature i) (badIndicator (fun x => x∈safe)) c≤affineDeletionBudget allowed := by
    intro i c hc
    rw [hsafe,←hbudget]
    exact legalChart_conditional_budget p auxiliary auxAllowed feature allowed hfeature hpair hauxpair i c hc
  have he0 : 0≤affineDeletionBudget allowed := by
    apply le_trans _ hglobal
    rw [expectation_apply]
    exact Finset.sum_nonneg (fun x _ => mul_nonneg (p.nonneg x) (by unfold badIndicator;split_ifs <;> norm_num))
  have hquarter : ‖deletion (chartProjection p feature allowed) (fun x => x∈safe)‖≤1/4 :=
    (chartDeletion_norm p feature allowed _ _ he0 hglobal hconditional).trans (by simpa only [Fintype.card_fin] using hsmall)
  have hD : ‖deletion (chartProjection p feature allowed) (fun x => x∈safe)‖<1 := lt_of_le_of_lt hquarter (by norm_num)
  have hehalf : affineDeletionBudget allowed≤1/2 := by
    nlinarith [mul_nonneg (Nat.cast_nonneg features : (0 : ℝ)≤features) he0]
  have hotherBudget : expectation (FiniteDist.uniform (Fin colors)) (paletteFailure auxAllowed)+
      ∑ i,expectation (FiniteDist.uniform (Fin colors)) (paletteFailure (otherAllowed i))≤affineDeletionBudget allowed := by
    rw [←hbudget]
    apply add_le_add_right
    apply Finset.sum_le_sum
    intro i _
    apply expectation_mono
    intro c
    by_cases hi : i=marked
    · simp [otherAllowed,hi,paletteFailure]
      split_ifs <;> norm_num
    · simp [otherAllowed,hi]
  have hbad : conditional p (feature marked) (badIndicator otherSafe) mark≤1/2 := by
    have hh := legalChart_conditional_budget p auxiliary auxAllowed feature otherAllowed hfeature hpair hauxpair marked mark (by simp [otherAllowed])
    exact hh.trans (hotherBudget.trans hehalf)
  let others := fun i : {i : Fin features // i≠marked} => feature i.1
  obtain ⟨spike,hspikeformula,hsmean,hsnonneg,hszero,hsmark,hsbound⟩ :=
    explicit_surviving_fiber_density p (feature marked) (hfeature marked) others
      (fun i => hpair marked i.1 i.2.symm) otherSafe mark hbad
  have hspike : spike=restrictedDensity p (fun x => x∈fiber) := by rw [hfiber];exact hspikeformula
  have hsallowed : ∀ i, i≠marked → ∀ x, feature i x∉allowed i → x∉fiber := by
    intro i hi x hx hf
    have ht := (congrFun hfiber x).mp hf
    exact hx (by simpa [otherSafe,legalChart,otherAllowed,hi] using ht.2.2 i)
  have hsb : ∀ i, i≠marked → ∀ c, conditional p (feature i) spike c≤2 := fun i hi c => hsbound ⟨i,hi⟩ c
  have hdefect := spikeDefect_norm p feature allowed marked atom spike ha hsnonneg hsb (by simpa only [Fintype.card_fin] using hsize)
  rw [hspike] at hsmean hsnonneg hsmark hsb hdefect
  refine ⟨hD,hquarter,hdefect,?_⟩
  apply explicitMarkedChartDensity_law charts colors features feature allowed safe fiber marked mark hfeature hpair
    (fun i x hx => by have hh := (congrFun hsafe x).mp hx;exact hh.2 i)
    (affineDeletionBudget allowed) he0 hglobal hconditional hsmall atom ha ha100 hsize hsmean hsallowed hsb
    (by simpa only [Fintype.card_fin] using hsmark) hD

end
end AFT.BoundaryCalibration
