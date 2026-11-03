import AFT.MarkedChartSampler

/-! # Exact positive law approximated by the executable marked-chart sampler -/
namespace AFT.BoundaryCalibration
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000

 theorem explicitMarkedChartDensity_law
    (charts colors features : ℕ) [NeZero charts] [NeZero colors]
    (feature : Fin features → Fin charts → Fin colors) (allowed : Fin features → Finset (Fin colors))
    (safe survivingFiber : Finset (Fin charts)) (marked : Fin features) (mark : Fin colors)
    (hfeature : ∀ i, (FiniteDist.uniform (Fin charts)).map (feature i)=FiniteDist.uniform (Fin colors))
    (hpair : ∀ i j, i≠j → (FiniteDist.uniform (Fin charts)).map (fun x => (feature i x,feature j x))=
      (FiniteDist.uniform (Fin colors)).prod (FiniteDist.uniform (Fin colors)))
    (hallowed : ∀ i x, x∈safe → feature i x∈allowed i)
    (error : ℝ) (herror : 0≤error)
    (hglobal : expectation (FiniteDist.uniform (Fin charts)) (badIndicator (fun x => x∈safe))≤error)
    (hconditional : ∀ i c, c∈allowed i → conditional (FiniteDist.uniform (Fin charts)) (feature i) (badIndicator (fun x => x∈safe)) c≤error)
    (hsmall : (2*features+1 : ℝ)*error≤1/4)
    (atom : ℝ) (ha : 0≤atom) (ha100 : atom≤1/100) (hsize : 4*atom*features≤1/25)
    (hspikemean : expectation (FiniteDist.uniform (Fin charts))
      (restrictedDensity (FiniteDist.uniform (Fin charts)) (fun x => x∈survivingFiber))=1)
    (hspikeallowed : ∀ i, i≠marked → ∀ x, feature i x∉allowed i → x∉survivingFiber)
    (hspikebound : ∀ i, i≠marked → ∀ c, conditional (FiniteDist.uniform (Fin charts)) (feature i)
      (restrictedDensity (FiniteDist.uniform (Fin charts)) (fun x => x∈survivingFiber)) c≤2)
    (hspikemark : ∀ c, conditional (FiniteDist.uniform (Fin charts)) (feature marked)
      (restrictedDensity (FiniteDist.uniform (Fin charts)) (fun x => x∈survivingFiber)) c=
      if c=mark then (colors : ℝ) else 0)
    (hD : ‖deletion (chartProjection (FiniteDist.uniform (Fin charts)) feature allowed) (fun x => x∈safe)‖<1) :
    ∃ law : FiniteDist (Fin charts),
      (∀ point, law.weight point=explicitMarkedChartDensity charts colors features feature allowed safe survivingFiber marked atom hD point/charts) ∧
      (∀ point, point∉safe → point∉survivingFiber → law.weight point=0) ∧
      (∀ c, (law.map (feature marked)).weight c=
        (1-atom)*(if c∈allowed marked then ((allowed marked).card : ℝ)⁻¹ else 0)+atom*(if c=mark then 1 else 0)) ∧
      (∀ i, i≠marked → ∀ c, (law.map (feature i)).weight c=if c∈allowed i then ((allowed i).card : ℝ)⁻¹ else 0) := by
  let p := FiniteDist.uniform (Fin charts)
  let spike := restrictedDensity p (fun x => x∈survivingFiber)
  change expectation p spike=1 at hspikemean
  change ∀ c, conditional p (feature marked) spike c=if c=mark then (colors : ℝ) else 0 at hspikemark
  have hspike : ∀ x, 0≤spike x := restrictedDensity_nonneg p _
  have hsallowed : ∀ i, i≠marked → ∀ x, feature i x∉allowed i → spike x=0 := by
    intro i hi x hx
    simp only [spike,restrictedDensity,eventIndicator,if_neg (hspikeallowed i hi x hx),zero_div]
  obtain ⟨repaired,hformula,hrmean,hrnonneg,hrzero,hrfirst,hrothers⟩ :=
    explicit_marked_repaired_density p feature allowed marked hfeature hpair (fun x => x∈safe) hallowed
      error herror hglobal hconditional (by simpa only [Fintype.card_fin] using hsmall)
      atom ha ha100 (by simpa only [Fintype.card_fin] using hsize) spike hspikemean hspike hsallowed hspikebound hD
  let final := (1-atom) • repaired+atom • spike
  have hfmean : expectation p final=1 := by
    simp only [final,map_add,map_smul,hrmean,hspikemean,smul_eq_mul,mul_one]
    ring
  have hfnonneg (x : Fin charts) : 0≤final x :=
    add_nonneg (mul_nonneg (by linarith) (hrnonneg x)) (mul_nonneg ha (hspike x))
  have hden : 1-atom≠0 := by linarith
  have hfinal (x : Fin charts) : final x=explicitMarkedChartDensity charts colors features feature allowed safe survivingFiber marked atom hD x := by
    dsimp only [final]
    rw [hformula]
    simp only [Pi.add_apply,Pi.smul_apply,Pi.sub_apply,smul_eq_mul,explicitMarkedChartDensity,safeMask_apply]
    by_cases hx : x∈safe
    · simp only [if_pos hx]
      field_simp [hden]
      ring
    · simp only [if_neg hx,mul_zero,sub_zero,zero_add]
      rfl
  let law := densityLaw p final hfnonneg hfmean
  refine ⟨law,?_,?_,?_,?_⟩
  · intro point
    change p.weight point*final point=_
    rw [hfinal]
    simp only [p,FiniteDist.uniform_weight,Fintype.card_fin]
    ring
  · intro point hs ht
    change p.weight point*final point=0
    simp only [final,Pi.add_apply,Pi.smul_apply,smul_eq_mul,hrzero point hs,spike,restrictedDensity,eventIndicator,if_neg ht,zero_div,mul_zero,add_zero]
  · intro c
    rw [densityLaw_marginal]
    change conditional p (feature marked) ((1-atom) • repaired+atom • spike) c/Fintype.card (Fin colors)=_
    simp only [map_add,map_smul,Pi.add_apply,Pi.smul_apply,smul_eq_mul,hrfirst,hspikemark,Fintype.card_fin]
    have hcolors : (colors : ℝ)≠0 := Nat.cast_ne_zero.mpr (NeZero.ne colors)
    split_ifs <;> field_simp
    all_goals ring
  · intro i hi c
    rw [densityLaw_marginal,hrothers i hi c,Fintype.card_fin]
    have hcolors : (colors : ℝ)≠0 := Nat.cast_ne_zero.mpr (NeZero.ne colors)
    split_ifs <;> field_simp
    all_goals ring

end
end AFT.BoundaryCalibration
