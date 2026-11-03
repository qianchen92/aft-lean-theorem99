import AFT.WholeBoundarySeed

/-! # A finite table whose primary monomials retain the whole boundary ideal -/
namespace AFT.RepresentedPolynomial
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {Color : Type*} [Fintype Color] [DecidableEq Color]

def wholeBoundaryMonomial (primary body : FiniteDist Color)
    (operator : (Color → ℝ) ≃ₗ[ℝ] (Color → ℝ)) (interior : Finset Color)
    (powers : InputSeed Color →₀ ℕ) : Table (InputSeed Color) :=
  if controlProductBodyOrder (monomialOccurrences powers)=0 then
    MvPolynomial.X (wholeBoundarySeed primary body operator interior (primaryMonomialSeed powers))
  else MvPolynomial.monomial powers 1

def wholeBoundaryTable (primary body : FiniteDist Color)
    (operator : (Color → ℝ) ≃ₗ[ℝ] (Color → ℝ)) (interior : Finset Color)
    (table : Table (InputSeed Color)) : Table (InputSeed Color) :=
  ∑ powers∈table.support,MvPolynomial.C (MvPolynomial.coeff powers table)*
    wholeBoundaryMonomial primary body operator interior powers

theorem wholeBoundaryMonomial_canonical (primary body : FiniteDist Color)
    (operator : (Color → ℝ) ≃ₗ[ℝ] (Color → ℝ)) (interior : Finset Color)
    (hprimary : ∀ color,primary.weight color≠0)
    (hlegal : ∀ profile,(∑ color,legalInputProjection operator (boundaryIdealProjection interior primary.weight) profile color)=0)
    (powers : InputSeed Color →₀ ℕ)
    (hc : ∀ seed∈powers.support,Hoeffding.Canonical (inputReference primary body seed) Finset.univ seed.kernel) :
    InputTableCanonical primary body (wholeBoundaryMonomial primary body operator interior powers) := by
  unfold wholeBoundaryMonomial
  split_ifs with hb
  · apply InputTableCanonical.X
    apply wholeBoundarySeed_canonical primary body operator interior hprimary hlegal _ rfl
    exact primaryMonomialSeed_canonical primary body powers hb hc
  · rw [inputTableCanonical_iff_vars,MvPolynomial.vars_monomial (one_ne_zero : (1 : ℝ)≠0)]
    exact hc

omit [Fintype Color] [DecidableEq Color] in
theorem monomial_body_exists (powers : InputSeed Color →₀ ℕ)
    (hb : controlProductBodyOrder (monomialOccurrences powers)≠0) :
    ∃ seed∈powers.support,seed.bodyOrder≠0 := by
  by_contra hn
  push_neg at hn
  apply hb
  unfold controlProductBodyOrder
  apply List.sum_eq_zero
  intro value hv
  obtain ⟨seed,hs,rfl⟩ := List.mem_map.mp hv
  exact hn seed (mem_monomialOccurrences_support powers seed hs)

theorem boundary_monomial_zero (primary body : FiniteDist Color)
    (primaryChannel bodyChannel : Color → Color → ℝ)
    (interior : Finset Color) (target : Color → ℝ) (powers : InputSeed Color →₀ ℕ)
    (hb : controlProductBodyOrder (monomialOccurrences powers)≠0)
    (hseed : ∀ seed∈powers.support,seed.bodyOrder≠0 →
      boundaryPolynomial interior target (seedOutput primary body primaryChannel bodyChannel seed)=0) :
    boundaryPolynomial interior target
      (outputHom primary body primaryChannel bodyChannel (MvPolynomial.monomial powers 1))=0 := by
  obtain ⟨seed,hs,hbseed⟩ := monomial_body_exists powers hb
  unfold outputHom
  rw [MvPolynomial.aeval_monomial]
  simp only [map_one,one_mul]
  unfold Finsupp.prod
  rw [map_prod]
  apply Finset.prod_eq_zero hs
  rw [map_pow,hseed seed hs hbseed,zero_pow (Finsupp.mem_support_iff.mp hs)]

theorem wholeBoundaryTable_output (primary body : FiniteDist Color)
    (rho : ℝ) (operator : (Color → ℝ) ≃ₗ[ℝ] (Color → ℝ)) (bodyChannel : Color → Color → ℝ)
    (interior : Finset Color) (hrange : ∀ profile,operator profile-profile∈canonicalInteriorProfiles interior)
    (hprimary : ∀ color,primary.weight color≠0)
    (table : Table (InputSeed Color))
    (hbody : ∀ powers∈table.support,controlProductBodyOrder (monomialOccurrences powers)≠0 →
      boundaryPolynomial interior primary.weight
        (outputHom primary body (fun input output => rho*LinearMap.toMatrix' operator.toLinearMap output input) bodyChannel
          (MvPolynomial.monomial powers 1))=0) :
    outputHom primary body (fun input output => rho*LinearMap.toMatrix' operator.toLinearMap output input) bodyChannel
      (wholeBoundaryTable primary body operator interior table)=
      outputHom primary body (fun input output => rho*LinearMap.toMatrix' operator.toLinearMap output input) bodyChannel table-
      boundaryPolynomial interior primary.weight
        (outputHom primary body (fun input output => rho*LinearMap.toMatrix' operator.toLinearMap output input) bodyChannel table) := by
  let output := outputHom primary body (fun input output => rho*LinearMap.toMatrix' operator.toLinearMap output input) bodyChannel
  let boundary := boundaryPolynomial interior primary.weight
  have expansion : output table=∑ powers∈table.support,MvPolynomial.C (MvPolynomial.coeff powers table)*
      output (MvPolynomial.monomial powers 1) := by
    conv_lhs => rw [MvPolynomial.as_sum table]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro powers _
    rw [show MvPolynomial.monomial powers (MvPolynomial.coeff powers table)=
      MvPolynomial.C (MvPolynomial.coeff powers table)*MvPolynomial.monomial powers 1 by rw [MvPolynomial.C_mul_monomial,mul_one]]
    rw [map_mul]
    exact congrArg (fun value => value*output (MvPolynomial.monomial powers 1)) (output.commutes _)
  change output (wholeBoundaryTable primary body operator interior table)=output table-boundary (output table)
  rw [expansion,wholeBoundaryTable,map_sum,map_sum,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro powers hp
  have hc (scalar : ℝ) : output (MvPolynomial.C scalar)=MvPolynomial.C scalar := output.commutes scalar
  have hbC (scalar : ℝ) : boundary (MvPolynomial.C scalar)=MvPolynomial.C scalar := boundary.commutes scalar
  rw [map_mul,hc,map_mul,hbC,← mul_sub]
  congr 1
  unfold wholeBoundaryMonomial
  split_ifs with hb
  · rw [outputHom_X,wholeBoundarySeed_output primary body rho operator bodyChannel interior hrange hprimary _ rfl,
      primaryMonomialSeed_output primary body _ bodyChannel powers hb]
  · rw [hbody powers hp hb,sub_zero]

theorem wholeBoundaryTable_canonical (primary body : FiniteDist Color)
    (operator : (Color → ℝ) ≃ₗ[ℝ] (Color → ℝ)) (interior : Finset Color)
    (hprimary : ∀ color,primary.weight color≠0)
    (hlegal : ∀ profile,(∑ color,legalInputProjection operator (boundaryIdealProjection interior primary.weight) profile color)=0)
    (table : Table (InputSeed Color)) (hc : InputTableCanonical primary body table) :
    InputTableCanonical primary body (wholeBoundaryTable primary body operator interior table) := by
  apply InputTableCanonical.sum
  intro powers hp
  exact (InputTableCanonical.C _).mul (wholeBoundaryMonomial_canonical primary body operator interior hprimary hlegal powers (hc powers hp))

theorem wholeBoundaryMonomial_hasOrder (primary body : FiniteDist Color)
    (operator : (Color → ℝ) ≃ₗ[ℝ] (Color → ℝ)) (interior : Finset Color)
    (powers : InputSeed Color →₀ ℕ) :
    HasOrder (fun seed => seed.primaryOrder+seed.bodyOrder)
      (weightedOrder (fun seed => seed.primaryOrder+seed.bodyOrder) powers)
      (wholeBoundaryMonomial primary body operator interior powers) := by
  unfold wholeBoundaryMonomial
  split_ifs
  · convert hasOrder_C_mul_X (fun seed : InputSeed Color => seed.primaryOrder+seed.bodyOrder)
      (weightedOrder (fun seed => seed.primaryOrder+seed.bodyOrder) powers)
      (wholeBoundarySeed primary body operator interior (primaryMonomialSeed powers)) 1
      (by rw [← primaryMonomialSeed_order powers]; exact le_refl _) using 1; simp
  · intro other ho
    rw [MvPolynomial.coeff_monomial]
    split_ifs with he
    · subst other; omega
    · rfl

theorem wholeBoundaryTable_hasOrder (primary body : FiniteDist Color)
    (operator : (Color → ℝ) ≃ₗ[ℝ] (Color → ℝ)) (interior : Finset Color)
    (minimum : ℕ) (table : Table (InputSeed Color))
    (ht : HasOrder (fun seed => seed.primaryOrder+seed.bodyOrder) minimum table) :
    HasOrder (fun seed => seed.primaryOrder+seed.bodyOrder) minimum
      (wholeBoundaryTable primary body operator interior table) := by
  apply hasOrder_sum
  intro powers hp
  have hm : minimum≤weightedOrder (fun seed => seed.primaryOrder+seed.bodyOrder) powers := by
    by_contra hn
    exact (MvPolynomial.mem_support_iff.mp hp) (ht powers (by omega))
  simpa only [Nat.zero_add] using hasOrder_mul (fun seed : InputSeed Color => seed.primaryOrder+seed.bodyOrder) 0 minimum
    (MvPolynomial.C (MvPolynomial.coeff powers table)) _ (hasOrder_zero _ _)
    (hasOrder_mono _ minimum _ _ (wholeBoundaryMonomial_hasOrder primary body operator interior powers) hm)

theorem wholeBoundaryTable_activity_le (primary body : FiniteDist Color)
    (primaryPool bodyPool radius bound : ℝ) (hradius : 0≤radius)
    (operator : (Color → ℝ) ≃ₗ[ℝ] (Color → ℝ)) (interior : Finset Color)
    (table : Table (InputSeed Color))
    (himages : ∀ powers∈table.support,
      activity (inputWeight primary body primaryPool bodyPool radius)
        (wholeBoundaryMonomial primary body operator interior powers)≤
      bound*monomialWeight (inputWeight primary body primaryPool bodyPool radius) powers) :
    activity (inputWeight primary body primaryPool bodyPool radius)
      (wholeBoundaryTable primary body operator interior table)≤
      bound*activity (inputWeight primary body primaryPool bodyPool radius) table := by
  let weight := inputWeight primary body primaryPool bodyPool radius
  have hw : ∀ seed,0≤weight seed := fun seed => inputWeight_nonneg _ _ _ _ _ seed hradius
  apply (activity_sum_le weight hw _ _).trans
  change _≤bound*(∑ powers∈table.support,|MvPolynomial.coeff powers table| * monomialWeight weight powers)
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro powers hp
  apply (activity_mul_le weight hw _ _).trans
  rw [activity_C]
  exact (mul_le_mul_of_nonneg_left (himages powers hp) (abs_nonneg _)).trans_eq (by ring)

end
end AFT.RepresentedPolynomial
