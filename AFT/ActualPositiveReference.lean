import AFT.BackgroundBoundaryTransform
import AFT.ActualBoundarySupport

/-! # The genuine inhomogeneous positive beta reference

There are `N-m` interior-uniform coordinates and `m` independent coordinates
with boundary probability `ρ B`. This is different from the iid product of
its mean `r`; its full centered generating polynomial is retained.
-/
namespace AFT.V7Calibration
open GaussianSource Filter RepresentedPolynomial
open scoped BigOperators Classical Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false

def actualInteriorProfile (C : ℝ) (n : ℕ) : Fin (Parameters.modulus n) → ℝ :=
  uniformFiniteProfile (boundaryPalette (Parameters.modulus n) (boundaryHalf C n))ᶜ

def actualBoundaryProfile (C : ℝ) (n : ℕ) : Fin (Parameters.modulus n) → ℝ :=
  uniformFiniteProfile (boundaryPalette (Parameters.modulus n) (boundaryHalf C n))

def actualReferenceBoundaryRate (C : ℝ) (n : ℕ) (beta : ℝ) : ℝ :=
  v7Activation C n*repairedBoundaryMass n C beta (boundaryHalf C n)

def actualReferenceMarkedProfile (C : ℝ) (n : ℕ) (beta : ℝ) : Fin (Parameters.modulus n) → ℝ :=
  (1-actualReferenceBoundaryRate C n beta) • actualInteriorProfile C n+
    actualReferenceBoundaryRate C n beta • actualBoundaryProfile C n

def actualPositiveReferencePolynomial (C : ℝ) (n : ℕ) (beta : ℝ) : Table (Fin (Parameters.modulus n)) :=
  singleGenerating (actualReferenceMean C n beta) (actualInteriorProfile C n)^(Parameters.dimension n-Parameters.legs n)*
    singleGenerating (actualReferenceMean C n beta) (actualReferenceMarkedProfile C n beta)^Parameters.legs n

theorem actual_primary_boundary_eventually (C : ℝ) (hC : 1≤C) :
    ∀ᶠ n in atTop,∀ beta : ℝ,∀ color∈boundaryPalette (Parameters.modulus n) (boundaryHalf C n),
      actualPrimary C n beta color = repairedBoundaryMass n C beta (boundaryHalf C n)/
        (boundaryPalette (Parameters.modulus n) (boundaryHalf C n)).card := by
  filter_upwards [actual_physical_supports_eventually C hC] with n hm beta color hc
  have hout := (mem_boundaryPalette _ _ color).mp hc
  have hcard : ((boundaryPalette (Parameters.modulus n) (boundaryHalf C n)).card : ℝ) ≠ 0 := by
    exact_mod_cast ne_of_gt (Finset.card_pos.mpr ⟨color,hc⟩)
  have hw : 2*(Parameters.safeMargin n : ℤ)≤Parameters.modulus n := by
    have hh := Parameters.safeSize_positive n
    unfold Parameters.safeSize at hh
    omega
  have hbase : basePrimary n C (boundaryHalf C n) (bodyShift C n) (bodyBlur C n)
      (startsPlus C n) (startsMinus C n) (pairSourceShift C n) (pairSourceLaw C n) color =
      v7BaseBoundaryMass C n (boundaryHalf C n)/(boundaryPalette (Parameters.modulus n) (boundaryHalf C n)).card := by
    unfold basePrimary
    rw [TrimmedSlice.actualFairBasePrimary_eq_average]
    have hbnd (starts : pairSample C n → ℤ) := TrimmedSlice.actualBasePrimary_boundary
      (Parameters.modulus n) (Parameters.safeMargin n) (boundaryHalf C n)
      (Parameters.anchorWidth n) (Parameters.bodies n) (Parameters.legs n) (v7Activation C n)
      (bodyShift C n) (bodyBlur C n).weight starts (pairSourceShift C n) (pairSourceLaw C n).weight
      hw hm.2 color.val hout
    rw [hbnd,hbnd]
    have hpopulation : (Parameters.bodies n : ℝ)+2*Parameters.legs n=Parameters.dimension n := by
      exact_mod_cast Parameters.population_identity n
    rw [hpopulation]
    simp only [Int.cast_natCast,v7BaseBoundaryMass]
    field_simp
    ring
  change calibratedPrimaryProfile _ _ _ _ color = _
  simp only [calibratedPrimaryProfile,Pi.add_apply,Pi.smul_apply,Pi.sub_apply,smul_eq_mul,
    uniformFiniteProfile,Finset.mem_compl,hc,not_true_eq_false,if_true,if_false,sub_zero]
  rw [hbase]
  ring

theorem actual_boundary_profiles_eventually (C : ℝ) (hC : 1≤C) :
    ∀ᶠ n in atTop,
      (boundaryPalette (Parameters.modulus n) (boundaryHalf C n)).Nonempty ∧
      (boundaryPalette (Parameters.modulus n) (boundaryHalf C n))ᶜ.Nonempty ∧
      (∑ color,actualInteriorProfile C n color)=1 ∧ (∑ color,actualBoundaryProfile C n color)=1 := by
  filter_upwards [legCutoff_le_square_eventually C hC,body_support_scales_eventually C hC,
    eventually_ge_atTop 2] with n hcut hs hn
  have hb : 0<boundaryHalf C n := by
    unfold boundaryHalf maxBodyShift v7RootCutoff queueCutoff
    simp only [Parameters.safeMargin,Parameters.security_eq n hn]
    have hh : 0<n^2 := pow_pos (by omega) _
    omega
  have hboundary : (boundaryPalette (Parameters.modulus n) (boundaryHalf C n)).Nonempty := by
    let zero : Fin (Parameters.modulus n) := ⟨0,(Parameters.modulus_prime n).pos⟩
    exact ⟨zero,(mem_boundaryPalette _ _ _).mpr (Or.inl (by simpa only [zero,Nat.cast_zero] using hb))⟩
  have hinterior : (boundaryPalette (Parameters.modulus n) (boundaryHalf C n))ᶜ.Nonempty := by
    obtain ⟨color,hcolor⟩ := safePalette_nonempty n
    refine ⟨color,Finset.mem_compl.mpr ?_⟩
    intro hc
    have hh := (mem_boundaryPalette _ _ _).mp hc
    simp only [safePalette,TrimmedSlice.paletteSlice,Finset.mem_filter,Finset.mem_univ,true_and,
      TrimmedSlice.mem_slice] at hcolor
    omega
  exact ⟨hboundary,hinterior,uniformFiniteProfile_mass _ hinterior,uniformFiniteProfile_mass _ hboundary⟩

theorem actual_reference_mean_boundary_fixed_eventually (C : ℝ) (hC : 1≤C) :
    ∀ᶠ n in atTop,∀ beta : ℝ,
      boundaryCollapse (boundaryPalette (Parameters.modulus n) (boundaryHalf C n))ᶜ
        (actualInteriorProfile C n) (actualReferenceMean C n beta)=actualReferenceMean C n beta := by
  filter_upwards [actual_boundary_profiles_eventually C hC] with n hp beta
  let interior := (boundaryPalette (Parameters.modulus n) (boundaryHalf C n))ᶜ
  have hcard : (interior.card : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hp.2.1.card_pos
  have hm : (∑ color∈interior,actualInteriorProfile C n color)=1 := by
    change (∑ color∈interior,uniformFiniteProfile interior color)=1
    calc
      _ = ∑ _color∈interior,(interior.card : ℝ)⁻¹ := Finset.sum_congr rfl (fun color hc => if_pos hc)
      _ = 1 := by simp [hcard]
  let change := (Parameters.legs n : ℝ)*v7Activation C n*
    (repairedBoundaryMass n C beta (boundaryHalf C n)-v7BaseBoundaryMass C n (boundaryHalf C n))/Parameters.dimension n
  apply boundaryCollapse_eq_self_of_interior_multiple interior _ _ hm
    ((interior.card : ℝ)/Parameters.modulus n-change)
  intro color hc
  have hb := Finset.mem_compl.mp hc
  simp only [actualReferenceMean,referenceMean,calibratedReferenceMean,Pi.add_apply,Pi.smul_apply,
    Pi.sub_apply,smul_eq_mul,actualInteriorProfile,uniformFiniteProfile,Finset.mem_compl,hb,not_false_eq_true,
    if_false,if_true,zero_sub]
  change 1/(Parameters.modulus n : ℝ)+change*(-(interior.card : ℝ)⁻¹) =
    ((interior.card : ℝ)/Parameters.modulus n-change)*(interior.card : ℝ)⁻¹
  have he : ((interior.card : ℝ)/Parameters.modulus n)*(interior.card : ℝ)⁻¹ =
      1/(Parameters.modulus n : ℝ) := by
    calc
      _ = ((interior.card : ℝ)*(interior.card : ℝ)⁻¹)/Parameters.modulus n := by ring
      _ = _ := by rw [mul_inv_cancel₀ hcard]
  rw [sub_mul,he]
  ring

theorem actual_primary_boundary_collapse_eventually (C : ℝ) (hC : 1≤C) (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ n in atTop,(Parameters.legs n : ℝ)/(2*Parameters.dimension n)≤beta n ∧
      beta n≤2*(Parameters.legs n : ℝ)/Parameters.dimension n) :
    ∀ᶠ n in atTop,
      boundaryCollapse (boundaryPalette (Parameters.modulus n) (boundaryHalf C n))ᶜ
        (actualInteriorProfile C n) (actualPrimary C n (beta n)) =
      (1-repairedBoundaryMass n C (beta n) (boundaryHalf C n)) • actualInteriorProfile C n+
        repairedBoundaryMass n C (beta n) (boundaryHalf C n) • actualBoundaryProfile C n := by
  filter_upwards [actual_primary_boundary_eventually C hC,actual_boundary_profiles_eventually C hC,
    actual_primary_probability_eventually C hC beta hbeta] with n hb hu hp
  let interior := (boundaryPalette (Parameters.modulus n) (boundaryHalf C n))ᶜ
  let B := repairedBoundaryMass n C (beta n) (boundaryHalf C n)
  let candidate := (1-B) • actualInteriorProfile C n+B • actualBoundaryProfile C n
  have hcard : (interior.card : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hu.2.1.card_pos
  have hm : (∑ color∈interior,actualInteriorProfile C n color)=1 := by
    change (∑ color∈interior,uniformFiniteProfile interior color)=1
    calc
      _ = ∑ _color∈interior,(interior.card : ℝ)⁻¹ := Finset.sum_congr rfl (fun color hc => if_pos hc)
      _ = 1 := by simp [hcard]
  have hcandidate : (∑ color,candidate color)=1 := by
    simp only [candidate,Pi.add_apply,Pi.smul_apply,smul_eq_mul,Finset.sum_add_distrib,← Finset.mul_sum,hu.2.2.1,hu.2.2.2]
    ring
  have he : boundaryCollapse interior (actualInteriorProfile C n) (actualPrimary C n (beta n)) =
      boundaryCollapse interior (actualInteriorProfile C n) candidate := by
    apply boundaryCollapse_eq_of_same_boundary
    · exact hp.2.trans hcandidate.symm
    · intro color hc
      have hc' : color∈boundaryPalette (Parameters.modulus n) (boundaryHalf C n) := by
        simpa only [interior,Finset.mem_compl,not_not] using hc
      rw [hb (beta n) color hc']
      simp only [candidate,Pi.add_apply,Pi.smul_apply,smul_eq_mul,actualInteriorProfile,actualBoundaryProfile,
        uniformFiniteProfile,Finset.mem_compl,hc',not_true_eq_false,if_false,if_true,mul_zero,zero_add]
      rfl
  apply he.trans
  apply boundaryCollapse_eq_self_of_interior_multiple interior _ candidate hm (1-B)
  intro color hc
  have hb' := Finset.mem_compl.mp hc
  simp only [candidate,Pi.add_apply,Pi.smul_apply,smul_eq_mul,actualBoundaryProfile,uniformFiniteProfile,
    hb',if_false,mul_zero,add_zero]

def actualReferenceInteriorLaw (C : ℝ) (n : ℕ) : FiniteDist (Fin (Parameters.modulus n)) :=
  probabilityOr (actualInteriorProfile C n) (actualCoreLaw n)

def actualReferenceMarkedLaw (C : ℝ) (n : ℕ) (beta : ℝ) : FiniteDist (Fin (Parameters.modulus n)) :=
  probabilityOr (actualReferenceMarkedProfile C n beta) (actualCoreLaw n)

/-- A genuine finite product law, including legal fallback for small parameters. -/
def actualPositiveReferenceLaw (C : ℝ) (n : ℕ) (beta : ℝ) :
    FiniteDist ((Fin (Parameters.dimension n-Parameters.legs n) ⊕ Fin (Parameters.legs n)) → Fin (Parameters.modulus n)) :=
  FiniteDist.independent (fun slot => match slot with
    | .inl _ => actualReferenceInteriorLaw C n
    | .inr _ => actualReferenceMarkedLaw C n beta)

theorem actual_positive_reference_laws_eventually (C : ℝ) (hC : 1≤C) (beta : ℕ → ℝ)
    (hbeta : ∀ᶠ n in atTop,(Parameters.legs n : ℝ)/(2*Parameters.dimension n)≤beta n ∧
      beta n≤2*(Parameters.legs n : ℝ)/Parameters.dimension n) :
    ∀ᶠ n in atTop,
      0≤actualReferenceBoundaryRate C n (beta n) ∧ actualReferenceBoundaryRate C n (beta n)≤1 ∧
      (actualReferenceInteriorLaw C n).weight=actualInteriorProfile C n ∧
      (actualReferenceMarkedLaw C n (beta n)).weight=actualReferenceMarkedProfile C n (beta n) := by
  filter_upwards [actual_boundary_profiles_eventually C hC,actual_primary_boundary_eventually C hC,
    actual_primary_probability_eventually C hC beta hbeta,eventually_ge_atTop 1] with n hu hb hp hn
  let boundary := boundaryPalette (Parameters.modulus n) (boundaryHalf C n)
  let B := repairedBoundaryMass n C (beta n) (boundaryHalf C n)
  have hcard : (boundary.card : ℝ)≠0 := by exact_mod_cast ne_of_gt hu.1.card_pos
  have hBmass : (∑ color∈boundary,actualPrimary C n (beta n) color)=B := by
    calc
      _ = ∑ _color∈boundary,B/(boundary.card : ℝ) := Finset.sum_congr rfl (fun color hc => hb _ color hc)
      _ = B := by simp only [Finset.sum_const,nsmul_eq_mul]; field_simp
  have hB0 : 0≤B := by
    rw [← hBmass]
    exact Finset.sum_nonneg fun color _ => (hp.1 color).le
  have hB1 : B≤1 := by
    rw [← hBmass,← hp.2]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun color _ _ => (hp.1 color).le)
  have ha0 : 0≤v7Activation C n := (activation_positive _ _ _ _ (legFeatureCount_positive C n hC hn)).le
  have ha1 : v7Activation C n≤1 := (activation_le_one_hundredth _ _ _ _).trans (by norm_num)
  have ht0 : 0≤actualReferenceBoundaryRate C n (beta n) := mul_nonneg ha0 hB0
  have ht1 : actualReferenceBoundaryRate C n (beta n)≤1 := by
    exact (mul_le_mul ha1 hB1 hB0 (by norm_num)).trans_eq (by norm_num)
  have hI (color) : 0≤actualInteriorProfile C n color := by
    unfold actualInteriorProfile uniformFiniteProfile
    split_ifs <;> positivity
  have hB (color) : 0≤actualBoundaryProfile C n color := by
    unfold actualBoundaryProfile uniformFiniteProfile
    split_ifs <;> positivity
  have hmarked (color) : 0≤actualReferenceMarkedProfile C n (beta n) color :=
    add_nonneg (mul_nonneg (sub_nonneg.mpr ht1) (hI color)) (mul_nonneg ht0 (hB color))
  have hmarkedMass : (∑ color,actualReferenceMarkedProfile C n (beta n) color)=1 := by
    simp only [actualReferenceMarkedProfile,Pi.add_apply,Pi.smul_apply,smul_eq_mul,Finset.sum_add_distrib,
      ← Finset.mul_sum,hu.2.2.1,hu.2.2.2]
    ring
  exact ⟨ht0,ht1,probabilityOr_weight _ _ ⟨hI,hu.2.2.1⟩,probabilityOr_weight _ _ ⟨hmarked,hmarkedMass⟩⟩

end
end AFT.V7Calibration
