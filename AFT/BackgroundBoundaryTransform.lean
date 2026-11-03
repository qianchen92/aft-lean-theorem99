import AFT.PhysicalBackgroundPolynomial
import AFT.Inverse

/-! # The polynomial transform that records the complete boundary law

The true positive reference is not the iid product of its mean. The
boundary transform therefore retains its full nonconstant polynomial.
-/
namespace AFT.RepresentedPolynomial
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {Color : Type*} [Fintype Color] [DecidableEq Color]

def profilePolynomialMap (operator : Module.End ℝ (Color → ℝ)) : Table Color →ₐ[ℝ] Table Color :=
  MvPolynomial.aeval (fun color => profileForm (operator (Pi.single color 1)))

theorem profilePolynomialMap_profileForm (operator : Module.End ℝ (Color → ℝ)) (profile : Color → ℝ) :
    profilePolynomialMap operator (profileForm profile) = profileForm (operator profile) := by
  have he : profile = ∑ color,profile color • (Pi.single color (1:ℝ) : Color → ℝ) := by
    funext color
    simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,Pi.single_apply]
    simp
  calc
    _ = ∑ color,MvPolynomial.C (profile color)*profileForm (operator (Pi.single color 1)) := by
      rw [profileForm_apply]
      simp only [map_sum,map_mul,profilePolynomialMap,MvPolynomial.aeval_C,MvPolynomial.aeval_X]
      rfl
    _ = profileForm (operator (∑ color,profile color • (Pi.single color (1:ℝ) : Color → ℝ))) := by
      rw [map_sum,map_sum]
      apply Finset.sum_congr rfl
      intro color _
      simp only [map_smul,MvPolynomial.smul_eq_C_mul]
    _ = _ := by rw [← he]

def boundaryPolynomial (interior : Finset Color) (target : Color → ℝ) : Table Color →ₐ[ℝ] Table Color :=
  profilePolynomialMap (boundaryCollapse interior target)

def boundaryInteriorFactor (interior : Finset Color) (target reference : Color → ℝ) : Table Color :=
  1+profileForm target-boundaryPolynomial interior target (profileForm reference)

omit [Fintype Color] in
theorem boundaryCollapse_eq_self_of_interior_multiple (interior : Finset Color) (target profile : Color → ℝ)
    (hm : ∑ color ∈ interior,target color=1) (scalar : ℝ)
    (hprofile : ∀ color∈interior,profile color=scalar*target color) :
    boundaryCollapse interior target profile=profile := by
  have hs : (∑ color∈interior,profile color)=scalar := by
    rw [Finset.sum_congr rfl hprofile,← Finset.mul_sum,hm,mul_one]
  funext color
  by_cases hc : color∈interior
  · rw [boundaryCollapse_interior _ _ _ _ hc,hs,hm,div_one,hprofile color hc]
  · exact boundaryCollapse_boundary _ _ _ _ hc

theorem boundaryCollapse_eq_of_same_boundary (interior : Finset Color) (target first second : Color → ℝ)
    (hm : (∑ color,first color)=(∑ color,second color))
    (hb : ∀ color∉interior,first color=second color) :
    boundaryCollapse interior target first=boundaryCollapse interior target second := by
  have hc : (∑ color∈interiorᶜ,first color)=(∑ color∈interiorᶜ,second color) :=
    Finset.sum_congr rfl (fun color hc => hb color (Finset.mem_compl.mp hc))
  have hs : (∑ color∈interior,first color)=(∑ color∈interior,second color) := by
    have hf := Finset.sum_add_sum_compl interior first
    have hg := Finset.sum_add_sum_compl interior second
    rw [hm,hc] at hf
    linarith
  funext color
  by_cases hi : color∈interior
  · simp only [boundaryCollapse_interior _ _ _ _ hi,hs]
  · simp only [boundaryCollapse_boundary _ _ _ _ hi,hb color hi]

theorem boundaryPolynomial_single_mass_one (interior : Finset Color) (target reference profile : Color → ℝ)
    (hm : ∑ color,profile color=1) :
    boundaryPolynomial interior target (singleGenerating reference profile) =
      1+profileForm (boundaryCollapse interior target profile)-profileForm (boundaryCollapse interior target reference) := by
  rw [singleGenerating_mass_one reference profile hm,map_add,map_one,map_sub]
  simp only [boundaryPolynomial,map_sub,profilePolynomialMap_profileForm]
  ring

omit [Fintype Color] in
theorem boundaryCollapse_single_inside (interior : Finset Color) (target : Color → ℝ)
    (ht : ∀ color ∉ interior,target color=0) (hm : ∑ color ∈ interior,target color=1)
    (source : Color) (hs : source∈interior) :
    boundaryCollapse interior target (Pi.single source 1) = target := by
  funext color
  simp only [boundaryCollapse,LinearMap.coe_mk,AddHom.coe_mk,hm,div_one]
  split_ifs with hc
  · simp [hs]
  · have hne : color≠source := by rintro rfl; exact hc hs
    simp [hne,ht color hc]

theorem boundaryPolynomial_centeredFactor_inside (interior : Finset Color) (target reference : Color → ℝ)
    (ht : ∀ color ∉ interior,target color=0) (hm : ∑ color ∈ interior,target color=1)
    (source : Color) (hs : source∈interior) :
    boundaryPolynomial interior target (centeredFactor reference source) = boundaryInteriorFactor interior target reference := by
  simp only [centeredFactor,map_sub,map_add,map_one]
  simp only [boundaryPolynomial,profilePolynomialMap,MvPolynomial.aeval_X]
  rw [boundaryCollapse_single_inside interior target ht hm source hs]
  rfl

theorem boundaryPolynomial_single_interior (interior : Finset Color) (target reference profile : Color → ℝ)
    (ht : ∀ color ∉ interior,target color=0) (hm : ∑ color ∈ interior,target color=1)
    (hp : ∀ color ∉ interior,profile color=0) :
    boundaryPolynomial interior target (singleGenerating reference profile) =
      MvPolynomial.C (∑ color,profile color)*boundaryInteriorFactor interior target reference := by
  unfold singleGenerating
  simp only [map_sum,map_mul]
  have he (color : Color) : boundaryPolynomial interior target (MvPolynomial.C (profile color)) =
      MvPolynomial.C (profile color) := (boundaryPolynomial interior target).commutes _
  simp_rw [he]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro color _
  by_cases hc : color∈interior
  · rw [boundaryPolynomial_centeredFactor_inside interior target reference ht hm color hc]
  · simp only [hp color hc,map_zero,zero_mul]

theorem boundaryPolynomial_triple_interior (interior : Finset Color) (target reference : Color → ℝ)
    (mass : Color → Color → Color → ℝ)
    (ht : ∀ color ∉ interior,target color=0) (hm : ∑ color ∈ interior,target color=1)
    (hs : ∀ first second third,mass first second third≠0 →
      first∈interior ∧ second∈interior ∧ third∈interior) :
    boundaryPolynomial interior target (tripleGenerating reference mass) =
      MvPolynomial.C (∑ first,∑ second,∑ third,mass first second third)*
        boundaryInteriorFactor interior target reference^3 := by
  unfold tripleGenerating
  simp only [map_sum,map_mul,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro first _
  apply Finset.sum_congr rfl
  intro second _
  apply Finset.sum_congr rfl
  intro third _
  have he : boundaryPolynomial interior target (MvPolynomial.C (mass first second third)) =
      MvPolynomial.C (mass first second third) := (boundaryPolynomial interior target).commutes _
  rw [he]
  by_cases hz : mass first second third=0
  · simp only [hz,map_zero,zero_mul]
  · have hc := hs first second third hz
    rw [boundaryPolynomial_centeredFactor_inside interior target reference ht hm first hc.1,
      boundaryPolynomial_centeredFactor_inside interior target reference ht hm second hc.2.1,
      boundaryPolynomial_centeredFactor_inside interior target reference ht hm third hc.2.2]
    ring

theorem boundaryPolynomial_triple_companions (interior : Finset Color) (target reference : Color → ℝ)
    (mass : Color → Color → Color → ℝ)
    (ht : ∀ color ∉ interior,target color=0) (hm : ∑ color ∈ interior,target color=1)
    (hs : ∀ first second third,mass first second third≠0 → second∈interior ∧ third∈interior) :
    boundaryPolynomial interior target (tripleGenerating reference mass) =
      boundaryPolynomial interior target (singleGenerating reference (fun first => ∑ second,∑ third,mass first second third))*
        boundaryInteriorFactor interior target reference^2 := by
  unfold tripleGenerating singleGenerating
  simp only [map_sum,map_mul,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro first _
  apply Finset.sum_congr rfl
  intro second _
  apply Finset.sum_congr rfl
  intro third _
  by_cases hz : mass first second third=0
  · simp only [hz,map_zero,zero_mul]
  · have hc := hs first second third hz
    rw [boundaryPolynomial_centeredFactor_inside interior target reference ht hm second hc.1,
      boundaryPolynomial_centeredFactor_inside interior target reference ht hm third hc.2]
    ring

end
end AFT.RepresentedPolynomial
