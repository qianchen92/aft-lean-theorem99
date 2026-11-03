import AFT.MeanOutput

/-! # Exact centered generating polynomials of finite physical laws -/
namespace AFT.RepresentedPolynomial
open scoped BigOperators Classical
noncomputable section
variable {Color : Type*} [Fintype Color]

theorem profileForm_apply (profile : Color → ℝ) :
    profileForm profile = ∑ color,MvPolynomial.C (profile color)*MvPolynomial.X color := rfl

/-- The color factor used by the actual centered histogram generating law. -/
def centeredFactor (reference : Color → ℝ) (color : Color) : MvPolynomial Color ℝ :=
  1+MvPolynomial.X color-profileForm reference

def singleGenerating (reference profile : Color → ℝ) : MvPolynomial Color ℝ :=
  ∑ color,MvPolynomial.C (profile color)*centeredFactor reference color

def pairForm (mass : Color → Color → ℝ) : MvPolynomial Color ℝ :=
  ∑ first,∑ second,MvPolynomial.C (mass first second)*MvPolynomial.X first*MvPolynomial.X second

def tripleForm (mass : Color → Color → Color → ℝ) : MvPolynomial Color ℝ :=
  ∑ first,∑ second,∑ third,MvPolynomial.C (mass first second third)*MvPolynomial.X first*MvPolynomial.X second*MvPolynomial.X third

def pairGenerating (reference : Color → ℝ) (mass : Color → Color → ℝ) : MvPolynomial Color ℝ :=
  ∑ first,∑ second,MvPolynomial.C (mass first second)*centeredFactor reference first*centeredFactor reference second

def tripleGenerating (reference : Color → ℝ) (mass : Color → Color → Color → ℝ) : MvPolynomial Color ℝ :=
  ∑ first,∑ second,∑ third,MvPolynomial.C (mass first second third)*centeredFactor reference first*
    centeredFactor reference second*centeredFactor reference third

theorem singleGenerating_formula (reference profile : Color → ℝ) :
    singleGenerating reference profile = profileForm profile+
      MvPolynomial.C (∑ color,profile color)*(1-profileForm reference) := by
  simp only [singleGenerating,centeredFactor,mul_sub,mul_add,mul_one,Finset.sum_sub_distrib,
    Finset.sum_add_distrib,← Finset.sum_mul,← map_sum,profileForm_apply]
  ring

theorem singleGenerating_mass_zero (reference profile : Color → ℝ) (hmass : ∑ color,profile color = 0) :
    singleGenerating reference profile = profileForm profile := by
  rw [singleGenerating_formula,hmass,map_zero,zero_mul,add_zero]

theorem singleGenerating_mass_one (reference profile : Color → ℝ) (hmass : ∑ color,profile color = 1) :
    singleGenerating reference profile = 1+profileForm (profile-reference) := by
  rw [singleGenerating_formula,hmass,map_one,one_mul,map_sub]
  ring

theorem pairForm_add (first second : Color → Color → ℝ) :
    pairForm (first+second) = pairForm first+pairForm second := by
  simp only [pairForm,Pi.add_apply,map_add,add_mul,Finset.sum_add_distrib]

theorem pairForm_sub (first second : Color → Color → ℝ) :
    pairForm (first-second) = pairForm first-pairForm second := by
  simp only [pairForm,Pi.sub_apply,map_sub,sub_mul,Finset.sum_sub_distrib]

theorem pairForm_smul (scalar : ℝ) (mass : Color → Color → ℝ) :
    pairForm (scalar • mass) = MvPolynomial.C scalar*pairForm mass := by
  simp only [pairForm,Pi.smul_apply,smul_eq_mul,map_mul,Finset.mul_sum,mul_assoc]

theorem pairForm_tensor (first second : Color → ℝ) :
    pairForm (fun a b => first a*second b) = profileForm first*profileForm second := by
  simp only [pairForm,profileForm_apply,map_mul]
  simp_rw [Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

theorem pairForm_canonical (reference : Color → ℝ) (mass : Color → Color → ℝ) :
    pairForm (SafePair.canonicalPair reference mass) = pairForm mass-
      profileForm reference*profileForm (fun b => ∑ a,mass a b)-
      profileForm (fun a => ∑ b,mass a b)*profileForm reference+
      MvPolynomial.C (∑ a,∑ b,mass a b)*profileForm reference^2 := by
  have heq : SafePair.canonicalPair reference mass = mass-
      (fun a b => reference a*(∑ x,mass x b))-
      (fun a b => (∑ y,mass a y)*reference b)+
      (∑ x,∑ y,mass x y) • (fun a b => reference a*reference b) := by
    funext a b
    simp only [SafePair.canonicalPair,Pi.add_apply,Pi.sub_apply,Pi.smul_apply,smul_eq_mul]
    ring
  rw [heq,pairForm_add,pairForm_sub,pairForm_sub,pairForm_smul]
  simp only [pairForm_tensor,pow_two]

theorem pairGenerating_formula (reference : Color → ℝ) (mass : Color → Color → ℝ) :
    pairGenerating reference mass = pairForm mass+
      profileForm (fun a => ∑ b,mass a b)*(1-profileForm reference)+
      profileForm (fun b => ∑ a,mass a b)*(1-profileForm reference)+
      MvPolynomial.C (∑ a,∑ b,mass a b)*(1-profileForm reference)^2 := by
  let T : MvPolynomial Color ℝ := 1-profileForm reference
  have hf (color : Color) : centeredFactor reference color = MvPolynomial.X color+T := by
    unfold centeredFactor T
    ring
  have hpoint (a b : Color) : MvPolynomial.C (mass a b)*(MvPolynomial.X a+T)*(MvPolynomial.X b+T) =
      MvPolynomial.C (mass a b)*MvPolynomial.X a*MvPolynomial.X b+
      MvPolynomial.C (mass a b)*MvPolynomial.X a*T+
      MvPolynomial.C (mass a b)*MvPolynomial.X b*T+MvPolynomial.C (mass a b)*T^2 := by ring
  unfold pairGenerating
  simp_rw [hf,hpoint]
  simp only [Finset.sum_add_distrib]
  have hrow : (∑ a,∑ b,MvPolynomial.C (mass a b)*MvPolynomial.X a*T) =
      profileForm (fun a => ∑ b,mass a b)*T := by
    simp only [profileForm_apply,Finset.sum_mul,map_sum]
  have hcol : (∑ a,∑ b,MvPolynomial.C (mass a b)*MvPolynomial.X b*T) =
      profileForm (fun b => ∑ a,mass a b)*T := by
    rw [Finset.sum_comm]
    simp only [profileForm_apply,Finset.sum_mul,map_sum]
  have hconst : (∑ a,∑ b,MvPolynomial.C (mass a b)*T^2) =
      MvPolynomial.C (∑ a,∑ b,mass a b)*T^2 := by
    simp only [map_sum,Finset.sum_mul]
  rw [hrow,hcol,hconst]
  rfl

/-- This identity is the full pair polynomial, not only its homogeneous
highest-degree term. Its quadratic part is the actual reference-canonical mass. -/
theorem pairGenerating_canonical (reference : Color → ℝ) (mass : Color → Color → ℝ) :
    pairGenerating reference mass = pairForm (SafePair.canonicalPair reference mass)+
      profileForm (fun a => (∑ b,mass a b)+(∑ b,mass b a)-
        2*(∑ x,∑ y,mass x y)*reference a)+MvPolynomial.C (∑ a,∑ b,mass a b) := by
  rw [pairGenerating_formula,pairForm_canonical]
  have heq : (fun a => (∑ b,mass a b)+(∑ b,mass b a)-2*(∑ x,∑ y,mass x y)*reference a) =
      (fun a => ∑ b,mass a b)+(fun a => ∑ b,mass b a)-(2*(∑ x,∑ y,mass x y)) • reference := rfl
  rw [heq,map_sub,map_add,map_smul]
  simp only [MvPolynomial.smul_eq_C_mul,map_mul,map_ofNat]
  ring

theorem tripleGenerating_tensor (reference : Color → ℝ) (pair : Color → Color → ℝ) (single : Color → ℝ) :
    tripleGenerating reference (fun a b c => pair a b*single c) =
      pairGenerating reference pair*singleGenerating reference single := by
  simp only [tripleGenerating,pairGenerating,singleGenerating,map_mul]
  simp_rw [Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro c _
  ring

theorem tripleForm_tensor (pair : Color → Color → ℝ) (single : Color → ℝ) :
    tripleForm (fun a b c => pair a b*single c) = pairForm pair*profileForm single := by
  simp only [tripleForm,pairForm,profileForm_apply,map_mul]
  simp_rw [Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro c _
  ring

/-- A true pair/body covariance contributes exactly its canonical cubic
and both endpoint/body quadratic terms. -/
theorem tripleGenerating_covariance (reference : Color → ℝ) (pair : Color → Color → ℝ) (single : Color → ℝ)
    (hp : (∑ a,∑ b,pair a b) = 0) (hs : ∑ c,single c = 0) :
    tripleGenerating reference (fun a b c => pair a b*single c) =
      tripleForm (fun a b c => SafePair.canonicalPair reference pair a b*single c)+
      pairForm (fun a c => (∑ b,pair a b)*single c)+
      pairForm (fun b c => (∑ a,pair a b)*single c) := by
  rw [tripleGenerating_tensor,pairGenerating_canonical,singleGenerating_mass_zero _ _ hs,hp]
  simp only [mul_zero,zero_mul,sub_zero,map_zero,add_zero]
  rw [show (fun a => (∑ b,pair a b)+(∑ b,pair b a)) =
    (fun a => ∑ b,pair a b)+(fun a => ∑ b,pair b a) from rfl,map_add,
    tripleForm_tensor,pairForm_tensor,pairForm_tensor]
  ring

end
end AFT.RepresentedPolynomial
