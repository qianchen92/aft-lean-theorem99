import AFT.BodyPathGeometry
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.ToLin

/-! # Actual path Gram matrix and the conditional covariance of body padding -/
namespace AFT.BodyPadding
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Matrix

def pathLinear (edges : ℕ) : (Fin edges → ℝ) →ₗ[ℝ] (Fin (edges+1) → ℝ) where
  toFun := realPath
  map_add' first second := by
    funext vertex
    have hs : (Fin.snoc (first+second) (0 : ℝ) : Fin (edges+1) → ℝ) vertex=(Fin.snoc first (0 : ℝ) : Fin (edges+1) → ℝ) vertex+(Fin.snoc second (0 : ℝ) : Fin (edges+1) → ℝ) vertex := by
      refine Fin.lastCases ?_ (fun vertex => ?_) vertex <;> simp
    have hc : (Fin.cons (0 : ℝ) (first+second) : Fin (edges+1) → ℝ) vertex=(Fin.cons (0 : ℝ) first : Fin (edges+1) → ℝ) vertex+(Fin.cons (0 : ℝ) second : Fin (edges+1) → ℝ) vertex := by
      refine Fin.cases ?_ (fun vertex => ?_) vertex <;> simp
    dsimp only [realPath,Pi.sub_apply,Pi.add_apply]
    rw [hs,hc]
    ring
  map_smul' scalar input := by
    funext vertex
    have hs : (Fin.snoc (scalar • input) (0 : ℝ) : Fin (edges+1) → ℝ) vertex=scalar*(Fin.snoc input (0 : ℝ) : Fin (edges+1) → ℝ) vertex := by
      refine Fin.lastCases ?_ (fun vertex => ?_) vertex <;> simp
    have hc : (Fin.cons (0 : ℝ) (scalar • input) : Fin (edges+1) → ℝ) vertex=scalar*(Fin.cons (0 : ℝ) input : Fin (edges+1) → ℝ) vertex := by
      refine Fin.cases ?_ (fun vertex => ?_) vertex <;> simp
    dsimp only [realPath,Pi.sub_apply,Pi.smul_apply,smul_eq_mul,RingHom.id_apply]
    rw [hs,hc]
    ring

def pathMatrix (edges : ℕ) : Matrix (Fin (edges+1)) (Fin edges) ℝ :=
  LinearMap.toMatrix' (pathLinear edges)

def pathGram (edges : ℕ) : Matrix (Fin edges) (Fin edges) ℝ :=
  (pathMatrix edges)ᴴ*pathMatrix edges

@[simp] theorem pathMatrix_mulVec (edges : ℕ) (input : Fin edges → ℝ) :
    (pathMatrix edges).mulVec input=realPath input :=
  LinearMap.toMatrix'_mulVec (pathLinear edges) input

theorem pathMatrix_injective (edges : ℕ) : Function.Injective (pathMatrix edges).mulVec := by
  intro first second he
  simp only [pathMatrix_mulVec] at he
  funext edge
  rw [← realPath_prefix first edge,← realPath_prefix second edge,he]

theorem pathGram_posDef (edges : ℕ) : (pathGram edges).PosDef :=
  Matrix.PosDef.conjTranspose_mul_self _ (pathMatrix_injective edges)

/-- The quadratic form of this exact matrix is the square norm of the
actual physical path incidence, including both endpoints. -/
theorem pathGram_quadratic (edges : ℕ) (input : Fin edges → ℝ) :
    star input ⬝ᵥ ((pathGram edges).mulVec input)=∑ vertex,realPath input vertex^2 := by
  unfold pathGram
  rw [← Matrix.mulVec_mulVec,Matrix.dotProduct_mulVec,Matrix.vecMul_conjTranspose]
  simp only [pathMatrix_mulVec,star_trivial,dotProduct,pow_two]

theorem pathGram_quadratic_upper (edges : ℕ) (input : Fin edges → ℝ) :
    star input ⬝ᵥ ((pathGram edges).mulVec input)≤4*∑ edge,input edge^2 := by
  rw [pathGram_quadratic]
  exact realPath_square_upper input

theorem pathGram_quadratic_lower (edges : ℕ) (input : Fin edges → ℝ) :
    (∑ edge,input edge^2)≤(edges+1 : ℝ)^2*(star input ⬝ᵥ ((pathGram edges).mulVec input)) := by
  rw [pathGram_quadratic]
  exact realPath_square_lower input

/-- The conditional covariance simplifies to sigma²(I-G/8). This is the
actual matrix appearing when an isotropic input is added to the padding
sigma²(8G⁻¹-I), before normalization of the resulting convolution. -/
def bodyConditionalCovariance (edges : ℕ) (sigma : ℝ) : Matrix (Fin edges) (Fin edges) ℝ :=
  sigma^2 • (1-(1/8 : ℝ) • pathGram edges)

theorem bodyConditionalCovariance_quadratic (edges : ℕ) (sigma : ℝ) (input : Fin edges → ℝ) :
    star input ⬝ᵥ ((bodyConditionalCovariance edges sigma).mulVec input)=
      sigma^2*((∑ edge,input edge^2)-(∑ vertex,realPath input vertex^2)/8) := by
  simp only [bodyConditionalCovariance,Matrix.smul_mulVec,Matrix.sub_mulVec,Matrix.one_mulVec,
    dotProduct_smul,dotProduct_sub,pathGram_quadratic,smul_eq_mul]
  simp only [star_trivial,dotProduct]
  congr 1
  simp only [pow_two]
  ring

theorem bodyConditionalCovariance_lower (edges : ℕ) (sigma : ℝ) (input : Fin edges → ℝ) :
    (sigma^2/2)*(∑ edge,input edge^2)≤
      star input ⬝ᵥ ((bodyConditionalCovariance edges sigma).mulVec input) := by
  rw [bodyConditionalCovariance_quadratic]
  have hh := mul_le_mul_of_nonneg_left (realPath_square_upper input) (sq_nonneg sigma)
  nlinarith

theorem bodyConditionalCovariance_upper (edges : ℕ) (sigma : ℝ) (input : Fin edges → ℝ) :
    star input ⬝ᵥ ((bodyConditionalCovariance edges sigma).mulVec input)≤
      sigma^2*(∑ edge,input edge^2) := by
  rw [bodyConditionalCovariance_quadratic]
  have hsum : 0≤∑ vertex,realPath input vertex^2 := Finset.sum_nonneg fun vertex _ => sq_nonneg _
  have hh := mul_nonneg (sq_nonneg sigma) hsum
  nlinarith

theorem bodyConditionalCovariance_posDef (edges : ℕ) (sigma : ℝ) (hsigma : sigma≠0) :
    (bodyConditionalCovariance edges sigma).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
  · change (bodyConditionalCovariance edges sigma)ᴴ=bodyConditionalCovariance edges sigma
    simp only [bodyConditionalCovariance,Matrix.conjTranspose_smul,Matrix.conjTranspose_sub,
      Matrix.conjTranspose_one,(pathGram_posDef edges).isHermitian.eq,star_trivial]
  · intro input hi
    have hex : ∃ edge,input edge≠0 := by
      by_contra hh
      apply hi
      funext edge
      simpa using not_exists.mp hh edge
    obtain ⟨edge,he⟩ := hex
    have hs : 0<∑ edge,input edge^2 :=
      Finset.sum_pos' (fun edge _ => sq_nonneg _) ⟨edge,Finset.mem_univ _,sq_pos_of_ne_zero he⟩
    exact (mul_pos (div_pos (sq_pos_of_ne_zero hsigma) (by norm_num)) hs).trans_le
      (bodyConditionalCovariance_lower edges sigma input)

end
end AFT.BodyPadding
