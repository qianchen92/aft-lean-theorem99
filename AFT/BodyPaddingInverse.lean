import AFT.BodyPaddingCovariance

/-! # Quantitative inverse bounds for the actual path Gram matrix -/
namespace AFT.BodyPadding
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Matrix

theorem pathMatrix_apply (edges : ℕ) (vertex : Fin (edges+1)) (edge : Fin edges) :
    pathMatrix edges vertex edge=
      (if vertex=edge.castSucc then 1 else 0)-(if vertex=edge.succ then 1 else 0) := by
  change realPath (Pi.single edge 1) vertex=_
  have hs : (Fin.snoc (Pi.single edge (1 : ℝ)) 0 : Fin (edges+1) → ℝ) vertex=
      if vertex=edge.castSucc then 1 else 0 := by
    refine Fin.lastCases ?_ (fun other => ?_) vertex
    · simp [ne_of_gt (Fin.castSucc_lt_last edge)]
    · simp [Pi.single_apply]
  have hc : (Fin.cons 0 (Pi.single edge (1 : ℝ)) : Fin (edges+1) → ℝ) vertex=
      if vertex=edge.succ then 1 else 0 := by
    refine Fin.cases ?_ (fun other => ?_) vertex
    · simp [Ne.symm (Fin.succ_ne_zero edge)]
    · simp [Pi.single_apply]
  exact congrArg₂ (·-·) hs hc

@[simp] theorem pathTranspose_mulVec (edges : ℕ) (input : Fin (edges+1) → ℝ) (edge : Fin edges) :
    ((pathMatrix edges)ᴴ.mulVec input) edge=input edge.castSucc-input edge.succ := by
  simp only [Matrix.mulVec,dotProduct,Matrix.conjTranspose_apply,star_trivial,pathMatrix_apply,
    sub_mul,Finset.sum_sub_distrib,ite_mul,one_mul,zero_mul,Finset.sum_ite_eq',Finset.mem_univ,if_true]

theorem pathTranspose_square_upper (edges : ℕ) (input : Fin (edges+1) → ℝ) :
    (∑ edge,((pathMatrix edges)ᴴ.mulVec input edge)^2)≤4*∑ vertex,input vertex^2 := by
  simp only [pathTranspose_mulVec]
  have hc : (∑ edge : Fin edges,input edge.castSucc^2)≤∑ vertex,input vertex^2 := by
    rw [Fin.sum_univ_castSucc]
    exact le_add_of_nonneg_right (sq_nonneg _)
  have hs : (∑ edge : Fin edges,input edge.succ^2)≤∑ vertex,input vertex^2 := by
    rw [Fin.sum_univ_succ]
    exact le_add_of_nonneg_left (sq_nonneg _)
  calc
    _ ≤ ∑ edge : Fin edges,(2*input edge.castSucc^2+2*input edge.succ^2) := by
      apply Finset.sum_le_sum
      intro edge _
      nlinarith [sq_nonneg (input edge.castSucc+input edge.succ)]
    _ = 2*(∑ edge : Fin edges,input edge.castSucc^2)+2*(∑ edge : Fin edges,input edge.succ^2) := by
      rw [Finset.sum_add_distrib,← Finset.mul_sum,← Finset.mul_sum]
    _ ≤ _ := by linarith

/-- For the physical incidence, the Gram square is bounded by four times
its Gram form. This directly controls the inverse, without an abstract
spectral estimate or an assumed conditioning constant. -/
theorem pathGram_square_upper (edges : ℕ) (input : Fin edges → ℝ) :
    (∑ edge,((pathGram edges).mulVec input edge)^2)≤
      4*(star input ⬝ᵥ ((pathGram edges).mulVec input)) := by
  rw [pathGram_quadratic]
  unfold pathGram
  rw [← Matrix.mulVec_mulVec,pathMatrix_mulVec]
  exact pathTranspose_square_upper edges (realPath input)

theorem pathGram_inverse_quadratic_lower (edges : ℕ) (input : Fin edges → ℝ) :
    (∑ edge,input edge^2)≤4*(star input ⬝ᵥ ((pathGram edges)⁻¹.mulVec input)) := by
  letI := (pathGram_posDef edges).isUnit.invertible
  have he : (pathGram edges).mulVec ((pathGram edges)⁻¹.mulVec input)=input := by
    rw [Matrix.mulVec_mulVec,Matrix.mul_inv_of_invertible,Matrix.one_mulVec]
  have hh := pathGram_square_upper edges ((pathGram edges)⁻¹.mulVec input)
  rw [he] at hh
  simpa only [star_trivial,dotProduct_comm] using hh

theorem pathGram_inverse_quadratic_upper (edges : ℕ) (input : Fin edges → ℝ) :
    star input ⬝ᵥ ((pathGram edges)⁻¹.mulVec input)≤(edges+1 : ℝ)^2*(∑ edge,input edge^2) := by
  letI := (pathGram_posDef edges).isUnit.invertible
  have he : (pathGram edges).mulVec ((pathGram edges)⁻¹.mulVec input)=input := by
    rw [Matrix.mulVec_mulVec,Matrix.mul_inv_of_invertible,Matrix.one_mulVec]
  have hh := pathGram_quadratic_lower edges ((pathGram edges)⁻¹.mulVec input)
  rw [he] at hh
  simp only [star_trivial,dotProduct_comm] at hh ⊢
  have hpos : 0 ≤ input ⬝ᵥ ((pathGram edges)⁻¹.mulVec input) := by
    simpa only [star_trivial] using (pathGram_posDef edges).inv.posSemidef.dotProduct_mulVec_nonneg input
  have hc := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin edges)) input
    ((pathGram edges)⁻¹.mulVec input)
  have hs : 0≤∑ edge,input edge^2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hm := mul_le_mul_of_nonneg_left hh hs
  have hineq : (input ⬝ᵥ ((pathGram edges)⁻¹.mulVec input)) *
      (input ⬝ᵥ ((pathGram edges)⁻¹.mulVec input))≤
      ((edges+1 : ℝ)^2*(∑ edge,input edge^2))*(input ⬝ᵥ ((pathGram edges)⁻¹.mulVec input)) := by
    dsimp only [dotProduct]
    dsimp only [dotProduct] at hm
    nlinarith only [hc,hm]
  rcases eq_or_lt_of_le hpos with hz|hp
  · rw [← hz]
    exact mul_nonneg (sq_nonneg _) hs
  · exact (mul_le_mul_iff_left₀ hp).mp (by simpa only [mul_comm] using hineq)

/-- The exact padding covariance from V7. -/
def bodyPaddingCovariance (edges : ℕ) (sigma : ℝ) : Matrix (Fin edges) (Fin edges) ℝ :=
  sigma^2 • ((8 : ℝ) • (pathGram edges)⁻¹-1)

theorem bodyPaddingCovariance_quadratic (edges : ℕ) (sigma : ℝ) (input : Fin edges → ℝ) :
    star input ⬝ᵥ ((bodyPaddingCovariance edges sigma).mulVec input)=
      sigma^2*(8*(star input ⬝ᵥ ((pathGram edges)⁻¹.mulVec input))-(∑ edge,input edge^2)) := by
  simp only [bodyPaddingCovariance,Matrix.smul_mulVec,Matrix.sub_mulVec,Matrix.one_mulVec,
    dotProduct_smul,dotProduct_sub,smul_eq_mul,star_trivial]
  simp only [dotProduct,pow_two]

theorem bodyPaddingCovariance_bounds (edges : ℕ) (sigma : ℝ) (input : Fin edges → ℝ) :
    sigma^2*(∑ edge,input edge^2)≤star input ⬝ᵥ ((bodyPaddingCovariance edges sigma).mulVec input) ∧
    star input ⬝ᵥ ((bodyPaddingCovariance edges sigma).mulVec input)≤
      8*sigma^2*(edges+1 : ℝ)^2*(∑ edge,input edge^2) := by
  rw [bodyPaddingCovariance_quadratic]
  have hl := mul_le_mul_of_nonneg_left (pathGram_inverse_quadratic_lower edges input) (sq_nonneg sigma)
  have hu := mul_le_mul_of_nonneg_left (pathGram_inverse_quadratic_upper edges input) (sq_nonneg sigma)
  have hs : 0≤sigma^2*(∑ edge,input edge^2) := mul_nonneg (sq_nonneg sigma) (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  constructor <;> nlinarith


theorem bodyPaddingCovariance_posDef (edges : ℕ) (sigma : ℝ) (hsigma : sigma≠0) :
    (bodyPaddingCovariance edges sigma).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
  · change (bodyPaddingCovariance edges sigma)ᴴ=bodyPaddingCovariance edges sigma
    simp only [bodyPaddingCovariance,Matrix.conjTranspose_smul,Matrix.conjTranspose_sub,
      Matrix.conjTranspose_one,(pathGram_posDef edges).inv.isHermitian.eq,star_trivial]
  · intro input hi
    have hex : ∃ edge,input edge≠0 := by
      by_contra hh
      apply hi
      funext edge
      simpa using not_exists.mp hh edge
    obtain ⟨edge,he⟩ := hex
    have hs : 0<∑ edge,input edge^2 :=
      Finset.sum_pos' (fun edge _ => sq_nonneg _) ⟨edge,Finset.mem_univ _,sq_pos_of_ne_zero he⟩
    exact (mul_pos (sq_pos_of_ne_zero hsigma) hs).trans_le
      (bodyPaddingCovariance_bounds edges sigma input).1

/-- Completing the square in the actual convolution gives precisely this
conditional covariance; the inverse formula is proved for the actual path
matrix, rather than assumed as a spectral condition. -/
theorem bodyConditionalCovariance_inverse_formula (edges : ℕ) (sigma : ℝ)
    (hsigma : sigma≠0) :
    ((sigma^2)⁻¹ • (1 : Matrix (Fin edges) (Fin edges) ℝ) +
      (bodyPaddingCovariance edges sigma)⁻¹)⁻¹=bodyConditionalCovariance edges sigma := by
  letI := (pathGram_posDef edges).isUnit.invertible
  letI := (bodyPaddingCovariance_posDef edges sigma hsigma).isUnit.invertible
  apply Matrix.inv_eq_right_inv
  apply (Matrix.mul_right_injective_of_invertible (bodyPaddingCovariance edges sigma))
  dsimp only
  rw [← Matrix.mul_assoc,Matrix.mul_add,Matrix.mul_inv_of_invertible]
  have hleft : bodyPaddingCovariance edges sigma*((sigma^2)⁻¹ • 1)+1=
      (8 : ℝ) • (pathGram edges)⁻¹ := by
    simp only [bodyPaddingCovariance,Matrix.mul_smul,Matrix.mul_one,
      smul_smul]
    rw [inv_mul_cancel₀ (pow_ne_zero _ hsigma),one_smul]
    abel
  rw [hleft,Matrix.mul_one]
  simp only [bodyConditionalCovariance,bodyPaddingCovariance,Matrix.mul_smul,
    Matrix.smul_mul,Matrix.mul_sub,Matrix.mul_one,Matrix.inv_mul_of_invertible,
    smul_sub,smul_smul]
  module

end
end AFT.BodyPadding
