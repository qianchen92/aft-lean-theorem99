import CurrentAFT.DiffuseProfiles
import AFT.RationalWindowTickets

/-! # Executable fair-bit sampling of the current Gaussian windows

The finite rational pi/exponential programs and integer ticket rounding
are instantiated at the current squared width. These are actual functions
of finite bit tapes, with exact window support and a proved whole-law
error. This module alone does not give the full affine sampler's runtime.
-/
namespace CurrentAFT.WindowGaussianSampler
open AFT GaussianSource RationalNumerics DiffuseProfiles
open scoped BigOperators Classical
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

def squaredWidth (security : ℕ) : ℚ := (security + 2 : ℚ)^2

theorem squaredWidth_positive (security : ℕ) : 0 < squaredWidth security := by
  unfold squaredWidth
  positivity

theorem squaredWidth_real (security : ℕ) :
    (squaredWidth security : ℝ) = (Parameters.sourceWidth security : ℝ)^2 := by
  unfold squaredWidth Parameters.sourceWidth Parameters.base
  push_cast
  rfl

/-- The precision input changes a single finite rational program, rather
than choosing an arbitrary finite real law by existence. -/
def draw (security cutoff bits : ℕ) : (Fin (windowTicketBits cutoff bits) → Fin 2) → Window cutoff :=
  windowGaussianDraw (squaredWidth security) cutoff bits

theorem draw_support (security cutoff bits : ℕ) (word : Fin (windowTicketBits cutoff bits) → Fin 2) :
    -(cutoff : ℤ) ≤ (draw security cutoff bits word).val ∧
      (draw security cutoff bits word).val ≤ (cutoff : ℤ) :=
  Finset.mem_Icc.mp (draw security cutoff bits word).property

noncomputable section

/-- The L1 error includes analytic rational approximation, normalization,
and finite ticket rounding, under the genuine independent fair-bit law. -/
theorem draw_l1 (security cutoff bits : ℕ) :
    (∑ point, |((FiniteDist.independent (fun _ : Fin (windowTicketBits cutoff bits) =>
      FiniteDist.uniform (Fin 2))).map (draw security cutoff bits)).weight point -
        (windowGaussian (Parameters.sourceWidth security) cutoff).weight point|) ≤ 1 / (2 : ℝ)^bits := by
  rw [show draw security cutoff bits = windowGaussianDraw (squaredWidth security) cutoff bits from rfl,
    windowGaussianDraw_law]
  exact windowTicketLaw_l1 _ _ _ _ (squaredWidth_positive security) (squaredWidth_real security)

theorem scalar_draw_l1 (security bits : ℕ) :
    (∑ point, |((FiniteDist.independent
      (fun _ : Fin (windowTicketBits (Parameters.sourceCutoff security - 1) bits) => FiniteDist.uniform (Fin 2))).map
        (draw security (Parameters.sourceCutoff security - 1) bits)).weight point - (scalarLaw security).weight point|) ≤
          1 / (2 : ℝ)^bits := draw_l1 security _ bits

theorem edge_draw_l1 (security bits : ℕ) :
    (∑ point, |((FiniteDist.independent
      (fun _ : Fin (windowTicketBits (edgeCutoff security) bits) => FiniteDist.uniform (Fin 2))).map
        (draw security (edgeCutoff security) bits)).weight point - (edgeLaw security).weight point|) ≤
          1 / (2 : ℝ)^bits := draw_l1 security _ bits

/-- Input randomness is polynomial in the current security parameter and
the requested precision counter. The runtime analysis remains separate. -/
theorem tape_length (security cutoff bits : ℕ) (hcutoff : cutoff ≤ Parameters.sourceCutoff security) :
    windowTicketBits cutoff bits ≤ bits + 2 * (security + 2)^2 + 3 := by
  unfold windowTicketBits
  simp only [Parameters.sourceCutoff, Parameters.base] at hcutoff
  omega

end
end CurrentAFT.WindowGaussianSampler
