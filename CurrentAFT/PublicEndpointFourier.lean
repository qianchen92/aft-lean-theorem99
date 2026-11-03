import CurrentAFT.FourierCoordinates
import CurrentAFT.PublicCore

/-! # Exact Fourier transport from the implementation palette to residues -/
namespace CurrentAFT.PublicEndpointFourier
open AFT FourierCoordinates
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
variable {Core Index Color : Type*} [Fintype Core] [Fintype Index] [Fintype Color]
  [DecidableEq Index] {modulus : ℕ} [NeZero modulus]

def wordEquiv (palette : Color ≃ ZMod modulus) : (Index → Color) ≃ (Index → ZMod modulus) :=
  Equiv.piCongrRight (fun _ => palette)

theorem mapped_mass (palette : Color ≃ ZMod modulus)
    (proposal : FiniteDist Core) (weight : Core → ℝ) (channel : Core → FiniteDist (Index → Color))
    (endpoint : Index → ZMod modulus) :
    endpointMass proposal weight (fun core => (channel core).map (wordEquiv palette)) endpoint =
      endpointMass proposal weight channel ((wordEquiv palette).symm endpoint) := by
  unfold endpointMass
  simp only [FiniteDist.map_equiv_weight]

theorem fourier_relabel (palette : Color ≃ ZMod modulus) (mass : (Index → Color) → ℝ)
    (frequency : Index → ZMod modulus) :
    signedFourier (fun endpoint => mass ((wordEquiv palette).symm endpoint)) (coordinateCharacter frequency) =
      FourierCoordinates.fourier palette (fun word => (mass word : ℂ)) frequency := by
  have h := (wordEquiv (Index := Index) palette).sum_comp
    (fun endpoint => (mass ((wordEquiv palette).symm endpoint) : ℂ) * coordinateCharacter frequency endpoint)
  simpa only [signedFourier, characterFourier, FourierCoordinates.fourier, scalarCharacter, coordinateCharacter,
    wordEquiv, Equiv.piCongrRight_apply, Equiv.coe_fn_mk, Equiv.symm_apply_apply] using h.symm

theorem mapped_fourier (palette : Color ≃ ZMod modulus)
    (proposal : FiniteDist Core) (weight : Core → ℝ) (channel : Core → FiniteDist (Index → Color))
    (frequency : Index → ZMod modulus) :
    signedFourier (endpointMass proposal weight (fun core => (channel core).map (wordEquiv palette)))
        (coordinateCharacter frequency) =
      FourierCoordinates.fourier palette (fun word => (endpointMass proposal weight channel word : ℂ)) frequency := by
  rw [show endpointMass proposal weight (fun core => (channel core).map (wordEquiv palette)) =
    fun endpoint => endpointMass proposal weight channel ((wordEquiv palette).symm endpoint) from
    funext (mapped_mass palette proposal weight channel)]
  exact fourier_relabel palette _ frequency

end
end CurrentAFT.PublicEndpointFourier
