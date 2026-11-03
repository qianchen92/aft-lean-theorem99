import AFT.RationalRejectionProgram
import AFT.GlobalPositiveRepair

/-! # Executable global rejection with all three error sources separated -/
namespace AFT.RationalRejectionProgram
open FiniteDist
open scoped BigOperators
variable {State Tape : Type*}

 def positiveDraw (decode : Tape → State) (raw : State → ℚ)
    (envelope bits attempts : ℕ) (fallback : State) :
    (Fin attempts → Tape×(Fin bits → Fin 2)) → State :=
  draw decode (fun point => max (raw point) 0/(envelope : ℚ)) bits attempts fallback

noncomputable section
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable [Fintype State] [Fintype Tape] [Nonempty Tape]

 omit [Fintype State] in
 theorem positiveCoinApprox_error (raw : State → ℚ) (score : State → ℝ)
    (envelope : ℕ) (he : 1≤envelope) (error : ℝ)
    (herror : ∀ point,|(raw point : ℝ)-score point|≤error) (point : State) :
    |((max (raw point) 0/(envelope : ℚ) : ℚ) : ℝ)-positiveCoin score envelope point|≤error := by
  have heR : (1 : ℝ)≤envelope := by exact_mod_cast he
  simp only [Rat.cast_div,Rat.cast_max,Rat.cast_zero,Rat.cast_natCast,positiveCoin]
  rw [←sub_div,abs_div,abs_of_pos (by linarith : (0 : ℝ)<envelope)]
  exact (div_le_self (abs_nonneg _) heR).trans
    ((abs_max_sub_max_le_abs _ _ _).trans (herror point))

/-- This theorem is for the actual finite-tape code above. It accounts for
proposal approximation, numerical score/coin approximation, and exhaustion.
The raw certificate also proves the acceptance floor, with no rare-record
normalizer in the executable program. -/
 theorem positiveDraw_tv (decode : Tape → State) (raw : State → ℚ)
    (proposal reference : FiniteDist State) (score : State → ℝ)
    (envelope bits attempts : ℕ) (fallback : State)
    (proposalError scoreError rawError : ℝ)
    (hproposal : TVBound ((uniform Tape).map decode) proposal proposalError)
    (hscore : ∀ point,|(raw point : ℝ)-score point|≤scoreError)
    (henvelope : 1≤envelope) (hbound : ∀ point,max (score point) 0≤(envelope : ℝ))
    (hraw : (∑ point,|weightedMass proposal score point-reference.weight point|)≤rawError)
    (hsmall : rawError≤1/2) :
    TVBound ((uniform (Fin attempts → Tape×(Fin bits → Fin 2))).map
      (positiveDraw decode raw envelope bits attempts fallback)) reference
      ((attempts : ℝ)*(1/(2 : ℝ)^bits+scoreError+proposalError)+
        (Real.exp (-(attempts : ℝ)*(1/2)/(envelope : ℝ))+2*rawError)) := by
  have heR : (0 : ℝ)<envelope := by exact_mod_cast (by omega : 0<envelope)
  have hcoin := positiveCoin_bounds score envelope heR hbound
  rw [positiveDraw,draw_law]
  have hn := RationalAcceptanceCoin.cappedRejection_error ((uniform Tape).map decode)
    (CanonicalMoments.pointLaw fallback) (positiveCoin score envelope) hcoin
    (fun point => max (raw point) 0/(envelope : ℚ)) bits attempts scoreError
    (positiveCoinApprox_error raw score envelope henvelope scoreError hscore)
  have hp := cappedRejection_proposal_tv ((uniform Tape).map decode) proposal
    (positiveCoin score envelope) hcoin (CanonicalMoments.pointLaw fallback) proposalError hproposal attempts
  have hg := globalPositive_capped_tv proposal reference (CanonicalMoments.pointLaw fallback)
    score rawError envelope attempts hraw hsmall heR hbound
  convert (hn.triangle hp).triangle hg using 1
  ring

end
end AFT.RationalRejectionProgram
