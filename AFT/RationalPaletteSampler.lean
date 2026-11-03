import AFT.RationalPositiveNormalize
import AFT.FiniteProductVariation
import AFT.RecordJointRepair

/-! # Executable positive normalization on any nonempty finite palette -/
namespace AFT.RationalPaletteSampler
open scoped BigOperators

/-- The match removes only the impossible empty-palette branch. The
nonempty program is the checked rational positive normalization sampler. -/
def draw : (colors : ℕ) → (hcolors : 0<colors) → (raw : Fin colors → ℚ) → (bits : ℕ) →
    (Fin (bits+colors+1) → Fin 2) → Fin colors
  | 0,h,_,_,_ => False.elim (Nat.not_lt_zero 0 h)
  | _colors+1,_,raw,bits,word => RationalNumerics.positiveNormalizeDraw raw bits word

def legalize {State : Type*} (allowed : State → Prop) [DecidablePred allowed]
    (fallback point : State) : State := if allowed point then point else fallback

def legalDraw (colors : ℕ) (hcolors : 0<colors) (raw : Fin colors → ℚ) (bits : ℕ)
    (allowed : Fin colors → Prop) [DecidablePred allowed] (fallback : Fin colors)
    (word : Fin (bits+colors+1) → Fin 2) : Fin colors :=
  legalize allowed fallback (draw colors hcolors raw bits word)

theorem legalDraw_allowed (colors : ℕ) (hcolors : 0<colors) (raw : Fin colors → ℚ) (bits : ℕ)
    (allowed : Fin colors → Prop) [DecidablePred allowed] (fallback : Fin colors)
    (hfallback : allowed fallback) (word : Fin (bits+colors+1) → Fin 2) :
    allowed (legalDraw colors hcolors raw bits allowed fallback word) := by
  unfold legalDraw legalize
  split_ifs with h
  · exact h
  · exact hfallback

noncomputable section
open FiniteDist
open scoped Classical
set_option backward.isDefEq.respectTransparency false

theorem draw_l1 (colors : ℕ) (hcolors : 0<colors) (raw : Fin colors → ℚ) (bits : ℕ)
    (reference : FiniteDist (Fin colors)) (error : ℝ)
    (herror : (∑ color,|(raw color : ℝ)-reference.weight color|)≤error) (hsmall : error≤1/2) :
    (∑ color,|((uniform (Fin (bits+colors+1) → Fin 2)).map
      (draw colors hcolors raw bits)).weight color-reference.weight color|)≤1/(2 : ℝ)^bits+4*error := by
  cases colors with
  | zero => omega
  | succ colors =>
    have hr := RationalNumerics.positiveNormalizeDraw_l1 raw bits
    have hp := RationalNumerics.positiveProgramLaw_l1 raw reference error herror hsmall
    rw [FiniteTicketSampler.independent_fair_bits_uniform] at hr
    apply le_trans _ (add_le_add hr hp)
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro color _
    exact abs_sub_le _ ((RationalNumerics.positiveProgramLaw raw).weight color) _

/-- Returning a fixed legal fallback on numerically introduced illegal
atoms contracts L1, since the exact reference has no such atoms. -/
theorem legalize_l1 {State : Type*} [Fintype State] (approximation reference : FiniteDist State)
    (allowed : State → Prop) [DecidablePred allowed] (fallback : State)
    (hsupport : ∀ point,reference.weight point≠0 → allowed point) :
    (∑ point,|(approximation.map (legalize allowed fallback)).weight point-reference.weight point|)≤
      ∑ point,|approximation.weight point-reference.weight point| := by
  have he : reference.map (legalize allowed fallback)=reference := by
    have hh := map_eq_of_support reference (legalize allowed fallback) id (fun point hp => by
      simp only [legalize,if_pos (hsupport point hp),id_eq])
    apply hh.trans
    ext point
    simp
  simpa only [he] using l1_map_le approximation reference (legalize allowed fallback)

theorem legalDraw_l1 (colors : ℕ) (hcolors : 0<colors) (raw : Fin colors → ℚ) (bits : ℕ)
    (allowed : Fin colors → Prop) [DecidablePred allowed] (fallback : Fin colors)
    (reference : FiniteDist (Fin colors)) (error : ℝ)
    (hsupport : ∀ color,reference.weight color≠0 → allowed color)
    (herror : (∑ color,|(raw color : ℝ)-reference.weight color|)≤error) (hsmall : error≤1/2) :
    (∑ color,|((uniform (Fin (bits+colors+1) → Fin 2)).map
      (legalDraw colors hcolors raw bits allowed fallback)).weight color-reference.weight color|)≤
      1/(2 : ℝ)^bits+4*error := by
  have hh := legalize_l1 ((uniform (Fin (bits+colors+1) → Fin 2)).map (draw colors hcolors raw bits))
    reference allowed fallback hsupport
  rw [FiniteDist.map_map] at hh
  exact hh.trans (draw_l1 colors hcolors raw bits reference error herror hsmall)

end
end AFT.RationalPaletteSampler
