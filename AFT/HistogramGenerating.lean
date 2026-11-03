import AFT.Hoeffding
import AFT.MeanOutput

/-! # Ordinary generating polynomials determine the entire finite histogram -/
namespace AFT.HistogramGenerating
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {Color Slot : Type*} [Fintype Color] [Fintype Slot]

/-- Color counts for an arbitrary finite set of physical coordinates. -/
def counts (word : Slot → Color) : Color →₀ ℕ := ∑ slot,Finsupp.single (word slot) 1

omit [Fintype Color] in
theorem counts_apply (word : Slot → Color) (color : Color) :
    counts word color = Fintype.card {slot // word slot=color} := by
  simp only [counts,Finsupp.finset_sum_apply,Finsupp.single_apply]
  simp only [← Finset.card_filter,← Fintype.card_subtype]

def boundedHistogram (N : ℕ) (hcard : Fintype.card Slot≤N) (word : Slot → Color) : Histogram N Color :=
  fun color => ⟨counts word color,by
    rw [counts_apply]
    exact Nat.lt_succ_of_le ((Fintype.card_subtype_le _).trans hcard)⟩

def histogramExponent (N : ℕ) (hist : Histogram N Color) : Color →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun color => (hist color : ℕ)

theorem histogramExponent_injective (N : ℕ) : Function.Injective (histogramExponent (Color:=Color) N) := by
  intro a b hab
  funext color
  apply Fin.ext
  exact DFunLike.congr_fun hab color

@[simp] theorem boundedHistogram_exponent (N : ℕ) (hcard : Fintype.card Slot≤N) (word : Slot → Color) :
    histogramExponent N (boundedHistogram N hcard word)=counts word := by ext color; rfl

omit [Fintype Color] in
theorem boundedHistogram_fin (N : ℕ) (word : Fin N → Color) :
    boundedHistogram N (by simp) word=histogram word := by
  funext color
  apply Fin.ext
  exact counts_apply word color

/-- This is the ordinary (uncentered) full generating polynomial. -/
def generating (law : FiniteDist (Slot → Color)) : MvPolynomial Color ℝ :=
  ∑ word,MvPolynomial.C (law.weight word)*∏ slot,MvPolynomial.X (word slot)

theorem generating_monomial (law : FiniteDist (Slot → Color)) :
    generating law = ∑ word,MvPolynomial.monomial (counts word) (law.weight word) := by
  apply Finset.sum_congr rfl
  intro word _
  rw [counts,MvPolynomial.monomial_sum_index]
  rfl

/-- Each ordinary generating coefficient is the probability of the actual
complete color-count vector, including the zero mass of invalid histograms. -/
theorem generating_coeff (N : ℕ) (hcard : Fintype.card Slot≤N)
    (law : FiniteDist (Slot → Color)) (hist : Histogram N Color) :
    MvPolynomial.coeff (histogramExponent N hist) (generating law)=
      (law.map (boundedHistogram N hcard)).weight hist := by
  rw [generating_monomial,FiniteDist.map_weight]
  simp only [MvPolynomial.coeff_sum,MvPolynomial.coeff_monomial]
  apply Finset.sum_congr rfl
  intro word _
  have he : counts word=histogramExponent N hist ↔ boundedHistogram N hcard word=hist := by
    rw [← boundedHistogram_exponent N hcard word]
    exact (histogramExponent_injective N).eq_iff
  simp only [he]
  split_ifs <;> rfl

/-- Equality of full PGFs gives equality of actual histogram distributions,
even if the coordinate types are different. -/
theorem histogram_law_eq_of_generating_eq {Other : Type*} [Fintype Other]
    (N : ℕ) (hslot : Fintype.card Slot≤N) (hother : Fintype.card Other≤N)
    (first : FiniteDist (Slot → Color)) (second : FiniteDist (Other → Color))
    (h : generating first=generating second) :
    first.map (boundedHistogram N hslot)=second.map (boundedHistogram N hother) := by
  ext hist
  rw [← generating_coeff,← generating_coeff,h]

/-- Finite product Fubini gives the usual product of one-coordinate PGFs. -/
theorem generating_independent (law : Slot → FiniteDist Color) :
    generating (FiniteDist.independent law)=∏ slot,RepresentedPolynomial.profileForm (law slot).weight := by
  change (∑ word : Slot → Color,MvPolynomial.C (∏ slot,(law slot).weight (word slot))*∏ slot,MvPolynomial.X (word slot))=_
  simp only [map_prod,← Finset.prod_mul_distrib,RepresentedPolynomial.profileForm,LinearMap.coe_mk,AddHom.coe_mk]
  exact (Fintype.prod_sum fun slot color => MvPolynomial.C ((law slot).weight color)*MvPolynomial.X color).symm

end
end AFT.HistogramGenerating
