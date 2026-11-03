import AFT.NumericalFamilyRules
import AFT.PairCoreProgram

/-! Canonicalization preserves uniform negligible errors in explicit pair arrays. -/
namespace AFT.RationalNumerics
open Filter
open scoped BigOperators Topology
noncomputable section
variable {Color Context : ℕ → Type*} [∀ n,Fintype (Color n)]

theorem UniformRationalApproximation.canonicalPair
    {reference : (n : ℕ) → Color n → ℚ} {trueReference : (n : ℕ) → Color n → ℝ}
    {mass : (n : ℕ) → Context n × Color n × Color n → ℚ}
    {trueMass : (n : ℕ) → Context n × Color n × Color n → ℝ}
    (href : UniformRationalApproximation reference trueReference)
    (hmass : UniformRationalApproximation mass trueMass)
    (C : ℝ) (degree : ℕ) (hC : 0 ≤ C)
    (hcard : ∀ᶠ n : ℕ in atTop,(Fintype.card (Color n) : ℝ) ≤ C*(n : ℝ)^degree) :
    UniformRationalApproximation
      (fun n (point : Context n × Color n × Color n) => rationalCanonicalPair (reference n)
        (fun first second => mass n (point.1,first,second)) point.2.1 point.2.2)
      (fun n point => SafePair.canonicalPair (trueReference n)
        (fun first second => trueMass n (point.1,first,second)) point.2.1 point.2.2) := by
  have hfirst := href.reindex (fun n (point : Context n × Color n × Color n) => point.2.1)
  have hsecond := href.reindex (fun n (point : Context n × Color n × Color n) => point.2.2)
  have hcol := (hmass.reindex (fun n (point : Color n × (Context n × Color n × Color n)) =>
    (point.2.1,point.1,point.2.2.2))).sum C degree hC hcard
  have hrow := (hmass.reindex (fun n (point : Color n × (Context n × Color n × Color n)) =>
    (point.2.1,point.2.2.1,point.1))).sum C degree hC hcard
  have htotalInner := (hmass.reindex (fun n (point : Color n × (Color n × (Context n × Color n × Color n))) =>
    (point.2.2.1,point.2.1,point.1))).sum C degree hC hcard
  have htotal := htotalInner.sum C degree hC hcard
  exact ((hmass.sub (hfirst.mul hcol)).sub (hrow.mul hsecond)).add ((htotal.mul hfirst).mul hsecond)

end
end AFT.RationalNumerics
