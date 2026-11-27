import TwoAxisHelicoid.ActualPrincipalPartRigidity
import TwoAxisHelicoid.GaussQuotientRigidity

namespace TwoAxisHelicoid
open Complex Set Metric

namespace MeromorphicPairInCharts
variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [CompactSpace X] [PreconnectedSpace X] [Nonempty X]

/-- On a compact connected complex curve, equal principal parts of actual
logarithmic Gauss differentials force a single nonzero global multiplier.
Both period vanishing and connectedness after deleting poles are derived. -/
theorem gauss_maps_proportional (D : MeromorphicPairInCharts X) {g₁ g₂ : X → ℂ}
    (hg₁ : ∀ p z, z ∈ ball (chartAt ℂ p p) (D.regularLeft.radius p) →
      (chartAt ℂ p).symm z ∉ chartPoleSet D.left →
      AnalyticAt ℂ (fun w : ℂ => g₁ ((chartAt ℂ p).symm w)) z)
    (hg₂ : ∀ p z, z ∈ ball (chartAt ℂ p p) (D.regularLeft.radius p) →
      (chartAt ℂ p).symm z ∉ chartPoleSet D.left →
      AnalyticAt ℂ (fun w : ℂ => g₂ ((chartAt ℂ p).symm w)) z)
    (hn₁ : ∀ x ∉ chartPoleSet D.left, g₁ x ≠ 0)
    (hn₂ : ∀ x ∉ chartPoleSet D.left, g₂ x ≠ 0)
    (hL : ∀ p z, z ∈ ball (chartAt ℂ p p) (D.regularLeft.radius p) →
      (chartAt ℂ p).symm z ∉ chartPoleSet D.left →
      D.left p z = HolomorphicCoefficientDisks.chartLogDerivative g₁ p z)
    (hR : ∀ p z, z ∈ ball (chartAt ℂ p p) (D.regularLeft.radius p) →
      (chartAt ℂ p).symm z ∉ chartPoleSet D.left →
      D.right p z = HolomorphicCoefficientDisks.chartLogDerivative g₂ p z) :
    ∃ c : ℂ, c ≠ 0 ∧ ∀ x ∉ chartPoleSet D.left, g₂ x = c*g₁ x := by
  have hPL : D.common.difference.ZeroRealAvoidingPeriods (chartPoleSet D.left)ᶜ D.left := by
    intro x c
    rw [c.integral_congr hL]
    exact HolomorphicCoefficientDisks.chartLogDerivative_zero_real_periods hg₁ hn₁ x c
  have hPR : D.common.difference.ZeroRealAvoidingPeriods (chartPoleSet D.left)ᶜ D.right := by
    intro x c
    rw [c.integral_congr hR]
    exact HolomorphicCoefficientDisks.chartLogDerivative_zero_real_periods hg₂ hn₂ x c
  apply D.common.difference.gauss_maps_proportional_of_log_derivative_eq D.poles_finite
    hg₁ hg₂ hn₁ hn₂
  intro p z hz hr
  exact (hR p z hz hr).symm.trans
    ((D.real_normalized_meromorphic_coefficients_equal hPL hPR p hz hr).symm.trans (hL p z hz hr))

end MeromorphicPairInCharts
end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.MeromorphicPairInCharts.gauss_maps_proportional
