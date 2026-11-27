import TwoAxisHelicoid.MeromorphicRealNormalization
import TwoAxisHelicoid.HeightPathPeriods
import TwoAxisHelicoid.LogDerivativePathPeriods

namespace TwoAxisHelicoid
open Complex Set Filter Metric InnerProductSpace
open scoped Topology

namespace MeromorphicPairInCharts
variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [CompactSpace X] [PreconnectedSpace X]

/-- The height part of fixed-principal-part rigidity. The real periods are
derived from the two single-valued harmonic height functions. -/
theorem harmonic_height_germs_equal (D : MeromorphicPairInCharts X) {H₁ H₂ : X → ℝ}
    (hH₁ : ∀ p z, z ∈ ball (chartAt ℂ p p) (D.regularLeft.radius p) →
      (chartAt ℂ p).symm z ∉ chartPoleSet D.left →
      HarmonicAt (fun w : ℂ => H₁ ((chartAt ℂ p).symm w)) z)
    (hH₂ : ∀ p z, z ∈ ball (chartAt ℂ p p) (D.regularLeft.radius p) →
      (chartAt ℂ p).symm z ∉ chartPoleSet D.left →
      HarmonicAt (fun w : ℂ => H₂ ((chartAt ℂ p).symm w)) z)
    (hL : ∀ p z, z ∈ ball (chartAt ℂ p p) (D.regularLeft.radius p) →
      (chartAt ℂ p).symm z ∉ chartPoleSet D.left →
      D.left p z = HolomorphicCoefficientDisks.chartHeightCoefficient H₁ p z)
    (hR : ∀ p z, z ∈ ball (chartAt ℂ p p) (D.regularLeft.radius p) →
      (chartAt ℂ p).symm z ∉ chartPoleSet D.left →
      D.right p z = HolomorphicCoefficientDisks.chartHeightCoefficient H₂ p z) (p : X) :
    D.left p =ᶠ[𝓝[≠] (chartAt ℂ p p)] D.right p := by
  apply D.real_normalized_meromorphic_germs_equal
  · intro x c
    rw [c.integral_congr hL]
    exact HolomorphicCoefficientDisks.chartHeightCoefficient_zero_real_periods hH₁ x c
  · intro x c
    rw [c.integral_congr hR]
    exact HolomorphicCoefficientDisks.chartHeightCoefficient_zero_real_periods hH₂ x c

/-- The logarithmic Gauss part of fixed-principal-part rigidity. Actual
single-valued nonvanishing Gauss maps supply the zero real periods of `dg/g`;
integer winding is not an additional hypothesis. -/
theorem gauss_logarithmic_germs_equal (D : MeromorphicPairInCharts X) {g₁ g₂ : X → ℂ}
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
      D.right p z = HolomorphicCoefficientDisks.chartLogDerivative g₂ p z) (p : X) :
    D.left p =ᶠ[𝓝[≠] (chartAt ℂ p p)] D.right p := by
  apply D.real_normalized_meromorphic_germs_equal
  · intro x c
    rw [c.integral_congr hL]
    exact HolomorphicCoefficientDisks.chartLogDerivative_zero_real_periods hg₁ hn₁ x c
  · intro x c
    rw [c.integral_congr hR]
    exact HolomorphicCoefficientDisks.chartLogDerivative_zero_real_periods hg₂ hn₂ x c

end MeromorphicPairInCharts
end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.MeromorphicPairInCharts.harmonic_height_germs_equal
#print axioms TwoAxisHelicoid.MeromorphicPairInCharts.gauss_logarithmic_germs_equal
